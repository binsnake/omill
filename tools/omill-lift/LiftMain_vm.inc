  std::shared_ptr<omill::VMTraceMap> vm_graph;
  std::vector<omill::NativeCallInfo> native_call_infos;
  if (vm_mode && !RawBinary) {
    vm_graph = std::make_shared<omill::VMTraceMap>(vm_entry_va, vm_exit_va);

    struct VMTraceLiftKey {
      uint64_t handler_va = 0;
      uint64_t incoming_hash = 0;
    };

    std::vector<VMTraceLiftKey> trace_work_items;
    std::vector<uint64_t> native_call_vas;
    llvm::DenseSet<uint64_t> seen_vm_trace_work;
    llvm::DenseMap<uint64_t, llvm::SmallVector<uint64_t, 2>>
        handler_trace_hashes;
    std::optional<uint64_t> imported_entry_seed_hash;

    // Demerging must preserve distinct incoming hashes for the same handler VA.
    // Deduplicating only on handler_va would collapse merged ops back together
    // before clone generation even begins, so the lift worklist is keyed by
    // (handler_va, incoming_hash).
    auto recordTraceWorkItem = [&](uint64_t handler_va, uint64_t incoming_hash) {
      uint64_t key = incoming_hash ^
                     (handler_va + 0x9E3779B97F4A7C15ull +
                      (incoming_hash << 6) + (incoming_hash >> 2));
      if (seen_vm_trace_work.insert(key).second)
        trace_work_items.push_back({handler_va, incoming_hash});

      auto &hashes = handler_trace_hashes[handler_va];
      if (std::find(hashes.begin(), hashes.end(), incoming_hash) == hashes.end())
        hashes.push_back(incoming_hash);
    };
    auto rememberFlatTrace = [&](const auto &records) {
      for (const auto &record : records)
        recordTraceWorkItem(record.handler_va, record.incoming_hash);
    };

    auto rememberRawTrace = [&](const auto &entries) {
      for (const auto &entry : entries)
        recordTraceWorkItem(entry.handler_va, entry.incoming_hash);
    };

    auto mergeSupplementalWrapperTrace = [&](StringRef primary_trace_path) {
      if (!VMTraceJSON.getNumOccurrences())
        return;

      SmallString<260> supplemental_path(primary_trace_path);
      sys::path::remove_filename(supplemental_path);
      sys::path::append(supplemental_path, "vm_trace_records.json");
      if (supplemental_path == primary_trace_path)
        return;
      if (!sys::fs::exists(supplemental_path))
        return;

      auto supplemental_graph = parseExternalVMTrace(supplemental_path);
      if (!supplemental_graph)
        return;

      unsigned merged_records = 0;
      llvm::DenseSet<uint64_t> merged_wrappers;
      for (uint64_t native_va : native_call_vas) {
        auto records = supplemental_graph->getTraceRecords(native_va);
        if (records.empty())
          continue;
        merged_wrappers.insert(native_va);
        for (const auto &record : records) {
          vm_graph->recordTrace(record);
          recordTraceWorkItem(record.handler_va, record.incoming_hash);
          ++merged_records;
        }
      }

      if (merged_records > 0) {
        errs() << "VMTraceMap: merged " << merged_records
               << " supplemental wrapper trace record(s) from "
               << supplemental_path << " for " << merged_wrappers.size()
               << " traced native target(s)\n";
      }
    };

    auto tagExactTraceHash = [&](llvm::Function &F, uint64_t handler_va) {
      auto it = handler_trace_hashes.find(handler_va);
      if (it == handler_trace_hashes.end() || it->second.size() != 1) {
        F.removeFnAttr("omill.vm_trace_in_hash");
        return;
      }
      F.addFnAttr("omill.vm_trace_in_hash",
                  llvm::utohexstr(it->second.front()));
    };
    // --- Populate vm_graph and trace_work_items from either external JSON
    //     or the built-in emulator. ---
    if (VMTraceJSON.getNumOccurrences()) {
      // External trace: load pre-computed VMTraceRecords from JSON.
      auto ext_graph = parseExternalVMTrace(VMTraceJSON);
      if (!ext_graph)
        return fail(1, "failed to parse --vm-trace-json");
      vm_graph = std::move(ext_graph);

      // Populate lift work items from the imported trace records.
      // Also collect native call targets (vmenter wrappers) that need
      // to be lifted as separate VM functions.
      for (const auto &handler_va : vm_graph->handlerEntries()) {
        auto records = vm_graph->getTraceRecords(handler_va);
        for (const auto &rec : records) {
          if (!imported_entry_seed_hash.has_value())
            imported_entry_seed_hash = rec.incoming_hash;
          recordTraceWorkItem(rec.handler_va, rec.incoming_hash);
          if (rec.native_target_va != 0) {
            native_call_vas.push_back(rec.native_target_va);
          }
        }
      }
      mergeSupplementalWrapperTrace(VMTraceJSON.getValue());
      events.emitInfo("vm_trace_imported", "external VM trace loaded",
                      {{"records",
                        static_cast<int64_t>(trace_work_items.size())},
                       {"source", VMTraceJSON.getValue()}});
    } else {
      omill::VMTraceEmulator solver(pe.memory_map, pe.image_base,
                                    vm_entry_va, vm_exit_va);

      // Set the handler segment range (seg006 bounds).
      uint64_t seg_start = vm_entry_va;
      uint64_t seg_end = vm_entry_va + 0x2000000;
      pe.memory_map.forEachRegion(
          [&](uint64_t base, const uint8_t *, size_t size) {
            if (vm_entry_va >= base && vm_entry_va < base + size) {
              seg_start = base;
              seg_end = base + size;
            }
          });
      solver.setHandlerSegmentRange(seg_start, seg_end);

      // Trace from the entry wrapper. Use vm_wrapper_va (which defaults to
      // func_va) so that --vm-wrapper can point to the actual lea/call pattern
      // even when --va is an outer function like DriverEntry.
      auto trace = solver.traceFromWrapper(vm_wrapper_va);
      if (!trace.empty()) {
        vm_graph->mergeTraceResults(solver);
        auto flat =
            vm_graph->followFlatTrace(vm_wrapper_va, trace.front().incoming_hash);
        events.emitInfo("vm_trace_built", "vm flat trace built",
                        {{"handlers", static_cast<int64_t>(flat.records.empty()
                                                           ? trace.size()
                                                           : flat.records.size())},
                         {"complete", flat.completed() ? int64_t{1} : int64_t{0}}});
        if (!flat.records.empty()) {
          rememberFlatTrace(flat.records);
        } else {
          rememberRawTrace(trace);
        }
      }

      // Trace from additional auto-detected wrappers.
      for (size_t wi = 1; wi < auto_detected_wrappers.size(); ++wi) {
        uint64_t extra_wrapper = auto_detected_wrappers[wi].second;
        auto extra_trace = solver.traceFromWrapper(extra_wrapper);
        if (!extra_trace.empty()) {
          vm_graph->mergeTraceResults(solver);
          auto flat = vm_graph->followFlatTrace(extra_wrapper,
                                                extra_trace.front().incoming_hash);
          if (!flat.records.empty()) {
            rememberFlatTrace(flat.records);
          } else {
            rememberRawTrace(extra_trace);
          }
        }
      }

      // Extract native call targets before the emulator goes out of scope.
      native_call_vas = solver.nativeCallTargets();
      native_call_infos = solver.nativeCallInfos();
      errs() << "Trace emulator captured " << native_call_infos.size()
             << " native call infos, " << native_call_vas.size()
             << " unique targets\n";
      for (unsigned i = 0; i < native_call_infos.size(); ++i) {
        errs() << "  [" << i << "] target=0x"
               << Twine::utohexstr(native_call_infos[i].target_va)
               << " from handler=0x"
               << Twine::utohexstr(native_call_infos[i].handler_va)
               << " R12=0x"
               << Twine::utohexstr(native_call_infos[i].r12_base)
               << " vmctx_size="
               << native_call_infos[i].vmcontext_snapshot.size()
               << "\n";
      }
    }

    auto seedWrapperTraceHash = [&](uint64_t wrapper_va) {
      if (!imported_entry_seed_hash.has_value())
        return;
      auto *fn = module->getFunction("sub_" + Twine::utohexstr(wrapper_va).str());
      if (!fn || fn->isDeclaration())
        return;
      fn->addFnAttr("omill.vm_trace_in_hash",
                    llvm::utohexstr(*imported_entry_seed_hash));
    };

    if (VMTraceJSON.getNumOccurrences()) {
      seedWrapperTraceHash(vm_wrapper_va);
      for (auto &[thunk_va, wrapper_va] : auto_detected_wrappers)
        seedWrapperTraceHash(wrapper_va);
    }

    if (lift_db && lift_db_builder) {
      std::vector<uint64_t> overlay_roots;
      std::vector<omill::StaticLiftOverlayKey> overlay_keys;
      overlay_roots.reserve(trace_work_items.size());
      overlay_keys.reserve(trace_work_items.size());
      for (const auto &item : trace_work_items) {
        overlay_roots.push_back(item.handler_va);
        overlay_keys.push_back({item.handler_va, item.incoming_hash});
      }
      llvm::sort(overlay_roots);
      overlay_roots.erase(std::unique(overlay_roots.begin(), overlay_roots.end()),
                          overlay_roots.end());

      lift_db_builder->buildFunctions(overlay_roots, *lift_db);
      lift_db_builder->importTraceMapAsOverlays(*vm_graph, overlay_keys,
                                                *lift_db);

      if (LiftDBOut.getNumOccurrences() > 0) {
        std::string lift_db_error;
        if (!omill::SaveLiftDatabaseToDirectory(*lift_db, LiftDBOut.getValue(),
                                                &lift_db_error)) {
          return fail(1, "failed to write --lift-db-out: " + lift_db_error);
        }
      }
    }

    // Lift only trace-reachable handlers.
    unsigned lifted_count = 0;
    unsigned failed_count = 0;
    unsigned skipped_count = 0;
    for (const auto &trace_item : trace_work_items) {
      uint64_t handler_va = trace_item.handler_va;
      // Skip if already lifted (e.g. func_va or vmenter/vmexit).
      std::string name = "sub_" + Twine::utohexstr(handler_va).str();
      if (auto *existing = module->getFunction(name)) {
        if (!existing->isDeclaration()) {
          // Tag existing function as a VM handler.
          existing->addFnAttr("omill.vm_handler");
          tagExactTraceHash(*existing, handler_va);
          // The VM wrapper is a boundary function: handlers get inlined
          // INTO it, but it must NOT be inlined into callers like
          // DriverEntry.  Tag it so VMHandlerInlinerPass excludes it
          // from the handler_set while keeping it in
          // VMDispatchResolution's scope (which requires vm_handler).
          if (handler_va == vm_wrapper_va) {
            existing->addFnAttr("omill.vm_wrapper");
          } else {
            for (auto &[tv, wv] : auto_detected_wrappers) {
              if (handler_va == wv) {
                existing->addFnAttr("omill.vm_wrapper");
                break;
              }
            }
          }
          continue;
        }
      }

      // Probe decode: skip handler VAs where the first instruction can't
      // be decoded.  These are typically decoy dispatch patterns in
      // obfuscated code with garbage RVAs pointing mid-instruction.
      {
        uint8_t probe_buf[15];
        if (!pe.memory_map.read(handler_va, probe_buf, sizeof(probe_buf))) {
          ++skipped_count;
          continue;
        }
        std::string_view probe_bytes(
            reinterpret_cast<const char *>(probe_buf), sizeof(probe_buf));
        remill::Instruction probe_inst;
        if (!arch->DecodeInstruction(handler_va, probe_bytes, probe_inst,
                                     arch->CreateInitialContext())) {
          ++skipped_count;
          continue;
        }
      }

      if (projection_lifter && projection_lifter->LiftFunction(handler_va)) {
        ++lifted_count;
        // Tag the lifted function.
        if (auto *fn = module->getFunction(name)) {
          fn->addFnAttr("omill.vm_handler");
          tagExactTraceHash(*fn, handler_va);
        } else {
          errs() << "  [WARN] Lift succeeded for 0x"
                 << Twine::utohexstr(handler_va)
                 << " but function " << name << " not found in module\n";
        }
      } else {
        errs() << "  [WARN] Lift FAILED for 0x"
               << Twine::utohexstr(handler_va) << "\n";
        ++failed_count;
      }
    }

    errs() << "VM bulk lift: " << lifted_count << " handlers lifted";
    if (skipped_count > 0)
      errs() << ", " << skipped_count << " skipped (bad VA)";
    if (failed_count > 0)
      errs() << ", " << failed_count << " failed";
    errs() << "\n";
    events.emitInfo("vm_bulk_lift_completed", "vm handler bulk lift complete",
                    {{"lifted", static_cast<int64_t>(lifted_count)},
                     {"skipped", static_cast<int64_t>(skipped_count)},
                     {"failed", static_cast<int64_t>(failed_count)}});

    // Lift native functions called through vmexit→call→vmentry.
    // These are regular (non-VM) functions that the VM handlers call
    // through temporary VM exit.  Lifting them enables ResolveIntToPtrCalls
    // to resolve the constant inttoptr calls after ABI recovery.
    if (!native_call_vas.empty()) {
      unsigned native_lifted = 0;
      auto tagTraceNativeTarget = [&](uint64_t native_va) {
        std::string tagged_name = "sub_" + Twine::utohexstr(native_va).str();
        if (auto *fn = module->getFunction(tagged_name)) {
          if (!fn->isDeclaration()) {
            fn->addFnAttr("omill.trace_native_target", "1");
            fn->addFnAttr(llvm::Attribute::NoInline);
          }
        }
      };
      for (uint64_t native_va : native_call_vas) {
        std::string name = "sub_" + Twine::utohexstr(native_va).str();
        if (auto *existing = module->getFunction(name)) {
          if (!existing->isDeclaration()) {
            tagTraceNativeTarget(native_va);
            continue;
          }
        }

        // Probe decode — skip if first instruction can't be decoded.
        {
          uint8_t probe_buf[15];
          if (!pe.memory_map.read(native_va, probe_buf, sizeof(probe_buf)))
            continue;
          std::string_view probe_bytes(
              reinterpret_cast<const char *>(probe_buf), sizeof(probe_buf));
          remill::Instruction probe_inst;
          if (!arch->DecodeInstruction(native_va, probe_bytes, probe_inst,
                                       arch->CreateInitialContext()))
            continue;
        }

        if (projection_lifter && projection_lifter->LiftFunction(native_va)) {
          ++native_lifted;
          tagTraceNativeTarget(native_va);
          // If this native VA is also in the trace work items (i.e. it's
          // a vmenter wrapper for an inner VM), tag it as vm_handler +
          // vm_wrapper so VMDispatchResolution can process it and
          // VMHandlerInliner won't inline it into callers.
          std::string name = "sub_" + Twine::utohexstr(native_va).str();
          if (auto *fn = module->getFunction(name)) {
            if (vm_graph && vm_graph->isVMHandler(native_va)) {
              fn->addFnAttr("omill.vm_handler");
              fn->addFnAttr("omill.vm_wrapper");
            }
          }
        }
      }
      errs() << "VM native lift: " << native_lifted << " native functions"
             << " (from " << native_call_vas.size() << " targets)\n";
    }

    // Tag native call targets that are vmenter wrappers (inner VM entry
    // points) so VMHandlerInliner preserves them as call boundaries.
    // Detection: follow jmp-thunks from the native VA, probe the resolved
    // body for [lea rsp,... / sub rsp,...] + call vmentry.
    if (!native_call_vas.empty() && vm_entry_va != 0) {
      unsigned wrapper_tagged = 0;
      for (uint64_t native_va : native_call_vas) {
        std::string name = "sub_" + Twine::utohexstr(native_va).str();
        auto *fn = module->getFunction(name);
        if (!fn || fn->isDeclaration())
          continue;
        // Already tagged as wrapper (e.g. matches vm_wrapper_va)?
        if (fn->hasFnAttribute("omill.vm_wrapper"))
          continue;
        // Follow jmp-thunks to the body.
        uint64_t resolved = native_va;
        for (int hop = 0; hop < 4; ++hop) {
          uint8_t tbuf[16];
          if (!pe.memory_map.read(resolved, tbuf, sizeof(tbuf)))
            break;
          if (tbuf[0] == 0xE9) {
            int32_t rel;
            std::memcpy(&rel, &tbuf[1], 4);
            resolved = resolved + 5 + static_cast<int64_t>(rel);
          } else if (tbuf[0] == 0xEB) {
            int8_t rel = static_cast<int8_t>(tbuf[1]);
            resolved = resolved + 2 + rel;
          } else {
            break;
          }
        }
        // Probe the resolved body for the wrapper pattern:
        //   optional lea rsp,[rsp-N] / sub rsp,N
        //   E8 <rel32>  (call near vmentry)
        uint8_t probe[32];
        if (!pe.memory_map.read(resolved, probe, sizeof(probe)))
          continue;
        unsigned p = 0;
        if (p + 8 <= sizeof(probe) &&
            probe[p] == 0x48 && probe[p+1] == 0x8D &&
            probe[p+2] == 0xA4 && probe[p+3] == 0x24) {
          p += 8;
        } else if (p + 5 <= sizeof(probe) &&
                   probe[p] == 0x48 && probe[p+1] == 0x8D &&
                   probe[p+2] == 0x64 && probe[p+3] == 0x24) {
          p += 5;
        } else if (p + 7 <= sizeof(probe) &&
                   probe[p] == 0x48 && probe[p+1] == 0x81 &&
                   probe[p+2] == 0xEC) {
          p += 7;
        }
        if (p + 5 > sizeof(probe) || probe[p] != 0xE8)
          continue;
        int32_t crel;
        std::memcpy(&crel, &probe[p+1], 4);
        uint64_t ctarget = resolved + p + 5 + static_cast<int64_t>(crel);
        // Accept if the call target is the vmentry, the vm wrapper, or
        // within 0x1000 of either.
        bool near_entry = (ctarget >= vm_entry_va - 0x1000 &&
                           ctarget <= vm_entry_va + 0x1000);
        bool near_wrapper = (vm_wrapper_va != 0 &&
                             ctarget >= vm_wrapper_va - 0x1000 &&
                             ctarget <= vm_wrapper_va + 0x1000);
        if (!near_entry && !near_wrapper)
          continue;
        // This native target is a vmenter wrapper.  Tag it so
        // VMHandlerInliner preserves it as a call boundary.
        fn->addFnAttr("omill.vm_wrapper");
        if (!fn->hasFnAttribute("omill.vm_handler"))
          fn->addFnAttr("omill.vm_handler");
        ++wrapper_tagged;
        errs() << "Native target 0x" << Twine::utohexstr(native_va)
               << " is vmenter wrapper (body 0x"
               << Twine::utohexstr(resolved) << ")\n";
      }
      if (wrapper_tagged > 0)
        errs() << "Tagged " << wrapper_tagged
               << " native targets as vmenter wrappers\n";
    }

    // Fix DeclareLiftedFunction naming collisions (sub_X.N → sub_X).
    // Must happen BEFORE setting attributes on vmentry/vmexit, because
    // the fix erases declarations (which may hold attributes from the
    // chain handler loop above) and renames definitions (which don't).
    for (auto &F : llvm::make_early_inc_range(*module)) {
      if (!F.isDeclaration())
        continue;
      auto fname = F.getName();
      if (!fname.starts_with("sub_"))
        continue;
      for (int i = 1; i <= 20; ++i) {
        std::string def_name = (fname + "." + Twine(i)).str();
        if (auto *def = module->getFunction(def_name)) {
          if (!def->isDeclaration()) {
            F.replaceAllUsesWith(def);
            F.eraseFromParent();
            def->setName(fname);
            break;
          }
        }
      }
    }

    bool verbose_vm_demerge = (std::getenv("OMILL_VM_VERBOSE") != nullptr);
    unsigned demerged_clone_count = 0;
    for (auto &[handler_va, hashes] : handler_trace_hashes) {
      if (verbose_vm_demerge) {
        errs() << "VM demerge candidate 0x" << Twine::utohexstr(handler_va)
               << " hashes=" << hashes.size() << "\n";
      }
      if (hashes.size() <= 1)
        continue;

      bool is_vm_wrapper_handler = (handler_va == vm_wrapper_va) ||
                                   (handler_va == vm_entry_va) ||
                                   (handler_va == vm_exit_va);
      if (!is_vm_wrapper_handler) {
        for (auto &[tv, wv] : auto_detected_wrappers) {
          if (handler_va == wv) {
            is_vm_wrapper_handler = true;
            break;
          }
        }
      }
      if (is_vm_wrapper_handler) {
        if (verbose_vm_demerge) {
          errs() << "  skip wrapper-like handler 0x"
                 << Twine::utohexstr(handler_va) << "\n";
        }
        continue;
      }

      auto *base_fn = module->getFunction(omill::liftedFunctionName(handler_va));
      if (!base_fn || base_fn->isDeclaration()) {
        if (verbose_vm_demerge) {
          errs() << "  missing lifted base for 0x"
                 << Twine::utohexstr(handler_va) << "\n";
        }
        continue;
      }

      for (uint64_t incoming_hash : hashes) {
        std::string clone_name =
            omill::demergedHandlerCloneName(handler_va, incoming_hash);
        if (module->getFunction(clone_name))
          continue;

        llvm::ValueToValueMapTy VMap;
        auto *clone = llvm::CloneFunction(base_fn, VMap);
        clone->setName(clone_name);
        clone->setLinkage(llvm::GlobalValue::InternalLinkage);
        clone->addFnAttr("omill.vm_handler");
        clone->addFnAttr("omill.vm_demerged_clone", "1");
        clone->addFnAttr("omill.vm_trace_in_hash",
                         llvm::utohexstr(incoming_hash));
        ++demerged_clone_count;

        if (verbose_vm_demerge) {
          errs() << "Demerged VM handler clone " << clone_name
                 << " from 0x" << Twine::utohexstr(handler_va)
                 << " hash=0x" << Twine::utohexstr(incoming_hash) << "\n";
        }
      }
    }
    if (demerged_clone_count > 0) {
      errs() << "VM demerge: materialized " << demerged_clone_count
             << " hash-keyed handler clones\n";
      if (events.enabled()) {
        events.emitInfo("vm_demerge_materialized",
                        "vm demerged handler clones materialized",
                        {{"clones", static_cast<int64_t>(demerged_clone_count)}});
      }
    }


    // After naming collisions are fixed, tag vmentry/vmexit as vm_handler
    // and set internal linkage.  Must happen AFTER the naming fix because
    // DeclareLiftedFunction creates sub_X.1 definitions for existing sub_X
    // declarations; the fix erases the declaration (losing any attributes
    // we set) and renames the definition.
    //
    // vmentry must NOT get AlwaysInline.  If inlined at Phase 0, its
    // __remill_function_return ends up inside DriverEntry; LowerFunctionReturn
    // (Phase 3b) converts it to `ret`, creating an early return that kills
    // DriverEntry's continuation code (hash computation + dispatch to the
    // first handler).  Instead, vmentry is tagged omill.vm_handler so
    // VMHandlerInlinerPass inlines it at Phase 3.56 — by that point
    // LowerFunctionReturn has already converted vmentry's return to a plain
    // `ret`, and LLVM's InlineFunction replaces it with a branch to the
    // continuation block.  The vmcontext alloca then lands on DriverEntry's
    // stack (fixing the dangling-pointer / 0xCC sentinel issue).
    if (auto *fn = module->getFunction(
            "sub_" + Twine::utohexstr(vm_entry_va).str())) {
      fn->addFnAttr("omill.vm_handler");
      fn->setLinkage(llvm::GlobalValue::InternalLinkage);
      // Tag direct callees of vmentry as vm_handlers too — they're
      // internal helpers (PIC relocation, etc.) that only make sense
      // in the caller's stack context and should be inlined into vmentry.
      for (auto &BB : *fn) {
        for (auto &I : BB) {
          if (auto *call = dyn_cast<CallInst>(&I)) {
            if (auto *callee = call->getCalledFunction()) {
              if (callee->getName().starts_with("sub_") &&
                  !callee->isDeclaration()) {
                callee->addFnAttr("omill.vm_handler");
                callee->setLinkage(llvm::GlobalValue::InternalLinkage);
              }
            }
          }
        }
      }
    } else {
      // vm_entry function not found at its exact VA — likely a thunk/E9
      // chain was resolved by remill, folding the vm_entry code into the
      // thunk's function.  Find functions that contain __remill_jump
      // (i.e., the unresolved indirect jump from the vm_enter tail) and tag
      // them as vm_handlers so VMDispatchResolution can resolve them.
      // At this point the passes haven't run yet, so the intrinsic is still
      // __remill_jump (later lowered to __omill_dispatch_jump).
      auto *jump_fn = module->getFunction("__remill_jump");
      if (jump_fn) {
        for (auto *user : jump_fn->users()) {
          if (auto *call = dyn_cast<CallInst>(user)) {
            auto *parent = call->getFunction();
            if (parent && !parent->isDeclaration() &&
                parent->getName().starts_with("sub_") &&
                !parent->hasFnAttribute("omill.vm_handler")) {
              parent->addFnAttr("omill.vm_handler");
              parent->addFnAttr("omill.vm_wrapper");
              parent->setLinkage(llvm::GlobalValue::InternalLinkage);
              errs() << "VM thunk fixup: tagged " << parent->getName()
                     << " as vm_handler+vm_wrapper (thunk-resolved vmenter)\n";
              // Also tag its callees
              for (auto &BB : *parent) {
                for (auto &I : BB) {
                  if (auto *inner_call = dyn_cast<CallInst>(&I)) {
                    if (auto *callee = inner_call->getCalledFunction()) {
                      if (callee->getName().starts_with("sub_") &&
                          !callee->isDeclaration() &&
                          !callee->hasFnAttribute("omill.vm_handler")) {
                        callee->addFnAttr("omill.vm_handler");
                        callee->setLinkage(llvm::GlobalValue::InternalLinkage);
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    if (vm_exit_va != 0) {
      if (auto *fn = module->getFunction(
              "sub_" + Twine::utohexstr(vm_exit_va).str())) {
        fn->addFnAttr("omill.vm_handler");
        fn->setLinkage(llvm::GlobalValue::InternalLinkage);
      }
    }
  }

  if (DumpIR) {
    std::error_code ec;
    raw_fd_ostream os("before.ll", ec, sys::fs::OF_Text);
    if (!ec) {
      module->print(os, nullptr);
      errs() << "Wrote before.ll\n";
    }
  }

  // Set up pass timing and verification instrumentation.
  PassInstrumentationCallbacks PIC;
  TimePassesHandler TimingHandler(OmillTimePasses);
  TimingHandler.registerCallbacks(PIC);

  struct PassTimingFrame {
    std::string pass_name;
    std::string ir_kind;
    std::string ir_name;
    const void *ir_ptr = nullptr;
    std::chrono::steady_clock::time_point started_at;
  };
  llvm::SmallVector<PassTimingFrame, 32> pass_timing_stack;

  auto describeIRUnit = [](Any IR) {
    std::pair<std::string, std::string> desc{"unknown", ""};
    if (const auto **F = any_cast<const Function *>(&IR)) {
      desc.first = "function";
      desc.second = (*F)->getName().str();
    } else if (const auto **MPtr = any_cast<const Module *>(&IR)) {
      desc.first = "module";
      desc.second = (*MPtr)->getModuleIdentifier();
    } else if (const auto **L = any_cast<const Loop *>(&IR)) {
      desc.first = "loop";
      desc.second = (*L)->getHeader()->getParent()->getName().str();
    }
    return desc;
  };

  auto irPointer = [](Any IR) -> const void * {
    if (const auto **F = any_cast<const Function *>(&IR))
      return *F;
    if (const auto **MPtr = any_cast<const Module *>(&IR))
      return *MPtr;
    if (const auto **L = any_cast<const Loop *>(&IR))
      return *L;
    return nullptr;
  };

  auto shouldEmitPassTiming = [&](StringRef PassName) {
    if (!events.enabled() || !events.detailed())
      return false;
    if (PassName.starts_with("PassManager") || PassName.contains("Adaptor"))
      return false;
    return true;
  };

  PIC.registerBeforeNonSkippedPassCallback(
      [&](StringRef PassName, Any IR) {
        if (!shouldEmitPassTiming(PassName))
          return;
        auto [ir_kind, ir_name] = describeIRUnit(IR);
        pass_timing_stack.push_back(
            {PassName.str(), std::move(ir_kind), std::move(ir_name),
             irPointer(IR), std::chrono::steady_clock::now()});
      });

  if (events.enabled()) {
    PIC.registerAfterPassCallback([&events](StringRef PassName, Any,
                                            const PreservedAnalyses &) {
      if (PassName.contains("PhaseMarkerPass")) {
        events.emitInfo("pipeline_phase_boundary", "phase boundary",
                        {{"pass", PassName.str()}});
      } else if (events.detailed() && PassName.contains("omill")) {
        events.emitInfo("pipeline_pass", "pass completed",
                        {{"pass", PassName.str()}});
      }
    });
    PIC.registerAfterPassCallback(
        [&](StringRef PassName, Any IR, const PreservedAnalyses &) {
          if (!shouldEmitPassTiming(PassName) || pass_timing_stack.empty())
            return;
          auto ir_ptr = irPointer(IR);
          for (auto it = pass_timing_stack.end(); it != pass_timing_stack.begin();) {
            --it;
            if (it->pass_name != PassName.str() || it->ir_ptr != ir_ptr)
              continue;
            auto duration_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                                   std::chrono::steady_clock::now() -
                                   it->started_at)
                                   .count();
            events.emitInfo("pipeline_pass_timing", "pass timing",
                            {{"pass", it->pass_name},
                             {"ir_kind", it->ir_kind},
                             {"ir_name", it->ir_name},
                             {"duration_ms",
                              static_cast<int64_t>(duration_ms)}});
            pass_timing_stack.erase(it);
            break;
          }
        });
    PIC.registerAfterPassInvalidatedCallback(
        [&](StringRef PassName, const PreservedAnalyses &) {
          if (!shouldEmitPassTiming(PassName) || pass_timing_stack.empty())
            return;
          for (auto it = pass_timing_stack.end(); it != pass_timing_stack.begin();) {
            --it;
            if (it->pass_name != PassName.str())
              continue;
            auto duration_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                                   std::chrono::steady_clock::now() -
                                   it->started_at)
                                   .count();
            events.emitInfo("pipeline_pass_timing", "pass timing",
                            {{"pass", it->pass_name},
                             {"ir_kind", it->ir_kind},
                             {"ir_name", it->ir_name},
                             {"duration_ms",
                              static_cast<int64_t>(duration_ms)},
                             {"invalidated_ir", true}});
            pass_timing_stack.erase(it);
            break;
          }
        });
  }

  // Set up pass infrastructure
  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;

  StandardInstrumentations SI(ctx, /*DebugLogging=*/false,
                              /*VerifyEach=*/false);
  SI.registerCallbacks(PIC, &MAM);

  // Custom safe verify-each: only runs after omill custom passes (not LLVM
  // standard passes) for performance.  Uses nullptr stream to avoid crash
  // in SlotTracker on corrupted modules.
  if (VerifyEach) {
    PIC.registerAfterPassCallback(
        [&](StringRef PassName, Any IR,
            const PreservedAnalyses &) {
          // Skip standard LLVM passes — verifying after every InstCombine/
          // GVN/SimplifyCFG etc. is prohibitively slow.
          static const char *const llvm_passes[] = {
              "InstCombinePass",
              "GVNPass",
              "SimplifyCFGPass",
              "SROAPass",
              "ADCEPass",
              "DSEPass",
              "EarlyCSEPass",
              "GlobalDCEPass",
              "AlwaysInlinerPass",
              "InlinerPass",
              "GlobalOptPass",
              "LoopSimplifyPass",
              "LCSSAPass",
              "LoopRotatePass",
              "LICMPass",
              "IndVarSimplifyPass",
              "LoopDeletionPass",
              "LoopUnrollPass",
              "JumpThreadingPass",
              "CorrelatedValuePropagationPass",
              "MemCpyOptPass",
              "SCCPPass",
              "BDCEPass",
              "ReassociatePass",
              "MergedLoadStoreMotionPass",
              "TailCallElimPass",
              "PromotePass",
              "AggressiveInstCombinePass",
              "LibCallsShrinkWrapPass",
              "ConstraintEliminationPass",
              "CoroSplitPass",
              "CoroElidePass",
              "InvalidateAnalysisPass",
              "RequireAnalysisPass",
              "VerifierPass",
              "PrintModulePass",
              "BitcodeWriterPass",
          };
          for (const char *p : llvm_passes) {
            if (PassName == p) return;
          }
          // Also skip pass manager wrappers and adaptors.
          if (PassName.starts_with("PassManager") ||
              PassName.starts_with("ModuleToFunction") ||
              PassName.starts_with("CGSCCToFunction") ||
              PassName.starts_with("ModuleInliner") ||
              PassName.starts_with("DevirtSCCRepeated") ||
              PassName.contains("Adaptor") ||
              PassName.contains("PassManager"))
            return;

          // Extract the module from whatever IR level we're at.
          const Module *M = nullptr;
          if (const auto **F = any_cast<const Function *>(&IR))
            M = (*F)->getParent();
          else if (const auto **MPtr = any_cast<const Module *>(&IR))
            M = *MPtr;
          else if (const auto **L = any_cast<const Loop *>(&IR))
            M = (*L)->getHeader()->getParent()->getParent();
          if (!M) return;

          if (verifyModule(*M, nullptr)) {
            errs() << "VERIFY-EACH: verification failed after pass: "
                   << PassName << "\n";
            events.emitError("verify_each_failed",
                             "module verification failed after pass",
                             {{"pass", PassName.str()}});
            events.emitTerminalFailure(1, "verify-each failure");
            // Don't try module->print() — SlotTracker may crash on
            // corrupted modules with dangling Comdat/Value references.
            // Per-function verification to narrow down:
            for (const auto &F : *M) {
              if (F.isDeclaration()) continue;
              if (verifyFunction(F, nullptr))
                errs() << "  broken function: " << F.getName() << "\n";
            }
            exit(1);
          }
        });
  }

  // --trace-func: print block/instruction counts after every pass for a
  // specific function.  Helps diagnose when the function body disappears.
  if (!TraceFunc.empty()) {
    // Track both the lifted name and the _native wrapper.
    std::string target_base = TraceFunc;
    std::string target_native = target_base + "_native";
    unsigned prev_blocks = 0, prev_insts = 0;
    unsigned prev_blocks_n = 0, prev_insts_n = 0;
    unsigned dump_seq = 0;

    // Helper: dump function IR to a file for post-mortem analysis.
    auto dumpFuncIR = [&](const Function *F, StringRef reason,
                          unsigned seq) {
      if (!DumpFuncPhases || !F || F->isDeclaration())
        return;
      std::string filename = (F->getName() + ".phase" +
                              llvm::Twine(seq) + ".ll").str();
      std::error_code EC;
      llvm::raw_fd_ostream OS(filename, EC);
      if (EC) return;
      OS << "; " << reason << "\n";
      F->print(OS);
      errs() << "[TRACE] dumped " << F->getName() << " → " << filename
             << " (" << reason << ")\n";
    };

    PIC.registerAfterPassCallback(
        [=, &prev_blocks, &prev_insts,
         &prev_blocks_n, &prev_insts_n,
         &dump_seq, &dumpFuncIR](
            StringRef PassName, Any IR, const PreservedAnalyses &) mutable {
          const Module *M = nullptr;
          if (const auto **F = any_cast<const Function *>(&IR))
            M = (*F)->getParent();
          else if (const auto **MPtr = any_cast<const Module *>(&IR))
            M = *MPtr;
          else if (const auto **L = any_cast<const Loop *>(&IR))
            M = (*L)->getHeader()->getParent()->getParent();
          if (!M) return;

          auto report = [&](const std::string &name,
                            unsigned &pb, unsigned &pi) {
            auto *F = M->getFunction(name);
            if (!F || F->isDeclaration()) {
              if (pb != 0 || pi != 0) {
                errs() << "[TRACE] " << PassName << " | " << name
                       << ": GONE (was " << pb << " blocks, "
                       << pi << " instrs)\n";
                pb = 0;
                pi = 0;
              }
              return;
            }
            unsigned blocks = 0, insts = 0;
            for (auto &BB : *F) {
              ++blocks;
              insts += BB.size();
            }
            if (blocks != pb || insts != pi) {
              int di = (pi > 0) ? (int)insts - (int)pi : 0;
              errs() << "[TRACE] " << PassName << " | " << name
                     << ": " << blocks << " blocks, " << insts
                     << " instrs";
              if (pb != 0) {
                int db = (int)blocks - (int)pb;
                errs() << " (delta: " << db << " blocks, "
                       << di << " instrs)";
              }
              errs() << "\n";

              // Dump IR on large drops (>30% instruction loss) or phase markers.
              bool is_phase = PassName.contains("PhaseMarker");
              bool large_drop = pi > 0 && di < 0 &&
                                (unsigned)(-di) > pi * 3 / 10;
              if (DumpFuncPhases && (is_phase || large_drop)) {
                std::string reason = (PassName + " | " +
                    llvm::Twine(blocks) + "bb/" +
                    llvm::Twine(insts) + "i").str();
                dumpFuncIR(F, reason, dump_seq++);
              }

              pb = blocks;
              pi = insts;
            }
          };

          report(target_base, prev_blocks, prev_insts);
          report(target_native, prev_blocks_n, prev_insts_n);
        });
  }

  PassBuilder PB(nullptr, PipelineTuningOptions(), std::nullopt, &PIC);

  // Register custom module analyses first and keep backing storage stable.
  omill::BinaryMemoryMap raw_memory_map;
  if (RawBinary) {
    raw_memory_map.addRegion(BaseAddress, raw_code.data(), raw_code.size(),
                             true, /*executable=*/true);
    raw_memory_map.setImageBase(BaseAddress);
    raw_memory_map.setImageSize(raw_code.size());
  }
  auto memory_map_holder =
      std::make_shared<omill::BinaryMemoryMap>(
          RawBinary ? std::move(raw_memory_map) : pe.memory_map);
  MAM.registerPass([memory_map_holder] {
    return omill::BinaryMemoryAnalysis(*memory_map_holder);
  });

  std::shared_ptr<omill::ExceptionInfo> exception_info_holder;
  if (!RawBinary && ResolveExceptions) {
    exception_info_holder =
        std::make_shared<omill::ExceptionInfo>(std::move(pe.exception_info));
    MAM.registerPass([exception_info_holder] {
      return omill::ExceptionInfoAnalysis(*exception_info_holder);
    });
  }

  // Build AAManager with omill's custom SegmentsAA before standard
  // registration so it's included in LLVM's AA pipeline.
  FAM.registerPass([&] {
    auto AAM = PB.buildDefaultAAPipeline();
    omill::registerAAWithManager(AAM);
    return AAM;
  });

  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);  // AAManager already registered, skipped.
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  omill::registerAnalyses(FAM);
  // Register remaining module analyses without overriding custom ones above.
  MAM.registerPass([&] { return omill::TargetArchAnalysis(); });
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });
  MAM.registerPass([&] { return omill::CallGraphAnalysis(); });
  MAM.registerPass([&] { return omill::LiftedFunctionAnalysis(); });
  MAM.registerPass([iterative_session] {
    return omill::IterativeLiftingSessionAnalysis(iterative_session);
  });
  MAM.registerPass([&] { return omill::VirtualCalleeRegistryAnalysis(); });
  MAM.registerPass([&] { return omill::VirtualMachineModelAnalysis(); });
  MAM.registerPass([&] { return omill::RegisterRoleMapAnalysis(); });
  if (!ResolveExceptions) {
    MAM.registerPass([&] { return omill::ExceptionInfoAnalysis(); });
  }

  // Register the emulator-derived VM trace map analysis.
  if (vm_graph) {
    MAM.registerPass([vm_graph] {
      return omill::VMTraceMapAnalysis(*vm_graph);
    });
  } else {
    MAM.registerPass([&] { return omill::VMTraceMapAnalysis(); });
  }

  // Register trace-lift callback so IterativeTargetResolutionPass can
  // lift new functions from resolved dispatch targets.
  auto safeTraceLiftTarget = [&](uint64_t pc) -> bool {
#if defined(_WIN32)
    __try {
#endif
      bool ok = projection_lifter && projection_lifter->LiftFunction(pc);
      if (ok)
        iterative_session->noteLiftedTarget(pc);
      return ok;
#if defined(_WIN32)
    } __except (1) {
      errs() << "WARNING: TraceLifter crashed at 0x"
             << llvm::Twine::utohexstr(pc) << "\n";
      if (events.detailed()) {
        events.emitWarn("trace_lift_crashed",
                        "trace lift crashed for discovered target",
                        {{"va", ("0x" + llvm::Twine::utohexstr(pc)).str()}});
      }
      return false;
    }
#endif
  };

  auto safeBlockLiftTarget = [&](uint64_t pc) -> bool {
    if (!block_lifter)
      return false;
#if defined(_WIN32)
    __try {
#endif
      llvm::SmallVector<uint64_t, 4> targets;
      auto *fn = projection_lifter ? projection_lifter->LiftBlock(pc, targets)
                                   : nullptr;
      if (fn)
        iterative_session->noteLiftedTarget(pc);
      return fn != nullptr;
#if defined(_WIN32)
    } __except (1) {
      errs() << "WARNING: BlockLifter crashed at 0x"
             << llvm::Twine::utohexstr(pc) << "\n";
      if (events.detailed()) {
        events.emitWarn("block_lift_crashed",
                        "block lift crashed for discovered target",
                        {{"va", ("0x" + llvm::Twine::utohexstr(pc)).str()}});
      }
      return false;
    }
#endif
  };

  {
    omill::TraceLiftCallback trace_cb;
    if (ResolveTargets) {
      trace_cb = safeTraceLiftTarget;
    }
    iterative_session->setTraceLiftCallback(trace_cb);
    MAM.registerPass([trace_cb] {
      return omill::TraceLiftAnalysis(trace_cb);
    });
  }

  // Always register BlockLiftAnalysis so late generic-static cleanup passes
  // can query it safely on both block-lift and plain-lift runs.
  omill::BlockLiftCallback lift_cb;
  if (block_lifter) {
    lift_cb = safeBlockLiftTarget;
  }
  iterative_session->setBlockLiftCallback(lift_cb);
  omill::AddCodeCallback add_code_cb;
  if (block_manager) {
    add_code_cb = [&block_manager](uint64_t pc, const uint8_t *data,
                                    size_t size) {
      block_manager->addCode(pc, data, size);
    };
  }
  MAM.registerPass([lift_cb, add_code_cb] {
    return omill::BlockLiftAnalysis(lift_cb, add_code_cb);
  });
  // Prime the lightweight block-lift callback analysis so later function
  // passes can retrieve it through getCachedResult via the module proxy.
  (void) MAM.getResult<omill::BlockLiftAnalysis>(*module);

  auto runPostPatchCleanup = [&](StringRef reason) {
    ModulePassManager MPM;
    omill::buildPostPatchCleanupPipeline(MPM, 80);
    MPM.run(*module, MAM);

    if (events.detailed()) {
      events.emitInfo("post_patch_cleanup_completed",
                      "post patch cleanup completed",
                      {{"reason", reason.str()}});
    }
  };

  auto runLateClosureCanonicalization = [&](StringRef reason) {
    ModulePassManager MPM;
    omill::buildLateClosureCanonicalizationPipeline(MPM);
    MPM.run(*module, MAM);

    if (events.detailed()) {
      events.emitInfo("late_closure_canonicalization_completed",
                      "late closure canonicalization completed",
                      {{"reason", reason.str()}});
    }
  };

  auto restoreVMHandlerAttrs = [&]() {
    if (!vm_graph)
      return;

    for (uint64_t va : vm_graph->handlerEntries()) {
      std::string name = "sub_" + Twine::utohexstr(va).str();
      if (auto *fn = module->getFunction(name)) {
        if (!fn->isDeclaration()) {
          fn->addFnAttr("omill.vm_handler");
          if (va == vm_wrapper_va)
            fn->addFnAttr("omill.vm_wrapper");
        }
      }
    }

    for (uint64_t va : {vm_entry_va, vm_exit_va}) {
      if (!va)
        continue;
      std::string name = "sub_" + Twine::utohexstr(va).str();
      if (auto *fn = module->getFunction(name)) {
        if (!fn->isDeclaration()) {
          fn->addFnAttr("omill.vm_handler");
          // Tag direct callees of vmentry/vmexit as vm_handlers too.
          if (va == vm_entry_va) {
            for (auto &BB : *fn) {
              for (auto &I : BB) {
                if (auto *call = dyn_cast<CallInst>(&I)) {
                  if (auto *callee = call->getCalledFunction()) {
                    if (callee->getName().starts_with("sub_") &&
                        !callee->isDeclaration()) {
                      callee->addFnAttr("omill.vm_handler");
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  };

  // Run the main pipeline (without ABI first)
  const bool requested_root_is_export =
      !RawBinary &&
      (std::find(pe.exported_function_starts.begin(),
                 pe.exported_function_starts.end(),
                 requested_func_va) != pe.exported_function_starts.end());
  const bool normalized_export_thunk_root =
      requested_root_is_export && requested_func_va != func_va;
  auto scanExportDirectCallsiteWin64ParamCount = [&](uint64_t target_va) {
    if (RawBinary || pe.is_macho || !requested_root_is_export)
      return 0u;
    if (target_arch != omill::TargetArch::kX86_64 || target_os_str != "windows")
      return 0u;

    auto mapPhysicalRegToParamIndex = [](unsigned reg_id)
        -> std::optional<unsigned> {
      switch (reg_id) {
        case 1:
          return 0;  // RCX
        case 2:
          return 1;  // RDX
        case 8:
          return 2;  // R8
        case 9:
          return 3;  // R9
        default:
          return std::nullopt;
      }
    };

    auto classifyWrittenWin64Param = [&](llvm::ArrayRef<uint8_t> inst_bytes)
        -> std::optional<unsigned> {
      if (inst_bytes.empty())
        return std::nullopt;

      size_t i = 0;
      uint8_t rex = 0;
      if ((inst_bytes[i] & 0xF0u) == 0x40u) {
        rex = inst_bytes[i++];
        if (i >= inst_bytes.size())
          return std::nullopt;
      }

      auto regFromOpcodeLowBits = [&](uint8_t opcode_low_bits) {
        return mapPhysicalRegToParamIndex(
            static_cast<unsigned>(opcode_low_bits) +
            ((rex & 0x1u) ? 8u : 0u));
      };
      auto regFromModRMReg = [&](uint8_t modrm) {
        return mapPhysicalRegToParamIndex(
            static_cast<unsigned>((modrm >> 3u) & 0x7u) +
            ((rex & 0x4u) ? 8u : 0u));
      };
      auto regFromModRMRM = [&](uint8_t modrm) {
        return mapPhysicalRegToParamIndex(
            static_cast<unsigned>(modrm & 0x7u) +
            ((rex & 0x1u) ? 8u : 0u));
      };

      const uint8_t opcode = inst_bytes[i];
      if (opcode >= 0xB8u && opcode <= 0xBFu)
        return regFromOpcodeLowBits(static_cast<uint8_t>(opcode - 0xB8u));

      if ((opcode == 0x8Bu || opcode == 0x8Du || opcode == 0x33u) &&
          (i + 1u) < inst_bytes.size()) {
        return regFromModRMReg(inst_bytes[i + 1u]);
      }

      if (opcode == 0x0Fu && (i + 2u) < inst_bytes.size() &&
          inst_bytes[i + 1u] == 0xB6u) {
        return regFromModRMReg(inst_bytes[i + 2u]);
      }

      if (opcode == 0x31u && (i + 1u) < inst_bytes.size()) {
        const uint8_t modrm = inst_bytes[i + 1u];
        if (((modrm >> 6u) & 0x3u) == 0x3u &&
            (((modrm >> 3u) & 0x7u) == (modrm & 0x7u))) {
          return regFromModRMRM(modrm);
        }
      }

      return std::nullopt;
    };

    auto scanDirectRel32CallsitesForTarget = [&](uint64_t callee_va) {
      unsigned max_param_count = 0;
      auto decode_ctx = arch->CreateInitialContext();
      remill::Instruction decoded_inst;
      auto isCallInstruction = [](llvm::ArrayRef<uint8_t> inst_bytes) {
        if (inst_bytes.empty())
          return false;
        size_t i = 0;
        if ((inst_bytes[i] & 0xF0u) == 0x40u) {
          ++i;
          if (i >= inst_bytes.size())
            return false;
        }
        const uint8_t opcode = inst_bytes[i];
        if (opcode == 0xE8u)
          return true;
        if (opcode == 0xFFu && (i + 1u) < inst_bytes.size()) {
          const uint8_t modrm = inst_bytes[i + 1u];
          return (((modrm >> 3u) & 0x7u) == 0x2u);
        }
        return false;
      };
      for (const auto &sec : pe.code_sections) {
        if (sec.storage_index >= pe.section_storage.size())
          continue;
        const auto &stored = pe.section_storage[sec.storage_index];
        if (stored.size() < 5u)
          continue;

        for (size_t i = 0; i + 5u <= stored.size(); ++i) {
          if (stored[i] != 0xE8u)
            continue;

          int32_t rel = 0;
          std::memcpy(&rel, stored.data() + i + 1u, sizeof(rel));
          const uint64_t call_pc = sec.va + i;
          const uint64_t call_target =
              call_pc + 5u + static_cast<int64_t>(rel);
          if (call_target != callee_va)
            continue;

          std::array<bool, 4> seen_param_writes = {
              false, false, false, false};
          const size_t window_start = (i > 48u) ? (i - 48u) : 0u;
          size_t cursor = window_start;
          while (cursor < i) {
            const size_t remaining = std::min<size_t>(15u, stored.size() - cursor);
            std::string_view probe_bytes(
                reinterpret_cast<const char *>(stored.data() + cursor), remaining);
            decoded_inst.Reset();
            if (!arch->DecodeInstruction(sec.va + cursor, probe_bytes, decoded_inst,
                                         decode_ctx) ||
                decoded_inst.NumBytes() == 0) {
              ++cursor;
              continue;
            }
            const size_t inst_size = std::min<size_t>(decoded_inst.NumBytes(), i - cursor);
            llvm::ArrayRef<uint8_t> inst_bytes(stored.data() + cursor, inst_size);
            if (isCallInstruction(inst_bytes)) {
              seen_param_writes = {false, false, false, false};
              cursor += decoded_inst.NumBytes();
              continue;
            }
            if (auto param_index = classifyWrittenWin64Param(inst_bytes)) {
              seen_param_writes[*param_index] = true;
            }
            cursor += decoded_inst.NumBytes();
          }

          unsigned param_count = 0;
          while (param_count < seen_param_writes.size() &&
                 seen_param_writes[param_count]) {
            ++param_count;
          }
          max_param_count = std::max(max_param_count, param_count);
        }
      }
      return max_param_count;
    };

    auto findDirectJmpThunkTarget = [&](uint64_t root_va)
        -> std::optional<uint64_t> {
      const auto *section = findCodeSection(pe, root_va);
      if (!section || section->storage_index >= pe.section_storage.size())
        return std::nullopt;
      const auto &stored = pe.section_storage[section->storage_index];
      const size_t offset = static_cast<size_t>(root_va - section->va);
      if (offset >= stored.size())
        return std::nullopt;
      const size_t remaining = stored.size() - offset;
      if (remaining >= 5u && stored[offset] == 0xE9u) {
        int32_t rel = 0;
        std::memcpy(&rel, stored.data() + offset + 1u, sizeof(rel));
        return root_va + 5u + static_cast<int64_t>(rel);
      }
      if (remaining >= 2u && stored[offset] == 0xEBu) {
        int8_t rel = static_cast<int8_t>(stored[offset + 1u]);
        return root_va + 2u + rel;
      }
      return std::nullopt;
    };

    unsigned max_param_count = scanDirectRel32CallsitesForTarget(target_va);
    if (max_param_count != 0)
      return max_param_count;

    if (auto thunk_target = findDirectJmpThunkTarget(target_va))
      return scanDirectRel32CallsitesForTarget(*thunk_target);

    return 0u;
  };
  auto annotateExportCallsiteWin64ParamHint = [&](uint64_t callsite_root_va,
                                                  uint64_t tagged_root_va) {
    const unsigned hint_count =
        scanExportDirectCallsiteWin64ParamCount(callsite_root_va);
    const bool debug_export_callsite_abi_hints =
        (std::getenv("OMILL_DEBUG_EXPORT_CALLSITE_ABI_HINTS") != nullptr);
    if (hint_count == 0)
      {
        if (debug_export_callsite_abi_hints) {
          errs() << "[export-callsite-abi-hint] root=0x"
                 << Twine::utohexstr(callsite_root_va) << " hint_count=0\n";
        }
      return;
      }

    unsigned tagged = 0;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      if (omill::extractEntryVA(F.getName()) != tagged_root_va)
        continue;
      F.addFnAttr("omill.export_callsite_win64_gpr_count",
                  std::to_string(hint_count));
      ++tagged;
    }

    if (debug_export_callsite_abi_hints) {
      errs() << "[export-callsite-abi-hint] root=0x"
             << Twine::utohexstr(callsite_root_va) << " tagged_root=0x"
             << Twine::utohexstr(tagged_root_va) << " hint_count="
             << hint_count << " tagged=" << tagged << "\n";
    }
    if (tagged != 0) {
      errs() << "Export callsite ABI hint: root=0x"
             << Twine::utohexstr(callsite_root_va) << " tagged_root=0x"
             << Twine::utohexstr(tagged_root_va) << " win64_gpr_params="
             << hint_count << " tagged_roots=" << tagged << "\n";
    }
  };
  auto scanExportEntryHiddenSeedExprs = [&](uint64_t root_va) {
    const bool debug_public_root_seeds =
        (std::getenv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS") != nullptr);
    const bool allow_requested_root_seed_scan =
        requested_root_is_export ||
        (!batch_vas.empty() ||
         (requested_func_va != 0 && root_va == requested_func_va));
    if (RawBinary || pe.is_macho || !allow_requested_root_seed_scan) {
      if (debug_public_root_seeds) {
        errs() << "[export-entry-seeds] root=0x" << Twine::utohexstr(root_va)
               << " skipped raw=" << RawBinary
               << " macho=" << pe.is_macho
               << " requested_root_is_export=" << requested_root_is_export
               << " requested_root_seed_scan="
               << allow_requested_root_seed_scan << "\n";
      }
      return std::string();
    }
    if (target_arch != omill::TargetArch::kX86_64 || target_os_str != "windows") {
      if (debug_public_root_seeds) {
        errs() << "[export-entry-seeds] root=0x" << Twine::utohexstr(root_va)
               << " skipped arch=" << static_cast<unsigned>(target_arch)
               << " os=" << target_os_str << "\n";
      }
      return std::string();
    }

    const auto *section = findCodeSection(pe, root_va);
    if (!section || section->storage_index >= pe.section_storage.size()) {
      if (debug_public_root_seeds) {
        errs() << "[export-entry-seeds] root=0x" << Twine::utohexstr(root_va)
               << " skipped missing section\n";
      }
      return std::string();
    }
    const auto &stored = pe.section_storage[section->storage_index];
    const size_t offset = static_cast<size_t>(root_va - section->va);
    if (offset >= stored.size()) {
      if (debug_public_root_seeds) {
        errs() << "[export-entry-seeds] root=0x" << Twine::utohexstr(root_va)
               << " skipped offset past section size\n";
      }
      return std::string();
    }

    enum class SeedReg : unsigned {
      RAX = 0,
      RCX = 1,
      RDX = 2,
      RBX = 3,
      RSP = 4,
      RBP = 5,
      RSI = 6,
      RDI = 7,
      R8 = 8,
      R9 = 9,
      R10 = 10,
      R11 = 11,
      R12 = 12,
      R13 = 13,
      R14 = 14,
      R15 = 15,
      Invalid = 255,
    };

    auto regName = [&](SeedReg reg) -> llvm::StringRef {
      switch (reg) {
        case SeedReg::RAX: return "RAX";
        case SeedReg::RCX: return "RCX";
        case SeedReg::RDX: return "RDX";
        case SeedReg::RBX: return "RBX";
        case SeedReg::RSP: return "RSP";
        case SeedReg::RBP: return "RBP";
        case SeedReg::RSI: return "RSI";
        case SeedReg::RDI: return "RDI";
        case SeedReg::R8: return "R8";
        case SeedReg::R9: return "R9";
        case SeedReg::R10: return "R10";
        case SeedReg::R11: return "R11";
        case SeedReg::R12: return "R12";
        case SeedReg::R13: return "R13";
        case SeedReg::R14: return "R14";
        case SeedReg::R15: return "R15";
        default: return "";
      }
    };

    auto regFromBase = [](unsigned id) -> SeedReg {
      switch (id & 0xfu) {
        case 0: return SeedReg::RAX;
        case 1: return SeedReg::RCX;
        case 2: return SeedReg::RDX;
        case 3: return SeedReg::RBX;
        case 4: return SeedReg::RSP;
        case 5: return SeedReg::RBP;
        case 6: return SeedReg::RSI;
        case 7: return SeedReg::RDI;
        case 8: return SeedReg::R8;
        case 9: return SeedReg::R9;
        case 10: return SeedReg::R10;
        case 11: return SeedReg::R11;
        case 12: return SeedReg::R12;
        case 13: return SeedReg::R13;
        case 14: return SeedReg::R14;
        case 15: return SeedReg::R15;
        default: return SeedReg::Invalid;
      }
    };

    auto paramRegIndex = [](SeedReg reg) -> std::optional<unsigned> {
      switch (reg) {
        case SeedReg::RCX: return 0u;
        case SeedReg::RDX: return 1u;
        case SeedReg::R8: return 2u;
        case SeedReg::R9: return 3u;
        default: return std::nullopt;
      }
    };

    struct SeedExpr {
      std::string text;
    };

    auto exprConst = [](uint64_t value) {
      return SeedExpr{"const(0x" + llvm::utohexstr(value) + ")"};
    };
    auto exprParam = [](unsigned index) {
      return SeedExpr{"param(" + std::to_string(index) + ")"};
    };
    auto exprUnary = [](llvm::StringRef op, const SeedExpr &arg) {
      return SeedExpr{(op + "(" + arg.text + ")").str()};
    };
    auto exprBinary = [](llvm::StringRef op, const SeedExpr &lhs,
                         const SeedExpr &rhs) {
      return SeedExpr{(op + "(" + lhs.text + "," + rhs.text + ")").str()};
    };

    auto makeZero = [&]() { return exprConst(0); };

    auto exprEqual = [](const SeedExpr &lhs, const SeedExpr &rhs) {
      return lhs.text == rhs.text;
    };

    std::array<std::optional<SeedExpr>, 16> regs;
    regs[static_cast<unsigned>(SeedReg::RCX)] = exprParam(0);
    regs[static_cast<unsigned>(SeedReg::RDX)] = exprParam(1);
    regs[static_cast<unsigned>(SeedReg::R8)] = exprParam(2);
    regs[static_cast<unsigned>(SeedReg::R9)] = exprParam(3);

    auto getRegExpr = [&](SeedReg reg) -> std::optional<SeedExpr> {
      if (reg == SeedReg::Invalid)
        return std::nullopt;
      return regs[static_cast<unsigned>(reg)];
    };
    auto setRegExpr = [&](SeedReg reg, SeedExpr expr) {
      if (reg == SeedReg::Invalid)
        return;
      regs[static_cast<unsigned>(reg)] = std::move(expr);
    };

    auto decodeReg = [&](uint8_t reg_bits, bool high_bit) {
      return regFromBase(static_cast<unsigned>(reg_bits) +
                         (high_bit ? 8u : 0u));
    };

    auto stopOnControlFlow = [&](uint8_t opcode) {
      if (opcode == 0xE8u || opcode == 0xE9u || opcode == 0xEBu ||
          opcode == 0xC3u || opcode == 0xC2u)
        return true;
      if ((opcode & 0xF0u) == 0x70u)
        return true;
      return false;
    };

    size_t cursor = offset;
    size_t decoded = 0;
    constexpr size_t kMaxDecoded = 24;
    const size_t end = std::min(stored.size(), offset + 96u);
    auto seed_decode_ctx = arch->CreateInitialContext();
    while (cursor < end && decoded < kMaxDecoded) {
      const size_t remaining = std::min<size_t>(15u, end - cursor);
      std::string_view probe_bytes(
          reinterpret_cast<const char *>(stored.data() + cursor), remaining);
      remill::Instruction decoded_inst;
      if (!arch->DecodeInstruction(section->va + cursor, probe_bytes,
                                   decoded_inst, seed_decode_ctx) ||
          decoded_inst.NumBytes() == 0) {
        break;
      }
      const size_t inst_len =
          std::min<size_t>(decoded_inst.NumBytes(), end - cursor);
      uint8_t rex = 0;
      size_t inst_start = cursor;
      uint8_t opcode = stored[cursor];
      if ((opcode & 0xF0u) == 0x40u) {
        rex = opcode;
        ++cursor;
        if (cursor >= end)
          break;
        opcode = stored[cursor];
      }

      if (stopOnControlFlow(opcode))
        break;
      if (opcode == 0x0Fu && cursor + 1u < end &&
          ((stored[cursor + 1u] & 0xF0u) == 0x80u)) {
        break;
      }

      bool handled = false;

      if (opcode >= 0x50u && opcode <= 0x5Fu) {
        cursor = inst_start + inst_len;
        handled = true;
      } else if ((opcode == 0x89u || opcode == 0x8Bu || opcode == 0x03u ||
                  opcode == 0x33u || opcode == 0x85u) &&
                 cursor + 1u < end) {
        uint8_t modrm = stored[cursor + 1u];
        if (((modrm >> 6u) & 0x3u) == 0x3u) {
          auto dst =
              decodeReg(static_cast<uint8_t>((modrm >> 3u) & 0x7u),
                        (rex & 0x4u) != 0);
          auto src =
              decodeReg(static_cast<uint8_t>(modrm & 0x7u),
                        (rex & 0x1u) != 0);
          if (opcode == 0x8Bu) {
            if (auto src_expr = getRegExpr(src)) {
              if (rex & 0x8u) {
                setRegExpr(dst, *src_expr);
              } else {
                setRegExpr(dst, exprUnary("zext32", *src_expr));
              }
            }
            handled = true;
          } else if (opcode == 0x89u) {
            if (auto src_expr = getRegExpr(dst)) {
              if (rex & 0x8u) {
                setRegExpr(src, *src_expr);
              } else {
                setRegExpr(src, exprUnary("zext32", *src_expr));
              }
            }
            handled = true;
          } else if (opcode == 0x03u && (rex & 0x8u)) {
            if (auto dst_expr = getRegExpr(dst)) {
              if (auto src_expr = getRegExpr(src)) {
                setRegExpr(dst, exprBinary("add64", *dst_expr, *src_expr));
              }
            }
            handled = true;
          } else if (opcode == 0x33u) {
            if (auto dst_expr = getRegExpr(dst)) {
              if (auto src_expr = getRegExpr(src)) {
                if (exprEqual(*dst_expr, *src_expr)) {
                  setRegExpr(dst, makeZero());
                } else if (rex & 0x8u) {
                  setRegExpr(dst, exprBinary("xor64", *dst_expr, *src_expr));
                } else {
                  setRegExpr(dst, exprBinary("xor32", *dst_expr, *src_expr));
                }
              }
            }
            handled = true;
          } else if (opcode == 0x85u) {
            handled = true;
          }
          if (handled)
            cursor = inst_start + inst_len;
        } else if (opcode == 0x89u || opcode == 0x85u) {
          // Ignore register spills / tests against stack slots in the prologue.
          cursor = inst_start + inst_len;
          handled = true;
        } else if (opcode == 0x8Bu) {
          // Ignore memory loads that feed stack-cookie / local-frame setup.
          // They are not stable public-root seeds, but they should not stop us
          // from seeing the real hidden live-ins that follow.
          auto dst =
              decodeReg(static_cast<uint8_t>((modrm >> 3u) & 0x7u),
                        (rex & 0x4u) != 0);
          setRegExpr(dst, exprConst(0));
          cursor = inst_start + inst_len;
          handled = true;
        }
      } else if (opcode >= 0xB8u && opcode <= 0xBFu && (rex & 0x8u) &&
                 cursor + 8u < end) {
        auto dst = decodeReg(static_cast<uint8_t>(opcode - 0xB8u),
                             (rex & 0x1u) != 0);
        uint64_t imm = 0;
        std::memcpy(&imm, stored.data() + cursor + 1u, sizeof(imm));
        setRegExpr(dst, exprConst(imm));
        cursor = inst_start + inst_len;
        handled = true;
      } else if (opcode == 0x8Du && cursor + 1u < end) {
        uint8_t modrm = stored[cursor + 1u];
        auto dst = decodeReg(static_cast<uint8_t>((modrm >> 3u) & 0x7u),
                             (rex & 0x4u) != 0);
        uint8_t mod = static_cast<uint8_t>((modrm >> 6u) & 0x3u);
        uint8_t rm = static_cast<uint8_t>(modrm & 0x7u);
        std::optional<SeedExpr> expr;

        if (mod == 0 && rm == 5u && cursor + 5u < end) {
          int32_t disp = 0;
          std::memcpy(&disp, stored.data() + cursor + 2u, sizeof(disp));
          uint64_t target = section->va + inst_start + inst_len +
                            static_cast<int64_t>(disp);
          expr = exprConst(target);
        } else if (rm == 4u && cursor + 2u < end) {
          uint8_t sib = stored[cursor + 2u];
          auto base = decodeReg(static_cast<uint8_t>(sib & 0x7u),
                                (rex & 0x1u) != 0);
          auto index = decodeReg(static_cast<uint8_t>((sib >> 3u) & 0x7u),
                                 (rex & 0x2u) != 0);
          if (auto base_expr = getRegExpr(base)) {
            expr = *base_expr;
            if (((sib >> 3u) & 0x7u) != 4u) {
              if (auto index_expr = getRegExpr(index))
                expr = exprBinary("add64", *expr, *index_expr);
            }
            if (mod == 1u && cursor + 3u < end) {
              int8_t disp = static_cast<int8_t>(stored[cursor + 3u]);
              expr = exprBinary("add64", *expr,
                                exprConst(static_cast<uint64_t>(
                                    static_cast<int64_t>(disp))));
            } else if (mod == 2u && cursor + 6u < end) {
              int32_t disp = 0;
              std::memcpy(&disp, stored.data() + cursor + 3u, sizeof(disp));
              expr = exprBinary("add64", *expr,
                                exprConst(static_cast<uint64_t>(
                                    static_cast<int64_t>(disp))));
            }
          }
        }

        if (expr) {
          setRegExpr(dst, *expr);
          handled = true;
        } else if (mod == 0u || mod == 1u || mod == 2u) {
          // Ignore LEA forms we don't currently model instead of bailing out.
          handled = true;
        }
        if (handled)
          cursor = inst_start + inst_len;
      } else if (opcode == 0x83u && cursor + 2u < end) {
        uint8_t modrm = stored[cursor + 1u];
        uint8_t imm = stored[cursor + 2u];
        if (((modrm >> 6u) & 0x3u) == 0x3u) {
          auto dst =
              decodeReg(static_cast<uint8_t>(modrm & 0x7u),
                        (rex & 0x1u) != 0);
          uint8_t subop = static_cast<uint8_t>((modrm >> 3u) & 0x7u);
          if (subop == 0x0u) {
            if (auto dst_expr = getRegExpr(dst)) {
              setRegExpr(dst, exprBinary("add64", *dst_expr, exprConst(imm)));
            }
            handled = true;
          } else if (subop == 0x4u) {
            if (auto dst_expr = getRegExpr(dst)) {
              setRegExpr(dst,
                         exprBinary("and32", *dst_expr, exprConst(imm)));
            }
            handled = true;
          } else if (subop == 0x5u || subop == 0x7u) {
            handled = true;
          }
        }
        if (handled)
          cursor = inst_start + inst_len;
      } else if (opcode == 0x81u && cursor + 5u < end) {
        uint8_t modrm = stored[cursor + 1u];
        if (((modrm >> 6u) & 0x3u) == 0x3u) {
          auto dst =
              decodeReg(static_cast<uint8_t>(modrm & 0x7u),
                        (rex & 0x1u) != 0);
          uint8_t subop = static_cast<uint8_t>((modrm >> 3u) & 0x7u);
          uint32_t imm = 0;
          std::memcpy(&imm, stored.data() + cursor + 2u, sizeof(imm));
          if (subop == 0x0u) {
            if (auto dst_expr = getRegExpr(dst)) {
              setRegExpr(dst, exprBinary("add64", *dst_expr, exprConst(imm)));
            }
            handled = true;
          } else if (subop == 0x4u) {
            if (auto dst_expr = getRegExpr(dst)) {
              setRegExpr(dst, exprBinary("and32", *dst_expr, exprConst(imm)));
            }
            handled = true;
          } else if (subop == 0x5u || subop == 0x7u) {
            handled = true;
          }
        }
        if (handled)
          cursor = inst_start + inst_len;
      } else if (opcode == 0xC1u && cursor + 2u < end) {
        uint8_t modrm = stored[cursor + 1u];
        uint8_t imm = stored[cursor + 2u];
        if (((modrm >> 6u) & 0x3u) == 0x3u && (rex & 0x8u)) {
          auto dst =
              decodeReg(static_cast<uint8_t>(modrm & 0x7u),
                        (rex & 0x1u) != 0);
          uint8_t subop = static_cast<uint8_t>((modrm >> 3u) & 0x7u);
          if (auto dst_expr = getRegExpr(dst)) {
            if (subop == 0x0u) {
              setRegExpr(dst,
                         exprBinary("rol64", *dst_expr, exprConst(imm)));
              handled = true;
            } else if (subop == 0x1u) {
              setRegExpr(dst,
                         exprBinary("ror64", *dst_expr, exprConst(imm)));
              handled = true;
            }
          }
        }
        if (handled)
          cursor = inst_start + inst_len;
      } else if (opcode == 0x0Fu && cursor + 1u < end &&
                 stored[cursor + 1u] == 0x1Fu) {
        cursor = inst_start + inst_len;
        handled = true;
      }

      if (!handled)
        break;

      ++decoded;
      if (cursor <= inst_start)
        break;
    }

    const unsigned public_param_count =
        scanExportDirectCallsiteWin64ParamCount(root_va);
    llvm::SmallVector<std::string, 8> seeds;
    for (unsigned i = 0; i < regs.size(); ++i) {
      auto reg = regFromBase(i);
      auto expr = regs[i];
      if (!expr || reg == SeedReg::Invalid)
        continue;
      auto param_index = paramRegIndex(reg);
      if (param_index && *param_index < public_param_count)
        continue;
      if (param_index && expr->text == exprParam(*param_index).text)
        continue;
      seeds.push_back((regName(reg) + "=" + expr->text).str());
    }
    auto joined = llvm::join(seeds, ";");
    if (debug_public_root_seeds) {
      errs() << "[export-entry-seeds] root=0x" << Twine::utohexstr(root_va)
             << " public_param_count=" << public_param_count
             << " decoded=" << decoded
             << " seeds=" << joined << "\n";
    }
    return joined;
  };
  auto annotateExportEntryHiddenSeedHint = [&](uint64_t root_va,
                                               uint64_t tagged_root_va) {
    auto seed_exprs = scanExportEntryHiddenSeedExprs(root_va);
    if (seed_exprs.empty())
      return;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      if (omill::extractEntryVA(F.getName()) != tagged_root_va)
        continue;
      F.addFnAttr("omill.export_entry_seed_exprs", seed_exprs);
    }
  };
  auto scanRequestedRootUsesRaxReturnHint = [&](uint64_t root_va) {
    if (!batch_vas.empty() || requested_func_va == 0 || root_va != requested_func_va)
      return false;
    if (RawBinary || pe.is_macho || target_arch != omill::TargetArch::kX86_64 ||
        target_os_str != "windows") {
      return false;
    }

    const auto *section = findCodeSection(pe, root_va);
    if (!section || section->storage_index >= pe.section_storage.size())
      return false;
    const auto &stored = pe.section_storage[section->storage_index];
    const size_t offset = static_cast<size_t>(root_va - section->va);
    if (offset >= stored.size())
      return false;

    auto instructionReferencesRax = [&](size_t inst_start, size_t inst_len) {
      if (inst_start >= stored.size() || inst_len == 0)
        return false;
      size_t cur = inst_start;
      const size_t inst_end = std::min(inst_start + inst_len, stored.size());
      uint8_t rex = 0;
      uint8_t opcode = stored[cur];
      if ((opcode & 0xF0u) == 0x40u) {
        rex = opcode;
        ++cur;
        if (cur >= inst_end)
          return false;
        opcode = stored[cur];
      }

      switch (opcode) {
        case 0x04:
        case 0x05:
        case 0x0C:
        case 0x0D:
        case 0x14:
        case 0x15:
        case 0x1C:
        case 0x1D:
        case 0x24:
        case 0x25:
        case 0x2C:
        case 0x2D:
        case 0x34:
        case 0x35:
        case 0x3C:
        case 0x3D:
          return true;
        default:
          break;
      }

      if (cur + 1 >= inst_end)
        return false;
      auto opcodeReferencesRaxViaModRM = [&](uint8_t op) {
        switch (op) {
          case 0x00: case 0x01: case 0x02: case 0x03:
          case 0x08: case 0x09: case 0x0A: case 0x0B:
          case 0x10: case 0x11: case 0x12: case 0x13:
          case 0x18: case 0x19: case 0x1A: case 0x1B:
          case 0x20: case 0x21: case 0x22: case 0x23:
          case 0x28: case 0x29: case 0x2A: case 0x2B:
          case 0x30: case 0x31: case 0x32: case 0x33:
          case 0x38: case 0x39: case 0x3A: case 0x3B:
          case 0x84: case 0x85: case 0x86: case 0x87:
          case 0x88: case 0x89: case 0x8A: case 0x8B:
            return true;
          default:
            return false;
        }
      };
      if (!opcodeReferencesRaxViaModRM(opcode))
        return false;

      uint8_t modrm = stored[cur + 1];
      const unsigned mod = static_cast<unsigned>((modrm >> 6u) & 0x3u);
      const unsigned reg = static_cast<unsigned>((modrm >> 3u) & 0x7u) +
                           ((rex & 0x4u) ? 8u : 0u);
      const unsigned rm = static_cast<unsigned>(modrm & 0x7u) +
                          ((rex & 0x1u) ? 8u : 0u);
      if (reg == 0 || rm == 0)
        return true;
      if (mod != 0x3u && (modrm & 0x7u) == 0x4u && cur + 2 < inst_end) {
        uint8_t sib = stored[cur + 2];
        const unsigned sib_index_bits = static_cast<unsigned>((sib >> 3u) & 0x7u);
        const unsigned base = static_cast<unsigned>(sib & 0x7u) +
                              ((rex & 0x1u) ? 8u : 0u);
        const unsigned index = sib_index_bits + ((rex & 0x2u) ? 8u : 0u);
        if (base == 0)
          return true;
        if (sib_index_bits != 0x4u && index == 0)
          return true;
      }
      return false;
    };

    bool saw_call = false;
    bool saw_rax_use_since_last_call = false;
    size_t cursor = offset;
    size_t decoded = 0;
    const size_t end = std::min(stored.size(), offset + 128u);
    auto decode_ctx = arch->CreateInitialContext();
    while (cursor < end && decoded < 32u) {
      const size_t remaining = std::min<size_t>(15u, end - cursor);
      std::string_view probe_bytes(
          reinterpret_cast<const char *>(stored.data() + cursor), remaining);
      remill::Instruction decoded_inst;
      if (!arch->DecodeInstruction(section->va + cursor, probe_bytes, decoded_inst,
                                   decode_ctx) ||
          decoded_inst.NumBytes() == 0) {
        break;
      }
      const size_t inst_start = cursor;
      const size_t inst_len =
          std::min<size_t>(decoded_inst.NumBytes(), end - cursor);
      uint8_t opcode = stored[cursor];
      if ((opcode & 0xF0u) == 0x40u && cursor + 1 < end)
        opcode = stored[cursor + 1];

      bool is_call = false;
      bool is_ret = false;
      if (opcode == 0xE8u) {
        is_call = true;
      } else if (opcode == 0xFFu && inst_start + 1 < end) {
        uint8_t modrm = stored[inst_start + 1];
        uint8_t subop = static_cast<uint8_t>((modrm >> 3u) & 0x7u);
        is_call = (subop == 0x2u || subop == 0x3u);
      } else if (opcode == 0xC3u || opcode == 0xC2u) {
        is_ret = true;
      }

      if (is_call) {
        saw_call = true;
        saw_rax_use_since_last_call = false;
      } else if (is_ret) {
        return saw_call && saw_rax_use_since_last_call;
      } else if (saw_call && instructionReferencesRax(inst_start, inst_len)) {
        saw_rax_use_since_last_call = true;
      }

      cursor = inst_start + inst_len;
      ++decoded;
    }
    return false;
  };

  auto scanRequestedRootReturnTransform = [&](uint64_t root_va)
      -> std::string {
    if (!batch_vas.empty() || requested_func_va == 0 || root_va != requested_func_va)
      return std::string();
    if (RawBinary || pe.is_macho || target_arch != omill::TargetArch::kX86_64 ||
        target_os_str != "windows") {
      return std::string();
    }

    const auto *section = findCodeSection(pe, root_va);
    if (!section || section->storage_index >= pe.section_storage.size())
      return std::string();
    const auto &stored = pe.section_storage[section->storage_index];
    const size_t offset = static_cast<size_t>(root_va - section->va);
    if (offset >= stored.size())
      return std::string();

    auto decode_ctx = arch->CreateInitialContext();
    size_t cursor = offset;
    size_t decoded = 0;
    const size_t end = std::min(stored.size(), offset + 128u);
    bool saw_call = false;
    std::string transform;
    while (cursor < end && decoded < 32u) {
      const size_t remaining = std::min<size_t>(15u, end - cursor);
      std::string_view probe_bytes(
          reinterpret_cast<const char *>(stored.data() + cursor), remaining);
      remill::Instruction decoded_inst;
      if (!arch->DecodeInstruction(section->va + cursor, probe_bytes, decoded_inst,
                                   decode_ctx) ||
          decoded_inst.NumBytes() == 0) {
        break;
      }
      const size_t inst_start = cursor;
      const size_t inst_len =
          std::min<size_t>(decoded_inst.NumBytes(), end - cursor);
      uint8_t opcode = stored[inst_start];
      if ((opcode & 0xF0u) == 0x40u && inst_start + 1 < end)
        opcode = stored[inst_start + 1];

      bool is_call = false;
      if (opcode == 0xE8u) {
        is_call = true;
      } else if (opcode == 0xFFu && inst_start + 1 < end) {
        uint8_t modrm = stored[inst_start + 1];
        uint8_t subop = static_cast<uint8_t>((modrm >> 3u) & 0x7u);
        is_call = (subop == 0x2u || subop == 0x3u);
      }

      if (is_call) {
        saw_call = true;
        transform.clear();
      } else if (opcode == 0x04u && saw_call && inst_start + inst_len > 1) {
        const uint8_t imm = stored[inst_start + inst_len - 1];
        transform = ("low8_add_const:" + std::to_string(imm));
      } else if ((opcode == 0xC3u || opcode == 0xC2u) && saw_call) {
        return transform;
      }

      cursor = inst_start + inst_len;
      ++decoded;
    }
    return std::string();
  };

  const std::string requested_root_entry_seed_exprs =
      (batch_vas.empty() && requested_func_va != 0)
          ? scanExportEntryHiddenSeedExprs(requested_func_va)
          : std::string();
  const bool requested_root_rax_return_hint =
      scanRequestedRootUsesRaxReturnHint(requested_func_va);
  const std::string requested_root_return_transform =
      scanRequestedRootReturnTransform(requested_func_va);
  auto reapplyRequestedRootEntrySeedHint = [&](uint64_t tagged_root_va) {
    const bool has_seed_hint = !requested_root_entry_seed_exprs.empty();
    const bool has_return_transform = !requested_root_return_transform.empty();
    if (!has_seed_hint && !requested_root_rax_return_hint && !has_return_transform)
      return;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      if (omill::extractEntryVA(F.getName()) != tagged_root_va)
        continue;
      if (has_seed_hint) {
        F.addFnAttr("omill.export_entry_seed_exprs",
                    requested_root_entry_seed_exprs);
      }
      if (requested_root_rax_return_hint)
        F.addFnAttr("omill.requested_root_rax_return_hint", "1");
      if (has_return_transform) {
        F.addFnAttr("omill.requested_root_return_transform",
                    requested_root_return_transform);
      }
    }
  };

  if (!NoABI) {
    if (!batch_vas.empty()) {
      for (uint64_t va : batch_vas) {
        annotateExportCallsiteWin64ParamHint(va, va);
        annotateExportEntryHiddenSeedHint(va, va);
      }
    } else if (func_va != 0) {
      annotateExportCallsiteWin64ParamHint(requested_func_va, func_va);
      reapplyRequestedRootEntrySeedHint(func_va);
    }
  }
  const uint64_t largest_executable_section_size = [&]() -> uint64_t {
    if (RawBinary)
      return raw_code.size();
    uint64_t max_size = 0;
    for (const auto &cs : pe.code_sections) {
      if (cs.storage_index < pe.section_storage.size())
        max_size = std::max<uint64_t>(max_size,
                                      pe.section_storage[cs.storage_index].size());
    }
    return max_size;
  }();
  const uint64_t executable_section_count =
      RawBinary ? 1ull : static_cast<uint64_t>(pe.code_sections.size());
  const uint64_t requested_root_rva =
      (!RawBinary && requested_func_va >= pe.image_base)
          ? (requested_func_va - pe.image_base)
          : 0;
  auto foldRecursiveDeclarationAliases = [&]() {
    for (auto &F : llvm::make_early_inc_range(*module)) {
      if (!F.isDeclaration())
        continue;
      auto fname = F.getName();
      if (!fname.starts_with("sub_"))
        continue;
      size_t dot = fname.rfind('.');
      if (dot == StringRef::npos || dot + 1 >= fname.size())
        continue;
      auto suffix = fname.drop_front(dot + 1);
      unsigned clone_index = 0;
      if (suffix.getAsInteger(10, clone_index))
        continue;
      std::string base_name = fname.take_front(dot).str();
      if (auto *base = module->getFunction(base_name)) {
        if (!base->isDeclaration()) {
          F.replaceAllUsesWith(base);
          F.eraseFromParent();
          errs() << "Folded recursive declaration alias " << fname
                 << " -> " << base_name << "\n";
        }
      }
    }
  };
  foldRecursiveDeclarationAliases();

  auto markRequestedRootInternalOutputRoots = [&](uint64_t root_va) {
    if (root_va == 0)
      return;
    bool marked = false;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      if (omill::extractEntryVA(F.getName()) == root_va ||
          omill::extractBlockPC(F.getName()) == root_va) {
        F.addFnAttr("omill.internal_output_root", "1");
        marked = true;
      }
    }
    if (!marked) {
      if (auto *F = omill::findLiftedOrCoveredFunctionByPC(*module, root_va);
          F && !F->isDeclaration()) {
        F->addFnAttr("omill.internal_output_root", "1");
      }
    }
  };
  if (func_va != 0)
    markRequestedRootInternalOutputRoots(func_va);

  omill::DevirtualizationRequest devirtualization_request;
  devirtualization_request.output_mode =
      NoABI ? omill::DevirtualizationOutputMode::kNoABI
            : omill::DevirtualizationOutputMode::kABI;
  devirtualization_request.deobfuscate = Deobfuscate;
  devirtualization_request.verify_rewrites =
      VerifyGenericStaticDevirtualization;
  devirtualization_request.force_devirtualize = force_devirtualize;
  devirtualization_request.auto_detect = true;
  if (!batch_vas.empty()) {
    devirtualization_request.root_vas.assign(batch_vas.begin(), batch_vas.end());
  } else if (func_va != 0) {
    devirtualization_request.root_vas.push_back(func_va);
  }

  const bool export_root_has_hidden_entry_seed_exprs =
      batch_vas.empty() && func_va != 0 &&
      !scanExportEntryHiddenSeedExprs(func_va).empty();
  omill::DevirtualizationCompatInputs devirtualization_compat_inputs;
  devirtualization_compat_inputs.requested_block_lift = BlockLift;
  devirtualization_compat_inputs.requested_generic_static =
      GenericStaticDevirtualize;
  devirtualization_compat_inputs.requested_vm_entry_mode = vm_mode;
  devirtualization_compat_inputs.env_generic_static =
      env_generic_static_devirtualize;
  devirtualization_compat_inputs.env_verify_generic_static =
      env_verify_generic_static_devirtualize;
  devirtualization_compat_inputs.env_force_generic_static =
      force_generic_static_devirtualize;
  devirtualization_compat_inputs.no_abi = NoABI;
  devirtualization_compat_inputs.requested_root_is_export =
      requested_root_is_export;
  devirtualization_compat_inputs.export_root_has_hidden_entry_seed_exprs =
      !NoABI && export_root_has_hidden_entry_seed_exprs;
  devirtualization_compat_inputs.requested_root_rva = requested_root_rva;
  devirtualization_compat_inputs.largest_executable_section_size =
      largest_executable_section_size;
  devirtualization_compat_inputs.executable_section_count =
      executable_section_count;

  omill::DevirtualizationPolicy devirtualization_policy;
