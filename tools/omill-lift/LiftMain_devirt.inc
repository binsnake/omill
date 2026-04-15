  omill::DevirtualizationOrchestrator devirtualization_orchestrator(
      devirtualization_policy, iterative_session);
  omill::DevirtualizationRuntime devirtualization_runtime(
      devirtualization_orchestrator);
  auto classifyRuntimeRecoveryQuality = [&](const llvm::Module &M) {
    return devirtualization_runtime.classifyRecoveryQuality(M);
  };
  auto classifySerializedRuntimeRecoveryQuality =
      [&](const llvm::Module &M)
      -> std::optional<omill::RecoveryQualitySummary> {
    if (verifyModule(const_cast<llvm::Module &>(M), nullptr))
      return classifyRuntimeRecoveryQuality(M);

    std::string ir_text;
    llvm::raw_string_ostream os(ir_text);
    M.print(os, nullptr);
    os.flush();

    llvm::LLVMContext verify_ctx;
    llvm::SMDiagnostic parse_error;
    auto verify_module =
        llvm::parseAssemblyString(ir_text, parse_error, verify_ctx);
    if (!verify_module || verifyModule(*verify_module, nullptr))
      return classifyRuntimeRecoveryQuality(M);
    return classifyRuntimeRecoveryQuality(*verify_module);
  };
  auto emit_latest_devirtualization_epoch = [&](llvm::StringRef message) {
    const auto &epochs = devirtualization_orchestrator.session().epochs;
    if (epochs.empty())
      return;
    const auto &epoch = epochs.back();
    events.emitInfo(
        "devirtualization_epoch", message.str(),
        {{"epoch", omill::toString(epoch.epoch)},
         {"changed", epoch.changed},
         {"clean", epoch.clean},
         {"units_lifted", static_cast<int64_t>(epoch.units_lifted)},
         {"units_reused", static_cast<int64_t>(epoch.units_reused)},
         {"unresolved_complete",
          static_cast<int64_t>(epoch.unresolved_exits_complete)},
         {"unresolved_incomplete",
          static_cast<int64_t>(epoch.unresolved_exits_incomplete)},
         {"unresolved_invalidated",
          static_cast<int64_t>(epoch.unresolved_exits_invalidated)},
         {"normalization_failures",
          static_cast<int64_t>(epoch.normalization_failures)},
         {"dispatches_materialized",
          static_cast<int64_t>(epoch.dispatches_materialized)},
         {"leaked_runtime_artifacts",
          static_cast<int64_t>(epoch.leaked_runtime_artifacts)}});
  };
  devirtualization_orchestrator.recordEpoch(
      omill::DevirtualizationEpoch::kInitialLiftNormalization, *module,
      devirtualization_request.output_mode, /*changed=*/true,
      "initial lift complete");
  emit_latest_devirtualization_epoch("initial lift complete");
  auto devirtualization_compat_plan =
      devirtualization_orchestrator.buildDriverCompatPlan(
          *module, devirtualization_request, devirtualization_compat_inputs);
  const auto &devirtualization_plan = devirtualization_compat_plan.execution;
  devirtualization_orchestrator.recordEpoch(
      omill::DevirtualizationEpoch::kDetectionSeedExtraction, *module,
      devirtualization_request.output_mode, /*changed=*/false,
      "devirtualization detection complete");
  emit_latest_devirtualization_epoch("devirtualization detection complete");
  devirtualization_orchestrator.recordEpoch(
      omill::DevirtualizationEpoch::kFrontierScheduling, *module,
      devirtualization_request.output_mode,
      !omill::collectSessionFrontierTargets(
           devirtualization_orchestrator.session())
           .empty(),
      "frontier scheduling complete");
  emit_latest_devirtualization_epoch("frontier scheduling complete");
  events.emitInfo("devirtualization_detection_completed",
                  "devirtualization detection complete",
                  {{"should_devirtualize",
                    devirtualization_plan.enable_devirtualization},
                   {"confidence",
                    omill::toString(
                        devirtualization_plan.detection.confidence)},
                   {"unresolved_dispatches",
                    static_cast<int64_t>(
                        devirtualization_plan.detection.unresolved_dispatches)},
                   {"protected_boundaries",
                    static_cast<int64_t>(
                        devirtualization_plan.detection.protected_boundaries)},
                   {"reasons",
                    static_cast<int64_t>(
                        devirtualization_plan.detection.reasons.size())}});
  if (devirtualization_plan.enable_devirtualization) {
    events.emitInfo("devirtualization_plan_selected",
                    "devirtualization plan selected",
                    {{"use_block_lift", devirtualization_compat_plan.use_block_lift},
                     {"use_generic_static",
                      devirtualization_compat_plan.use_generic_static},
                     {"disable_legacy_vm_path",
                      devirtualization_plan.disable_legacy_vm_path},
                     {"export_root_fallback_mode",
                      omill::toString(
                          devirtualization_compat_plan.export_root_fallback_mode)},
                     {"generic_static_reason",
                      omill::toString(
                          devirtualization_compat_plan.generic_static_reason)},
                     {"always_inline_reason",
                      omill::toString(
                          devirtualization_compat_plan.always_inline_reason)},
                     {"use_pre_abi_noabi_cleanup",
                      devirtualization_compat_plan.use_pre_abi_noabi_cleanup}});
  }

  omill::PipelineOptions opts;
  opts.target_arch = target_arch;
  opts.target_os = target_os_str;
  opts.recover_abi = false;
  opts.no_abi_mode = NoABI;
  opts.deobfuscate = Deobfuscate;
  opts.resolve_indirect_targets = ResolveTargets;
  opts.max_resolution_iterations = MaxIterations;
  opts.interprocedural_const_prop = IPCP;
  opts.use_block_lifting = use_block_lift_mode;
  opts.vm_devirtualize = vm_mode;
  opts.generic_static_devirtualize =
      force_devirtualize || GenericStaticDevirtualize ||
      env_generic_static_devirtualize;
  opts.verify_generic_static_devirtualization =
      VerifyGenericStaticDevirtualization ||
      env_verify_generic_static_devirtualize;
  devirtualization_orchestrator.applyDriverCompatPlan(
      devirtualization_compat_plan, opts);
  // Restore CLI-driven flags that applyDriverCompatPlan may have
  // overwritten with the compat plan's values.
  if (NoABI)
    opts.no_abi_mode = true;
  if (GenericStaticDevirtualize)
    opts.generic_static_devirtualize = true;
  if (devirtualization_plan.enable_devirtualization)
    opts.session_graph = &devirtualization_orchestrator.session().graph;
  if (devirtualization_compat_plan.suppress_legacy_vm_mode) {
    events.emitInfo("legacy_vm_mode_suppressed",
                    "legacy VM mode suppressed by devirtualization plan",
                    {{"forced", force_devirtualize},
                     {"reason", omill::toString(
                                    devirtualization_compat_plan
                                        .legacy_vm_mode_reason)}});
  }
  const bool fast_plain_export_root_fallback =
      devirtualization_compat_plan.export_root_fallback_mode ==
      omill::DevirtualizationExportRootFallbackMode::kFastPlain;
  const bool stable_no_gsd_export_root_fallback =
      devirtualization_compat_plan.export_root_fallback_mode ==
      omill::DevirtualizationExportRootFallbackMode::kStableLarge;
  if (fast_plain_export_root_fallback) {
    errs() << "Generic static devirtualization skipped: using fast "
              "non-GSD path for a small plain export root\n";
    events.emitInfo("generic_static_devirtualization_skipped",
                    "generic static devirtualization skipped",
                    {{"reason", omill::toString(
                                    devirtualization_compat_plan
                                        .generic_static_reason)}});
  }
  if (!fast_plain_export_root_fallback && stable_no_gsd_export_root_fallback) {
    errs() << "Generic static devirtualization skipped: using stable "
              "non-GSD export-root path for a large export root\n";
    events.emitInfo("generic_static_devirtualization_skipped",
                    "generic static devirtualization skipped",
                    {{"reason", omill::toString(
                                    devirtualization_compat_plan
                                        .generic_static_reason)}});
  }
  if (!fast_plain_export_root_fallback &&
      !stable_no_gsd_export_root_fallback &&
      !opts.generic_static_devirtualize &&
      devirtualization_compat_plan.generic_static_reason ==
          omill::DevirtualizationCompatReason::kNoVmLikeCandidates) {
    errs() << "Generic static devirtualization skipped: no VM-like candidates\n";
    events.emitInfo("generic_static_devirtualization_skipped",
                    "generic static devirtualization skipped",
                    {{"reason", omill::toString(
                                    devirtualization_compat_plan
                                        .generic_static_reason)}});
  }
  const bool auto_skip_always_inline_for_internal_root =
      devirtualization_compat_plan.auto_skip_always_inline;
  std::unique_ptr<ScopedEnvOverride> auto_skip_always_inline_guard;
  // Don't suppress the always-inliner when block-lifting is active —
  // the block lifter emits one function per basic block, and those
  // must be inlined into the output root to produce coherent IR.
  if ((auto_skip_always_inline_for_internal_root ||
       stable_no_gsd_export_root_fallback) &&
      !use_block_lift_mode) {
    auto_skip_always_inline_guard =
        std::make_unique<ScopedEnvOverride>("OMILL_SKIP_ALWAYS_INLINE", "1");
    errs() << "Always-inliner suppressed after selecting a stable non-GSD "
              "root path\n";
    events.emitInfo("always_inliner_auto_suppressed",
                    "always-inliner suppressed after selecting stable root path",
                    {{"reason", omill::toString(
                                    devirtualization_compat_plan
                                        .always_inline_reason)}});
  }
  const bool use_pre_abi_noabi_cleanup =
      devirtualization_compat_plan.use_pre_abi_noabi_cleanup;
  if (!DumpVirtualModel.empty())
    setEnvIfUnset("OMILL_DUMP_VIRTUAL_MODEL", DumpVirtualModel.c_str());
  if (auto v = parseBoolEnv("OMILL_SKIP_BLOCK_MERGE"); v.value_or(false)) {
    opts.merge_block_functions_after_fixpoint = false;
  }
  const bool preserve_lift_infrastructure = ResolveTargets && !NoABI;
  opts.preserve_lifted_semantics = preserve_lift_infrastructure;
  if (opts.generic_static_devirtualize) {
    errs() << "Generic static devirtualization enabled\n";
    events.emitInfo("generic_static_devirtualization_enabled",
                    "generic static devirtualization enabled",
                    {{"verify", opts.verify_generic_static_devirtualization}});
  }

  auto fixLiftedFunctionNamingCollisions = [&]() {
    for (auto &F : llvm::make_early_inc_range(*module)) {
      if (!F.isDeclaration())
        continue;
      auto name = F.getName();
      if (!name.starts_with("sub_"))
        continue;
      for (int i = 1; i <= 20; ++i) {
        std::string def_name = (name + "." + llvm::Twine(i)).str();
        if (auto *def = module->getFunction(def_name)) {
          if (!def->isDeclaration()) {
            F.replaceAllUsesWith(def);
            F.eraseFromParent();
            def->setName(name);
            break;
          }
        }
      }
    }
  };

  auto tagNewlyLiftedFunctions =
      [&](llvm::StringRef attr_name,
          const llvm::DenseSet<llvm::Function *> &pre_lift_funcs) {
        for (auto &F : *module) {
          if (!pre_lift_funcs.count(&F) && !F.isDeclaration())
            F.addFnAttr(attr_name, "1");
        }
      };

  auto clearLiftRoundAttr = [&](llvm::StringRef attr_name) {
    for (auto &F : *module) {
      if (F.getFnAttribute(attr_name).isValid())
        F.removeFnAttr(attr_name);
    }
  };

  auto hasOpenOutputRootHazards = [&]() {
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee)
            return true;

          auto name = callee->getName();
          if (omill::isDispatchIntrinsicName(name))
            return true;
          if (name.starts_with("blk_") && callee->isDeclaration())
            return true;
          if (name.starts_with("sub_") && !name.ends_with("_native") &&
              callee->isDeclaration())
            return true;
        }
      }
    }
    return false;
  };

  auto moduleHasStructuralOutputFrontierArtifacts = [&]() {
    if (devirtualization_plan.enable_devirtualization &&
        devirtualization_orchestrator.hasBlockingUnstableFrontierState(
            *module)) {
      return true;
    }

    auto has_live_uses = [&](llvm::StringRef name) {
      if (auto *F = module->getFunction(name))
        return !F->use_empty();
      return false;
    };

    if (has_live_uses("__omill_missing_block_handler")) {
      return true;
    }

    for (auto &F : *module) {
      if (F.isDeclaration() &&
          (F.getName().starts_with("blk_") ||
           F.getName().starts_with("block_"))) {
        return true;
      }
    }

    return hasOpenOutputRootHazards();
  };

  auto countDefinedOutputRoots = [&]() {
    unsigned count = 0;
    for (auto &F : *module) {
      if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
        ++count;
    }
    return count;
  };

  auto pruneToDefinedOutputRootClosure = [&]() {
    auto isCodeAddressForPrune = [&](uint64_t target) {
      if (RawBinary)
        return target >= BaseAddress &&
               target < BaseAddress + raw_code.size();
      for (auto &sec : pe.code_sections) {
        if (target >= sec.va && target < sec.va + sec.size)
          return true;
      }
      return false;
    };
    auto lookupDefinedLiftedOrBlockTarget =
        [&](uint64_t target) -> llvm::Function * {
      for (llvm::StringRef prefix : {"blk_", "block_", "sub_"}) {
        std::string name = (prefix + llvm::utohexstr(target)).str();
        if (auto *fn = module->getFunction(name); fn && !fn->isDeclaration())
          return fn;
      }
      return nullptr;
    };

    llvm::SmallVector<llvm::Function *, 16> roots;
    for (auto &F : *module) {
      if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
        roots.push_back(&F);
    }
    if (roots.empty())
      return;

    llvm::SmallVector<llvm::Function *, 32> worklist(roots.begin(), roots.end());
    auto patchable_targets = omill::collectOutputRootClosureTargets(
        *module,
        [&](uint64_t target) { return isCodeAddressForPrune(target); },
        [&](uint64_t target) {
          return lookupDefinedLiftedOrBlockTarget(target) != nullptr;
        },
        [&](uint64_t target) { return target; },
        /*include_defined_targets=*/true);
    auto enqueuePatchableTargets = [&](const std::vector<uint64_t> &targets) {
      for (uint64_t target : targets) {
        if (auto *target_fn = lookupDefinedLiftedOrBlockTarget(target))
          worklist.push_back(target_fn);
      }
    };
    enqueuePatchableTargets(patchable_targets.constant_code_targets);
    enqueuePatchableTargets(patchable_targets.constant_calli_targets);
    enqueuePatchableTargets(patchable_targets.constant_dispatch_targets);
    enqueuePatchableTargets(
        patchable_targets.annotated_vm_continuation_targets);

    llvm::DenseSet<llvm::Function *> reachable;
    while (!worklist.empty()) {
      llvm::Function *F = worklist.pop_back_val();
      if (!F || F->isDeclaration() || !reachable.insert(F).second)
        continue;
      for (auto &BB : *F) {
        for (auto &I : BB) {
          for (llvm::Value *operand : I.operands()) {
            auto *callee = llvm::dyn_cast<llvm::Function>(operand);
            if (!callee || callee->isDeclaration())
              continue;
            worklist.push_back(callee);
          }
        }
      }
    }

    auto isPrunableLiftedOrDeadHelper = [&](llvm::Function &F) {
      if (reachable.count(&F))
        return false;
      if (F.hasFnAttribute("omill.output_root"))
        return false;
      if (F.getName().starts_with("__omill_compact_recursive_source_oracle"))
        return false;
      return F.getName().starts_with("blk_") || F.getName().starts_with("block_") ||
             F.getName().starts_with("sub_") ||
             F.getName().starts_with("vm_entry_") ||
             omill::isDispatchIntrinsicName(F.getName());
    };

    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      if (!isPrunableLiftedOrDeadHelper(F))
        continue;
      if (!F.hasLocalLinkage())
        F.setLinkage(llvm::GlobalValue::InternalLinkage);
    }

    {
      llvm::ModulePassManager DeadMPM;
      DeadMPM.addPass(llvm::GlobalDCEPass());
      DeadMPM.run(*module, MAM);
    }

    llvm::SmallVector<llvm::Function *, 32> dead_decls;
    for (auto &F : *module) {
      if (!F.isDeclaration() || !F.use_empty())
        continue;
      if (F.getName().starts_with("blk_") || F.getName().starts_with("block_") ||
          F.getName().starts_with("sub_") ||
          F.getName().starts_with("vm_entry_") ||
          omill::isDispatchIntrinsicName(F.getName())) {
        dead_decls.push_back(&F);
      }
    }
    for (llvm::Function *F : dead_decls)
      F->eraseFromParent();
  };

  std::function<void()> rerunLateNativeArgRepair = []() {};
  auto canonicalizeTerminalMissingBlockDispatchSuffixes = [&]() -> bool {
    if (!opts.no_abi_mode)
      return false;

    auto *trap = llvm::Intrinsic::getOrInsertDeclaration(
        module.get(), llvm::Intrinsic::trap);
    llvm::SmallVector<llvm::CallInst *, 8> terminal_calls;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || callee->getName() != "__omill_missing_block_handler")
            continue;

          bool saw_terminal_dispatch = false;
          bool conflict = false;
          for (llvm::Instruction *next = call->getNextNonDebugInstruction();
               next; next = next->getNextNonDebugInstruction()) {
            if (llvm::isa<llvm::ReturnInst>(next))
              break;
            if (auto *CB = llvm::dyn_cast<llvm::CallBase>(next)) {
              auto *next_callee = CB->getCalledFunction();
              if (!next_callee) {
                conflict = true;
                break;
              }
              if (next_callee->isIntrinsic())
                continue;
              if (next_callee->getName() == "__remill_jump" ||
                  omill::isDispatchJumpName(next_callee->getName())) {
                saw_terminal_dispatch = true;
                continue;
              }
              if (next_callee->getName() == "__omill_missing_block_handler")
                continue;
              conflict = true;
              break;
            }
            if (next->isTerminator() && !llvm::isa<llvm::ReturnInst>(next)) {
              conflict = true;
              break;
            }
          }

          if (!conflict && saw_terminal_dispatch)
            terminal_calls.push_back(call);
        }
      }
    }

    bool changed = false;
    for (auto *call : terminal_calls) {
      auto *BB = call->getParent();
      llvm::IRBuilder<> ir(call);
      ir.CreateCall(trap);
      auto *new_term = ir.CreateUnreachable();
      while (&BB->back() != new_term) {
        auto &dead = BB->back();
        if (!dead.use_empty() && !dead.getType()->isVoidTy()) {
          dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
        }
        dead.eraseFromParent();
      }
      changed = true;
    }

    return changed;
  };
  auto runFinalOutputCleanup = [&]() {
    if (parseBoolEnv("OMILL_SKIP_OUTPUT_FINAL_CLEANUP").value_or(false))
      return;
    if (devirtualization_plan.enable_devirtualization)
      devirtualization_orchestrator.refreshSessionState(*module);
    if (canonicalizeTerminalMissingBlockDispatchSuffixes())
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    if (moduleHasStructuralOutputFrontierArtifacts())
      return;
    {
      llvm::ModulePassManager LateMPM;
      omill::buildLateCleanupPipeline(LateMPM, opts);
      LateMPM.run(*module, MAM);
    }
    llvm::PassBuilder PB;
    llvm::ModulePassManager MPM =
        PB.buildPerModuleDefaultPipeline(llvm::OptimizationLevel::O2);
    MPM.run(*module, MAM);
    if (canonicalizeTerminalMissingBlockDispatchSuffixes())
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    rerunLateNativeArgRepair();
    if (std::getenv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS") != nullptr) {
      std::error_code ec;
      llvm::raw_fd_ostream os("after_final_output_cleanup.ll", ec,
                              llvm::sys::fs::OF_Text);
      if (!ec)
        module->print(os, nullptr);
    }
  };
  std::function<void()> rerunFocusedNativeHelperControlFlowRecovery = []() {};
  [[maybe_unused]] auto rewriteLocalNativeJumpTableDispatches = [&]() {
    auto parseNativeTargetPC = [&](llvm::StringRef name) -> uint64_t {
      if (uint64_t pc = omill::extractEntryVA(name); pc != 0)
        return pc;
      auto parsePrefixedHex = [&](llvm::StringRef prefix) -> uint64_t {
        if (!name.starts_with(prefix))
          return 0;
        auto rest = name.drop_front(prefix.size());
        size_t hex_len = 0;
        while (hex_len < rest.size() && llvm::isHexDigit(rest[hex_len]))
          ++hex_len;
        if (hex_len == 0)
          return 0;
        uint64_t pc = 0;
        if (rest.substr(0, hex_len).getAsInteger(16, pc))
          return 0;
        return pc;
      };
      if (uint64_t pc = parsePrefixedHex("blk_"); pc != 0)
        return pc;
      if (uint64_t pc = parsePrefixedHex("block_"); pc != 0)
        return pc;
      return 0;
    };

    llvm::DenseMap<uint64_t, llvm::Function *> local_native_targets;
    llvm::SmallDenseSet<uint64_t, 16> local_case_pcs;
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.getName().ends_with("_native"))
        continue;
      if (uint64_t pc = parseNativeTargetPC(F.getName()); pc != 0)
        local_native_targets[pc] = &F;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *SI = llvm::dyn_cast<llvm::SwitchInst>(&I);
          if (!SI || !SI->getCondition()->getType()->isIntegerTy(64))
            continue;
          for (auto &Case : SI->cases())
            local_case_pcs.insert(Case.getCaseValue()->getZExtValue());
        }
      }
    }

    auto findStateOffsetPtr = [&](llvm::Function &F, uint64_t offset)
        -> llvm::Value * {
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(&I);
          if (!GEP || GEP->getNumOperands() < 2)
            continue;
          auto *idx = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(1));
          if (!idx || idx->getZExtValue() != offset)
            continue;
          return GEP;
        }
      }
      return nullptr;
    };

    unsigned rewrite_count = 0;
    unsigned void_rewrite_count = 0;
    const bool debug_public_root_seeds =
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.getName().ends_with("_native"))
        continue;
      auto *RetST = llvm::dyn_cast<llvm::StructType>(F.getReturnType());
      if (!RetST || RetST->getNumElements() != 8) {
        if (debug_public_root_seeds && F.getName() == "blk_18000227d_native")
          errs() << "[abi-post] local-jt skip ret-shape " << F.getName()
                 << "\n";
        continue;
      }

      llvm::CallBase *dispatch_call = nullptr;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          auto *Callee = CB ? CB->getCalledFunction() : nullptr;
          if (!Callee)
            continue;
          auto Name = Callee->getName();
          if (omill::isDispatchJumpName(Name)) {
            dispatch_call = CB;
            break;
          }
        }
        if (dispatch_call)
          break;
      }
      if (!dispatch_call) {
        if (debug_public_root_seeds && F.getName() == "blk_18000227d_native")
          errs() << "[abi-post] local-jt skip no-dispatch " << F.getName()
                 << "\n";
        continue;
      }

      auto *target_pc = dispatch_call->getArgOperand(1);
      auto *eax_ptr = findStateOffsetPtr(F, 2216);
      auto *arg2232_ptr = findStateOffsetPtr(F, 2232);
      auto *arg2280_ptr = findStateOffsetPtr(F, 2280);
      auto *arg2296_ptr = findStateOffsetPtr(F, 2296);
      auto *arg2328_ptr = findStateOffsetPtr(F, 2328);
      auto *arg2408_ptr = findStateOffsetPtr(F, 2408);
      auto *arg2440_ptr = findStateOffsetPtr(F, 2440);
      auto *arg2456_ptr = findStateOffsetPtr(F, 2456);
      if (!eax_ptr || !arg2232_ptr || !arg2280_ptr || !arg2296_ptr ||
          !arg2328_ptr || !arg2408_ptr || !arg2440_ptr || !arg2456_ptr) {
        if (debug_public_root_seeds && F.getName() == "blk_18000227d_native") {
          errs() << "[abi-post] local-jt skip ptrs " << F.getName()
                 << " eax=" << (eax_ptr != nullptr)
                 << " 2232=" << (arg2232_ptr != nullptr)
                 << " 2280=" << (arg2280_ptr != nullptr)
                 << " 2296=" << (arg2296_ptr != nullptr)
                 << " 2328=" << (arg2328_ptr != nullptr)
                 << " 2408=" << (arg2408_ptr != nullptr)
                 << " 2440=" << (arg2440_ptr != nullptr)
                 << " 2456=" << (arg2456_ptr != nullptr) << "\n";
        }
        continue;
      }

      auto *dispatch_block = dispatch_call->getParent();
      auto *load_block = dispatch_block->splitBasicBlock(
          std::next(dispatch_call->getIterator()), "resolved.dispatch.loads");
      auto *switch_block = dispatch_block->splitBasicBlock(
          dispatch_call->getIterator(), "resolved.dispatch.switch");
      switch_block->getTerminator()->eraseFromParent();

      llvm::IRBuilder<> Builder(switch_block);
      auto *state2232 = Builder.CreateLoad(Builder.getInt64Ty(), arg2232_ptr,
                                           "tb.state2232");
      auto *state2280 = Builder.CreateLoad(Builder.getInt64Ty(), arg2280_ptr,
                                           "tb.state2280");
      auto *state2328 = Builder.CreateLoad(Builder.getInt64Ty(), arg2328_ptr,
                                           "tb.state2328");
      auto *state2440 = Builder.CreateLoad(Builder.getInt64Ty(), arg2440_ptr,
                                           "tb.state2440");

      auto *switch_inst =
          Builder.CreateSwitch(target_pc, dispatch_block, local_case_pcs.size());

      for (uint64_t case_pc : local_case_pcs) {
        if (case_pc == 0)
          continue;

        if (auto it = local_native_targets.find(case_pc);
            it != local_native_targets.end()) {
          auto *CaseRetST =
              llvm::dyn_cast<llvm::StructType>(it->second->getReturnType());
          if (!CaseRetST || CaseRetST->getNumElements() != 8)
            continue;
          auto *case_block = llvm::BasicBlock::Create(
              ctx, "resolved.case." + llvm::utohexstr(case_pc), &F, load_block);
          llvm::IRBuilder<> case_builder(case_block);
          auto *case_call = case_builder.CreateCall(
              it->second->getFunctionType(), it->second,
              {state2232, state2280, state2328, state2440});
          case_call->setCallingConv(it->second->getCallingConv());
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {0}), eax_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {1}), arg2232_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {2}), arg2328_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {3}), arg2296_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {4}), arg2280_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {5}), arg2408_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {6}), arg2440_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {7}), arg2456_ptr);
          case_builder.CreateBr(load_block);
          switch_inst->addCase(case_builder.getInt64(case_pc), case_block);
        } else {
          auto *loop_block = llvm::BasicBlock::Create(
              ctx, "resolved.selfloop." + llvm::utohexstr(case_pc), &F,
              load_block);
          llvm::IRBuilder<> loop_builder(loop_block);
          loop_builder.CreateBr(loop_block);
          switch_inst->addCase(loop_builder.getInt64(case_pc), loop_block);
        }
      }

      ++rewrite_count;
      if (debug_public_root_seeds && F.getName() == "blk_18000227d_native")
        errs() << "[abi-post] local-jt rewrote " << F.getName() << "\n";
    }

    for (auto &F : *module) {
      if (F.isDeclaration() || !F.getName().ends_with("_native") ||
          !F.getReturnType()->isVoidTy()) {
        continue;
      }

      bool already_rewritten = false;
      for (auto &BB : F) {
        auto BBName = BB.getName();
        if (BBName.starts_with("resolved.dispatch") ||
            BBName.starts_with("resolved.case.") ||
            BBName.starts_with("resolved.selfloop.")) {
          already_rewritten = true;
          break;
        }
      }
      if (already_rewritten)
        continue;

      llvm::CallBase *dispatch_call = nullptr;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          auto *Callee = CB ? CB->getCalledFunction() : nullptr;
          if (!Callee)
            continue;
          auto Name = Callee->getName();
          if (omill::isDispatchJumpName(Name)) {
            dispatch_call = CB;
            break;
          }
        }
        if (dispatch_call)
          break;
      }
      if (!dispatch_call)
        continue;

      auto *eax_ptr = findStateOffsetPtr(F, 2216);
      auto *arg2232_ptr = findStateOffsetPtr(F, 2232);
      auto *arg2280_ptr = findStateOffsetPtr(F, 2280);
      auto *arg2296_ptr = findStateOffsetPtr(F, 2296);
      auto *arg2328_ptr = findStateOffsetPtr(F, 2328);
      auto *arg2408_ptr = findStateOffsetPtr(F, 2408);
      auto *arg2440_ptr = findStateOffsetPtr(F, 2440);
      auto *arg2456_ptr = findStateOffsetPtr(F, 2456);
      if (!eax_ptr || !arg2232_ptr || !arg2280_ptr || !arg2296_ptr ||
          !arg2328_ptr || !arg2408_ptr || !arg2440_ptr || !arg2456_ptr) {
        continue;
      }

      auto *switch_block = dispatch_call->getParent();
      auto *after_block =
          switch_block->splitBasicBlock(dispatch_call->getIterator(),
                                       "resolved.dispatch.dynamic");
      switch_block->getTerminator()->eraseFromParent();

      llvm::IRBuilder<> Builder(switch_block);
      auto *state2232 = Builder.CreateLoad(Builder.getInt64Ty(), arg2232_ptr,
                                           "tb.state2232");
      auto *state2280 = Builder.CreateLoad(Builder.getInt64Ty(), arg2280_ptr,
                                           "tb.state2280");
      auto *state2328 = Builder.CreateLoad(Builder.getInt64Ty(), arg2328_ptr,
                                           "tb.state2328");
      auto *state2440 = Builder.CreateLoad(Builder.getInt64Ty(), arg2440_ptr,
                                           "tb.state2440");
      auto *switch_inst = Builder.CreateSwitch(dispatch_call->getArgOperand(1),
                                               after_block,
                                               local_case_pcs.size());

      for (uint64_t case_pc : local_case_pcs) {
        if (case_pc == 0)
          continue;

        if (auto it = local_native_targets.find(case_pc);
            it != local_native_targets.end()) {
          auto *CaseRetST =
              llvm::dyn_cast<llvm::StructType>(it->second->getReturnType());
          if (!CaseRetST || CaseRetST->getNumElements() != 8)
            continue;
          auto *case_block = llvm::BasicBlock::Create(
              ctx, "resolved.case." + llvm::utohexstr(case_pc), &F,
              after_block);
          llvm::IRBuilder<> case_builder(case_block);
          auto *case_call = case_builder.CreateCall(
              it->second->getFunctionType(), it->second,
              {state2232, state2280, state2328, state2440});
          case_call->setCallingConv(it->second->getCallingConv());
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {0}), eax_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {1}), arg2232_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {2}), arg2328_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {3}), arg2296_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {4}), arg2280_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {5}), arg2408_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {6}), arg2440_ptr);
          case_builder.CreateStore(
              case_builder.CreateExtractValue(case_call, {7}), arg2456_ptr);
          case_builder.CreateBr(after_block);
          switch_inst->addCase(case_builder.getInt64(case_pc), case_block);
        }
      }

      ++void_rewrite_count;
    }

    if ((rewrite_count > 0 || void_rewrite_count > 0) && debug_public_root_seeds) {
      errs() << "[abi-post] local-native-jumptable-rewrite count="
             << rewrite_count << " void_count=" << void_rewrite_count << "\n";
    }
  };

  auto liftedNameFor = [&](uint64_t pc, bool native) {
    std::string name = "sub_" + llvm::Twine::utohexstr(pc).str();
    if (native)
      name += "_native";
    return name;
  };

  auto blockNameFor = [&](uint64_t pc, bool native) {
    std::string name = "blk_" + llvm::Twine::utohexstr(pc).str();
    if (native)
      name += "_native";
    return name;
  };

  auto findLiftedOrBlockFunction = [&](uint64_t pc, bool native)
      -> llvm::Function * {
    if (auto *fn = module->getFunction(liftedNameFor(pc, native)))
      return fn;
    return module->getFunction(blockNameFor(pc, native));
  };

  auto nearbyLiftedEntrySearchWindow = [&]() -> uint64_t {
    switch (target_arch) {
      case omill::TargetArch::kAArch64:
        return 4;
      case omill::TargetArch::kX86_64:
      default:
        return 128;
    }
  };

  auto extractLiftedOrBlockEntryPC =
      [&](llvm::StringRef name, bool native) -> std::optional<uint64_t> {
    if (native) {
      if (!name.ends_with("_native"))
        return std::nullopt;
      name = name.drop_back(strlen("_native"));
    } else if (name.ends_with("_native")) {
      return std::nullopt;
    }

    if (uint64_t pc = omill::extractEntryVA(name); pc != 0)
      return pc;

    if (name.starts_with("blk_"))
      name = name.drop_front(4);
    else if (name.starts_with("block_"))
      name = name.drop_front(6);
    else
      return std::nullopt;

    size_t hex_len = 0;
    while (hex_len < name.size() && llvm::isHexDigit(name[hex_len]))
      ++hex_len;
    if (hex_len == 0)
      return std::nullopt;

    uint64_t pc = 0;
    if (name.substr(0, hex_len).getAsInteger(16, pc) || pc == 0)
      return std::nullopt;
    return pc;
  };

  auto findNearestDefinedLiftedOrBlockFunction =
      [&](uint64_t target_pc, bool native,
          uint64_t *resolved_pc = nullptr) -> llvm::Function * {
    if (!target_pc)
      return nullptr;

    const uint64_t window = nearbyLiftedEntrySearchWindow();
    llvm::Function *best = nullptr;
    uint64_t best_pc = 0;
    uint64_t best_distance = std::numeric_limits<uint64_t>::max();

    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      auto entry_pc = extractLiftedOrBlockEntryPC(F.getName(), native);
      if (!entry_pc)
        continue;

      const uint64_t distance = (*entry_pc > target_pc)
                                    ? (*entry_pc - target_pc)
                                    : (target_pc - *entry_pc);
      if (distance == 0 || distance > window)
        continue;

      if (!best || distance < best_distance ||
          (distance == best_distance && *entry_pc < best_pc)) {
        best = &F;
        best_pc = *entry_pc;
        best_distance = distance;
      }
    }

    if (best && resolved_pc)
      *resolved_pc = best_pc;
    return best;
  };

  auto findExactOrNearbyLiftedOrBlockFunction =
      [&](uint64_t target_pc, bool native,
          uint64_t *resolved_pc = nullptr) -> llvm::Function * {
    if (auto *exact = findLiftedOrBlockFunction(target_pc, native)) {
      if (!exact->isDeclaration()) {
        if (resolved_pc)
          *resolved_pc = target_pc;
        return exact;
      }
    }
    return findNearestDefinedLiftedOrBlockFunction(target_pc, native,
                                                   resolved_pc);
  };

  auto collectConstantCodeCallTargets =
      [&](llvm::function_ref<bool(const llvm::Function &)> include_function) {
        llvm::DenseSet<uint64_t> targets;
        for (auto &F : *module) {
          if (!include_function(F))
            continue;
          for (auto &BB : F) {
            for (auto &I : BB) {
              auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!call || call->getCalledFunction())
                continue;
              auto *callee_op = call->getCalledOperand();
              llvm::ConstantInt *ci = nullptr;
              if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(callee_op)) {
                if (ce->getOpcode() == llvm::Instruction::IntToPtr)
                  ci = llvm::dyn_cast<llvm::ConstantInt>(ce->getOperand(0));
              }
              if (!ci) {
                if (auto *itp = llvm::dyn_cast<llvm::IntToPtrInst>(callee_op))
                  ci = llvm::dyn_cast<llvm::ConstantInt>(itp->getOperand(0));
              }
              if (!ci)
                continue;
              uint64_t target = ci->getZExtValue();
              if (target == 0)
                continue;

              bool in_code = false;
              if (RawBinary) {
                in_code = (target >= BaseAddress &&
                           target < BaseAddress + raw_code.size());
              } else {
                for (auto &sec : pe.code_sections) {
                  if (target >= sec.va && target < sec.va + sec.size) {
                    in_code = true;
                    break;
                  }
                }
              }
              if (!in_code)
                continue;

              targets.insert(target);
            }
          }
        }
        return targets;
      };

  auto isCodeAddressInCurrentInput = [&](uint64_t target) {
    if (target == 0)
      return false;
    if (RawBinary) {
      return target >= BaseAddress && target < BaseAddress + raw_code.size();
    }
    for (auto &sec : pe.code_sections) {
      if (target >= sec.va && target < sec.va + sec.size)
        return true;
    }
    return false;
  };

  auto hasDefinedLiftedOrBlockTarget = [&](uint64_t target) {
    auto *lifted = omill::findLiftedOrCoveredFunctionByPC(*module, target);
    if (lifted && !lifted->isDeclaration())
      return true;
    if (!NoABI) {
      if (auto *modeled =
              omill::findStructuralCodeTargetFunctionByPC(*module, target);
          modeled && modeled->isDeclaration() &&
          (modeled->hasFnAttribute("omill.native_direct_target_pc") ||
           modeled->hasFnAttribute("omill.native_boundary_pc") ||
           modeled->hasFnAttribute("omill.vm_enter_target_pc") ||
           modeled->hasFnAttribute("omill.executable_target_pc"))) {
        return true;
      }
    }
    return false;
  };

  auto findDefinedStructuralCodeTargetFunction =
      [&](uint64_t pc) -> llvm::Function * {
        if (!pc)
          return nullptr;
        for (auto &F : *module) {
          if (F.isDeclaration())
            continue;
          if (omill::extractStructuralCodeTargetPC(F) == pc)
            return &F;
        }
        return nullptr;
      };

  auto findPreferredDefinedCodeTargetFunction =
      [&](uint64_t pc, bool native = false) -> llvm::Function * {
        if (auto *target_fn = findLiftedOrBlockFunction(pc, native);
            target_fn && !target_fn->isDeclaration()) {
          return target_fn;
        }
        if (!native) {
          if (auto *structural = findDefinedStructuralCodeTargetFunction(pc)) {
            return structural;
          }
        }
        return nullptr;
      };

  auto patchConstantIntToPtrCallsToNative =
      [&](llvm::ArrayRef<uint64_t> targets, llvm::StringRef event_name,
          llvm::StringRef event_message) {
        llvm::DenseSet<uint64_t> target_set(targets.begin(), targets.end());
        unsigned patched_local_target = 0;
        unsigned patched_boundary = 0;

        auto maybeGetConstantCodeTarget =
            [&](llvm::CallBase &call) -> std::optional<uint64_t> {
          if (call.getCalledFunction())
            return std::nullopt;

          auto *callee_op = call.getCalledOperand();
          llvm::ConstantInt *ci = nullptr;
          if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(callee_op)) {
            if (ce->getOpcode() == llvm::Instruction::IntToPtr)
              ci = llvm::dyn_cast<llvm::ConstantInt>(ce->getOperand(0));
          }
          if (!ci) {
            if (auto *itp = llvm::dyn_cast<llvm::IntToPtrInst>(callee_op))
              ci = llvm::dyn_cast<llvm::ConstantInt>(itp->getOperand(0));
          }
          if (!ci)
            return std::nullopt;
          return ci->getZExtValue();
        };

        auto rewriteCallTarget = [&](llvm::CallBase &call, llvm::Value *callee) {
          auto *old_callee = call.getCalledOperand();
          call.setCalledOperand(callee);
          if (auto *inst = llvm::dyn_cast<llvm::Instruction>(old_callee)) {
            if (inst->use_empty())
              inst->eraseFromParent();
          }
        };

        for (auto &F : *module) {
          for (auto &BB : F) {
            for (auto &I : llvm::make_early_inc_range(BB)) {
              auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
              if (!call)
                continue;

              auto pc = maybeGetConstantCodeTarget(*call);
              if (!pc || !target_set.contains(*pc) || *pc == 0)
                continue;

              if (auto *target_fn =
                      findPreferredDefinedCodeTargetFunction(*pc)) {
                rewriteCallTarget(*call, target_fn);
                ++patched_local_target;
                continue;
              }

              if (RawBinary)
                continue;

              auto boundary =
                  omill::classifyProtectedBoundary(pe.memory_map, *pc);
              if (!boundary)
                continue;

              auto callee =
                  omill::getOrInsertProtectedBoundaryDecl(*module,
                                                          call->getFunctionType(),
                                                          *boundary);
              rewriteCallTarget(*call, callee.getCallee());
              ++patched_boundary;
            }
          }
        }

        const unsigned patched = patched_local_target + patched_boundary;
        if (patched > 0) {
          errs() << "Patched " << patched
                 << " inttoptr call sites to direct calls";
          if (patched_boundary > 0)
            errs() << " (" << patched_local_target << " local, "
                   << patched_boundary << " protected-boundary)";
          errs() << "\n";
          if (events.detailed()) {
            events.emitInfo(event_name, event_message,
                            {{"patched_uses", static_cast<int64_t>(patched)},
                             {"patched_local_targets",
                              static_cast<int64_t>(patched_local_target)},
                             {"patched_boundaries",
                              static_cast<int64_t>(patched_boundary)}});
          }
          runPostPatchCleanup(event_name);
        }
        return patched;
      };

  auto resolveRelativeCalliTargetPc = [&](llvm::Function &F, llvm::Value *target_value)
      -> std::optional<uint64_t> {
    if (!target_value)
      return std::nullopt;
    target_value = target_value->stripPointerCasts();
    if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(target_value))
      return ci->getZExtValue();

    const uint64_t base_pc = omill::extractStructuralCodeTargetPC(F);
    if (!base_pc || F.arg_size() < 2)
      return std::nullopt;

    auto *pc_arg = F.getArg(1);
    auto decodeAddSub = [&](llvm::BinaryOperator *binop) -> std::optional<uint64_t> {
      if (!binop)
        return std::nullopt;
      auto *lhs_ci = llvm::dyn_cast<llvm::ConstantInt>(
          binop->getOperand(0)->stripPointerCasts());
      auto *rhs_ci = llvm::dyn_cast<llvm::ConstantInt>(
          binop->getOperand(1)->stripPointerCasts());
      auto *lhs = binop->getOperand(0)->stripPointerCasts();
      auto *rhs = binop->getOperand(1)->stripPointerCasts();

      if (binop->getOpcode() == llvm::Instruction::Add) {
        if (lhs == pc_arg && rhs_ci)
          return base_pc + rhs_ci->getZExtValue();
        if (rhs == pc_arg && lhs_ci)
          return base_pc + lhs_ci->getZExtValue();
      } else if (binop->getOpcode() == llvm::Instruction::Sub) {
        if (lhs == pc_arg && rhs_ci)
          return base_pc - rhs_ci->getZExtValue();
      }
      return std::nullopt;
    };

    if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(target_value))
      return decodeAddSub(binop);
    return std::nullopt;
  };

  auto collectConstantCalliTargets =
      [&](llvm::function_ref<bool(const llvm::Function &)> include_function) {
        llvm::DenseSet<uint64_t> targets;
        for (auto &F : *module) {
          if (!include_function(F))
            continue;
          for (auto &BB : F) {
            for (auto &I : BB) {
              auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
              if (!call || call->arg_size() < 3)
                continue;
              auto *callee = llvm::dyn_cast<llvm::Function>(
                  call->getCalledOperand()->stripPointerCasts());
              if (!callee || !callee->getName().contains("CALLI"))
                continue;
              auto target = resolveRelativeCalliTargetPc(F, call->getArgOperand(2));
              if (!target || !isCodeAddressInCurrentInput(*target))
                continue;
              targets.insert(*target);
            }
          }
        }
        return targets;
      };

  auto patchConstantCalliTargetsToDirectCalls =
      [&](llvm::ArrayRef<uint64_t> targets, llvm::StringRef event_name,
          llvm::StringRef event_message) {
        llvm::DenseSet<uint64_t> target_set(targets.begin(), targets.end());
        unsigned patched_local_target = 0;
        unsigned patched_boundary = 0;
        unsigned patched_executable_placeholder = 0;
        auto maybeGetConstantCalliTarget =
            [&](llvm::CallBase &call) -> std::optional<uint64_t> {
          if (call.arg_size() < 3)
            return std::nullopt;
          auto *callee = llvm::dyn_cast<llvm::Function>(
              call.getCalledOperand()->stripPointerCasts());
          if (!callee || !callee->getName().contains("CALLI"))
            return std::nullopt;
          return resolveRelativeCalliTargetPc(*call.getFunction(),
                                              call.getArgOperand(2));
        };

        auto rewriteCalliToDirectCall = [&](llvm::CallBase &call,
                                           llvm::FunctionType *callee_ty,
                                           llvm::Value *callee) {
          llvm::IRBuilder<> Builder(&call);
          llvm::SmallVector<llvm::Value *, 3> args = {
              call.getArgOperand(1), call.getArgOperand(2),
              call.getArgOperand(0)};
          auto *new_call =
              Builder.CreateCall(callee_ty, callee, args, call.getName());
          new_call->setCallingConv(call.getCallingConv());
          if (auto *old_call = llvm::dyn_cast<llvm::CallInst>(&call))
            new_call->setTailCallKind(old_call->getTailCallKind());
          new_call->setDebugLoc(call.getDebugLoc());
          if (!call.use_empty()) {
            if (call.getType() == new_call->getType()) {
              call.replaceAllUsesWith(new_call);
            } else if (!call.getType()->isVoidTy()) {
              call.replaceAllUsesWith(
                  llvm::PoisonValue::get(call.getType()));
            }
          }
          call.eraseFromParent();
        };

        auto lifted_fn_ty = llvm::FunctionType::get(
            llvm::PointerType::getUnqual(ctx),
            {llvm::PointerType::getUnqual(ctx), llvm::Type::getInt64Ty(ctx),
             llvm::PointerType::getUnqual(ctx)},
            false);

        for (auto &F : *module) {
          for (auto &BB : F) {
            for (auto &I : llvm::make_early_inc_range(BB)) {
              auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
              if (!call)
                continue;

              auto pc = maybeGetConstantCalliTarget(*call);
              if (!pc || !target_set.contains(*pc) || *pc == 0)
                continue;

              if (auto *target_fn =
                      findPreferredDefinedCodeTargetFunction(*pc)) {
                rewriteCalliToDirectCall(*call, target_fn->getFunctionType(),
                                         target_fn);
                ++patched_local_target;
                continue;
              }
              if (RawBinary)
                continue;

              auto boundary =
                  omill::classifyProtectedBoundary(pe.memory_map, *pc);
              if (boundary) {
                auto callee = omill::getOrInsertProtectedBoundaryDecl(
                    *module, lifted_fn_ty, *boundary);
                rewriteCalliToDirectCall(*call, lifted_fn_ty, callee.getCallee());
                ++patched_boundary;
                continue;
              }

              auto placeholder_name =
                  (llvm::Twine("omill_executable_target_") +
                   llvm::utohexstr(*pc))
                      .str();
              auto *placeholder = module->getFunction(placeholder_name);
              if (!placeholder) {
                placeholder = llvm::Function::Create(
                    lifted_fn_ty, llvm::GlobalValue::ExternalLinkage,
                    placeholder_name, *module);
                omill::ExecutableTargetFact fact;
                fact.raw_target_pc = *pc;
                fact.kind = omill::ExecutableTargetKind::kExecutablePlaceholder;
                fact.trust = omill::ExecutableTargetTrust::kUntrustedExecutable;
                omill::writeExecutableTargetFact(*placeholder, fact);
              }
              rewriteCalliToDirectCall(*call, lifted_fn_ty, placeholder);
              ++patched_executable_placeholder;
            }
          }
        }

        const unsigned patched = patched_local_target + patched_boundary +
                                 patched_executable_placeholder;
        if (patched > 0) {
          errs() << "Patched " << patched
                 << " constant CALLI site(s) to direct calls";
          if (patched_local_target > 0)
            errs() << " (local=" << patched_local_target << ")";
          if (patched_boundary > 0)
            errs() << " (boundary=" << patched_boundary << ")";
          if (patched_executable_placeholder > 0)
            errs() << " (placeholder=" << patched_executable_placeholder << ")";
          errs() << "\n";
          if (events.detailed()) {
            events.emitInfo(
                event_name, event_message,
                {{"patched_calls", static_cast<int64_t>(patched)},
                 {"patched_local_targets",
                  static_cast<int64_t>(patched_local_target)},
                 {"patched_boundaries",
                  static_cast<int64_t>(patched_boundary)},
                 {"patched_executable_placeholders",
                  static_cast<int64_t>(patched_executable_placeholder)}});
          }
        }
        return patched;
      };

  auto patchConstantDispatchTargetsToDirectCalls =
      [&](llvm::ArrayRef<uint64_t> targets, llvm::StringRef event_name,
          llvm::StringRef event_message) {
        llvm::DenseSet<uint64_t> target_set(targets.begin(), targets.end());
        unsigned patched_local_target = 0;
        unsigned patched_boundary = 0;

        auto lifted_fn_ty = llvm::FunctionType::get(
            llvm::PointerType::getUnqual(ctx),
            {llvm::PointerType::getUnqual(ctx), llvm::Type::getInt64Ty(ctx),
             llvm::PointerType::getUnqual(ctx)},
            false);

        for (auto &F : *module) {
          for (auto &BB : F) {
            for (auto &I : llvm::make_early_inc_range(BB)) {
              auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!call || call->arg_size() < 3)
                continue;
              auto *callee = call->getCalledFunction();
              if (!callee || !omill::isDispatchIntrinsicName(callee->getName()))
                continue;
              auto *ci = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
              if (!ci)
                continue;
              const uint64_t target = ci->getZExtValue();
              if (!target_set.contains(target) || target == 0)
                continue;

              llvm::Value *direct_callee = nullptr;
              llvm::FunctionType *direct_ty = nullptr;
              if (auto *target_fn =
                      findPreferredDefinedCodeTargetFunction(target)) {
                direct_callee = target_fn;
                direct_ty = target_fn->getFunctionType();
                ++patched_local_target;
              } else if (!RawBinary) {
                auto boundary =
                    omill::classifyProtectedBoundary(pe.memory_map, target);
                if (!boundary)
                  continue;
                auto boundary_callee = omill::getOrInsertProtectedBoundaryDecl(
                    *module, lifted_fn_ty, *boundary);
                direct_callee = boundary_callee.getCallee();
                direct_ty = lifted_fn_ty;
                ++patched_boundary;
              } else {
                continue;
              }

              llvm::IRBuilder<> Builder(call);
              auto *new_call = Builder.CreateCall(
                  direct_ty, direct_callee,
                  {call->getArgOperand(0), call->getArgOperand(1),
                   call->getArgOperand(2)},
                  call->getName());
              new_call->setCallingConv(call->getCallingConv());
              new_call->setDebugLoc(call->getDebugLoc());
              if (!call->use_empty()) {
                if (call->getType() == new_call->getType()) {
                  call->replaceAllUsesWith(new_call);
                } else if (!call->getType()->isVoidTy()) {
                  call->replaceAllUsesWith(
                      llvm::PoisonValue::get(call->getType()));
                }
              }
              call->eraseFromParent();
            }
          }
        }

        const unsigned patched = patched_local_target + patched_boundary;
        if (patched > 0) {
          errs() << "Patched " << patched
                 << " constant dispatch site(s) to direct calls";
          if (patched_local_target > 0)
            errs() << " (local=" << patched_local_target << ")";
          if (patched_boundary > 0)
            errs() << " (boundary=" << patched_boundary << ")";
          errs() << "\n";
          if (events.detailed()) {
            events.emitInfo(
                event_name, event_message,
                {{"patched_calls", static_cast<int64_t>(patched)},
                 {"patched_local_targets",
                  static_cast<int64_t>(patched_local_target)},
                 {"patched_boundaries",
                  static_cast<int64_t>(patched_boundary)}});
          }
        }
        return patched;
      };

  auto patchDeclaredLiftedOrBlockCallsToDefinedTargets =
      [&](llvm::ArrayRef<uint64_t> targets, llvm::StringRef event_name,
          llvm::StringRef event_message) {
        llvm::DenseSet<uint64_t> target_set(targets.begin(), targets.end());
        unsigned patched = 0;
        auto effectiveBoundaryContinuationTarget =
            [&](llvm::Function &callee) -> std::optional<uint64_t> {
          auto fact = omill::readBoundaryFact(callee);
          if (!fact)
            return std::nullopt;
          if (fact->continuation_entry_transform &&
              fact->continuation_entry_transform->jump_target_pc) {
            return fact->continuation_entry_transform->jump_target_pc;
          }
          if (fact->suppresses_normal_fallthrough)
            return fact->controlled_return_pc;
          return fact->continuation_pc;
        };
        auto effectiveBoundaryNativeTarget =
            [&](llvm::Function &callee) -> std::optional<uint64_t> {
          auto fact = omill::readBoundaryFact(callee);
          if (!fact)
            return std::nullopt;
          if (fact->native_target_pc)
            return fact->native_target_pc;
          return fact->boundary_pc;
        };


        for (auto &F : *module) {
          for (auto &BB : F) {
            for (auto &I : llvm::make_early_inc_range(BB)) {
              auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
              if (!call)
                continue;
              auto *callee = call->getCalledFunction();
              if (!callee || !callee->isDeclaration())
                continue;
              uint64_t target_pc =
                  omill::extractStructuralCodeTargetPC(*callee);
              if (target_pc == 0)
                continue;
              auto *target_fn =
                  target_set.contains(target_pc)
                      ? findPreferredDefinedCodeTargetFunction(target_pc)
                      : nullptr;
              if (!target_fn) {
                auto native_target_pc = effectiveBoundaryNativeTarget(*callee);
                if (native_target_pc && target_set.contains(*native_target_pc))
                  target_fn = findPreferredDefinedCodeTargetFunction(*native_target_pc);
              }
              if (!target_fn) {
                auto continuation_pc = effectiveBoundaryContinuationTarget(*callee);
                if (continuation_pc && target_set.contains(*continuation_pc))
                  target_fn = findPreferredDefinedCodeTargetFunction(*continuation_pc);
              }
              if (!target_fn || target_fn->isDeclaration() ||
                  target_fn == callee ||
                  target_fn->getFunctionType() != call->getFunctionType()) {
                continue;
              }
              call->setCalledFunction(target_fn);
              ++patched;
            }
          }
        }

        if (patched > 0) {
          errs() << "Patched " << patched
                 << " declared lifted/block call site(s) to defined targets\n";
          if (events.detailed()) {
            events.emitInfo(event_name, event_message,
                            {{"patched_calls", static_cast<int64_t>(patched)}});
          }
        }
        return patched;
      };

  auto collectDeclaredStructuralTargetsWithDefinedImplementations = [&]() {
    llvm::DenseSet<uint64_t> targets;
    for (auto &F : *module) {
      if (!F.isDeclaration())
        continue;
      const uint64_t target_pc = omill::extractStructuralCodeTargetPC(F);
      if (!target_pc)
        continue;
      auto *defined = findPreferredDefinedCodeTargetFunction(target_pc);
      if (!defined || defined->isDeclaration() || defined == &F)
        continue;
      targets.insert(target_pc);
    }
    return llvm::SmallVector<uint64_t, 16>(targets.begin(), targets.end());
  };

  auto collectExecutablePlaceholderDeclarationTargets = [&]() {
    llvm::SmallVector<uint64_t, 16> targets;
    llvm::DenseSet<uint64_t> seen;
    for (auto &F : *module) {
      if (!F.isDeclaration())
        continue;
      auto fact = omill::readExecutableTargetFact(F);
      if (!fact)
        continue;
      if (fact->kind != omill::ExecutableTargetKind::kExecutablePlaceholder &&
          fact->kind != omill::ExecutableTargetKind::kInvalidatedExecutableEntry) {
        continue;
      }
      const uint64_t target_pc = fact->raw_target_pc;
      if (!target_pc || !isCodeAddressInCurrentInput(target_pc))
        continue;
      if (!seen.insert(target_pc).second)
        continue;
      targets.push_back(target_pc);
    }
    return targets;
  };

  auto rerunLateDiscoveryPipeline = [&](llvm::StringRef attr_name, bool run_abi,
                                        bool skip_missing_block_lift,
                                        bool clear_attr = true,
                                        bool include_closed_slice_context =
                                            true) {
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    llvm::DenseSet<llvm::Function *> pre_rerun_funcs;
    llvm::DenseSet<llvm::Function *> pre_rerun_defs;
    const bool debug_continuation_lifts =
        parseBoolEnv("OMILL_DEBUG_CONTINUATION_LIFTS").value_or(false);
    for (auto &F : *module) {
      pre_rerun_funcs.insert(&F);
      if (!F.isDeclaration())
        pre_rerun_defs.insert(&F);
    }

    omill::PipelineOptions late_opts = opts;
    late_opts.resolve_indirect_targets = false;
    late_opts.skip_closed_slice_missing_block_lift = skip_missing_block_lift;
    if (skip_missing_block_lift) {
      // The late missing-block wave already lifts a fixed target set. Avoid
      // re-entering the global block-discovery epoch here; it adds a large
      // amount of work and can chase unrelated continuations before the
      // explicit bounded continuation round below runs.
      late_opts.use_block_lifting = false;
      late_opts.merge_block_functions_after_fixpoint = false;
    }
    const bool use_closed_slice_context =
        include_closed_slice_context && !run_abi &&
        opts.generic_static_devirtualize && opts.use_block_lifting;
    late_opts.scope_predicate =
        [attr_name = attr_name.str(), use_closed_slice_context](
            llvm::Function &F) {
          if (F.getFnAttribute(attr_name).isValid())
            return true;
          return use_closed_slice_context &&
                 F.hasFnAttribute("omill.closed_root_slice");
        };
    late_opts.preserve_lifted_semantics = preserve_lift_infrastructure;

    auto runScopedLatePipeline = [&](const omill::PipelineOptions &rerun_opts,
                                     llvm::StringRef stage_name) {
      const bool debug_late_output_target_rerun =
          parseBoolEnv("OMILL_DEBUG_LATE_OUTPUT_ROOT_TARGET_RERUN")
              .value_or(false);
      if (debug_late_output_target_rerun)
        errs() << "[late-output-target] scoped-main-start stage="
               << stage_name << "\n";
      ModulePassManager MPM;
      omill::buildPipeline(MPM, rerun_opts);
      MPM.run(*module, MAM);
      if (debug_late_output_target_rerun)
        errs() << "[late-output-target] scoped-main-done stage="
               << stage_name << "\n";
      emitIterativeSessionEvents(events, iterative_session, stage_name);
      if (run_abi) {
        if (debug_late_output_target_rerun)
          errs() << "[late-output-target] scoped-abi-start stage="
                 << stage_name << "\n";
        ModulePassManager MPM;
        omill::buildABIRecoveryPipeline(MPM, rerun_opts);
        MPM.run(*module, MAM);
        if (debug_late_output_target_rerun)
          errs() << "[late-output-target] scoped-abi-done stage="
                 << stage_name << "\n";
      }
    };

    runScopedLatePipeline(late_opts, "late-discovery-rerun");

    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      const bool is_new_function = !pre_rerun_funcs.count(&F);
      const bool became_defined = !is_new_function && !pre_rerun_defs.count(&F);
      if (!is_new_function && !became_defined)
        continue;
      F.addFnAttr(attr_name, "1");
      F.addFnAttr("omill.closed_root_slice", "1");
      if (!F.hasLocalLinkage())
        F.setLinkage(llvm::GlobalValue::InternalLinkage);
      if (debug_continuation_lifts) {
        errs() << "[late-rerun-new-fn] attr=" << attr_name
               << " fn=" << F.getName()
               << " existing_decl=" << (became_defined ? 1 : 0) << "\n";
      }
    }

    if (clear_attr)
      clearLiftRoundAttr(attr_name);
  };

  auto isInCode = [&](uint64_t target) {
    if (RawBinary)
      return target >= BaseAddress && target < BaseAddress + raw_code.size();
    for (auto &sec : pe.code_sections) {
      if (target >= sec.va && target < sec.va + sec.size)
        return true;
    }
    return false;
  };

  auto readCodeBytes = [&](uint64_t pc, uint8_t *buf, size_t size) {
    if (RawBinary) {
      if (pc < BaseAddress || pc >= BaseAddress + raw_code.size())
        return false;
      const auto offset = static_cast<size_t>(pc - BaseAddress);
      if (offset + size > raw_code.size())
        return false;
      std::memcpy(buf, raw_code.data() + offset, size);
      return true;
    }
    return pe.memory_map.read(pc, buf, size);
  };

  auto looksLikeLateMissingBlockRoot = [&](uint64_t pc) {
    __try {
      if (!isInCode(pc))
        return false;

      constexpr unsigned kMaxProbeInstructions = 12;
      uint64_t current_pc = pc;
      for (unsigned i = 0; i < kMaxProbeInstructions; ++i) {
        uint8_t probe_buf[15] = {};
        if (!readCodeBytes(current_pc, probe_buf, sizeof(probe_buf)))
          return false;

        std::string_view probe_bytes(
            reinterpret_cast<const char *>(probe_buf), sizeof(probe_buf));
        remill::Instruction probe_inst;
        if (!arch->DecodeInstruction(current_pc, probe_bytes, probe_inst,
                                     arch->CreateInitialContext())) {
          return false;
        }

        switch (probe_inst.category) {
          case remill::Instruction::kCategoryInvalid:
          case remill::Instruction::kCategoryError:
          case remill::Instruction::kCategoryDirectFunctionCall:
          case remill::Instruction::kCategoryIndirectFunctionCall:
          case remill::Instruction::kCategoryConditionalDirectFunctionCall:
          case remill::Instruction::kCategoryConditionalIndirectFunctionCall:
            return false;

          case remill::Instruction::kCategoryDirectJump:
          case remill::Instruction::kCategoryIndirectJump:
          case remill::Instruction::kCategoryConditionalBranch:
          case remill::Instruction::kCategoryConditionalIndirectJump:
          case remill::Instruction::kCategoryFunctionReturn:
          case remill::Instruction::kCategoryConditionalFunctionReturn:
          case remill::Instruction::kCategoryAsyncHyperCall:
          case remill::Instruction::kCategoryConditionalAsyncHyperCall:
            return true;

          case remill::Instruction::kCategoryNormal:
          case remill::Instruction::kCategoryNoOp:
            current_pc = probe_inst.next_pc;
            break;
        }
      }

      return false;
    } __except (1) {
      return false;
    }
  };

  auto collectContinuationTargetsForScope =
      [&](llvm::function_ref<bool(const llvm::Function &)> include_fn) {
    llvm::DenseSet<uint64_t> targets;
    const bool debug_continuation_lifts =
        parseBoolEnv("OMILL_DEBUG_CONTINUATION_LIFTS").value_or(false);
    const bool debug_markers_enabled =
        std::getenv("OMILL_DEBUG_MARKER_FILE") != nullptr;

    auto parseContinuationPC =
        [&](llvm::StringRef name) -> std::optional<uint64_t> {
      if (name.starts_with("blk_")) {
        uint64_t pc = 0;
        if (!name.drop_front(4).getAsInteger(16, pc))
          return pc;
        return std::nullopt;
      }
      if (name.starts_with("block_")) {
        uint64_t pc = 0;
        if (!name.drop_front(6).getAsInteger(16, pc))
          return pc;
      }
      return std::nullopt;
    };

    for (auto &F : *module) {
      if (F.isDeclaration() || !include_fn(F))
        continue;
      if (debug_markers_enabled) {
        appendDebugMarker((llvm::Twine("late:continuation_scan_fn:") +
                           F.getName())
                              .str()
                              .c_str());
      }
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call || call->arg_size() < 2)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || !callee->isDeclaration())
            continue;
          auto maybe_pc = parseContinuationPC(callee->getName());
          if (!maybe_pc)
            continue;
          if (debug_markers_enabled) {
            appendDebugMarker((llvm::Twine("late:continuation_candidate:") +
                               F.getName() + "->" + callee->getName() +
                               "@0x" + llvm::Twine::utohexstr(*maybe_pc))
                                  .str()
                                  .c_str());
          }
          auto *pc_arg =
              llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!pc_arg || pc_arg->getZExtValue() != *maybe_pc)
            continue;
          if (debug_markers_enabled) {
            appendDebugMarker((llvm::Twine("late:continuation_before_probe:0x") +
                               llvm::Twine::utohexstr(*maybe_pc))
                                  .str()
                                  .c_str());
          }
          const bool accepted = looksLikeLateMissingBlockRoot(*maybe_pc);
          if (debug_markers_enabled) {
            appendDebugMarker((llvm::Twine("late:continuation_after_probe:0x") +
                               llvm::Twine::utohexstr(*maybe_pc) + "=" +
                               llvm::Twine(accepted ? 1 : 0))
                                  .str()
                                  .c_str());
          }
          if (debug_continuation_lifts) {
            errs() << "[late-continuation-candidate] pc=0x"
                   << llvm::Twine::utohexstr(*maybe_pc)
                   << " caller=" << F.getName()
                   << " accepted=" << (accepted ? 1 : 0) << "\n";
          }
          if (!accepted)
            continue;
          targets.insert(*maybe_pc);
        }
      }
    }

    return targets;
  };

  auto collectClosedSliceContinuationTargets = [&]() {
    return collectContinuationTargetsForScope([](const llvm::Function &F) {
      return F.hasFnAttribute("omill.closed_root_slice");
    });
  };

  auto collectClosedSliceMissingBlockTargets = [&]() {
    llvm::DenseSet<uint64_t> targets;
    const bool debug_continuation_lifts =
        parseBoolEnv("OMILL_DEBUG_CONTINUATION_LIFTS").value_or(false);

    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.closed_root_slice"))
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call || call->arg_size() < 2)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || callee->getName() != "__remill_missing_block")
            continue;
          auto *pc_arg =
              llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!pc_arg)
            continue;
          const uint64_t pc = pc_arg->getZExtValue();
          const bool looks_like_root =
              pc != 0 && looksLikeLateMissingBlockRoot(pc);
          if (debug_continuation_lifts) {
            errs() << "[late-missing-candidate] pc=0x"
                   << llvm::Twine::utohexstr(pc)
                   << " caller=" << F.getName()
                   << " accepted=" << (looks_like_root ? 1 : 0) << "\n";
          }
          if (!looks_like_root)
            continue;
          targets.insert(pc);
        }
      }
    }

    return targets;
  };

  auto collectOutputRootMissingBlockTargets = [&]() {
    llvm::DenseSet<uint64_t> targets;
    const bool debug_continuation_lifts =
        parseBoolEnv("OMILL_DEBUG_CONTINUATION_LIFTS").value_or(false);

    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      if (!F.hasFnAttribute("omill.output_root") &&
          !F.hasFnAttribute("omill.closed_root_slice_root"))
        continue;

      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call || call->arg_size() < 2)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || callee->getName() != "__remill_missing_block")
            continue;
          auto *pc_arg =
              llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!pc_arg)
            continue;
          const uint64_t pc = pc_arg->getZExtValue();
          const bool looks_like_root =
              pc != 0 && looksLikeLateMissingBlockRoot(pc);
          const auto *existing = findLiftedOrBlockFunction(pc, /*native=*/false);
          if (debug_continuation_lifts) {
            errs() << "[late-output-boundary-candidate] pc=0x"
                   << llvm::Twine::utohexstr(pc)
                   << " caller=" << F.getName()
                   << " accepted=" << (looks_like_root ? 1 : 0)
                   << " existing=" << (existing && !existing->isDeclaration())
                   << "\n";
          }
          if (!looks_like_root)
            continue;
          if (existing && !existing->isDeclaration())
            continue;
          targets.insert(pc);
        }
      }
    }

    return targets;
  };

  auto collectAllConstantMissingBlockTargets = [&]() {
    llvm::DenseSet<uint64_t> targets;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call || call->arg_size() < 2)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || callee->getName() != "__remill_missing_block")
            continue;
          auto *pc_arg =
              llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!pc_arg || pc_arg->isZero())
            continue;
          targets.insert(pc_arg->getZExtValue());
        }
      }
    }
    return targets;
  };

  auto liftScopedTargets = [&](llvm::ArrayRef<uint64_t> targets,
                               llvm::StringRef attr_name, bool run_abi,
                               bool skip_missing_block_lift,
                               bool clear_attr = true,
                               bool mark_closed_root_slice = true,
                               bool use_direct_lifter = false,
                               bool include_closed_slice_context = true,
                               bool rerun_discovery = true) {
    const bool debug_markers_enabled =
        std::getenv("OMILL_DEBUG_MARKER_FILE") != nullptr;
    auto block_cb = iterative_session->blockLiftCallback();
    if (!use_direct_lifter && !block_cb)
      return false;

    llvm::DenseSet<llvm::Function *> pre_lift_funcs;
    for (auto &F : *module)
      pre_lift_funcs.insert(&F);

    unsigned lifted_any = 0;
    for (uint64_t pc : targets) {
      if (debug_markers_enabled) {
        appendDebugMarker((llvm::Twine("late:lift_target:before:0x") +
                           llvm::Twine::utohexstr(pc) + ":direct=" +
                           llvm::Twine(use_direct_lifter ? 1 : 0))
                              .str()
                              .c_str());
      }
      auto *existing = findLiftedOrBlockFunction(pc, /*native=*/false);
      if (existing && !existing->isDeclaration())
        continue;

      bool lifted = false;
      const bool prefer_direct_lifter_for_structural_block_decl =
          !use_direct_lifter && existing && existing->isDeclaration() &&
          (existing->getName().starts_with("blk_") ||
           existing->getName().starts_with("block_"));
      __try {
        iterative_session->queueTarget(pc);
        if (use_direct_lifter || prefer_direct_lifter_for_structural_block_decl) {
          lifted = safeTraceLiftTarget(pc);
        } else if (block_cb(pc)) {
          lifted = true;
        }
      } __except (1) {
        lifted = false;
      }
      if (debug_markers_enabled) {
        appendDebugMarker((llvm::Twine("late:lift_target:after:0x") +
                           llvm::Twine::utohexstr(pc) + "=" +
                           llvm::Twine(lifted ? 1 : 0))
                              .str()
                              .c_str());
      }
      if (lifted)
        ++lifted_any;
    }

    if (!lifted_any)
      return false;

    fixLiftedFunctionNamingCollisions();
    tagNewlyLiftedFunctions(attr_name, pre_lift_funcs);
    for (auto &F : *module) {
      if (!F.getFnAttribute(attr_name).isValid())
        continue;
      if (mark_closed_root_slice)
        F.addFnAttr("omill.closed_root_slice", "1");
      if (!F.hasLocalLinkage())
        F.setLinkage(llvm::GlobalValue::InternalLinkage);
    }
    if (rerun_discovery) {
      if (debug_markers_enabled) {
        appendDebugMarker((llvm::Twine("late:lift_target:before_rerun:") +
                           attr_name)
                              .str()
                              .c_str());
      }
      rerunLateDiscoveryPipeline(attr_name, run_abi, skip_missing_block_lift,
                                 clear_attr, include_closed_slice_context);
      if (debug_markers_enabled) {
        appendDebugMarker((llvm::Twine("late:lift_target:after_rerun:") +
                           attr_name)
                              .str()
                              .c_str());
      }
    } else if (clear_attr) {
      clearLiftRoundAttr(attr_name);
    }
    return true;
  };

  auto liftLateTargets = [&](llvm::ArrayRef<uint64_t> targets) {
    return liftScopedTargets(targets, "omill.late_newly_lifted",
                             /*run_abi=*/false,
                             /*skip_missing_block_lift=*/true,
                             /*clear_attr=*/true,
                             /*mark_closed_root_slice=*/true,
                             /*use_direct_lifter=*/false,
                             /*include_closed_slice_context=*/false,
                             /*rerun_discovery=*/true);
  };

  auto liftLateMissingBlockTargets = [&](llvm::ArrayRef<uint64_t> targets) {
    bool changed = liftScopedTargets(targets, "omill.late_newly_lifted",
                                     /*run_abi=*/false,
                                     /*skip_missing_block_lift=*/true,
                                     /*clear_attr=*/true,
                                     /*mark_closed_root_slice=*/true,
                                     /*use_direct_lifter=*/true,
                                     /*include_closed_slice_context=*/false,
                                     /*rerun_discovery=*/false);

    llvm::SmallVector<uint64_t, 8> unresolved_exact_targets;
    for (uint64_t pc : targets) {
      auto *existing = findLiftedOrBlockFunction(pc, /*native=*/false);
      if (!existing || existing->isDeclaration())
        unresolved_exact_targets.push_back(pc);
    }

    if (!unresolved_exact_targets.empty()) {
      changed |= liftScopedTargets(unresolved_exact_targets,
                                   "omill.late_newly_lifted",
                                   /*run_abi=*/false,
                                   /*skip_missing_block_lift=*/true,
                                   /*clear_attr=*/true,
                                   /*mark_closed_root_slice=*/true,
                                   /*use_direct_lifter=*/false,
                                   /*include_closed_slice_context=*/false,
                                   /*rerun_discovery=*/false);
    }

    return changed;
  };

  auto liftLateTerminalBoundaryTargets = [&](llvm::ArrayRef<uint64_t> targets) {
    return liftScopedTargets(targets, "omill.late_boundary_target_lifted",
                             /*run_abi=*/false,
                             /*skip_missing_block_lift=*/true,
                             /*clear_attr=*/true,
                             /*mark_closed_root_slice=*/false);
  };

  auto runLateContinuationRounds = [&](unsigned max_rounds) {
    constexpr unsigned kMaxTargetsPerRound = 8;

    for (unsigned round = 0; round < max_rounds; ++round) {
      appendDebugMarker(
          (llvm::Twine("late:continuation_round_") + llvm::Twine(round) +
           ":before_collect")
              .str()
              .c_str());
      auto targets = collectClosedSliceContinuationTargets();
      appendDebugMarker(
          (llvm::Twine("late:continuation_round_") + llvm::Twine(round) +
           ":after_collect targets=" + llvm::Twine(targets.size()))
              .str()
              .c_str());
      if (targets.empty())
        break;

      llvm::SmallVector<uint64_t, 16> ordered_targets(targets.begin(),
                                                      targets.end());
      llvm::sort(ordered_targets);
      if (ordered_targets.size() > kMaxTargetsPerRound)
        ordered_targets.resize(kMaxTargetsPerRound);

      appendDebugMarker(
          (llvm::Twine("late:continuation_round_") + llvm::Twine(round) +
           ":before_lift targets=" + llvm::Twine(ordered_targets.size()))
              .str()
              .c_str());
      if (!liftLateTargets(ordered_targets))
        break;
      appendDebugMarker(
          (llvm::Twine("late:continuation_round_") + llvm::Twine(round) +
           ":after_lift")
              .str()
              .c_str());
    }
  };

  auto hasClosedSlicePendingOpaqueEdges = [&]() {
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.closed_root_slice"))
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee)
            continue;
          auto name = callee->getName();
          if (omill::isDispatchIntrinsicName(name)) {
            return true;
          }
          if ((name.starts_with("blk_") || name.starts_with("block_")) &&
              callee->isDeclaration()) {
            return true;
          }
        }
      }
    }
    return false;
  };

  auto rerunLateContinuationPipeline = [&]() {
    if (devirtualization_plan.enable_devirtualization)
      return;
    if (!opts.generic_static_devirtualize || !opts.use_block_lifting ||
        parseBoolEnv("OMILL_SKIP_LATE_CONTINUATION_RERUN").value_or(false)) {
      return;
    }

    // Keep the no-ABI late continuation wave opt-in. The current generic path
    // already closes the corpus roots without it, and reopening the graph here
    // can destabilize large samples after the slice is already semantically
    // closed. Use the env knob when explicitly experimenting on unresolved
    // cases.
    if (NoABI &&
        !parseBoolEnv("OMILL_ENABLE_NOABI_LATE_CONTINUATION_RERUN")
             .value_or(false)) {
      return;
    }

    runLateContinuationRounds(/*max_rounds=*/NoABI ? 1u : 3u);
    appendDebugMarker("late:after_continuation_rounds");

    if (NoABI ||
        parseBoolEnv("OMILL_SKIP_LATE_MISSING_BLOCK_RERUN").value_or(false)) {
      return;
    }

    constexpr unsigned kMaxMissingTargetRounds = 3;
    constexpr unsigned kMaxMissingTargetsPerRound = 8;
    for (unsigned round = 0; round < kMaxMissingTargetRounds; ++round) {
      appendDebugMarker(
          (llvm::Twine("late:missing_block_round_") + llvm::Twine(round) +
           ":before_collect")
              .str()
              .c_str());
      auto missing_targets = collectClosedSliceMissingBlockTargets();
      appendDebugMarker(
          (llvm::Twine("late:missing_block_round_") + llvm::Twine(round) +
           ":after_collect targets=" + llvm::Twine(missing_targets.size()))
              .str()
              .c_str());
      if (missing_targets.empty())
        break;

      llvm::SmallVector<uint64_t, 8> ordered_missing_targets(
          missing_targets.begin(), missing_targets.end());
      llvm::sort(ordered_missing_targets);
      if (ordered_missing_targets.size() > kMaxMissingTargetsPerRound)
        ordered_missing_targets.resize(kMaxMissingTargetsPerRound);

      appendDebugMarker(
          (llvm::Twine("late:missing_block_round_") + llvm::Twine(round) +
           ":before_lift targets=" + llvm::Twine(ordered_missing_targets.size()))
              .str()
              .c_str());
      if (!liftLateMissingBlockTargets(ordered_missing_targets))
        break;

      llvm::DenseSet<uint64_t> target_set(ordered_missing_targets.begin(),
                                          ordered_missing_targets.end());
      unsigned patched = 0;
      unsigned patched_nearby = 0;
      for (auto &F : *module) {
        if (F.isDeclaration())
          continue;
        for (auto &BB : F) {
          for (auto &I : llvm::make_early_inc_range(BB)) {
            auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!call || call->arg_size() < 2)
              continue;
            auto *callee = call->getCalledFunction();
            if (!callee || callee->getName() != "__remill_missing_block")
              continue;

            auto *pc_arg =
                llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
            if (!pc_arg)
              continue;
            const uint64_t target_pc = pc_arg->getZExtValue();
            if (!target_set.contains(target_pc) || target_pc == 0)
              continue;

            uint64_t resolved_target_pc = 0;
            auto *target = findExactOrNearbyLiftedOrBlockFunction(
                target_pc, /*native=*/false, &resolved_target_pc);
            if (!target || target == &F || target->isDeclaration())
              continue;
            if (target->getFunctionType() != call->getFunctionType())
              continue;

            call->setCalledFunction(target);
            ++patched;
            patched_nearby +=
                static_cast<unsigned>(resolved_target_pc != target_pc);
          }
        }
      }
      if (patched > 0 && events.detailed()) {
        events.emitInfo("late_missing_block_patch",
                        "patched late missing-block calls to lifted targets",
                        {{"round", static_cast<int64_t>(round)},
                         {"patched_uses", static_cast<int64_t>(patched)},
                         {"patched_nearby_uses",
                          static_cast<int64_t>(patched_nearby)}});
      }
      appendDebugMarker(
          (llvm::Twine("late:missing_block_round_") + llvm::Twine(round) +
           ":after_lift patched=" + llvm::Twine(patched) +
           " nearby=" + llvm::Twine(patched_nearby))
              .str()
              .c_str());
    }
    appendDebugMarker("late:after_missing_block_lift");
  };

  auto patchConstantMissingBlockCallsToLiftedTargets =
      [&](llvm::ArrayRef<uint64_t> targets, llvm::StringRef event_name,
          llvm::StringRef event_message) {
        llvm::DenseSet<uint64_t> target_set(targets.begin(), targets.end());
        unsigned patched = 0;
        unsigned patched_nearby = 0;

        for (auto &F : *module) {
          if (F.isDeclaration())
            continue;
          for (auto &BB : F) {
            for (auto &I : llvm::make_early_inc_range(BB)) {
              auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!call || call->arg_size() < 2)
                continue;
              auto *callee = call->getCalledFunction();
              if (!callee || callee->getName() != "__remill_missing_block")
                continue;

              auto *pc_arg =
                  llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
              if (!pc_arg)
                continue;
              const uint64_t target_pc = pc_arg->getZExtValue();
              if (!target_set.contains(target_pc) || target_pc == 0)
                continue;

              uint64_t resolved_target_pc = 0;
              auto *target = findExactOrNearbyLiftedOrBlockFunction(
                  target_pc, /*native=*/false, &resolved_target_pc);
              if (!target || target == &F || target->isDeclaration())
                continue;
              if (target->getFunctionType() != call->getFunctionType())
                continue;

              call->setCalledFunction(target);
              ++patched;
              patched_nearby +=
                  static_cast<unsigned>(resolved_target_pc != target_pc);
            }
          }
        }

        if (patched == 0)
          return;

        errs() << "Patched " << patched
               << " __remill_missing_block call sites to lifted targets\n";
        if (events.detailed()) {
          events.emitInfo(event_name, event_message,
                          {{"patched_uses", static_cast<int64_t>(patched)},
                           {"patched_nearby_uses",
                            static_cast<int64_t>(patched_nearby)}});
        }
      };

  auto rerunLateTerminalBoundaryTargetPipeline = [&]() {
    if (NoABI || !opts.use_block_lifting)
      return;
    if (parseBoolEnv("OMILL_SKIP_LATE_TERMINAL_BOUNDARY_RERUN")
            .value_or(false)) {
      return;
    }

    auto targets = collectOutputRootMissingBlockTargets();
    if (targets.empty())
      return;

    constexpr unsigned kMaxTargetsPerRound = 4;
    llvm::SmallVector<uint64_t, 8> ordered_targets(targets.begin(),
                                                   targets.end());
    llvm::sort(ordered_targets);
    if (ordered_targets.size() > kMaxTargetsPerRound)
      ordered_targets.resize(kMaxTargetsPerRound);

    if (!devirtualization_plan.enable_devirtualization) {
      if (!liftLateTerminalBoundaryTargets(ordered_targets))
        return;
    }

    patchConstantMissingBlockCallsToLiftedTargets(
        ordered_targets, "late_terminal_boundary_patch",
        "patched late terminal boundary missing-block calls");
  };

  auto normalizeKnownVmContinuationTarget = [&](uint64_t target) -> uint64_t {
    if (target == 0 || !isCodeAddressInCurrentInput(target))
      return target;
    if (opts.target_arch != omill::TargetArch::kX86_64)
      return target;

    llvm::SmallDenseSet<uint64_t, 8> visited;
    uint64_t current = target;
    bool recovered_overlap_entry = false;
    if (auto canonical =
            omill::canonicalizeLiftTargetForOverlap(&pe.memory_map, current,
                                                    opts.target_arch)) {
      recovered_overlap_entry = (*canonical != current);
      current = *canonical;
    }
    for (unsigned hop = 0; hop < 4; ++hop) {
      if (!visited.insert(current).second)
        break;
      uint8_t bytes[8] = {};
      if (!pe.memory_map.read(current, bytes, sizeof(bytes)))
        break;

      uint64_t next = 0;
      if (bytes[0] == 0xE9) {
        int32_t rel = 0;
        std::memcpy(&rel, &bytes[1], sizeof(rel));
        next = static_cast<uint64_t>(static_cast<int64_t>(current) + 5 +
                                     static_cast<int64_t>(rel));
      } else if (bytes[0] == 0xEB) {
        int8_t rel = static_cast<int8_t>(bytes[1]);
        next = static_cast<uint64_t>(static_cast<int64_t>(current) + 2 +
                                     static_cast<int64_t>(rel));
      } else {
        break;
      }

      if (next == 0 || !isCodeAddressInCurrentInput(next))
        break;
      current = next;
    }

    if (current >= 5 &&
        !omill::isExactX86DirectControlFlowFallthrough(&pe.memory_map,
                                                       current)) {
      uint8_t call_bytes[5] = {};
      const uint64_t call_pc = current - 5;
      if (isCodeAddressInCurrentInput(call_pc) &&
          pe.memory_map.read(call_pc, call_bytes, sizeof(call_bytes)) &&
          call_bytes[0] == 0xE8) {
        current = call_pc;
      }
    }

    if (auto canonical =
            omill::canonicalizeLiftTargetForOverlap(&pe.memory_map, current,
                                                    opts.target_arch)) {
      recovered_overlap_entry = recovered_overlap_entry ||
                                (*canonical != current);
      current = *canonical;
    }

    if (auto covered_pc =
            omill::findNearestCoveredLiftedOrBlockPC(*module, current, 0x20)) {
      uint64_t candidate = *covered_pc;
      if (candidate > current && (candidate - current) <= 8)
        return current;
      if (recovered_overlap_entry && candidate < current &&
          (current - candidate) <= 8)
        return current;
      if (auto canonical =
              omill::canonicalizeLiftTargetForOverlap(&pe.memory_map, candidate,
                                                      opts.target_arch)) {
        return *canonical;
      }
      return candidate;
    }
    return current;
  };

  auto collectOutputRootClosureSummary = [&]() {
    return omill::collectOutputRootClosureTargets(
        *module,
        [&](uint64_t target) { return isCodeAddressInCurrentInput(target); },
        [&](uint64_t target) { return hasDefinedLiftedOrBlockTarget(target); },
        [&](uint64_t target) {
          return normalizeKnownVmContinuationTarget(target);
        });
  };

  auto collectOutputRootConstantCodeCallTargets = [&]() {
    llvm::DenseSet<uint64_t> targets;
    for (uint64_t target : collectOutputRootClosureSummary().constant_code_targets)
      targets.insert(target);
    return targets;
  };

  auto collectOutputRootConstantCalliTargets = [&]() {
    llvm::DenseSet<uint64_t> targets;
    for (uint64_t target :
         collectOutputRootClosureSummary().constant_calli_targets) {
      targets.insert(target);
    }
    return targets;
  };

  auto collectOutputRootConstantDispatchTargets = [&]() {
    llvm::DenseSet<uint64_t> targets;
    for (uint64_t target :
         collectOutputRootClosureSummary().constant_dispatch_targets) {
      targets.insert(target);
    }
    return targets;
  };

  auto collectOutputRootAnnotatedVmContinuationTargets = [&]() {
    llvm::DenseSet<uint64_t> targets;
    for (uint64_t target :
         collectOutputRootClosureSummary().annotated_vm_continuation_targets) {
      targets.insert(target);
    }
    return targets;
  };

  auto rerunLateOutputRootTargetPipeline = [&]() {
    const bool enable_late_output_target_rerun =
        parseBoolEnv("OMILL_ENABLE_LATE_OUTPUT_ROOT_TARGET_RERUN")
            .value_or(false);
    if (!opts.use_block_lifting)
      return;
    if (!enable_late_output_target_rerun) {
      return;
    }
    if (parseBoolEnv("OMILL_SKIP_LATE_OUTPUT_ROOT_TARGET_RERUN")
            .value_or(false)) {
      return;
    }
    const bool debug_late_output_target_rerun =
        parseBoolEnv("OMILL_DEBUG_LATE_OUTPUT_ROOT_TARGET_RERUN")
            .value_or(false);

    constexpr unsigned kMaxRounds = 2;
    constexpr unsigned kMaxTargetsPerRound = 2;

    for (unsigned round = 0; round < kMaxRounds; ++round) {
      if (debug_late_output_target_rerun)
        errs() << "[late-output-target] round=" << (round + 1)
               << " collect\n";
      auto targets = collectOutputRootConstantCodeCallTargets();
      auto calli_targets = collectOutputRootConstantCalliTargets();
      targets.insert(calli_targets.begin(), calli_targets.end());
      auto dispatch_targets = collectOutputRootConstantDispatchTargets();
      targets.insert(dispatch_targets.begin(), dispatch_targets.end());
      auto vm_targets = collectOutputRootAnnotatedVmContinuationTargets();
      targets.insert(vm_targets.begin(), vm_targets.end());
      if (debug_late_output_target_rerun) {
        errs() << "[late-output-target] round=" << (round + 1)
               << " raw-code=" << collectOutputRootConstantCodeCallTargets().size()
               << " raw-calli=" << calli_targets.size()
               << " raw-dispatch=" << dispatch_targets.size()
               << " raw-vm=" << vm_targets.size()
               << " merged=" << targets.size() << "\n";
      }
      if (targets.empty())
        break;

      llvm::SmallVector<uint64_t, 8> ordered_targets(targets.begin(),
                                                     targets.end());
      llvm::sort(ordered_targets);
      ordered_targets.erase(
          std::remove_if(ordered_targets.begin(), ordered_targets.end(),
                         [&](uint64_t pc) {
                           auto *lifted =
                               findLiftedOrBlockFunction(pc, /*native=*/false);
                           auto *native =
                               findLiftedOrBlockFunction(pc, /*native=*/true);
                           return (lifted && !lifted->isDeclaration()) ||
                                  (native && !native->isDeclaration());
                         }),
          ordered_targets.end());
      if (ordered_targets.empty())
        break;
      if (ordered_targets.size() > kMaxTargetsPerRound)
        ordered_targets.resize(kMaxTargetsPerRound);
      bool vm_only_targets = !ordered_targets.empty();
      for (uint64_t pc : ordered_targets) {
        if (!vm_targets.count(pc)) {
          vm_only_targets = false;
          break;
        }
      }
      if (debug_late_output_target_rerun) {
        errs() << "[late-output-target] round=" << (round + 1)
               << " targets=";
        for (uint64_t pc : ordered_targets)
          errs() << " 0x" << llvm::Twine::utohexstr(pc);
        errs() << " mode=" << (vm_only_targets ? "iterative-vm" : "direct")
               << "\n";
      }

      ScopedEnvOverride skip_always_inline("OMILL_SKIP_ALWAYS_INLINE", "1");
      if (debug_late_output_target_rerun)
        errs() << "[late-output-target] round=" << (round + 1)
               << " lift+rerun\n";
      if (!liftScopedTargets(ordered_targets, "omill.late_output_target_lifted",
                             /*run_abi=*/!vm_only_targets,
                             /*skip_missing_block_lift=*/true,
                             /*clear_attr=*/true,
                             /*mark_closed_root_slice=*/false,
                             /*use_direct_lifter=*/!vm_only_targets && !NoABI)) {
        break;
      }

      if (debug_late_output_target_rerun)
        errs() << "[late-output-target] round=" << (round + 1)
               << " patch\n";
      patchConstantIntToPtrCallsToNative(
          ordered_targets, "late_output_root_target_patch",
          "patched output-root constant inttoptr calls");
      patchConstantCalliTargetsToDirectCalls(
          ordered_targets, "late_output_root_calli_patch",
          "patched output-root constant CALLI callsites");
      patchConstantDispatchTargetsToDirectCalls(
          ordered_targets, "late_output_root_dispatch_patch",
          "patched output-root constant dispatch callsites");

      // The new targets may expose another constant callsite in the root.
      // Recompute analyses before the next bounded round.
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      if (debug_late_output_target_rerun)
        errs() << "[late-output-target] round=" << (round + 1)
               << " done\n";
    }
  };

  auto rerunFinalClosedSlicePipeline = [&]() {
    if (devirtualization_plan.enable_devirtualization)
      return;
    if (!opts.generic_static_devirtualize || !opts.use_block_lifting || !NoABI ||
        parseBoolEnv("OMILL_SKIP_FINAL_CLOSED_SLICE_RERUN").value_or(false)) {
      return;
    }
    if (!hasClosedSlicePendingOpaqueEdges())
      return;

    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    omill::PipelineOptions late_opts = opts;
    late_opts.resolve_indirect_targets = false;
    late_opts.use_block_lifting = false;
    late_opts.merge_block_functions_after_fixpoint = false;
    late_opts.skip_closed_slice_missing_block_lift = true;
    late_opts.scope_predicate = [](llvm::Function &F) {
      return F.hasFnAttribute("omill.closed_root_slice");
    };
    late_opts.preserve_lifted_semantics = preserve_lift_infrastructure;

    ModulePassManager MPM;
    omill::buildPipeline(MPM, late_opts);
    MPM.run(*module, MAM);
    emitIterativeSessionEvents(events, iterative_session,
                               "late-closed-slice-rerun");
  };

  auto countLiftedPipelineFunctions = [&]() {
    unsigned count = 0;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      auto name = F.getName();
      if (name.starts_with("sub_") || name.starts_with("blk_") ||
          name.starts_with("block_") || name.starts_with("__lifted_") ||
          F.hasFnAttribute("omill.output_root") ||
          F.hasFnAttribute("omill.vm_wrapper") ||
          F.hasFnAttribute("omill.vm_handler") ||
          F.hasFnAttribute("omill.vm_newly_lifted") ||
          F.hasFnAttribute("omill.newly_lifted") ||
          F.getFnAttribute("omill.vm_demerged_clone").isValid() ||
          F.getFnAttribute("omill.vm_outlined_virtual_call").isValid()) {
        ++count;
      }
    }
    return count;
  };

  if (opts.no_abi_mode)
    module->setModuleFlag(llvm::Module::Override, "omill.no_abi_mode", 1u);
  std::string requested_root_env_value;
  std::unique_ptr<ScopedEnvOverride> requested_root_va_guard;
  if (func_va != 0) {
    requested_root_env_value =
        (llvm::Twine("0x") + llvm::Twine::utohexstr(func_va)).str();
    requested_root_va_guard = std::make_unique<ScopedEnvOverride>(
        "OMILL_REQUESTED_ROOT_VA", requested_root_env_value.c_str());
  }


  constexpr uint64_t kLargeExecutableSectionBytes = 256ull << 10;
