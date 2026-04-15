  omill::setProcessMemoryLimit(32ULL * 1024 * 1024 * 1024);  // 32 GB
  InitLLVM X(argc, argv);
  cl::ParseCommandLineOptions(argc, argv,
      "omill-lift: Lift a function from a PE/Mach-O binary and optimize\n");
  configureDriverLogging(argv[0]);

  LiftEventLogger events;
  if (!events.init(EventJSONL, EventDetail, InputFilename))
    return 1;
  events.emitInfo("run_started", "omill-lift started",
                  {{"input", InputFilename}});

  auto fail = [&](int code, StringRef reason) -> int {
    events.emitError("run_error", reason);
    events.emitTerminalFailure(code, reason);
    return code;
  };

  // Check for batch/scan modes that don't require --va.
  bool batch_mode = (ScanSection.getNumOccurrences() > 0 ||
                     DeobfTargets.getNumOccurrences() > 0 ||
                     DeobfSection.getNumOccurrences() > 0 ||
                     AllFunctions);

  // Parse VA — for raw binaries, default to base address if --va not given.
  uint64_t func_va = 0;
  if (FuncVA.getNumOccurrences() > 0) {
    if (StringRef(FuncVA).starts_with("0x") ||
        StringRef(FuncVA).starts_with("0X")) {
      StringRef(FuncVA).drop_front(2).getAsInteger(16, func_va);
    } else {
      StringRef(FuncVA).getAsInteger(16, func_va);
    }
  } else if (RawBinary) {
    func_va = BaseAddress;
  } else if (!batch_mode) {
    errs() << "--va is required for single-function lifting\n";
    return fail(1, "--va is required for single-function lifting");
  }
  if (func_va == 0 && !RawBinary && !batch_mode) {
    errs() << "Invalid VA: " << FuncVA << "\n";
    return fail(1, "invalid --va value");
  }
  const uint64_t requested_func_va = func_va;
  if (func_va != 0)
    errs() << "Lifting function at VA 0x" << Twine::utohexstr(func_va) << "\n";

  // Parse VM entry/exit VAs if provided.
  uint64_t vm_entry_va = 0, vm_exit_va = 0;
  auto parseHexOpt = [](const std::string &s) -> uint64_t {
    uint64_t v = 0;
    StringRef sr(s);
    if (sr.starts_with("0x") || sr.starts_with("0X"))
      sr.drop_front(2).getAsInteger(16, v);
    else
      sr.getAsInteger(16, v);
    return v;
  };
  if (VMEntry.getNumOccurrences() > 0)
    vm_entry_va = parseHexOpt(VMEntry);
  if (VMExit.getNumOccurrences() > 0)
    vm_exit_va = parseHexOpt(VMExit);

  uint64_t vm_wrapper_va = 0;
  if (VMWrapper.getNumOccurrences() > 0)
    vm_wrapper_va = parseHexOpt(VMWrapper);

  if (!SolveStateFields.empty() && !SolveControlVA.getNumOccurrences())
    return fail(1, "--solve-state-field requires --solve-control-va");

  uint64_t solve_control_va = 0;
  if (SolveControlVA.getNumOccurrences() > 0)
    solve_control_va = parseHexOpt(SolveControlVA);

  bool vm_mode = (vm_entry_va != 0);

  const bool has_external_vm_trace = VMTraceJSON.getNumOccurrences() > 0;
  const bool force_devirtualize = Devirtualize;
  const bool env_generic_static_devirtualize =
      parseBoolEnv("OMILL_GENERIC_STATIC_DEVIRT").value_or(false);
  const bool env_verify_generic_static_devirtualize =
      parseBoolEnv("OMILL_VERIFY_GENERIC_STATIC_DEVIRT").value_or(false);
  const bool force_generic_static_devirtualize =
      parseBoolEnv("OMILL_FORCE_GENERIC_STATIC_DEVIRT").value_or(false);
  bool use_block_lift_mode =
      BlockLift || force_devirtualize || GenericStaticDevirtualize ||
      env_generic_static_devirtualize;
  if (vm_mode) {
    // Default wrapper to func_va if not explicitly specified.
    if (vm_wrapper_va == 0)
      vm_wrapper_va = func_va;
    errs() << "VM mode: vmenter=0x" << Twine::utohexstr(vm_entry_va)
           << " vmexit=0x" << Twine::utohexstr(vm_exit_va);
    if (vm_wrapper_va != func_va)
      errs() << " wrapper=0x" << Twine::utohexstr(vm_wrapper_va);
    errs() << "\n";
    events.emitInfo("vm_mode",
                    "vm devirtualization mode enabled",
                    {{"vm_entry", ("0x" + Twine::utohexstr(vm_entry_va)).str()},
                     {"vm_exit", ("0x" + Twine::utohexstr(vm_exit_va)).str()}});
  }
  if (force_devirtualize) {
    events.emitInfo("devirtualization_requested",
                    "library-owned devirtualization requested",
                    {{"forced", true},
                     {"compat_block_lift", static_cast<bool>(BlockLift)},
                     {"compat_generic_static",
                      static_cast<bool>(GenericStaticDevirtualize)}});
  }

  // --- Binary loading with format auto-detection ---
  PEInfo pe;
  std::vector<uint8_t> raw_code;
  remill::ArchName detected_arch = remill::kArchAMD64_AVX;
  remill::OSName detected_os = remill::kOSWindows;
  omill::TargetArch target_arch = omill::TargetArch::kX86_64;
  std::string target_os_str = "windows";
  events.emitInfo("input_load_started", "loading input");

  if (RawBinary) {
    auto buf_or_err = MemoryBuffer::getFile(InputFilename);
    if (!buf_or_err) {
      errs() << "Cannot open " << InputFilename << ": "
             << buf_or_err.getError().message() << "\n";
      return fail(1, "cannot open raw input file");
    }
    auto &buf = *buf_or_err;
    raw_code.assign(
        reinterpret_cast<const uint8_t *>(buf->getBufferStart()),
        reinterpret_cast<const uint8_t *>(buf->getBufferEnd()));
    errs() << "Loaded raw binary: " << raw_code.size()
           << " bytes at base 0x" << Twine::utohexstr(BaseAddress) << "\n";
    detected_os = remill::kOSLinux;
    target_os_str = "linux";
    events.emitInfo("input_load_completed", "raw input loaded",
                    {{"mode", "raw"},
                     {"bytes", static_cast<int64_t>(raw_code.size())},
                     {"base", ("0x" + Twine::utohexstr(BaseAddress)).str()}});
  } else {
    // Auto-detect binary format by peeking at the magic bytes.
    bool is_macho = looksLikeMachOInput(InputFilename);

    if (is_macho) {
      if (!loadMachO(InputFilename, pe, detected_arch, detected_os))
        return fail(1, "failed to load Mach-O input");
      if (detected_arch == remill::kArchAArch64LittleEndian) {
        target_arch = omill::TargetArch::kAArch64;
        target_os_str = "darwin";
      } else {
        target_arch = omill::TargetArch::kX86_64;
        target_os_str = "darwin";
      }
      errs() << "Loaded Mach-O: image_base=0x"
             << Twine::utohexstr(pe.image_base)
             << " code_sections=" << pe.code_sections.size()
             << " arch=" << (target_arch == omill::TargetArch::kAArch64
                                 ? "aarch64" : "x86_64") << "\n";
    } else {
      // Default: PE/COFF
      if (!loadPE(InputFilename, pe))
        return fail(1, "failed to load PE input");
      errs() << "Loaded PE: image_base=0x" << Twine::utohexstr(pe.image_base)
             << " code_sections=" << pe.code_sections.size() << "\n";
    }
    for (const auto &cs : pe.code_sections) {
      errs() << "  code: 0x" << Twine::utohexstr(cs.va)
             << " (" << cs.size << " bytes)\n";
    }
    if (pe.code_sections.empty()) {
      errs() << "No executable sections found in input binary\n";
      return fail(1, "no executable sections found");
    }
    events.emitInfo("input_load_completed",
                    pe.is_macho ? "Mach-O input loaded" : "PE input loaded",
                    {{"mode", pe.is_macho ? "macho" : "pe"},
                     {"image_base", ("0x" + Twine::utohexstr(pe.image_base)).str()},
                     {"code_sections", static_cast<int64_t>(pe.code_sections.size())}});

    // Auto-detect vm_entry/vm_exit when not specified via CLI.
    // The Unicorn redirect emulation traces through the VMP section and
    // captures the first/last VMP addresses hit.
    if (vm_entry_va == 0 && func_va != 0 && !pe.is_macho &&
        (GenericStaticDevirtualize || env_generic_static_devirtualize ||
         force_devirtualize)) {
      auto rr = omill::analyzeReturnAddressRedirectEx(
          pe.memory_map, func_va);
      if (rr.vm_entry_va != 0) {
        vm_entry_va = rr.vm_entry_va;
        vm_exit_va = rr.vm_exit_va;
        vm_mode = true;
        // Use the call site as wrapper VA — the trace emulator's wrapper
        // parser expects the LEA RSP + CALL vmentry pattern at this address.
        if (vm_wrapper_va == 0)
          vm_wrapper_va = rr.vm_call_site ? rr.vm_call_site : func_va;
        errs() << "Auto-detected VM entry/exit from Unicorn redirect:\n"
               << "  vm_entry=0x" << Twine::utohexstr(vm_entry_va)
               << " vm_exit=0x" << Twine::utohexstr(vm_exit_va)
               << " vm_call_site=0x" << Twine::utohexstr(rr.vm_call_site)
               << "\n";
        events.emitInfo("vm_auto_detected",
                        "auto-detected VM entry/exit from Unicorn redirect",
                        {{"vm_entry", ("0x" + Twine::utohexstr(vm_entry_va)).str()},
                         {"vm_exit", ("0x" + Twine::utohexstr(vm_exit_va)).str()}});
      }
    }

    auto resolveDirectJmpThunkTarget = [&](uint64_t root_va)
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
        const uint64_t target_va = root_va + 5u + static_cast<int64_t>(rel);
        if (findCodeSection(pe, target_va))
          return target_va;
      }
      if (remaining >= 2u && stored[offset] == 0xEBu) {
        int8_t rel = static_cast<int8_t>(stored[offset + 1u]);
        const uint64_t target_va = root_va + 2u + rel;
        if (findCodeSection(pe, target_va))
          return target_va;
      }
      return std::nullopt;
    };

    if (!batch_mode && !vm_mode && func_va != 0 &&
        std::find(pe.exported_function_starts.begin(),
                  pe.exported_function_starts.end(),
                  requested_func_va) != pe.exported_function_starts.end()) {
      if (auto thunk_target = resolveDirectJmpThunkTarget(requested_func_va)) {
        if (*thunk_target != requested_func_va) {
          errs() << "Export thunk root normalized: 0x"
                 << Twine::utohexstr(requested_func_va) << " -> 0x"
                 << Twine::utohexstr(*thunk_target) << "\n";
          func_va = *thunk_target;
        }
      }
    }

    // --scan-section: classify functions and output JSON, then exit.
    if (ScanSection.getNumOccurrences() > 0) {
      events.emitInfo("scan_started", "scan-section started",
                      {{"section", ScanSection}});
      auto results = scanSection(ScanSection, pe);
      // Filter by minimum size unless --scan-all.
      if (!ScanAll) {
        results.erase(
            std::remove_if(results.begin(), results.end(),
                           [](const ScanResult &r) {
                             return r.size < MinFuncSize;
                           }),
            results.end());
      }
      errs() << "Scanned " << results.size() << " functions in '"
             << ScanSection << "'\n";

      if (ScanOutput == "-") {
        writeScanJSON(results, InputFilename, pe.image_base, ScanSection,
                      outs());
      } else {
        std::error_code ec;
        raw_fd_ostream out(ScanOutput, ec, sys::fs::OF_Text);
        if (ec) {
          errs() << "Error opening " << ScanOutput << ": "
                 << ec.message() << "\n";
          return fail(1, "scan-output open failed");
        }
        writeScanJSON(results, InputFilename, pe.image_base, ScanSection, out);
      }
      events.emitInfo("scan_completed", "scan-section completed",
                      {{"section", ScanSection},
                       {"function_count", static_cast<int64_t>(results.size())}});
      events.emitTerminalSuccess(ScanOutput == "-"
                                     ? StringRef("<stdout>")
                                     : StringRef(ScanOutput));
      return 0;
    }
  }

  // Collect batch VAs from --deobf-targets, --deobf-section, or
  // --all-functions.
  std::vector<uint64_t> batch_vas;
  if (DeobfTargets.getNumOccurrences() > 0) {
    batch_vas = parseDeobfTargets(DeobfTargets);
    if (batch_vas.empty()) {
      errs() << "No valid VAs in " << DeobfTargets << "\n";
      return fail(1, "no valid VAs in --deobf-targets");
    }
    errs() << "Batch mode: " << batch_vas.size()
           << " targets from " << DeobfTargets << "\n";
  } else if (DeobfSection.getNumOccurrences() > 0) {
    events.emitInfo("batch_discovery_started",
                    "discovering targets from section",
                    {{"section", DeobfSection}});
    auto results = scanSection(DeobfSection, pe);
    for (const auto &r : results) {
      if (r.size >= MinFuncSize)
        batch_vas.push_back(r.va);
    }
    if (batch_vas.empty()) {
      errs() << "No functions >= " << MinFuncSize
             << "B in section '" << DeobfSection << "'\n";
      return fail(1, "no qualifying functions found in --deobf-section");
    }
    errs() << "Section mode: " << batch_vas.size()
           << " functions from '" << DeobfSection << "' (>= "
           << MinFuncSize << "B)\n";
    // Force deobfuscation on for --deobf-section.
    Deobfuscate = true;
  } else if (AllFunctions) {
    if (RawBinary) {
      errs() << "--all-functions is not supported for raw binaries\n";
      return fail(1, "--all-functions is not supported for raw binaries");
    }
    batch_vas = collectBatchFunctionStarts(pe);
    if (batch_vas.empty()) {
      errs() << "No discovered functions in executable sections\n";
      return fail(1, "no discovered functions found");
    }
    errs() << "All-functions mode: " << batch_vas.size()
           << " discovered functions\n";
    events.emitInfo("batch_discovery_started",
                    "discovering all executable functions",
                    {{"count", static_cast<int64_t>(batch_vas.size())}});
  }
  if (!batch_vas.empty()) {
    events.emitInfo("batch_targets_ready", "batch target set created",
                    {{"count", static_cast<int64_t>(batch_vas.size())}});
  }

  // Set up remill with the detected architecture.
  LLVMContext ctx;
  auto arch = remill::Arch::Get(ctx, detected_os, detected_arch);
  if (!arch) {
    errs() << "Failed to create arch (arch="
           << static_cast<int>(detected_arch)
           << " os=" << static_cast<int>(detected_os) << ")\n";
    return fail(1, "failed to create arch");
  }

  auto module = remill::LoadArchSemantics(arch.get());
  if (!module) {
    errs() << "Failed to load arch semantics\n";
    return fail(1, "failed to load arch semantics");
  }

  // Load code into the trace manager.
  omill::BufferTraceManager manager;
  manager.setModuleAndArch(module.get(), arch.get());
  if (!RawBinary)
    manager.setBinaryMemoryMap(&pe.memory_map);
  manager.setTargetArch(target_arch);
  if (RawBinary) {
    manager.setCode(raw_code.data(), raw_code.size(), BaseAddress);
  } else {
    for (const auto &cs : pe.code_sections) {
      auto &stored = pe.section_storage[cs.storage_index];
      manager.setCode(stored.data(), stored.size(), cs.va);
    }
  }
  if (!batch_vas.empty())
    manager.setBaseAddr(batch_vas.front());
  else if (func_va != 0)
    manager.setBaseAddr(func_va);

  if (!RawBinary && ResolveExceptions && !pe.exception_info.empty()) {
    errs() << "Parsed .pdata: " << pe.exception_info.getHandlerVAs().size()
           << " unique handler(s)\n";
  }

  uint64_t early_largest_executable_section_size = 0;
  if (!vm_mode && !RawBinary && NoABI && func_va != 0) {
    for (const auto &cs : pe.code_sections) {
      if (cs.storage_index < pe.section_storage.size()) {
        early_largest_executable_section_size =
            std::max<uint64_t>(early_largest_executable_section_size,
                               pe.section_storage[cs.storage_index].size());
      }
    }
    constexpr uint64_t kLargeExecutableSectionBytes = 256ull << 10;
    if (pe.code_sections.size() > 1 &&
        early_largest_executable_section_size >= kLargeExecutableSectionBytes) {
      use_block_lift_mode = true;
      events.emitInfo(
          "block_lift_auto_enabled",
          "block lift auto-enabled for large no-abi multi-section input",
          {{"largest_executable_section_size",
            static_cast<int64_t>(early_largest_executable_section_size)},
           {"code_sections",
            static_cast<int64_t>(pe.code_sections.size())}});
    }
  }

  // Lift
  // Lift
  omill::TraceLifter lifter(arch.get(), manager);
  auto iterative_session =
      std::make_shared<omill::IterativeLiftingSession>("omill-lift");
  iterative_session->setBlockLiftingEnabled(use_block_lift_mode);
  std::unique_ptr<omill::LiftDatabase> lift_db;
  std::unique_ptr<omill::StaticLiftBuilder> lift_db_builder;

  std::unique_ptr<omill::BufferBlockManager> block_manager;
  std::unique_ptr<omill::BlockLifter> block_lifter;
  std::unique_ptr<omill::RemillProjectionLifter> projection_lifter;
  if (!vm_mode) {
    block_manager = std::make_unique<omill::BufferBlockManager>();
    block_manager->setModule(module.get());
    if (!RawBinary)
      block_manager->setBinaryMemoryMap(&pe.memory_map);
    block_manager->setTargetArch(target_arch);
    if (RawBinary) {
      block_manager->setCode(raw_code.data(), raw_code.size(), BaseAddress);
    } else {
      for (auto &sec : pe.code_sections) {
        auto &data = pe.section_storage[sec.storage_index];
        block_manager->setCode(data.data(), data.size(), sec.va);
      }
    }
    block_lifter =
        std::make_unique<omill::BlockLifter>(arch.get(), *block_manager);
  }
  projection_lifter = std::make_unique<omill::RemillProjectionLifter>(
      nullptr, lifter, block_lifter.get());

  const bool persistent_lift_db_requested =
      LiftDBIn.getNumOccurrences() > 0 || LiftDBOut.getNumOccurrences() > 0;
  const bool auto_static_lift_db =
      !vm_mode && !RawBinary && target_arch == omill::TargetArch::kX86_64 &&
      (!batch_vas.empty() || func_va != 0);

  if (persistent_lift_db_requested || auto_static_lift_db) {
    if (persistent_lift_db_requested &&
        target_arch != omill::TargetArch::kX86_64) {
      return fail(1, "lift-db currently supports x64 only");
    }
    if (persistent_lift_db_requested && RawBinary) {
      return fail(1, "lift-db static builder does not support raw binary mode");
    }

    // Feed TraceLifter/BlockLifter from a static lift-db for file-backed x64
    // inputs so control-flow recovery reuses StaticLiftBuilder's block
    // boundaries instead of rediscovering mid-block targets from raw decode.
    if (target_arch == omill::TargetArch::kX86_64 && !RawBinary) {
      lift_db = std::make_unique<omill::LiftDatabase>();
      auto &db = *lift_db;
      std::string lift_db_error;
      if (LiftDBIn.getNumOccurrences() > 0 && !LiftDBRebuild) {
        auto loaded_db =
            omill::LoadLiftDatabaseFromDirectory(LiftDBIn.getValue(),
                                                 &lift_db_error);
        if (!loaded_db) {
          return fail(1, "failed to load --lift-db-in: " + lift_db_error);
        }
        db = std::move(*loaded_db);
      }

      db.manifest().image_path = InputFilename;
      db.manifest().image_id = InputFilename;
      db.manifest().image_base = RawBinary ? BaseAddress : pe.image_base;
      if (RawBinary)
        db.manifest().image_size = raw_code.size();
      db.manifest().arch = omill::LiftDbArch::kX64;

      std::vector<uint64_t> lift_db_roots;
      lift_db_roots.reserve(batch_vas.size() + 1);
      if (!batch_vas.empty()) {
        for (uint64_t va : batch_vas)
          lift_db_roots.push_back(va);
      } else if (func_va != 0) {
        lift_db_roots.push_back(func_va);
      }

      omill::StaticLiftBuilderOptions lift_db_builder_options;
      lift_db_builder_options.refresh_existing = LiftDBRebuild;
      lift_db_builder = std::make_unique<omill::StaticLiftBuilder>(
          arch.get(), RawBinary ? nullptr : &pe.memory_map, target_arch,
          lift_db_builder_options);
      lift_db_builder->buildFunctions(lift_db_roots, db);
      lifter.SetLiftDatabase(lift_db.get());
      if (block_lifter) {
        block_lifter->SetLiftDatabase(lift_db.get());
      }
      projection_lifter = std::make_unique<omill::RemillProjectionLifter>(
          lift_db.get(), lifter, block_lifter.get());

      if (!vm_mode && LiftDBOut.getNumOccurrences() > 0 &&
          !omill::SaveLiftDatabaseToDirectory(db, LiftDBOut.getValue(),
                                              &lift_db_error)) {
        return fail(1, "failed to write --lift-db-out: " + lift_db_error);
      }
    }
  }

  if (!batch_vas.empty()) {
    for (uint64_t va : batch_vas)
      iterative_session->queueTarget(va);
  } else if (func_va != 0) {
    iterative_session->queueTarget(func_va);
  }
  events.emitInfo("lifting_started", "lifting started");

  auto tagOutputRoot = [&](uint64_t va) {
    std::string base = "sub_" + llvm::Twine::utohexstr(va).str();
    if (auto *fn = module->getFunction(base)) {
      if (!fn->isDeclaration())
        fn->addFnAttr("omill.output_root");
      return;
    }
    for (int i = 1; i <= 20; ++i) {
      if (auto *fn = module->getFunction((base + "." + std::to_string(i)).c_str())) {
        if (!fn->isDeclaration()) {
          fn->addFnAttr("omill.output_root");
          return;
        }
      }
    }
    std::string block_name = "blk_" + llvm::Twine::utohexstr(va).str();
    if (auto *fn = module->getFunction(block_name)) {
      if (!fn->isDeclaration())
        fn->addFnAttr("omill.output_root");
    }
  };

  // Wrapper VAs detected during auto-detection (thunk_va, wrapper_va).
  std::vector<std::pair<uint64_t, uint64_t>> auto_detected_wrappers;

  if (!batch_vas.empty()) {
    // Batch lifting mode.
    unsigned lifted = 0, failed = 0;
    for (uint64_t va : batch_vas) {
      if (events.detailed()) {
        events.emitInfo("lift_target_started", "lifting target",
                        {{"va", ("0x" + Twine::utohexstr(va)).str()}});
      }
      bool ok = false;
      if (use_block_lift_mode && !vm_mode && block_lifter) {
        ok = projection_lifter && projection_lifter->LiftReachable(va) > 0;
      } else {
        ok = projection_lifter && projection_lifter->LiftFunction(va);
      }
      if (ok) {
        iterative_session->noteLiftedTarget(va);
        ++lifted;
      } else {
        ++failed;
      }
    }
    errs() << "Batch lift: " << lifted << " succeeded, "
           << failed << " failed\n";
    events.emitInfo("lifting_batch_completed", "batch lift finished",
                    {{"lifted", static_cast<int64_t>(lifted)},
                     {"failed", static_cast<int64_t>(failed)}});
    if (lifted == 0) {
      errs() << "No functions lifted\n";
      return fail(1, "no functions lifted");
    }
    for (uint64_t va : batch_vas)
      tagOutputRoot(va);
  } else {
  auto liftEarlyPushJumpContinuationTargets = [&]() {
    if (RawBinary || !block_lifter || !use_block_lift_mode)
      return;
    const bool debug_markers_enabled =
        std::getenv("OMILL_DEBUG_MARKER_FILE") != nullptr;
    if (debug_markers_enabled)
      appendDebugMarker("early-continuation:scan-begin");
    llvm::SmallVector<uint64_t, 8> targets;
    llvm::DenseSet<uint64_t> seen_targets;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call || call->arg_size() < 2)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || callee->getName() != "__remill_function_call")
            continue;
          auto *pc_ci = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!pc_ci)
            continue;
          const uint64_t thunk_pc = pc_ci->getZExtValue();
          uint8_t bytes[10] = {};
          if (!pe.memory_map.read(thunk_pc, bytes, sizeof(bytes)))
            continue;
          if (bytes[0] != 0x68 || bytes[5] != 0xE9)
            continue;
          int32_t rel32 = 0;
          std::memcpy(&rel32, &bytes[6], sizeof(rel32));
          const uint64_t jump_target = static_cast<uint64_t>(
              static_cast<int64_t>(thunk_pc + 10) + static_cast<int64_t>(rel32));
          if (!seen_targets.insert(jump_target).second)
            continue;
          if (omill::findLiftedOrBlockFunctionByPC(*module, jump_target))
            continue;
          targets.push_back(jump_target);
        }
      }
    }

    if (debug_markers_enabled) {
      appendDebugMarker((llvm::Twine("early-continuation:scan-done:") +
                         llvm::Twine(targets.size()))
                            .str()
                            .c_str());
    }
    if (targets.empty())
      return;

    constexpr size_t kMaxEarlyContinuationTargets = 2;
    if (targets.size() > kMaxEarlyContinuationTargets)
      targets.resize(kMaxEarlyContinuationTargets);

    for (uint64_t target : targets) {
      if (debug_markers_enabled) {
        appendDebugMarker((llvm::Twine("early-continuation:lift-begin:0x") +
                           llvm::Twine::utohexstr(target))
                              .str()
                              .c_str());
      }
      llvm::SmallVector<uint64_t, 16> discovered_targets;
      llvm::Function *lifted = nullptr;
      __try {
        lifted = projection_lifter
                     ? projection_lifter->LiftBlock(target, discovered_targets)
                     : nullptr;
      } __except (1) {
        lifted = nullptr;
      }
      if (debug_markers_enabled) {
        appendDebugMarker(lifted ? "early-continuation:lift-end:1"
                                 : "early-continuation:lift-end:0");
      }
      if (lifted)
        iterative_session->noteLiftedTarget(target);
    }
  };

    // Single-function lifting mode.
    if (use_block_lift_mode && !vm_mode && block_lifter) {
      if (!projection_lifter || projection_lifter->LiftReachable(func_va) == 0) {
        errs() << "BlockLifter::LiftReachable() failed\n";
        return fail(1, "block lifter failed");
      }
      iterative_session->noteLiftedTarget(func_va);
      tagOutputRoot(func_va);
      liftEarlyPushJumpContinuationTargets();
    } else {
    // If available, lift the handler first so Remill reuses a canonical
    // sub_<va> function instead of creating a late duplicate (sub_<va>.1).
    uint64_t auto_handler_va = 0;
    if (!RawBinary && ResolveExceptions) {
      if (auto *entry = pe.exception_info.lookup(func_va)) {
        auto_handler_va = entry->handler_va;
      }
    }
    if (auto_handler_va != 0 && auto_handler_va != func_va) {
      errs() << "Auto-lifting exception handler at 0x"
             << Twine::utohexstr(auto_handler_va) << "\n";
      if (events.detailed()) {
        events.emitInfo("lift_handler_started", "auto-lifting exception handler",
                        {{"va", ("0x" + Twine::utohexstr(auto_handler_va)).str()}});
      }
      if (!projection_lifter ||
          !projection_lifter->LiftFunction(auto_handler_va)) {
        errs() << "WARNING: failed to lift handler at 0x"
               << Twine::utohexstr(auto_handler_va) << "\n";
        events.emitWarn("lift_handler_failed", "failed to lift exception handler",
                        {{"va", ("0x" + Twine::utohexstr(auto_handler_va)).str()}});
      } else {
        iterative_session->noteLiftedTarget(auto_handler_va);
      }
    }

    if (!projection_lifter || !projection_lifter->LiftFunction(func_va)) {
      errs() << "TraceLifter::Lift() failed\n";
      return fail(1, "trace lifter failed");
    }
    iterative_session->noteLiftedTarget(func_va);
    tagOutputRoot(func_va);
    }

    // Auto-detect VM wrappers when --vm-wrapper is not specified.
    // DriverEntry (or similar outer function) calls thunks (E9 jmp) that
    // resolve to actual VM wrappers.  Collect ALL detected wrappers.
    if (vm_mode && vm_wrapper_va == func_va) {
      auto *entry_fn = module->getFunction(
          "sub_" + llvm::Twine::utohexstr(func_va).str());
      if (entry_fn) {
        for (auto &BB : *entry_fn) {
          for (auto &I : BB) {
            auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!call || call->arg_size() < 2)
              continue;
            auto *callee_fn = call->getCalledFunction();
            if (!callee_fn)
              continue;
            auto callee_name = callee_fn->getName();
            if (!callee_name.starts_with("sub_"))
              continue;
            uint64_t callee_va = 0;
            callee_name.drop_front(4).getAsInteger(16, callee_va);
            if (callee_va == 0)
              continue;

            // Follow jmp-thunks to a real function body.
            uint64_t resolved = callee_va;
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
            if (resolved == callee_va)
              continue;  // not a thunk

            // Probe the resolved VA for the wrapper pattern:
            //   optional lea rsp,[rsp-N] / sub rsp,N
            //   E8 <rel32>  (call to vmentry or near it)
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
            // Accept if the call target is within a reasonable range of vmentry.
            if (ctarget < vm_entry_va - 0x1000 || ctarget > vm_entry_va + 0x1000)
              continue;

            // Avoid duplicates (same wrapper from different thunks).
            bool dup = false;
            for (auto &[tv, wv] : auto_detected_wrappers)
              if (wv == resolved) { dup = true; break; }
            if (dup) continue;

            errs() << "Auto-detected VM wrapper at 0x"
                   << Twine::utohexstr(resolved)
                   << " (via thunk sub_"
                   << Twine::utohexstr(callee_va) << ")\n";
            auto_detected_wrappers.push_back({callee_va, resolved});
          }
        }
      }
      // Use the first detected wrapper as the primary one.
      if (!auto_detected_wrappers.empty())
        vm_wrapper_va = auto_detected_wrappers.front().second;
    }

    // When --vm-wrapper differs from --va, fold jmp-thunks between
    // func_va and the VM wrapper so that the entry function calls the
    // wrapper directly.  Without this, remill's TraceLifter follows the
    // thunk's JMP and duplicates the wrapper's code inside the thunk
    // function, producing an incomplete copy (only the first VM chain)
    // that confuses ABI recovery.
    if (vm_mode && vm_wrapper_va != func_va) {
      // Ensure the wrapper is lifted.
      {
        std::string wrapper_name =
            "sub_" + llvm::Twine::utohexstr(vm_wrapper_va).str();
        auto *wrapper_fn = module->getFunction(wrapper_name);
        if (!wrapper_fn || wrapper_fn->isDeclaration()) {
          errs() << "Auto-lifting VM wrapper at 0x"
                 << Twine::utohexstr(vm_wrapper_va) << "\n";
          projection_lifter->LiftFunction(vm_wrapper_va);
        }
      }

      // Detect jmp-thunks between the entry function and the wrapper by
      // reading binary bytes.  A jmp-thunk is a single E9/EB JMP
      // instruction that transfers to another function.  When the target
      // is the VM wrapper (or chains to it), rewrite the caller to call
      // the wrapper directly.
      //
      // Remill's TraceLifter creates DIRECT calls to lifted functions
      // (e.g. `call @sub_1400d5dc4(...)`) rather than going through
      // `__remill_function_call`.  So we scan for calls to `sub_*`
      // functions and check if the callee's VA is a jmp-thunk.
      auto *entry_fn = module->getFunction(
          "sub_" + llvm::Twine::utohexstr(func_va).str());
      if (entry_fn) {
        for (auto &BB : *entry_fn) {
          for (auto &I : BB) {
            auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!call || call->arg_size() < 2)
              continue;
            auto *callee_fn = call->getCalledFunction();
            if (!callee_fn)
              continue;

            // Parse VA from the callee function name (sub_<hex>).
            auto callee_name = callee_fn->getName();
            if (!callee_name.starts_with("sub_"))
              continue;
            uint64_t callee_va = 0;
            callee_name.drop_front(4).getAsInteger(16, callee_va);
            if (callee_va == 0 || callee_va == vm_wrapper_va)
              continue;

            // Follow up to 3 levels of jmp-thunks to find the wrapper.
            uint64_t resolved = callee_va;
            for (int hop = 0; hop < 3; ++hop) {
              uint8_t thunk_buf[16];
              if (!pe.memory_map.read(resolved, thunk_buf, sizeof(thunk_buf)))
                break;
              // E9 rel32 = near relative jmp (5 bytes)
              if (thunk_buf[0] == 0xE9) {
                int32_t rel;
                std::memcpy(&rel, &thunk_buf[1], 4);
                resolved = resolved + 5 + static_cast<int64_t>(rel);
              }
              // EB rel8 = short relative jmp (2 bytes)
              else if (thunk_buf[0] == 0xEB) {
                int8_t rel = static_cast<int8_t>(thunk_buf[1]);
                resolved = resolved + 2 + rel;
              } else {
                break;
              }
            }

            if (resolved != vm_wrapper_va)
              continue;

            // This callee is a jmp-thunk chain to the VM wrapper.
            // Rewrite the call to target the wrapper directly.
            errs() << "Folding jmp-thunk: sub_"
                   << Twine::utohexstr(callee_va) << " -> sub_"
                   << Twine::utohexstr(vm_wrapper_va) << "\n";

            std::string wrapper_name =
                "sub_" + llvm::Twine::utohexstr(vm_wrapper_va).str();
            auto *wrapper_fn = module->getFunction(wrapper_name);
            if (!wrapper_fn)
              continue;

            // Rewrite: call @sub_<thunk_va>(state, pc, mem)
            //       → call @sub_<wrapper_va>(state, wrapper_va, mem)
            call->setCalledFunction(wrapper_fn);
            // Fix the program_counter argument to the wrapper's address.
            auto *pc_arg = call->getArgOperand(1);
            call->setArgOperand(
                1, llvm::ConstantInt::get(pc_arg->getType(), vm_wrapper_va));

            // Delete the thunk function — it's a duplicated partial
            // copy of the wrapper that would confuse ABI recovery.
            std::string thunk_name =
                "sub_" + llvm::Twine::utohexstr(callee_va).str();
            if (auto *thunk_fn = module->getFunction(thunk_name)) {
              if (!thunk_fn->use_empty()) {
                // Can't delete if it has other uses; just leave it.
                errs() << "  (thunk has other callers, keeping)\n";
              } else {
                thunk_fn->eraseFromParent();
                errs() << "  (deleted thunk sub_"
                       << Twine::utohexstr(callee_va) << ")\n";
              }
            }
          }
        }
      }
    }

    // Process additional auto-detected wrappers (beyond the first one
    // which was handled above as vm_wrapper_va).
    if (vm_mode && auto_detected_wrappers.size() > 1) {
      auto *entry_fn = module->getFunction(
          "sub_" + llvm::Twine::utohexstr(func_va).str());
      for (size_t wi = 1; wi < auto_detected_wrappers.size(); ++wi) {
        uint64_t thunk_va = auto_detected_wrappers[wi].first;
        uint64_t wrapper_va = auto_detected_wrappers[wi].second;

        // Lift the wrapper.
        std::string wrapper_name =
            "sub_" + llvm::Twine::utohexstr(wrapper_va).str();
        auto *wrapper_fn = module->getFunction(wrapper_name);
        if (!wrapper_fn || wrapper_fn->isDeclaration()) {
          errs() << "Auto-lifting VM wrapper at 0x"
                 << Twine::utohexstr(wrapper_va) << "\n";
          projection_lifter->LiftFunction(wrapper_va);
          wrapper_fn = module->getFunction(wrapper_name);
        }
        if (!wrapper_fn)
          continue;

        // Fold the thunk to this wrapper.
        if (entry_fn) {
          std::string thunk_name =
              "sub_" + llvm::Twine::utohexstr(thunk_va).str();
          for (auto &BB : *entry_fn) {
            for (auto &I : BB) {
              auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!call || call->arg_size() < 2)
                continue;
              auto *callee_fn = call->getCalledFunction();
              if (!callee_fn || callee_fn->getName() != thunk_name)
                continue;
              errs() << "Folding jmp-thunk: sub_"
                     << Twine::utohexstr(thunk_va) << " -> sub_"
                     << Twine::utohexstr(wrapper_va) << "\n";
              call->setCalledFunction(wrapper_fn);
              auto *pc_arg = call->getArgOperand(1);
              call->setArgOperand(
                  1, llvm::ConstantInt::get(pc_arg->getType(), wrapper_va));
            }
          }
          // Delete the thunk if unused.
          if (auto *thunk_fn = module->getFunction(thunk_name)) {
            if (thunk_fn->use_empty()) {
              thunk_fn->eraseFromParent();
              errs() << "  (deleted thunk sub_"
                     << Twine::utohexstr(thunk_va) << ")\n";
            }
          }
        }
      }
    }
  }
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
        errs() << "Folded lifted declaration alias " << fname << " -> "
               << base_name << "\n";
      }
    }
  }
  errs() << "Lifting complete\n";
  events.emitInfo("lifting_completed", "lifting complete");

  // VM mode: use the trace emulator to discover handlers reachable from the
  // entry wrapper, then lift only those. No byte-pattern bulk scan — further
  // targets are discovered naturally by the pipeline's iterative resolution.
