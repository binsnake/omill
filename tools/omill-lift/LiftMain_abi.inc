  const bool large_noabi_lift =
      opts.no_abi_mode &&
      (countLiftedPipelineFunctions() >= 512 ||
       (!vm_mode && !RawBinary && pe.code_sections.size() > 1 &&
        early_largest_executable_section_size >= kLargeExecutableSectionBytes));
  std::unique_ptr<ScopedEnvOverride> auto_skip_late_cleanup_guard;
  std::unique_ptr<ScopedEnvOverride> auto_skip_output_final_cleanup_guard;
  std::unique_ptr<ScopedEnvOverride> auto_skip_late_const_memory_fold_guard;
  std::unique_ptr<ScopedEnvOverride> auto_disable_recursive_output_recovery_guard;
  std::unique_ptr<ScopedEnvOverride> auto_skip_terminal_boundary_side_probe_guard;
  std::unique_ptr<ScopedEnvOverride> auto_skip_terminal_boundary_secondary_root_guard;
  std::unique_ptr<ScopedEnvOverride> auto_skip_late_output_target_rerun_guard;
  std::unique_ptr<ScopedEnvOverride> auto_skip_late_terminal_boundary_rerun_guard;
  std::unique_ptr<ScopedEnvOverride> auto_skip_noabi_final_remill_normalization_guard;
  if (large_noabi_lift) {
    const auto lifted_function_count = countLiftedPipelineFunctions();
    auto_skip_late_cleanup_guard =
        std::make_unique<ScopedEnvOverride>("OMILL_SKIP_LATE_CLEANUP", "1");
    auto_skip_output_final_cleanup_guard = std::make_unique<ScopedEnvOverride>(
        "OMILL_SKIP_OUTPUT_FINAL_CLEANUP", "1");
    auto_skip_late_const_memory_fold_guard = std::make_unique<ScopedEnvOverride>(
        "OMILL_SKIP_LATE_CONST_MEMORY_FOLD", "1");
    auto_skip_noabi_final_remill_normalization_guard =
        std::make_unique<ScopedEnvOverride>(
            "OMILL_SKIP_NOABI_FINAL_REMILL_NORMALIZATION", "1");
    events.emitInfo("late_cleanup_auto_suppressed",
                    "late cleanup suppressed for large no-abi module",
                    {{"lifted_functions",
                      static_cast<int64_t>(lifted_function_count)}});
    events.emitInfo(
        "late_const_memory_fold_auto_suppressed",
        "late const memory fold suppressed for large no-abi module",
        {{"lifted_functions",
          static_cast<int64_t>(lifted_function_count)}});
    events.emitInfo(
        "final_output_cleanup_auto_suppressed",
        "final output cleanup suppressed for large no-abi module",
        {{"lifted_functions",
          static_cast<int64_t>(lifted_function_count)}});
    if (opts.generic_static_devirtualize) {
      auto_disable_recursive_output_recovery_guard =
          std::make_unique<ScopedEnvOverride>(
              "OMILL_DISABLE_RECURSIVE_OUTPUT_RECOVERY", "1");
      auto_skip_terminal_boundary_side_probe_guard =
          std::make_unique<ScopedEnvOverride>(
              "OMILL_SKIP_TERMINAL_BOUNDARY_SIDE_PROBE", "1");
      auto_skip_terminal_boundary_secondary_root_guard =
          std::make_unique<ScopedEnvOverride>(
              "OMILL_SKIP_TERMINAL_BOUNDARY_SECONDARY_ROOT_RECOVERY", "1");
      auto_skip_late_output_target_rerun_guard =
          std::make_unique<ScopedEnvOverride>(
              "OMILL_SKIP_LATE_OUTPUT_ROOT_TARGET_RERUN", "1");
      auto_skip_late_terminal_boundary_rerun_guard =
          std::make_unique<ScopedEnvOverride>(
              "OMILL_SKIP_LATE_TERMINAL_BOUNDARY_RERUN", "1");
      events.emitInfo(
          "recursive_output_recovery_auto_suppressed",
          "recursive output recovery suppressed for large no-abi generic-static module",
          {{"lifted_functions",
            static_cast<int64_t>(lifted_function_count)}});
    }
  }

  if (large_noabi_lift && opts.generic_static_devirtualize && !opts.scope_predicate) {
    opts.scope_predicate = [](llvm::Function &F) {
      return F.hasFnAttribute("omill.output_root") ||
             F.hasFnAttribute("omill.internal_output_root") ||
             F.hasFnAttribute("omill.closed_root_slice_root");
    };
    events.emitInfo("large_noabi_generic_static_scoped",
                    "scoped large no-abi generic-static run to root functions");
  }

  module->setModuleFlag(
      llvm::Module::Override, "omill.large_noabi_generic_static_scope",
      static_cast<uint32_t>(large_noabi_lift && opts.generic_static_devirtualize ? 1u
                                                                  : 0u));

  events.emitInfo("pipeline_started", "main pipeline started");
  {
    ModulePassManager MPM;
    omill::buildPipeline(MPM, opts);
    MPM.run(*module, MAM);
    omill::repairMalformedPHIs(*module);
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
  }
  emitIterativeSessionEvents(events, iterative_session, "main-pipeline");
  errs() << "Main pipeline complete\n";
  events.emitInfo("pipeline_completed", "main pipeline completed");
  if (!NoABI && func_va != 0)
    reapplyRequestedRootEntrySeedHint(func_va);
  dumpModuleIfEnvEnabled(*module, "OMILL_DEBUG_DUMP_AFTER_MAIN_PIPELINE",
                         "after_main_pipeline.ll");
  if (devirtualization_plan.enable_devirtualization) {
    devirtualization_orchestrator.recordEpoch(
        omill::DevirtualizationEpoch::kIncrementalBlockLift, *module,
        devirtualization_request.output_mode, /*changed=*/true,
        "main pipeline completed");
    emit_latest_devirtualization_epoch("main pipeline completed");
    devirtualization_orchestrator.recordEpoch(
        omill::DevirtualizationEpoch::kNormalizationCacheAdmission, *module,
        devirtualization_request.output_mode, /*changed=*/true,
        "normalized lift-unit cache refreshed");
    emit_latest_devirtualization_epoch("normalized lift-unit cache refreshed");
    if (opts.generic_static_devirtualize) {
      devirtualization_orchestrator.recordEpoch(
          omill::DevirtualizationEpoch::kCfgMaterialization, *module,
          devirtualization_request.output_mode, /*changed=*/true,
          "generic materialization completed");
      emit_latest_devirtualization_epoch("generic materialization completed");
    }
    devirtualization_orchestrator.recordEpoch(
        omill::DevirtualizationEpoch::kContinuationClosure, *module,
        devirtualization_request.output_mode, /*changed=*/true,
        "post-pipeline cleanup completed");
    emit_latest_devirtualization_epoch("post-pipeline cleanup completed");
  }

  bool noabi_output_root_targets_patched = false;
  auto runSharedLateStep = [&](llvm::StringRef label, auto &&fn) {
    const bool debug_late_steps =
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
    if (debug_late_steps) {
      errs() << "[late-step] begin " << label << "\n";
    }
    if (events.detailed()) {
      events.emitInfo("late_step_started", "late step started",
                      {{"label", label.str()}});
    }
    fn();
    if (events.detailed()) {
      events.emitInfo("late_step_completed", "late step completed",
                      {{"label", label.str()}});
    }
    if (debug_late_steps) {
      errs() << "[late-step] end " << label << "\n";
    }
  };

  appendDebugMarker("late:before_continuation");
  runSharedLateStep("rerun_late_continuation_pipeline", [&] {
    rerunLateContinuationPipeline();
  });
  appendDebugMarker("late:after_continuation");
  appendDebugMarker("late:before_terminal_boundary");
  runSharedLateStep("rerun_late_terminal_boundary_target_pipeline", [&] {
    rerunLateTerminalBoundaryTargetPipeline();
  });
  appendDebugMarker("late:after_terminal_boundary");
  appendDebugMarker("late:before_final_closed_slice");
  runSharedLateStep("rerun_final_closed_slice_pipeline", [&] {
    rerunFinalClosedSlicePipeline();
  });
  appendDebugMarker("late:after_final_closed_slice");
  dumpModuleIfEnvEnabled(*module, "OMILL_DEBUG_DUMP_AFTER_LATE_RERUNS",
                         "after_late_reruns.ll");

  auto moduleFlagEnabled = [&](llvm::StringRef flag_name) {
    auto *md = module->getModuleFlag(flag_name);
    auto *constant_md = llvm::dyn_cast_or_null<llvm::ConstantAsMetadata>(md);
    auto *constant_int =
        constant_md
            ? llvm::dyn_cast<llvm::ConstantInt>(constant_md->getValue())
            : nullptr;
    return constant_int && constant_int->isOne();
  };

  auto countInternalSyntheticBlockCalls = [&]() {
    unsigned count = 0;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || callee->isDeclaration())
            continue;
          auto name = callee->getName();
          if (!name.starts_with("blk_") && !name.starts_with("block_"))
            continue;
          ++count;
        }
      }
    }
    return count;
  };

  auto hasLiveDispatchReference = [&]() {
    for (auto &F : *module) {
      if (omill::isDispatchIntrinsicName(F.getName()) && !F.use_empty())
        return true;
    }
    return false;
  };

  auto hasLiveFunctionWithPrefix = [&](llvm::StringRef prefix) {
    for (auto &F : *module) {
      if (F.getName().starts_with(prefix) && !F.use_empty())
        return true;
    }
    return false;
  };

  auto rerunNoAbiClosedSliceCleanupReplay = [&]() {
    if (!NoABI ||
        (std::getenv("OMILL_SKIP_NOABI_POST_MAIN_CLEANUP_REPLAY") != nullptr))
      return;
    if (!moduleFlagEnabled("omill.closed_root_slice_scope"))
      return;
    if (hasLiveDispatchReference())
      return;
    if (hasLiveFunctionWithPrefix("vm_entry_"))
      return;

    const unsigned before_block_calls = countInternalSyntheticBlockCalls();
    auto countReachableLiveRemillMemoryIntrinsics = [&]() -> unsigned {
      llvm::DenseSet<llvm::Function *> reachable;
      llvm::SmallVector<llvm::Function *, 32> worklist;

      auto enqueue = [&](llvm::Function *F) {
        if (!F || F->isDeclaration() || !reachable.insert(F).second)
          return;
        worklist.push_back(F);
      };

      for (auto &F : *module) {
        if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root") &&
            !F.hasFnAttribute("omill.internal_output_root")) {
          enqueue(&F);
        }
      }
      if (reachable.empty()) {
        for (auto &F : *module) {
          if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
            enqueue(&F);
        }
      }

      for (size_t i = 0; i < worklist.size(); ++i) {
        llvm::Function *F = worklist[i];
        for (auto &BB : *F) {
          for (auto &I : BB) {
            auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!CB)
              continue;
            auto *callee = CB->getCalledFunction();
            if (!callee || callee->isDeclaration())
              continue;
            enqueue(callee);
          }
        }
      }

      unsigned count = 0;
      for (auto *F : reachable) {
        for (auto &BB : *F) {
          for (auto &I : BB) {
            auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!CB)
              continue;
            auto *callee = CB->getCalledFunction();
            if (!callee)
              continue;
            auto name = callee->getName();
            if (name.starts_with("__remill_read_memory_") ||
                name.starts_with("__remill_write_memory_")) {
              ++count;
            }
          }
        }
      }
      return count;
    };

    if (before_block_calls == 0)
      return;
    const unsigned before_live_memory_intrinsics =
        countReachableLiveRemillMemoryIntrinsics();

    omill::PipelineOptions replay_opts = opts;
    replay_opts.generic_static_devirtualize = false;
    replay_opts.verify_generic_static_devirtualization = false;
    replay_opts.resolve_indirect_targets = false;
    replay_opts.interprocedural_const_prop = false;
    replay_opts.deobfuscate = false;
    replay_opts.recover_abi = false;
    replay_opts.use_block_lifting = false;
    replay_opts.no_abi_mode = true;
    replay_opts.preserve_lifted_semantics = false;

    events.emitInfo("noabi_cleanup_replay_started",
                    "post-main no-abi cleanup replay started",
                    {{"internal_blk_calls_before",
                     static_cast<int64_t>(before_block_calls)},
                     {"reachable_live_remill_memory_intrinsics_before",
                      static_cast<int64_t>(before_live_memory_intrinsics)}});
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    {
      ModulePassManager ReplayMPM;
      omill::buildPipeline(ReplayMPM, replay_opts);
      ReplayMPM.run(*module, MAM);
    }
    const unsigned after_block_calls = countInternalSyntheticBlockCalls();
    const unsigned after_live_memory_intrinsics =
        countReachableLiveRemillMemoryIntrinsics();
    events.emitInfo("noabi_cleanup_replay_completed",
                    "post-main no-abi cleanup replay completed",
                    {{"internal_blk_calls_before",
                      static_cast<int64_t>(before_block_calls)},
                     {"internal_blk_calls_after",
                      static_cast<int64_t>(after_block_calls)},
                     {"reachable_live_remill_memory_intrinsics_before",
                      static_cast<int64_t>(before_live_memory_intrinsics)},
                     {"reachable_live_remill_memory_intrinsics_after",
                      static_cast<int64_t>(after_live_memory_intrinsics)}});
  };

  rerunNoAbiClosedSliceCleanupReplay();

  if (VerifyEach && verifyModule(*module, nullptr)) {
    errs() << "ERROR: module verification failed after main pipeline\n";
    for (const auto &F : *module)
      if (!F.isDeclaration() && verifyFunction(F, nullptr))
        errs() << "  broken function: " << F.getName() << "\n";
    return fail(1, "module verification failed after main pipeline");
  }

  if (DumpIR) {
    std::error_code ec;
    raw_fd_ostream os("after.ll", ec, sys::fs::OF_Text);
    if (!ec) {
      module->print(os, nullptr);
      errs() << "Wrote after.ll\n";
    }
  }

  std::optional<std::string> pre_abi_checkpoint_text;
  const bool enable_debug_sample_native_fixups =
      parseBoolEnv("OMILL_ENABLE_DEBUG_SAMPLE_NATIVE_FIXUPS")
          .value_or(false);

  // ABI recovery
  if (!NoABI) {
    appendDebugMarker("abi:enter");
    if (!opts.generic_static_devirtualize)
      restoreVMHandlerAttrs();
    appendDebugMarker("abi:after_restore_vm_attrs");

    auto repairDeclaredContinuationWrappersInModule =
        [&](llvm::Module &M) -> unsigned {
      auto findNearestDefinedLiftedOrBlockInModule =
          [&](uint64_t target_pc, bool native,
              uint64_t *resolved_pc = nullptr) -> llvm::Function * {
            if (!target_pc)
              return nullptr;

            const uint64_t window = nearbyLiftedEntrySearchWindow();
            llvm::Function *best = nullptr;
            uint64_t best_pc = 0;
            uint64_t best_distance = std::numeric_limits<uint64_t>::max();

            for (auto &F : M) {
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

      unsigned rewritten = 0;
      auto *i64_ty = llvm::Type::getInt64Ty(M.getContext());
      for (auto &F : M) {
        if (F.isDeclaration())
          continue;
        for (auto &BB : F) {
          for (auto &I : llvm::make_early_inc_range(BB)) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI || CI->arg_size() < 3)
              continue;
            auto *callee = CI->getCalledFunction();
            if (!callee || !callee->isDeclaration())
              continue;
            auto name = callee->getName();
            if (!(name.starts_with("blk_") || name.starts_with("block_")) ||
                name.ends_with("_native")) {
              continue;
            }
            auto *pc_ci = llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(1));
            if (!pc_ci)
              continue;

            uint64_t resolved_pc = 0;
            auto *target = findNearestDefinedLiftedOrBlockInModule(
                pc_ci->getZExtValue(), /*native=*/false, &resolved_pc);
            if (!target || target == callee || target->isDeclaration())
              continue;

            if (auto *helper =
                    llvm::dyn_cast<llvm::CallInst>(CI->getArgOperand(2))) {
              if (auto *helper_callee = helper->getCalledFunction();
                  helper_callee &&
                  omill::isDispatchIntrinsicName(helper_callee->getName()) &&
                  helper->arg_size() >= 3) {
                CI->setArgOperand(2, helper->getArgOperand(2));
                if (helper->use_empty())
                  helper->eraseFromParent();
              }
            }

            CI->setCalledFunction(target);
            CI->setArgOperand(1, llvm::ConstantInt::get(i64_ty, resolved_pc));
            ++rewritten;
          }
        }
      }

      for (auto &F : M) {
        if (F.isDeclaration())
          continue;
        for (auto &BB : F) {
          for (auto &I : llvm::make_early_inc_range(BB)) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI || CI->arg_size() < 3)
              continue;
            auto *callee = CI->getCalledFunction();
            if (!callee || !callee->isDeclaration())
              continue;
            auto name = callee->getName();
            if (!omill::isDispatchIntrinsicName(name)) {
              continue;
            }
            auto *pc_ci =
                llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(1));
            if (!pc_ci)
              continue;

            uint64_t resolved_pc = 0;
            auto *target = findNearestDefinedLiftedOrBlockInModule(
                pc_ci->getZExtValue(), /*native=*/false, &resolved_pc);
            if (!target || target->isDeclaration() ||
                target->getFunctionType()->getNumParams() != CI->arg_size()) {
              continue;
            }

            if (auto *helper =
                    llvm::dyn_cast<llvm::CallInst>(CI->getArgOperand(2))) {
              if (auto *helper_callee = helper->getCalledFunction();
                  helper_callee &&
                  omill::isDispatchIntrinsicName(helper_callee->getName()) &&
                  helper->arg_size() >= 3) {
                CI->setArgOperand(2, helper->getArgOperand(2));
                if (helper->use_empty())
                  helper->eraseFromParent();
              }
            }

            CI->setCalledFunction(target);
            CI->setArgOperand(1, llvm::ConstantInt::get(i64_ty, resolved_pc));
            ++rewritten;
          }
        }
      }
      return rewritten;
    };

    {
      unsigned rewritten_live_pre_abi =
          repairDeclaredContinuationWrappersInModule(*module);
      if (rewritten_live_pre_abi != 0) {
        errs() << "[abi-prep] repaired-live-pre-abi-edges="
               << rewritten_live_pre_abi << "\n";
        MAM.invalidate(*module, llvm::PreservedAnalyses::none());
        omill::repairMalformedPHIs(*module);
      }
    }

    if (use_pre_abi_noabi_cleanup) {
      // The pre-ABI generic cleanup reuses the safer no-ABI closed-slice path
      // to flatten the slice before signature recovery. Clear the marker before
      // ABI recovery so ABI-only rewrites do not inherit no-ABI mode.
      module->setModuleFlag(llvm::Module::Override, "omill.no_abi_mode", 0u);
    }
    events.emitInfo("abi_recovery_started", "abi recovery started");
    {
      auto checkpoint_patch_targets = collectAllConstantMissingBlockTargets();
      if (!checkpoint_patch_targets.empty()) {
        llvm::SmallVector<uint64_t, 16> ordered_targets(
            checkpoint_patch_targets.begin(), checkpoint_patch_targets.end());
        llvm::sort(ordered_targets);
        patchConstantMissingBlockCallsToLiftedTargets(
            ordered_targets, "abi_pre_checkpoint_missing_block_patch",
            "patched pre-ABI missing-block calls to lifted targets");
      }
    }


    appendDebugMarker("abi:before_repair_phis");
    omill::repairMalformedPHIs(*module);
    appendDebugMarker("abi:after_repair_phis");
    appendDebugMarker("abi:before_raw_checkpoint_print");
    {
      std::string checkpoint_ir;
      llvm::raw_string_ostream checkpoint_os(checkpoint_ir);
      module->print(checkpoint_os, nullptr);
      checkpoint_os.flush();
      pre_abi_checkpoint_text = std::move(checkpoint_ir);
    }
    appendDebugMarker("abi:after_raw_checkpoint_print");
    {
      std::error_code ec;
      raw_fd_ostream os("before_abi.ll", ec, sys::fs::OF_Text);
      if (!ec) {
        os << *pre_abi_checkpoint_text;
        errs() << "Saved before_abi.ll\n";
      }
    }

    if (!parseBoolEnv("OMILL_SKIP_ABI_PREPATCH_OUTPUT_ROOT_CALLI")
             .value_or(false)) {
      auto output_root_calli_targets = collectConstantCalliTargets(
          [](const llvm::Function &) { return true; });
      if (!output_root_calli_targets.empty()) {
        llvm::SmallVector<uint64_t, 32> ordered_calli_targets(
            output_root_calli_targets.begin(), output_root_calli_targets.end());
        llvm::sort(ordered_calli_targets);
        if (patchConstantCalliTargetsToDirectCalls(
                ordered_calli_targets,
                "abi_prepatch_output_root_calli",
                "patched pre-ABI output-root constant CALLI callsites") > 0) {
          omill::repairMalformedPHIs(*module);
        }
      }
    }


    // ABI recovery relies on fresh module analyses. Reusing analysis state
    // from the pre-ABI main pipeline can miscompile recovered roots, because
    // the module shape changed substantially during lifting/devirtualization.
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    ModulePassManager MPM;
    omill::buildABIRecoveryPipeline(MPM, opts);
    MPM.run(*module, MAM);
    errs() << "ABI recovery complete\n";
    events.emitInfo("abi_recovery_completed", "abi recovery completed");
    dumpModuleIfEnvEnabled(*module, "OMILL_DEBUG_DUMP_AFTER_ABI_CORE",
                           "after_abi_core.ll");
    if (VerifyEach && verifyModule(*module, nullptr)) {
      errs() << "ERROR: module verification failed after ABI recovery\n";
      for (const auto &F : *module)
        if (!F.isDeclaration() && verifyFunction(F, nullptr))
          errs() << "  broken function: " << F.getName() << "\n";
      return fail(1, "module verification failed after ABI recovery");
    }

    // Patch B3 call sites: after ABI recovery created _native wrappers,
    // scan for inttoptr(i64 X to ptr) call targets where @sub_X_native
    // exists, and rewrite them to direct calls.  This resolves constant
    // targets that were discovered during VM discovery or optimization
    // but couldn't be resolved at the time (the target wasn't lifted yet
    // when RewriteLiftedCallsToNative ran).
    if (!parseBoolEnv("OMILL_SKIP_ABI_POSTPATCH_CONSTANT_CALL_PATCH")
             .value_or(false)) {
      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] patchConstantIntToPtrCallsToNative:start\n";
      auto targets_to_patch =
          collectConstantCodeCallTargets([](const llvm::Function &) {
            return true;
          });
      llvm::SmallVector<uint64_t, 32> ordered_targets(targets_to_patch.begin(),
                                                      targets_to_patch.end());
      patchConstantIntToPtrCallsToNative(
          ordered_targets, "abi_patch_callsites",
          "patched inttoptr callsites");
      auto calli_targets_to_patch =
          collectConstantCalliTargets([](const llvm::Function &) {
            return true;
          });
      llvm::SmallVector<uint64_t, 32> ordered_calli_targets(
          calli_targets_to_patch.begin(), calli_targets_to_patch.end());
      patchConstantCalliTargetsToDirectCalls(
          ordered_calli_targets, "abi_patch_calli_callsites",
          "patched constant CALLI callsites");
      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] patchConstantIntToPtrCallsToNative:end\n";
    }

    // Legacy wrapper-oriented ABI post-fixups were retired with the
    // `_native` compatibility pipeline. The direct canonical ABI path keeps
    // the lightweight constant-target patch above and skips the wrapper-only
    // B3/native repair machinery entirely.
#if 0
    auto fixupB3DispatchArgMismatches = [&]() {
      // Fixup B3 direct calls whose resolved _native callee ended up with a
      // different signature. B3 materializes ABI regs plus callee-saved regs;
      // late discovery can also introduce under-passed direct calls once the
      // real _native prototype becomes available. Rebuild the call arguments
      // by matching param State offsets instead of trusting positional order.
      omill::StateFieldMap sfm(*module);
      auto arch_abi =
          omill::ArchABI::get(omill::TargetArch::kX86_64, "windows");

      // Build B3 arg-to-State-offset table (ABI regs then callee-saved).
      llvm::SmallVector<unsigned, 16> b3_arg_offsets;
      for (auto &reg : arch_abi.param_regs) {
        auto f = sfm.fieldByName(reg);
        if (f) b3_arg_offsets.push_back(f->offset);
      }
      for (auto &cs : arch_abi.callee_saved) {
        auto f = sfm.fieldByName(cs);
        if (f) b3_arg_offsets.push_back(f->offset);
      }

      auto *i64_ty = llvm::Type::getInt64Ty(ctx);
      unsigned fixup_count = 0;
      bool debug_public_root_seeds =
          parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
      auto parseHiddenSeedExprMap = [&](llvm::StringRef seed_text) {
        llvm::DenseMap<unsigned, std::string> result;
        llvm::SmallVector<llvm::StringRef, 16> seed_entries;
        seed_text.split(seed_entries, ';', -1, false);
        for (auto entry : seed_entries) {
          entry = entry.trim();
          if (entry.empty())
            continue;
          auto pair = entry.split('=');
          if (pair.first.empty() || pair.second.empty())
            continue;
          auto field = sfm.fieldByName(pair.first.trim());
          if (!field.has_value())
            continue;
          result[field->offset] = pair.second.trim().str();
        }
        return result;
      };

      for (auto &F : *module) {
        if (!F.getName().ends_with("_native")) continue;
        if (debug_public_root_seeds) {
          errs() << "[post-abi-fixup] scanning-function=" << F.getName()
                 << " args=" << F.arg_size()
                 << " decl=" << F.isDeclaration() << "\n";
        }
        const bool is_requested_export_native_root =
            requested_root_is_export && batch_vas.empty() && func_va != 0 &&
            omill::extractEntryVA(F.getName()) == func_va;
        if (debug_public_root_seeds &&
            F.getName().contains("sub_1800020e0_native")) {
          errs() << "[post-abi-fixup] saw " << F.getName()
                 << " requested_export_native_root="
                 << is_requested_export_native_root
                 << " output_root=" << F.hasFnAttribute("omill.output_root")
                 << "\n";
        }
        llvm::SmallVector<int, 16> caller_param_offsets;
        if (auto attr = F.getFnAttribute("omill.param_state_offsets");
            attr.isValid() && attr.isStringAttribute()) {
          llvm::SmallVector<llvm::StringRef, 16> caller_offset_strs;
          attr.getValueAsString().split(caller_offset_strs, ',');
          for (auto &off_str : caller_offset_strs) {
            if (off_str == "stack" || off_str == "xmm") {
              caller_param_offsets.push_back(-1);
              continue;
            }
            unsigned off = 0;
            if (off_str.getAsInteger(10, off))
              caller_param_offsets.push_back(-1);
            else
              caller_param_offsets.push_back(static_cast<int>(off));
          }
        }
        llvm::DenseMap<unsigned, std::string> caller_hidden_seed_exprs;
        if (auto attr = F.getFnAttribute("omill.export_entry_seed_exprs");
            attr.isValid() && attr.isStringAttribute()) {
          caller_hidden_seed_exprs =
              parseHiddenSeedExprMap(attr.getValueAsString());
        }
        auto getCallerParamValue = [&](llvm::IRBuilder<> &Builder,
                                       unsigned arg_index) -> llvm::Value * {
          if (arg_index >= F.arg_size())
            return llvm::ConstantInt::get(i64_ty, 0);
          auto *arg = F.getArg(arg_index);
          if (arg->getType()->isPointerTy()) {
            return Builder.CreatePtrToInt(arg, i64_ty,
                                          arg->getName() + ".i64");
          }
          if (arg->getType()->isIntegerTy(64))
            return arg;
          if (arg->getType()->isIntegerTy())
            return Builder.CreateIntCast(arg, i64_ty, false,
                                         arg->getName() + ".i64");
          return llvm::ConstantInt::get(i64_ty, 0);
        };

        std::function<llvm::Value *(llvm::IRBuilder<> &, llvm::StringRef)>
            evalSeedExpr;
        evalSeedExpr = [&](llvm::IRBuilder<> &Builder,
                           llvm::StringRef text) -> llvm::Value * {
          text = text.trim();
          if (text.starts_with("param(") && text.ends_with(")")) {
            unsigned idx = 0;
            if (!text.drop_front(6).drop_back().getAsInteger(10, idx))
              return getCallerParamValue(Builder, idx);
            return nullptr;
          }
          if (text.starts_with("const(") && text.ends_with(")")) {
            auto body = text.drop_front(6).drop_back();
            uint64_t value = 0;
            if (body.starts_with("0x")) {
              if (!body.drop_front(2).getAsInteger(16, value))
                return llvm::ConstantInt::get(i64_ty, value);
            } else if (!body.getAsInteger(10, value)) {
              return llvm::ConstantInt::get(i64_ty, value);
            }
            return nullptr;
          }

          auto parseCallArgs = [&](llvm::StringRef body)
              -> std::optional<std::pair<llvm::StringRef, llvm::StringRef>> {
            int depth = 0;
            for (size_t idx = 0; idx < body.size(); ++idx) {
              char c = body[idx];
              if (c == '(')
                ++depth;
              else if (c == ')')
                --depth;
              else if (c == ',' && depth == 0) {
                return std::pair(body.take_front(idx),
                                 body.drop_front(idx + 1));
              }
            }
            return std::nullopt;
          };

          auto evalUnary = [&](llvm::StringRef op) -> llvm::Value * {
            if (!text.starts_with(op) || !text.ends_with(")"))
              return nullptr;
            auto arg = text.drop_front(op.size()).drop_back();
            auto *v = evalSeedExpr(Builder, arg);
            if (!v)
              return nullptr;
            return Builder.CreateAnd(v,
                                     llvm::ConstantInt::get(i64_ty,
                                                            0xffffffffull));
          };

          auto evalBinary = [&](llvm::StringRef op,
                                auto &&fn) -> llvm::Value * {
            if (!text.starts_with(op) || !text.ends_with(")"))
              return nullptr;
            auto body = text.drop_front(op.size()).drop_back();
            auto parts = parseCallArgs(body);
            if (!parts)
              return nullptr;
            auto *lhs = evalSeedExpr(Builder, parts->first);
            auto *rhs = evalSeedExpr(Builder, parts->second);
            if (!lhs || !rhs)
              return nullptr;
            return fn(lhs, rhs);
          };

          if (auto *v = evalUnary("zext32("))
            return v;
          if (auto *v = evalBinary("add64(",
                                   [&](llvm::Value *lhs, llvm::Value *rhs) {
                                     return Builder.CreateAdd(lhs, rhs);
                                   }))
            return v;
          if (auto *v = evalBinary("xor64(",
                                   [&](llvm::Value *lhs, llvm::Value *rhs) {
                                     return Builder.CreateXor(lhs, rhs);
                                   }))
            return v;
          if (auto *v = evalBinary("xor32(",
                                   [&](llvm::Value *lhs, llvm::Value *rhs) {
                                     auto *x = Builder.CreateXor(lhs, rhs);
                                     return Builder.CreateAnd(
                                         x,
                                         llvm::ConstantInt::get(i64_ty,
                                                                0xffffffffull));
                                   }))
            return v;
          if (auto *v = evalBinary("and32(",
                                   [&](llvm::Value *lhs, llvm::Value *rhs) {
                                     auto *x = Builder.CreateAnd(lhs, rhs);
                                     return Builder.CreateAnd(
                                         x,
                                         llvm::ConstantInt::get(i64_ty,
                                                                0xffffffffull));
                                   }))
            return v;
          return nullptr;
        };

        if (is_requested_export_native_root && !caller_hidden_seed_exprs.empty() &&
            !F.empty()) {
          llvm::SmallDenseSet<unsigned, 8> rewritten_root_seed_offsets;
          for (auto &I : llvm::make_early_inc_range(F.front())) {
            auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
            if (!SI || !SI->getValueOperand()->getType()->isIntegerTy(64))
              continue;
            auto *gep = llvm::dyn_cast<llvm::GetElementPtrInst>(
                SI->getPointerOperand()->stripPointerCasts());
            if (!gep || gep->getNumIndices() != 1)
              continue;
            auto *idx_ci =
                llvm::dyn_cast<llvm::ConstantInt>(gep->idx_begin()->get());
            if (!idx_ci)
              continue;
            unsigned target_off = static_cast<unsigned>(idx_ci->getZExtValue());
            auto it = caller_hidden_seed_exprs.find(target_off);
            if (it == caller_hidden_seed_exprs.end())
              continue;
            llvm::IRBuilder<> Builder(SI);
            if (auto *seed_value = evalSeedExpr(Builder, it->second)) {
              SI->setOperand(0, seed_value);
              rewritten_root_seed_offsets.insert(target_off);
              ++fixup_count;
              if (debug_public_root_seeds) {
                errs() << "[post-abi-fixup] rewrote-root-seed-store fn="
                       << F.getName() << " offset=" << target_off
                       << " expr=" << it->second << "\n";
              }
            }
          }

          llvm::Instruction *insertion_point = nullptr;
          for (auto &I : F.front()) {
            if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
              if (auto *callee = CB->getCalledFunction();
                  callee && !callee->isDeclaration()) {
                insertion_point = &I;
                break;
              }
            }
          }
          if (!insertion_point)
            insertion_point = F.front().getTerminator();

          llvm::Value *state_ptr = nullptr;
          for (auto &I : F.front()) {
            auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I);
            if (!AI)
              continue;
            if (AI->getAllocatedType()->isStructTy() &&
                AI->getAllocatedType()->getStructName().contains("State")) {
              state_ptr = AI;
              break;
            }
          }

          if (state_ptr && insertion_point) {
            for (const auto &entry : caller_hidden_seed_exprs) {
              unsigned target_off = entry.first;
              if (rewritten_root_seed_offsets.count(target_off))
                continue;
              llvm::IRBuilder<> Builder(insertion_point);
              auto *offset_ptr = Builder.CreateInBoundsGEP(
                  Builder.getInt8Ty(), state_ptr, Builder.getInt64(target_off),
                  F.getName() + ".seed.ptr");
              if (auto *seed_value = evalSeedExpr(Builder, entry.second)) {
                Builder.CreateStore(seed_value, offset_ptr);
                rewritten_root_seed_offsets.insert(target_off);
                ++fixup_count;
                if (debug_public_root_seeds) {
                  errs() << "[post-abi-fixup] inserted-root-seed-store fn="
                         << F.getName() << " offset=" << target_off
                         << " expr=" << entry.second << "\n";
                }
              }
            }
          }
        }
        for (auto &BB : F) {
          for (auto &I : llvm::make_early_inc_range(BB)) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI) continue;
            auto *callee = llvm::dyn_cast<llvm::Function>(
                CI->getCalledOperand()->stripPointerCasts());
            if (!callee || !callee->getName().ends_with("_native"))
              continue;
            if (debug_public_root_seeds) {
              errs() << "[post-abi-fixup] consider-call caller=" << F.getName()
                     << " callee=" << callee->getName()
                     << " call_args=" << CI->arg_size()
                     << " callee_args=" << callee->arg_size() << "\n";
            }
            if (callee->hasFnAttribute("omill.vm_handler") &&
                (F.hasFnAttribute("omill.vm_wrapper") ||
                 F.getFnAttribute("omill.vm_outlined_virtual_call").isValid()))
              continue;
            auto callHasSuspiciousSameArityOperands = [&]() {
              for (unsigned i = 0; i < CI->arg_size(); ++i) {
                auto *arg = CI->getArgOperand(i);
                if (llvm::isa<llvm::PoisonValue>(arg) ||
                    llvm::isa<llvm::UndefValue>(arg))
                  return true;
              }
              return false;
            };
            bool allow_same_arity_rewrite =
                (!caller_hidden_seed_exprs.empty() &&
                 is_requested_export_native_root) ||
                callHasSuspiciousSameArityOperands();
            if (debug_public_root_seeds &&
                is_requested_export_native_root &&
                callee->getName().ends_with("_native")) {
              errs() << "[post-abi-fixup] caller=" << F.getName()
                     << " callee=" << callee->getName()
                     << " same_arity=" << (CI->arg_size() == callee->arg_size())
                     << " allow_same_arity=" << allow_same_arity_rewrite
                     << " caller_hidden_seeds="
                     << caller_hidden_seed_exprs.size() << "\n";
            }
            if (CI->arg_size() == callee->arg_size() &&
                !allow_same_arity_rewrite)
              continue;

            auto attr =
                callee->getFnAttribute("omill.param_state_offsets");
            if (!attr.isValid() || !attr.isStringAttribute()) continue;

            llvm::SmallVector<llvm::StringRef, 16> callee_offset_strs;
            attr.getValueAsString().split(callee_offset_strs, ',');
            if (callee_offset_strs.size() != callee->arg_size()) continue;

            auto defaultMissingI64Arg = [&]() -> llvm::Value * {
              // Late ABI call repair should fail conservatively. Using poison
              // here turns unmapped helper params into immediate UB in the
              // final recovered artifact, which is worse than preserving a
              // deterministic zero/default state.
              return llvm::ConstantInt::get(i64_ty, 0);
            };

            // Match each callee param to a B3 arg by State offset.
            llvm::SmallVector<llvm::Value *, 16> new_args;
            bool ok = true;
            llvm::IRBuilder<> Builder(CI);
            for (auto &off_str : callee_offset_strs) {
              if (off_str == "stack" || off_str == "xmm") {
                if (new_args.size() < CI->arg_size())
                  new_args.push_back(CI->getArgOperand(new_args.size()));
                else
                  new_args.push_back(defaultMissingI64Arg());
                continue;
              }
              unsigned target_off;
              if (off_str.getAsInteger(10, target_off)) {
                ok = false;
                break;
              }
              bool found = false;
              if (is_requested_export_native_root) {
                for (unsigned i = 0;
                     i < caller_param_offsets.size() && i < F.arg_size(); ++i) {
                  if (caller_param_offsets[i] ==
                      static_cast<int>(target_off)) {
                    new_args.push_back(F.getArg(i));
                    found = true;
                    break;
                  }
                }
                if (auto it = caller_hidden_seed_exprs.find(target_off);
                    it != caller_hidden_seed_exprs.end()) {
                  if (auto *seed_value = evalSeedExpr(Builder, it->second)) {
                    new_args.push_back(seed_value);
                    found = true;
                  }
                }
              } else {
                for (unsigned i = 0;
                     i < b3_arg_offsets.size() && i < CI->arg_size(); ++i) {
                  if (b3_arg_offsets[i] == target_off) {
                    new_args.push_back(CI->getArgOperand(i));
                    found = true;
                    break;
                  }
                }
                if (!found) {
                  for (unsigned i = 0;
                       i < caller_param_offsets.size() && i < F.arg_size();
                       ++i) {
                    if (caller_param_offsets[i] ==
                        static_cast<int>(target_off)) {
                      new_args.push_back(F.getArg(i));
                      found = true;
                      break;
                    }
                  }
                }
                if (!found) {
                  if (auto it = caller_hidden_seed_exprs.find(target_off);
                      it != caller_hidden_seed_exprs.end()) {
                    if (auto *seed_value = evalSeedExpr(Builder, it->second)) {
                      new_args.push_back(seed_value);
                      found = true;
                    }
                  }
                }
              }
              if (!found) {
                if (new_args.size() < CI->arg_size())
                  new_args.push_back(CI->getArgOperand(new_args.size()));
                else
                  new_args.push_back(defaultMissingI64Arg());
              }
            }
            if (!ok) continue;

            bool changed_args = (CI->arg_size() != new_args.size());
            if (!changed_args && CI->arg_size() == new_args.size()) {
              for (unsigned i = 0; i < CI->arg_size(); ++i) {
                if (new_args[i] != CI->getArgOperand(i)) {
                  changed_args = true;
                  break;
                }
              }
            }
            if (!changed_args)
              continue;

            if (debug_public_root_seeds &&
                is_requested_export_native_root) {
              errs() << "[post-abi-fixup] rewriting caller=" << F.getName()
                     << " callee=" << callee->getName()
                     << " args=" << CI->arg_size() << "\n";
            }

            for (unsigned i = 0; i < new_args.size() && i < CI->arg_size(); ++i) {
              auto *current = CI->getArgOperand(i);
              auto *replacement = new_args[i];
              if (replacement->getType() == current->getType())
                continue;
              if (replacement->getType()->isIntegerTy() &&
                  current->getType()->isIntegerTy()) {
                new_args[i] = Builder.CreateIntCast(
                    replacement, current->getType(), false,
                    callee->getName() + ".arg.cast");
              } else if (replacement->getType()->isPointerTy() &&
                         current->getType()->isIntegerTy()) {
                new_args[i] = Builder.CreatePtrToInt(
                    replacement, current->getType(),
                    callee->getName() + ".arg.pti");
              } else if (replacement->getType()->isIntegerTy() &&
                         current->getType()->isPointerTy()) {
                new_args[i] = Builder.CreateIntToPtr(
                    replacement, current->getType(),
                    callee->getName() + ".arg.itp");
              }
            }

            auto *new_call = llvm::CallInst::Create(
                callee->getFunctionType(), callee, new_args,
                callee->getReturnType()->isVoidTy() ? "" : CI->getName(),
                CI->getIterator());
            new_call->setCallingConv(CI->getCallingConv());
            new_call->setAttributes(CI->getAttributes());
            // Handle return type mismatch (B3 returns i64, callee may
            // return struct).
            if (!CI->use_empty()) {
              if (CI->getType() == new_call->getType()) {
                CI->replaceAllUsesWith(new_call);
              } else if (llvm::isa<llvm::StructType>(
                             new_call->getType())) {
                auto *ev = llvm::ExtractValueInst::Create(
                    new_call, {0}, "ret.primary",
                    std::next(new_call->getIterator()));
                CI->replaceAllUsesWith(ev);
              } else {
                CI->replaceAllUsesWith(
                    llvm::PoisonValue::get(CI->getType()));
              }
            }
            CI->eraseFromParent();
            ++fixup_count;
          }
        }
      }
      if (fixup_count > 0)
        errs() << "Fixed " << fixup_count
               << " B3 dispatch calls with mismatched arg counts\n";
    };
    if (!parseBoolEnv("OMILL_SKIP_ABI_POSTPATCH_B3_FIXUP").value_or(false)) {
      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] fixupB3DispatchArgMismatches:start\n";
      fixupB3DispatchArgMismatches();
      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] fixupB3DispatchArgMismatches:end\n";
    }
    auto repairSyntheticStackTopStateArgs = [&]() {
      auto syntheticStateArgIndex = [&](llvm::Function &Callee)
          -> std::optional<unsigned> {
        for (unsigned i = 0; i < Callee.arg_size(); ++i) {
          auto *arg = Callee.getArg(i);
          for (auto *U : arg->users()) {
            auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(U);
            if (!BO || BO->getOpcode() != llvm::Instruction::Add)
              continue;
            auto *lhs_ci =
                llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0));
            auto *rhs_ci =
                llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
            if ((lhs_ci && lhs_ci->getZExtValue() == 9116) ||
                (rhs_ci && rhs_ci->getZExtValue() == 9116)) {
              return i;
            }
          }
        }
        return std::nullopt;
      };

      auto rebuildSyntheticStackBase = [&](llvm::Value *V,
                                           llvm::IRBuilder<> &Builder)
          -> llvm::Value * {
        auto *PTI = llvm::dyn_cast<llvm::PtrToIntInst>(V);
        if (!PTI)
          return nullptr;
        auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(
            PTI->getPointerOperand()->stripPointerCasts());
        if (!GEP || GEP->getNumOperands() < 2)
          return nullptr;
        auto *idx = llvm::dyn_cast<llvm::ConstantInt>(GEP->getOperand(1));
        if (!idx || idx->getZExtValue() < 65504)
          return nullptr;
        auto *base_ptr = GEP->getPointerOperand();
        return Builder.CreatePtrToInt(base_ptr, V->getType(),
                                      "synthetic.stack.base");
      };

      for (auto &F : *module) {
        if (F.isDeclaration() || !F.getName().ends_with("_native"))
          continue;
        for (auto &BB : F) {
          for (auto &I : llvm::make_early_inc_range(BB)) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            auto *Callee = CI ? CI->getCalledFunction() : nullptr;
            if (!Callee || Callee->isDeclaration() ||
                !Callee->getName().ends_with("_native")) {
              continue;
            }
            if (Callee == &F || Callee->getName() == F.getName())
              continue;
            auto state_arg_index = syntheticStateArgIndex(*Callee);
            if (!state_arg_index || *state_arg_index >= CI->arg_size())
              continue;
            llvm::IRBuilder<> Builder(CI);
            auto *replacement = rebuildSyntheticStackBase(
                CI->getArgOperand(*state_arg_index), Builder);
            if (!replacement)
              continue;
            CI->setArgOperand(*state_arg_index, replacement);
          }
        }
      }
    };

    auto materializeZeroedSyntheticStateArgs = [&]() {
      auto syntheticStateArgIndex = [&](llvm::Function &Callee)
          -> std::optional<unsigned> {
        for (unsigned i = 0; i < Callee.arg_size(); ++i) {
          auto *arg = Callee.getArg(i);
          for (auto *U : arg->users()) {
            auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(U);
            if (!BO || BO->getOpcode() != llvm::Instruction::Add)
              continue;
            auto *lhs_ci =
                llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0));
            auto *rhs_ci =
                llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
            if ((lhs_ci && lhs_ci->getZExtValue() == 9116) ||
                (rhs_ci && rhs_ci->getZExtValue() == 9116)) {
              return i;
            }
          }
        }
        return std::nullopt;
      };

      constexpr uint64_t kSyntheticStateBytes = 69632;
      auto *stack_ty = llvm::ArrayType::get(
          llvm::Type::getInt8Ty(ctx), kSyntheticStateBytes);

      for (auto &F : *module) {
        if (F.isDeclaration() || !F.getName().ends_with("_native") ||
            F.empty()) {
          continue;
        }
        auto &entry = F.getEntryBlock();
        llvm::Instruction *entry_ip = &*entry.getFirstInsertionPt();
        for (auto &BB : F) {
          for (auto &I : llvm::make_early_inc_range(BB)) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            auto *Callee = CI ? CI->getCalledFunction() : nullptr;
            if (!Callee || Callee->isDeclaration() ||
                !Callee->getName().ends_with("_native")) {
              continue;
            }
            if (Callee == &F || Callee->getName() == F.getName())
              continue;
            auto state_arg_index = syntheticStateArgIndex(*Callee);
            if (!state_arg_index || *state_arg_index >= CI->arg_size())
              continue;
            auto *zero_ci =
                llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(*state_arg_index));
            if (!zero_ci || !zero_ci->isZero())
              continue;

            llvm::IRBuilder<> EntryBuilder(entry_ip);
            auto *alloca = EntryBuilder.CreateAlloca(
                stack_ty, nullptr,
                Callee->getName() + ".synthetic_state");

            llvm::IRBuilder<> Builder(CI);
            Builder.CreateMemSet(alloca, Builder.getInt8(0),
                                 kSyntheticStateBytes, llvm::MaybeAlign(16));
            auto *replacement = Builder.CreatePtrToInt(
                alloca, CI->getArgOperand(*state_arg_index)->getType(),
                Callee->getName() + ".synthetic_state.i64");
            CI->setArgOperand(*state_arg_index, replacement);
          }
        }
      }
    };

    rerunLateNativeArgRepair = [&]() {
      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] fixupB3DispatchArgMismatches:late-rerun:start\n";
      fixupB3DispatchArgMismatches();
      repairSyntheticStackTopStateArgs();
      materializeZeroedSyntheticStateArgs();
      omill::repairMalformedPHIs(*module);
      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] fixupB3DispatchArgMismatches:late-rerun:end\n";
    };

    {
      rerunFocusedNativeHelperControlFlowRecovery = [&]() {
      auto in_output_root_native_closure = [&](llvm::Function &Candidate) {
        if (Candidate.isDeclaration() || !Candidate.getName().ends_with("_native"))
          return false;

        llvm::SmallVector<llvm::Function *, 32> worklist;
        llvm::SmallPtrSet<llvm::Function *, 32> seen;
        for (auto &F : *module) {
          if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root") ||
              !F.getName().ends_with("_native")) {
            continue;
          }
          if (seen.insert(&F).second)
            worklist.push_back(&F);
        }

        while (!worklist.empty()) {
          llvm::Function *Current = worklist.pop_back_val();
          if (Current == &Candidate)
            return true;
          for (auto &BB : *Current) {
            for (auto &I : BB) {
              auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
              if (!CB)
                continue;
              auto *Callee = CB->getCalledFunction();
              if (!Callee || Callee->isDeclaration() ||
                  !Callee->getName().ends_with("_native")) {
                continue;
              }
              if (seen.insert(Callee).second)
                worklist.push_back(Callee);
            }
          }
        }
        return false;
      };

      auto needs_recovery = [&](llvm::Function &F) {
        if (!in_output_root_native_closure(F))
          return false;
        for (auto &BB : F) {
          for (auto &I : BB) {
            auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!CB)
              continue;
            auto *Callee = CB->getCalledFunction();
            if (!Callee)
              continue;
            auto Name = Callee->getName();
            if (omill::isDispatchIntrinsicName(Name) ||
                Name == "__remill_function_return") {
              return true;
            }
          }
        }
        return false;
      };

      bool has_candidates = false;
      for (auto &F : *module) {
        if (needs_recovery(F)) {
          has_candidates = true;
          break;
        }
      }
      if (!has_candidates)
        return;

      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] focused-native-cf-recovery:start\n";

      llvm::ModulePassManager FocusedMPM;
      FocusedMPM.addPass(
          llvm::RequireAnalysisPass<omill::LiftedFunctionAnalysis,
                                    llvm::Module>());
      llvm::FunctionPassManager FPM;
      FPM.addPass(
          omill::LowerRemillIntrinsicsPass(omill::LowerCategories::Phase3));
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(omill::JumpTableConcretizerPass());
      FPM.addPass(omill::ResolveAndLowerControlFlowPass(
          omill::ResolvePhases::RecoverTables |
          omill::ResolvePhases::SymbolicSolve |
          omill::ResolvePhases::ResolveTargets));
      FPM.addPass(omill::LowerRemillIntrinsicsPass(
          omill::LowerCategories::ResolvedDispatch));
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::ADCEPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      FocusedMPM.addPass(
          llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
      FocusedMPM.run(*module, MAM);

      auto canonicalizeDispatchDecl = [&](llvm::StringRef dispatch_name,
                                          llvm::StringRef remill_name) {
        auto *dispatch = module->getFunction(dispatch_name);
        auto *remill = module->getFunction(remill_name);
        if (!dispatch || !remill)
          return;
        auto *expected_ty = remill->getFunctionType();
        if (dispatch->getFunctionType() == expected_ty)
          return;

        auto *replacement = llvm::Function::Create(
            expected_ty, dispatch->getLinkage(), dispatch_name + ".fixed",
            module.get());
        replacement->copyAttributesFrom(dispatch);

        llvm::SmallVector<llvm::CallBase *, 16> calls;
        for (auto *U : dispatch->users()) {
          if (auto *CB = llvm::dyn_cast<llvm::CallBase>(U))
            calls.push_back(CB);
        }

        for (auto *CB : calls) {
          llvm::IRBuilder<> Builder(CB);
          llvm::SmallVector<llvm::Value *, 8> args;
          args.reserve(CB->arg_size());
          for (auto &Arg : CB->args())
            args.push_back(Arg.get());
          auto *new_call = Builder.CreateCall(expected_ty, replacement, args);
          new_call->setCallingConv(CB->getCallingConv());
          new_call->setAttributes(CB->getAttributes());
          if (!CB->use_empty()) {
            if (new_call->getType() == CB->getType()) {
              CB->replaceAllUsesWith(new_call);
            } else if (!CB->getType()->isVoidTy()) {
              CB->replaceAllUsesWith(
                  llvm::PoisonValue::get(CB->getType()));
            }
          }
          CB->eraseFromParent();
        }

        dispatch->eraseFromParent();
        replacement->setName(dispatch_name);
      };

      canonicalizeDispatchDecl("__omill_dispatch_jump", "__remill_jump");
      canonicalizeDispatchDecl("__omill_dispatch_call", "__remill_function_call");

      auto rewriteVoidNativeJumpTableDispatches = [&]() {
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
          if (F.isDeclaration() || !F.getName().ends_with("_native") ||
              !in_output_root_native_closure(F)) {
            continue;
          }
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

        auto findLocalNativeTarget = [&](uint64_t case_pc)
            -> llvm::Function * {
          if (auto it = local_native_targets.find(case_pc);
              it != local_native_targets.end()) {
            return it->second;
          }
          llvm::Function *best = nullptr;
          uint64_t best_distance = UINT64_MAX;
          for (auto &[target_pc, target_fn] : local_native_targets) {
            uint64_t distance =
                target_pc > case_pc ? (target_pc - case_pc) : (case_pc - target_pc);
            if (distance > 0x80)
              continue;
            if (distance < best_distance) {
              best_distance = distance;
              best = target_fn;
            }
          }
          return best;
        };

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
        for (auto &F : *module) {
          if (F.isDeclaration() || !F.getName().ends_with("_native") ||
              !in_output_root_native_closure(F) || !F.getReturnType()->isVoidTy()) {
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
          auto *target_pc = dispatch_call->getArgOperand(1);
          auto *after_block =
              switch_block->splitBasicBlock(dispatch_call->getIterator(),
                                           "resolved.dispatch.dynamic");
          switch_block->getTerminator()->eraseFromParent();
          dispatch_call->eraseFromParent();

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
              Builder.CreateSwitch(target_pc, after_block, local_case_pcs.size());

          auto buildStateArgsForCallee =
              [&](llvm::IRBuilder<> &CaseBuilder, llvm::Function &Callee) {
                llvm::SmallVector<llvm::Value *, 16> args;
                auto attr = Callee.getFnAttribute("omill.param_state_offsets");
                if (!attr.isValid() || !attr.isStringAttribute()) {
                  if (Callee.arg_size() >= 1)
                    args.push_back(state2232);
                  if (Callee.arg_size() >= 2)
                    args.push_back(state2280);
                  if (Callee.arg_size() >= 3)
                    args.push_back(state2328);
                  if (Callee.arg_size() >= 4)
                    args.push_back(state2440);
                  while (args.size() < Callee.arg_size())
                    args.push_back(llvm::ConstantInt::get(Builder.getInt64Ty(), 0));
                  return args;
                }

                llvm::SmallVector<llvm::StringRef, 16> offset_strs;
                attr.getValueAsString().split(offset_strs, ',');
                if (offset_strs.size() != Callee.arg_size()) {
                  while (args.size() < Callee.arg_size())
                    args.push_back(llvm::ConstantInt::get(Builder.getInt64Ty(), 0));
                  return args;
                }

                for (auto token : offset_strs) {
                  token = token.trim();
                  if (token == "stack" || token == "xmm") {
                    args.push_back(llvm::ConstantInt::get(Builder.getInt64Ty(), 0));
                    continue;
                  }
                  unsigned offset = 0;
                  if (token.getAsInteger(10, offset)) {
                    args.push_back(llvm::ConstantInt::get(Builder.getInt64Ty(), 0));
                    continue;
                  }
                  auto *state_ptr = findStateOffsetPtr(F, offset);
                  if (!state_ptr) {
                    args.push_back(llvm::ConstantInt::get(Builder.getInt64Ty(), 0));
                    continue;
                  }
                  args.push_back(CaseBuilder.CreateLoad(Builder.getInt64Ty(),
                                                        state_ptr,
                                                        "resolved.arg." + token));
                }
                return args;
              };

          for (uint64_t case_pc : local_case_pcs) {
            if (case_pc == 0)
              continue;
            if (auto *target_fn = findLocalNativeTarget(case_pc)) {
              auto *case_block = llvm::BasicBlock::Create(
                  ctx, "resolved.case." + llvm::utohexstr(case_pc), &F,
                  after_block);
              llvm::IRBuilder<> case_builder(case_block);
              auto case_args = buildStateArgsForCallee(case_builder, *target_fn);
              auto *case_call = case_builder.CreateCall(
                  target_fn->getFunctionType(), target_fn, case_args);
              case_call->setCallingConv(target_fn->getCallingConv());
              if (auto *CaseRetST =
                      llvm::dyn_cast<llvm::StructType>(target_fn->getReturnType());
                  CaseRetST && CaseRetST->getNumElements() == 8) {
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
              }
              case_builder.CreateBr(after_block);
              switch_inst->addCase(case_builder.getInt64(case_pc), case_block);
            } else {
              auto *loop_block = llvm::BasicBlock::Create(
                  ctx, "resolved.selfloop." + llvm::utohexstr(case_pc), &F,
                  after_block);
              llvm::IRBuilder<> loop_builder(loop_block);
              loop_builder.CreateBr(loop_block);
              switch_inst->addCase(loop_builder.getInt64(case_pc), loop_block);
            }
          }

          ++rewrite_count;
        }

        if (rewrite_count > 0 &&
            parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false)) {
          errs() << "[abi-post] void-native-jumptable-rewrite count="
                 << rewrite_count << "\n";
        }
      };
      rewriteVoidNativeJumpTableDispatches();

      if (std::getenv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS") != nullptr) {
        std::error_code ec;
        llvm::raw_fd_ostream os("after_focused_native_cf_recovery.ll", ec,
                                llvm::sys::fs::OF_Text);
        if (!ec)
          module->print(os, nullptr);
      }

      if (parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false))
        errs() << "[abi-post] focused-native-cf-recovery:end\n";
      };
      rerunFocusedNativeHelperControlFlowRecovery();
    }

    dumpModuleIfEnvEnabled(*module, "OMILL_DEBUG_DUMP_AFTER_ABI_POSTPATCH",
                           "after_abi_postpatch.ll");
    if (std::getenv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS") != nullptr) {
      std::error_code ec;
      llvm::raw_fd_ostream os("after_b3_fixup.ll", ec, llvm::sys::fs::OF_Text);
      if (!ec)
        module->print(os, nullptr);
    }

    if (enable_debug_sample_native_fixups) {
      if (auto *flattened_root = module->getFunction("sub_1800020e0_native");
          flattened_root && !flattened_root->isDeclaration()) {
        if (auto *flattened_case301 =
                module->getFunction("sub_180002301_native");
            flattened_case301 && !flattened_case301->isDeclaration()) {
          flattened_case301->removeFnAttr(llvm::Attribute::AlwaysInline);
          flattened_case301->addFnAttr(llvm::Attribute::NoInline);
        }
      }
    }

#endif
    auto shouldRunPostABIDeobfOn = [&](llvm::Function &F) {
      if (F.isDeclaration())
        return false;
      return F.hasFnAttribute("omill.output_root") ||
             F.hasFnAttribute("omill.closed_root_slice");
    };

    // Post-ABI deobfuscation runs directly on the canonical recovered roots.
    if (Deobfuscate || ResolveTargets) {
      llvm::FunctionPassManager FPM;
      omill::buildDeobfuscationPipeline(FPM, opts);
      for (auto &F : *module) {
        if (!shouldRunPostABIDeobfOn(F))
          continue;
        auto &FAM =
            MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(*module)
                .getManager();
        auto PA = FPM.run(F, FAM);
        if (!PA.areAllPreserved())
          FAM.invalidate(F, PA);
      }
      errs() << "Post-ABI deobfuscation complete\n";
      events.emitInfo("post_abi_deobf_completed", "post-ABI deobfuscation completed");
      dumpModuleIfEnvEnabled(*module, "OMILL_DEBUG_DUMP_AFTER_POST_ABI_DEOBF",
                             "after_post_abi_deobf.ll");
      rerunFocusedNativeHelperControlFlowRecovery();
    }

    rerunLateOutputRootTargetPipeline();

    [[maybe_unused]] auto patchTraceNativeWrapperCalls = [&]() {
      if (!vm_mode || !vm_graph || vm_graph->empty())
        return;

      auto parseHashAttr = [&](llvm::Function &F,
                               llvm::StringRef attr_name)
          -> std::optional<uint64_t> {
        auto attr = F.getFnAttribute(attr_name);
        if (!attr.isValid() || !attr.isStringAttribute())
          return std::nullopt;
        uint64_t value = 0;
        auto text = attr.getValueAsString();
        if (text.getAsInteger(16, value))
          return std::nullopt;
        return value;
      };

      auto parseNativeVA = [&](llvm::Function &F) -> std::optional<uint64_t> {
        if (!F.getName().ends_with("_native"))
          return std::nullopt;
        auto base_name = F.getName().drop_back(strlen("_native"));
        if (!base_name.starts_with("sub_"))
          return std::nullopt;
        uint64_t va = 0;
        if (base_name.drop_front(4).getAsInteger(16, va) || va == 0)
          return std::nullopt;
        return va;
      };

      unsigned patched = 0;
      unsigned skipped = 0;
      for (auto &F : *module) {
        if (F.isDeclaration() || !F.hasFnAttribute("omill.vm_wrapper"))
          continue;
        auto wrapper_va = parseNativeVA(F);
        if (!wrapper_va)
          continue;

        std::optional<uint64_t> seed_hash =
            parseHashAttr(F, "omill.vm_trace_in_hash");
        if (!seed_hash) {
          auto records = vm_graph->getTraceRecords(*wrapper_va);
          if (records.size() == 1)
            seed_hash = records.front().incoming_hash;
        }
        if (!seed_hash) {
          errs() << "Trace-native patch: no seed hash for " << F.getName()
                 << "\n";
          continue;
        }

        auto flat = vm_graph->followFlatTrace(*wrapper_va, *seed_hash);
        llvm::SmallVector<uint64_t, 4> trace_native_targets;
        for (const auto &record : flat.records) {
          if (record.native_target_va != 0)
            trace_native_targets.push_back(record.native_target_va);
        }
        if (trace_native_targets.empty()) {
          errs() << "Trace-native patch: wrapper " << F.getName()
                 << " seed=0x" << Twine::utohexstr(*seed_hash)
                 << " flat_records=" << flat.records.size()
                 << " stop_reason=" << static_cast<unsigned>(flat.stop_reason)
                 << " produced no native targets\n";
          continue;
        }

        llvm::SmallVector<llvm::CallInst *, 4> indirect_calls;
        for (auto &BB : F) {
          for (auto &I : BB) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI)
              continue;
            if (llvm::isa<llvm::Function>(
                    CI->getCalledOperand()->stripPointerCasts()))
              continue;
            indirect_calls.push_back(CI);
          }
        }
        if (indirect_calls.empty()) {
          errs() << "Trace-native patch: wrapper " << F.getName()
                 << " has no indirect calls to rewrite\n";
          continue;
        }
        if (indirect_calls.size() != trace_native_targets.size()) {
          errs() << "Trace-native patch skipped for " << F.getName()
                 << " (indirect_calls=" << indirect_calls.size()
                 << ", trace_native_targets=" << trace_native_targets.size()
                 << ")\n";
          ++skipped;
          continue;
        }

        for (unsigned i = 0; i < indirect_calls.size(); ++i) {
          uint64_t target_va = trace_native_targets[i];
          std::string target_name =
              "sub_" + llvm::Twine::utohexstr(target_va).str() + "_native";
          auto *target_fn = module->getFunction(target_name);
          if (!target_fn || target_fn->isDeclaration()) {
            errs() << "Trace-native patch missing target " << target_name
                   << " for wrapper " << F.getName() << "\n";
            break;
          }

          auto *CI = indirect_calls[i];
          llvm::SmallVector<llvm::Value *, 16> args;
          for (auto &Arg : CI->args())
            args.push_back(Arg.get());

          llvm::IRBuilder<> Builder(CI);
          llvm::Value *direct_callee = target_fn;
          if (target_fn->getType() != CI->getCalledOperand()->getType()) {
            direct_callee = Builder.CreateBitCast(
                target_fn, CI->getCalledOperand()->getType(),
                target_name + ".cast");
          }
          auto *new_call = Builder.CreateCall(
              CI->getFunctionType(), direct_callee, args, CI->getName());
          new_call->setCallingConv(CI->getCallingConv());
          new_call->setAttributes(CI->getAttributes());
          if (!CI->use_empty())
            CI->replaceAllUsesWith(new_call);
          CI->eraseFromParent();
          ++patched;
        }
      }

      if (patched > 0) {
        errs() << "Patched " << patched
               << " VM wrapper indirect call(s) from imported trace\n";
        runPostPatchCleanup("trace_native_wrapper_calls");
      } else if (skipped > 0) {
        errs() << "Trace-native wrapper patch skipped " << skipped
               << " wrapper(s)\n";
      }
    };
    // Legacy wrapper cloning/patching was removed with the `_native`
    // compatibility pipeline.
  }

  // Late target discovery: after ABI recovery folds MBA chains (via
  // EliminateStateStruct + RecoverStackFrame + SROA + GVN), scan for
  // constant inttoptr call targets that point to unlifted code addresses.
  // Lift them directly into the current module/session, rerun the pipeline
  // + ABI on just the newly-lifted slice, and keep cleanup of Remill
  // infrastructure deferred until iterative discovery is fully closed.
  const bool run_post_abi_late_discovery =
      opts.resolve_indirect_targets && !NoABI &&
      !(opts.use_block_lifting && !opts.vm_devirtualize);
  if (run_post_abi_late_discovery) {
    llvm::DenseMap<uint64_t, uint64_t> nested_vm_helper_targets;
    llvm::DenseMap<uint64_t, uint64_t> nested_vm_helper_deltas;
    struct NestedHelperCallsite {
      std::string caller_name;
      std::string helper_name;
      unsigned ordinal = 0;
      std::optional<uint64_t> hash;
    };
    struct HashResolvedCall {
      std::string caller_name;
      std::string helper_name;
      unsigned ordinal = 0;
      uint64_t hash = 0;
      uint64_t target_va = 0;
    };
    // --- Virtual callee registry (formal, first-class) ---
    // VirtualCalleeRecord is the canonical data structure.  We keep a
    // separate Function* cache because VirtualCalleeRecord is serializable
    // (no LLVM pointers) while the Function* is session-local.
    llvm::StringMap<omill::VirtualCalleeRecord> outlined_virtual_callee_records;
    llvm::StringMap<llvm::Function *> outlined_virtual_callee_fns;
    bool verbose_vm_outlined = (std::getenv("OMILL_VM_VERBOSE") != nullptr);

    auto ensureOutlinedVirtualCallee = [&](llvm::Function *base_fn,
                                           const std::string &clone_name,
                                           llvm::StringRef caller_name,
                                           std::optional<uint64_t> hash,
                                           llvm::StringRef kind,
                                           unsigned round_index,
                                           uint64_t handler_va = 0,
                                           std::optional<uint64_t> trace_hash = std::nullopt)
        -> std::pair<llvm::Function *, bool> {
      if (!base_fn || base_fn->isDeclaration())
        return {nullptr, false};

      auto fn_it = outlined_virtual_callee_fns.find(clone_name);
      if (fn_it != outlined_virtual_callee_fns.end()) {
        if (fn_it->second)
          return {fn_it->second, false};
      }

      llvm::Function *clone = base_fn->getParent()->getFunction(clone_name);
      bool created = false;
      if (!clone) {
        llvm::ValueToValueMapTy VMap;
        clone = llvm::CloneFunction(base_fn, VMap);
        clone->setName(clone_name);
        created = true;
      }

      // Boundary markers — these are the minimal attrs that downstream passes
      // check for inlining/outlining decisions.  Detail data lives in the
      // registry metadata, not duplicated as attrs.
      clone->setLinkage(llvm::GlobalValue::InternalLinkage);
      clone->addFnAttr(llvm::Attribute::NoInline);
      clone->addFnAttr("omill.vm_outlined_virtual_call", "1");
      // Trace linkage attrs — propagated through ABI wrapper generation by
      // RecoverFunctionSignatures so the registry can reconstruct trace keys
      // from the _native function after the pipeline.
      if (handler_va != 0)
        clone->addFnAttr("omill.vm_handler_va",
                         llvm::utohexstr(handler_va));
      if (trace_hash)
        clone->addFnAttr("omill.vm_trace_hash",
                         llvm::utohexstr(*trace_hash));
      if (hash)
        clone->addFnAttr("omill.vm_helper_hash", llvm::utohexstr(*hash));
      else
        clone->removeFnAttr("omill.vm_helper_hash");

      outlined_virtual_callee_fns[clone_name] = clone;

      auto &record = outlined_virtual_callee_records[clone_name];
      if (record.clone_name.empty()) {
        record.clone_name = clone_name;
        record.base_name = base_fn->getName().str();
        record.caller_name = caller_name.str();
        record.kind = kind.str();
        record.hash = hash;
        record.first_round = round_index;
        record.handler_va = handler_va;
        record.trace_hash = trace_hash;
      }

      if (created && verbose_vm_outlined) {
        errs() << "Outlined virtual callee " << clone_name
               << " kind=" << kind
               << " base=" << base_fn->getName();
        if (hash)
          errs() << " hash=0x" << Twine::utohexstr(*hash);
        if (handler_va != 0)
          errs() << " handler_va=0x" << Twine::utohexstr(handler_va);
        if (trace_hash)
          errs() << " trace_hash=0x" << Twine::utohexstr(*trace_hash);
        errs() << " caller=" << caller_name
               << " round=" << round_index << "\n";
      }

      return {clone, created};
    };


    auto syncOutlinedVirtualCalleeRegistry = [&]() {
      std::vector<omill::VirtualCalleeRecord> records;
      records.reserve(outlined_virtual_callee_records.size());
      for (const auto &entry : outlined_virtual_callee_records) {
        records.push_back(entry.getValue());
      }
      omill::setVirtualCalleeRegistryMetadata(*module, records);
    };


    auto collectNestedVMHelperTargets = [&]() {
      nested_vm_helper_targets.clear();
      nested_vm_helper_deltas.clear();
      if (!vm_mode || RawBinary || has_external_vm_trace || true)
        return;

      auto followJmpThunks = [&](uint64_t va) {
        uint64_t resolved = va;
        for (unsigned hop = 0; hop < 4; ++hop) {
          uint8_t thunk_buf[16];
          if (!pe.memory_map.read(resolved, thunk_buf, sizeof(thunk_buf)))
            break;
          if (thunk_buf[0] == 0xE9) {
            int32_t rel = 0;
            std::memcpy(&rel, &thunk_buf[1], 4);
            resolved = resolved + 5 + static_cast<int64_t>(rel);
            continue;
          }
          if (thunk_buf[0] == 0xEB) {
            int8_t rel = static_cast<int8_t>(thunk_buf[1]);
            resolved = resolved + 2 + rel;
            continue;
          }
          break;
        }
        return resolved;
      };

      uint64_t seg_start = vm_entry_va;
      uint64_t seg_end = vm_entry_va + 0x2000000;
      pe.memory_map.forEachRegion(
          [&](uint64_t base, const uint8_t *, size_t size) {
            if (vm_entry_va >= base && vm_entry_va < base + size) {
              seg_start = base;
              seg_end = base + size;
            }
          });

      omill::VMTraceEmulator solver(pe.memory_map, pe.image_base,
                                         vm_entry_va, vm_exit_va);
      solver.setHandlerSegmentRange(seg_start, seg_end);

      for (auto &F : *module) {
        if (F.isDeclaration() || !F.getName().ends_with("_native") ||
            F.hasFnAttribute("omill.vm_wrapper")) {
          continue;
        }

        auto base_name = F.getName().drop_back(strlen("_native"));
        if (!base_name.starts_with("sub_"))
          continue;

        uint64_t helper_va = 0;
        if (base_name.drop_front(4).getAsInteger(16, helper_va) ||
            helper_va == 0) {
          continue;
        }

        llvm::SmallVector<llvm::CallInst *, 2> indirect_calls;
        for (auto &BB : F) {
          for (auto &I : BB) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI)
              continue;
            if (llvm::isa<llvm::Function>(
                    CI->getCalledOperand()->stripPointerCasts())) {
              continue;
            }
            indirect_calls.push_back(CI);
          }
        }
        if (indirect_calls.size() != 1)
          continue;

        uint64_t wrapper_va = followJmpThunks(helper_va);
        if (wrapper_va == 0 || wrapper_va == helper_va ||
            wrapper_va == vm_wrapper_va) {
          continue;
        }

        auto trace = solver.traceFromWrapper(wrapper_va);
        if (trace.empty() || trace.front().successors.empty())
          continue;

        uint64_t target_va = trace.front().successors.front();
        if (target_va == 0)
          continue;

        nested_vm_helper_targets[helper_va] = target_va;
        nested_vm_helper_deltas[helper_va] = solver.lastDelta();
      }
    };

    struct HashBufferInfo {
      uint64_t hash = 0;
      std::array<uint32_t, 5> words = {};
      std::vector<std::pair<int64_t, uint64_t>> scratch_qwords;
      std::vector<std::pair<int64_t, uint64_t>> precall_qwords;
      uint64_t return_seed = 0;
    };

    auto getAddConst = [&](llvm::Value *V) -> std::optional<int64_t> {
      auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V);
      if (!BO)
        return std::nullopt;
      auto *C = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
      if (!C || C->getBitWidth() > 64)
        return std::nullopt;
      if (BO->getOpcode() == llvm::Instruction::Add)
        return C->getSExtValue();
      if (BO->getOpcode() == llvm::Instruction::Sub)
        return -C->getSExtValue();
      return std::nullopt;
    };

    auto getStackDisp = [&](llvm::Value *V) -> std::optional<int64_t> {
      if (auto disp = getAddConst(V))
        return disp;
      auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(V);
      if (!GEP)
        return std::nullopt;
      llvm::APInt offset(64, 0, true);
      if (!GEP->accumulateConstantOffset(module->getDataLayout(), offset))
        return std::nullopt;
      return static_cast<int64_t>(offset.getSExtValue()) - 65504;
    };

    auto decodeHashBuffer =
        [&](llvm::CallInst *CI) -> std::optional<HashBufferInfo> {
      constexpr int64_t kSnapshotSpan = 0x2000;
      uint32_t words[5] = {};
      unsigned found = 0;
      std::vector<std::pair<int64_t, uint64_t>> scratch_qwords;
      std::vector<std::pair<int64_t, uint64_t>> precall_qwords;
      for (auto It = CI->getIterator(); It != CI->getParent()->begin();) {
        --It;
        if (llvm::isa<llvm::CallBase>(&*It))
          break;
        auto *SI = llvm::dyn_cast<llvm::StoreInst>(&*It);
        if (!SI)
          continue;
        auto *C = llvm::dyn_cast<llvm::ConstantInt>(SI->getValueOperand());
        if (!C)
          continue;
        auto disp = getStackDisp(SI->getPointerOperand());
        if (C->getBitWidth() == 32 && found < 5) {
          if (disp && *disp < 0 && *disp >= -0x1000)
            words[found++] = C->getZExtValue();
          continue;
        }
        if (C->getBitWidth() == 64 && disp &&
            *disp >= -0x1000 && *disp < kSnapshotSpan) {
          precall_qwords.emplace_back(*disp, C->getZExtValue());
          if (*disp < 0)
            scratch_qwords.emplace_back(*disp, C->getZExtValue());
        }
      }
      if (found != 5)
        return std::nullopt;
      std::reverse(std::begin(words), std::end(words));
      uint64_t return_seed = scratch_qwords.empty()
                                 ? 0
                                 : scratch_qwords.front().second;
      std::reverse(scratch_qwords.begin(), scratch_qwords.end());
      std::reverse(precall_qwords.begin(), precall_qwords.end());
      HashBufferInfo info;
      for (unsigned i = 0; i < 5; ++i)
        info.words[i] = words[i];
      info.hash = static_cast<uint64_t>(words[0]) |
                  (static_cast<uint64_t>(words[1]) << 32);
      info.scratch_qwords = std::move(scratch_qwords);
      info.precall_qwords = std::move(precall_qwords);
      info.return_seed = return_seed;
      return info;
    };

    auto collectHashResolvedCalls = [&]() {
      llvm::SmallVector<HashResolvedCall, 8> resolved_calls;
      if (!vm_mode || RawBinary || true)
        return resolved_calls;
      llvm::DenseMap<llvm::Value *, uint64_t> helper_value_cache;
      llvm::DenseMap<uint64_t, std::optional<uint64_t>> per_wrapper_seed;

      auto followJmpThunks = [&](uint64_t va) {
        uint64_t resolved = va;
        for (unsigned hop = 0; hop < 4; ++hop) {
          uint8_t thunk_buf[16];
          if (!pe.memory_map.read(resolved, thunk_buf, sizeof(thunk_buf)))
            break;
          if (thunk_buf[0] == 0xE9) {
            int32_t rel = 0;
            std::memcpy(&rel, &thunk_buf[1], 4);
            resolved = resolved + 5 + static_cast<int64_t>(rel);
            continue;
          }
          if (thunk_buf[0] == 0xEB) {
            int8_t rel = static_cast<int8_t>(thunk_buf[1]);
            resolved = resolved + 2 + rel;
            continue;
          }
          break;
        }
        return resolved;
      };

      uint64_t seg_start = vm_entry_va;
      uint64_t seg_end = vm_entry_va + 0x2000000;
      pe.memory_map.forEachRegion(
          [&](uint64_t base, const uint8_t *, size_t size) {
            if (vm_entry_va >= base && vm_entry_va < base + size) {
              seg_start = base;
              seg_end = base + size;
            }
          });

      auto getConstI64 = [&](llvm::Value *V) -> std::optional<uint64_t> {
        if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V))
          return CI->getZExtValue();
        return std::nullopt;
      };
      auto resolveNestedHelperValue =
          [&](llvm::Value *V) -> std::optional<uint64_t> {
        if (auto it = helper_value_cache.find(V); it != helper_value_cache.end())
          return it->second;
        auto *CI = llvm::dyn_cast<llvm::CallInst>(V);
        if (!CI)
          return std::nullopt;
        auto *callee = llvm::dyn_cast<llvm::Function>(
            CI->getCalledOperand()->stripPointerCasts());
        if (!callee || !callee->getName().ends_with("_native"))
          return std::nullopt;
        auto base = callee->getName().drop_back(strlen("_native"));
        if (!base.starts_with("sub_"))
          return std::nullopt;
        uint64_t callee_va = 0;
        if (base.drop_front(4).getAsInteger(16, callee_va) || callee_va == 0)
          return std::nullopt;
        // Only resolve if the callee is a known wrapper.
        if (!nested_vm_helper_targets.count(callee_va))
          return std::nullopt;
        auto &seed = per_wrapper_seed[callee_va];
        if (!seed) {
          uint64_t wrapper_va = followJmpThunks(callee_va);
          if (wrapper_va == 0) wrapper_va = callee_va;
          omill::VMTraceEmulator solver(pe.memory_map, pe.image_base,
                                             vm_entry_va, vm_exit_va);
          solver.setHandlerSegmentRange(seg_start, seg_end);
          auto results = solver.traceFromWrapper(wrapper_va);
          auto targets = solver.nativeCallTargets();
          if (targets.size() == 1) {
            seed = targets.front();
          } else {
            for (auto &entry : results) {
              if (entry.handler_va == wrapper_va || entry.successors.empty())
                continue;
              seed = entry.successors.front();
              break;
            }
          }
        }
        if (!seed)
          return std::nullopt;
        helper_value_cache[V] = *seed;
        return *seed;
      };
      auto getConcreteI64 = [&](llvm::Value *V) -> std::optional<uint64_t> {
        if (auto c = getConstI64(V))
          return c;
        return resolveNestedHelperValue(V);
      };

      auto buildVMWrapperSnapshot =
          [&](llvm::CallInst *CI, const HashBufferInfo &buffer_info)
              -> std::vector<uint8_t> {
        constexpr size_t kSnapshotSize = 0x2000;
        constexpr uint64_t kSub1402A110ERet = 0xFFFFFFFFFFD61E74ull;

        std::vector<uint8_t> snapshot(kSnapshotSize, 0);
        auto putI64 = [&](size_t off, uint64_t value) {
          if (off + sizeof(value) > snapshot.size())
            return;
          std::memcpy(snapshot.data() + off, &value, sizeof(value));
        };
        auto putBufferWord = [&](size_t off, uint32_t value) {
          if (off + sizeof(value) > snapshot.size())
            return;
          std::memcpy(snapshot.data() + off, &value, sizeof(value));
        };
        auto getArgConcreteOr = [&](unsigned index, uint64_t fallback) {
          if (index >= CI->arg_size())
            return fallback;
          if (auto value = getConcreteI64(CI->getArgOperand(index)))
            return *value;
          return fallback;
        };

        uint64_t synthetic_vm_base =
            omill::VMTraceEmulator::syntheticVMContextBase();
        uint64_t synthetic_saved_rsp = synthetic_vm_base + 0x1800;
        auto mapScratchDisp = [&](int64_t disp, int64_t fallback) {
          if (disp >= 0 || disp < -0x1000)
            disp = fallback;
          return synthetic_saved_rsp + disp;
        };
        int64_t buffer_disp = -0x150;
        if (CI->arg_size() > 1) {
          if (auto disp = getAddConst(CI->getArgOperand(1)))
            buffer_disp = *disp;
        }
        uint64_t synthetic_buffer = mapScratchDisp(buffer_disp, -0x150);
        size_t buffer_off =
            static_cast<size_t>(synthetic_buffer - synthetic_vm_base);
        for (unsigned i = 0; i < buffer_info.words.size(); ++i)
          putBufferWord(buffer_off + i * sizeof(uint32_t),
                        buffer_info.words[i]);
        bool has_explicit_1c0 = false;
        bool has_explicit_1c8 = false;
        for (auto &[disp, value] : buffer_info.precall_qwords) {
          if (disp >= 0) {
            size_t off = static_cast<size_t>(disp);
            putI64(off, value);
            has_explicit_1c0 |= (off == 0x1C0);
            has_explicit_1c8 |= (off == 0x1C8);
            continue;
          }
          uint64_t addr = mapScratchDisp(disp, disp);
          size_t off = static_cast<size_t>(addr - synthetic_vm_base);
          putI64(off, value);
        }

        int64_t scratch_disp = -0x78;
        if (CI->arg_size() > 7) {
          if (auto disp = getAddConst(CI->getArgOperand(7)))
            scratch_disp = *disp;
        }
        uint64_t synthetic_scratch = mapScratchDisp(scratch_disp, -0x78);

        // After ABI recovery, the VM wrapper performs a small setup
        // around the vmentry and then tail-calls the first handler.
        // Seed the synthetic register and home-space slots from that
        // nested callsite, not from the helper's original wrapper arguments.
        uint64_t chain_rcx = getArgConcreteOr(2, 0);
        uint64_t chain_rdx = getArgConcreteOr(3, 0);
        uint64_t chain_r8 = getArgConcreteOr(8, 0);
        uint64_t home_rcx = chain_rcx;
        uint64_t home_rdx = chain_rdx;
        uint64_t home_r8 = chain_r8;
        uint64_t home_r9 = 0;
        putI64(0x30, getArgConcreteOr(7, 0));                // RBP
        putI64(0x38, synthetic_buffer);                      // RDX
        putI64(0x40, getArgConcreteOr(4, 0));                // RBX
        putI64(0x50, home_rcx);                              // pre-shift [rsp+8]
        putI64(0x58, home_rdx);                              // pre-shift [rsp+10]
        putI64(0x60, home_r8);                               // pre-shift [rsp+18]
        putI64(0x68, home_r9);                               // pre-shift [rsp+20]
        putI64(0x78, home_r8);                               // R8
        putI64(0x80, home_r9);                               // R9
        putI64(0x88, getArgConcreteOr(9, 0));                // R13
        putI64(0x90, home_rcx);                              // RCX
        putI64(0x98, getArgConcreteOr(8, 0));                // R12
        putI64(0xB8, synthetic_scratch);                     // helper scratch
        putI64(0xC0, synthetic_saved_rsp);                   // saved RSP-ish
        putI64(0xE0, kSub1402A110ERet);                      // sub_1402A110E
        putI64(0x108, 0);                                    // RAX
        putI64(0x110, getArgConcreteOr(10, 0));              // R14
        putI64(0x128, getArgConcreteOr(5, 0));               // RSI
        putI64(0x140, getArgConcreteOr(11, 0));              // R15
        putI64(0x158, 0);                                    // R10 scratch
        putI64(0x170, getArgConcreteOr(6, 0));               // RDI
        putI64(0x188, 0);                                    // R11 scratch
        // The wrapper stores [vmctx+0x38] to [*[vmctx+0xB8] + 0x10]
        // before tail-calling the first handler.
        putI64(static_cast<size_t>(synthetic_scratch - synthetic_vm_base) +
                   0x10,
               synthetic_buffer);
        // The first handler frame-shift re-bases [vmctx+0xB8] by -0x178
        // before the next stage consumes [*[vmctx+0xB8] + 0x10]. Seed the
        // shifted alias as well so the buffer pointer survives that move.
        if (synthetic_scratch >= synthetic_vm_base + 0x168) {
          putI64(static_cast<size_t>(synthetic_scratch - synthetic_vm_base) -
                     0x168,
                 synthetic_buffer);
        }
        if (!has_explicit_1c0 && buffer_info.return_seed != 0)
          putI64(0x1C0, buffer_info.return_seed);
        else if (!has_explicit_1c0)
          putI64(0x1C0, 0);
        if (!has_explicit_1c8)
          putI64(0x1C8, home_rcx);
        putI64(0x1D0, home_rdx);
        putI64(0x1D8, home_r8);
        putI64(0x1E0, home_r9);

        return snapshot;
      };

      for (auto &[helper_va, handler_va] : nested_vm_helper_targets) {
        (void)handler_va;
        uint64_t delta = nested_vm_helper_deltas.lookup(helper_va);
        if (delta == 0)
          continue;

        std::string helper_name =
            "sub_" + llvm::Twine::utohexstr(helper_va).str() + "_native";
        uint64_t wrapper_va = followJmpThunks(helper_va);
        if (wrapper_va == 0)
          wrapper_va = helper_va;
        for (auto &F : *module) {
          unsigned ordinal = 0;
          for (auto &BB : F) {
            for (auto &I : BB) {
              auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!CI)
                continue;
              auto *callee = llvm::dyn_cast<llvm::Function>(
                  CI->getCalledOperand()->stripPointerCasts());
              if (!callee || callee->getName() != helper_name)
                continue;

              auto buffer_info = decodeHashBuffer(CI);
              if (!buffer_info) {
                ++ordinal;
                continue;
              }

              omill::VMTraceEmulator solver(pe.memory_map, pe.image_base,
                                                 vm_entry_va, vm_exit_va);
              solver.setHandlerSegmentRange(seg_start, seg_end);
              auto snapshot = buildVMWrapperSnapshot(CI, *buffer_info);
              (void)delta;
              (void)handler_va;
              (void)solver.traceFromWrapperWithSnapshot(wrapper_va, snapshot);
              auto targets = solver.nativeCallTargets();
              if (targets.size() != 1) {
                errs() << "Trace-emulated resolve for " << helper_name
                       << " hash=0x" << Twine::utohexstr(buffer_info->hash)
                       << " produced "
                       << targets.size() << " native target(s)\n";
                if (getenv("OMILL_DEBUG_CHAIN")) {
                  errs() << "  call: ";
                  CI->print(errs());
                  errs() << "\n";
                  errs() << "  precall qwords:";
                  for (auto &[disp, value] : buffer_info->precall_qwords)
                    errs() << " [" << disp << "]=0x"
                           << Twine::utohexstr(value);
                  errs() << "\n";
                }
                ++ordinal;
                continue;
              }

              HashResolvedCall resolved;
              resolved.caller_name = F.getName().str();
              resolved.helper_name = helper_name;
              resolved.ordinal = ordinal;
              resolved.hash = buffer_info->hash;
              resolved.target_va = targets.front();
              resolved_calls.push_back(std::move(resolved));
              ++ordinal;
            }
          }
        }
      }

      return resolved_calls;
    };

    auto collectNestedHelperCallsites = [&]() {
      llvm::SmallVector<NestedHelperCallsite, 8> callsites;
      if (!vm_mode || RawBinary || true)
        return callsites;

      llvm::DenseSet<uint64_t> helper_vas;
      for (auto &[helper_va, _] : nested_vm_helper_targets)
        helper_vas.insert(helper_va);
      if (helper_vas.empty())
        return callsites;

      for (auto &F : *module) {
        llvm::DenseMap<uint64_t, unsigned> ordinal_per_helper;
        for (auto &BB : F) {
          for (auto &I : BB) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI)
              continue;
            auto *callee = llvm::dyn_cast<llvm::Function>(
                CI->getCalledOperand()->stripPointerCasts());
            if (!callee || !callee->getName().ends_with("_native"))
              continue;
            auto base_name = callee->getName().drop_back(strlen("_native"));
            if (!base_name.starts_with("sub_"))
              continue;
            uint64_t helper_va = 0;
            if (base_name.drop_front(4).getAsInteger(16, helper_va) ||
                !helper_vas.contains(helper_va)) {
              continue;
            }

            NestedHelperCallsite info;
            info.caller_name = F.getName().str();
            info.helper_name = callee->getName().str();
            info.ordinal = ordinal_per_helper[helper_va]++;
            auto hbuf = decodeHashBuffer(CI);
            info.hash = hbuf ? std::optional(hbuf->hash) : std::nullopt;
            callsites.push_back(std::move(info));
          }
        }
      }
      return callsites;
    };

    for (unsigned round = 0; round < 3; ++round) {
      if (events.detailed()) {
        events.emitInfo("late_discovery_round_started",
                        "late target discovery round started",
                        {{"round", static_cast<int64_t>(round + 1)}});
      }
      // Collect constant inttoptr call targets.
      // Match both ConstantExpr::IntToPtr and IntToPtrInst with constant
      // operands — LLVM 21 no longer folds inttoptr(const) instructions
      // to ConstantExpr form, so B3 dynamic rewrites from
      // RewriteLiftedCallsToNative produce IntToPtrInst after GVN folds.
      llvm::DenseSet<uint64_t> late_targets;
      for (auto &F : *module) {
        for (auto &BB : F) {
          for (auto &I : BB) {
            auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!call)
              continue;

            if (auto *callee = call->getCalledFunction()) {
              if (callee->getName().contains("CALLI") &&
                  call->arg_size() >= 3) {
                auto *ci =
                    llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(2));
                if (!ci)
                  continue;
                const uint64_t target = ci->getZExtValue();
                if (!isCodeAddressInCurrentInput(target))
                  continue;
                if (hasDefinedLiftedOrBlockTarget(target))
                  continue;
                late_targets.insert(target);
                continue;
              }

              if (!callee->isDeclaration())
                continue;
              if (!callee->getName().starts_with("sub_"))
                continue;
              auto *FT = callee->getFunctionType();
              if (FT->getNumParams() != 3 ||
                  FT->getReturnType() != llvm::PointerType::getUnqual(ctx) ||
                  FT->getParamType(0) != llvm::PointerType::getUnqual(ctx) ||
                  FT->getParamType(1) != llvm::Type::getInt64Ty(ctx) ||
                  FT->getParamType(2) != llvm::PointerType::getUnqual(ctx)) {
                continue;
              }

              const uint64_t target = omill::extractEntryVA(callee->getName());
              if (!isCodeAddressInCurrentInput(target))
                continue;
              if (hasDefinedLiftedOrBlockTarget(target))
                continue;
              late_targets.insert(target);
              continue;
            }

            auto *callee_op = call->getCalledOperand();
            llvm::ConstantInt *ci = nullptr;
            // Case 1: ConstantExpr inttoptr.
            if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(callee_op)) {
              if (ce->getOpcode() == llvm::Instruction::IntToPtr)
                ci = llvm::dyn_cast<llvm::ConstantInt>(ce->getOperand(0));
            }
            // Case 2: IntToPtrInst with constant operand.
            if (!ci) {
              if (auto *itp = llvm::dyn_cast<llvm::IntToPtrInst>(callee_op))
                ci = llvm::dyn_cast<llvm::ConstantInt>(itp->getOperand(0));
            }
            if (!ci)
              continue;
            uint64_t target = ci->getZExtValue();
            if (target == 0)
              continue;
            if (!isCodeAddressInCurrentInput(target))
              continue;
            if (hasDefinedLiftedOrBlockTarget(target))
              continue;
            late_targets.insert(target);
          }
        }
      }
      collectNestedVMHelperTargets();

      auto hash_resolved_calls = collectHashResolvedCalls();
      auto nested_helper_callsites = collectNestedHelperCallsites();
      for (auto &[helper_va, target_va] : nested_vm_helper_targets) {
        std::string native_name =
            "sub_" + llvm::Twine::utohexstr(target_va).str() + "_native";
        auto *existing = module->getFunction(native_name);
        if (!existing || existing->isDeclaration())
          late_targets.insert(target_va);
        errs() << "Nested VM helper sub_" << Twine::utohexstr(helper_va)
               << "_native -> first handler 0x"
               << Twine::utohexstr(target_va) << "\n";
      }
      for (auto &resolved : hash_resolved_calls) {
        std::string native_name =
            "sub_" + llvm::Twine::utohexstr(resolved.target_va).str() +
            "_native";
        auto *existing = module->getFunction(native_name);
        if (!existing || existing->isDeclaration())
          late_targets.insert(resolved.target_va);
        errs() << "Hash-resolved " << resolved.helper_name << " call "
               << resolved.ordinal << " hash=0x"
               << Twine::utohexstr(resolved.hash) << " -> 0x"
               << Twine::utohexstr(resolved.target_va) << "\n";
      }
      if (late_targets.empty()) {
        errs() << "Late discovery round " << (round + 1)
               << ": no new targets\n";
        break;
      }

      errs() << "Late discovery round " << (round + 1) << ": "
             << late_targets.size() << " new target(s)\n";
      events.emitInfo("late_discovery_targets", "late discovery targets found",
                      {{"round", static_cast<int64_t>(round + 1)},
                       {"targets", static_cast<int64_t>(late_targets.size())}});

      // Lift late targets directly into the current session/module and rerun
      // the normal pipeline on just the newly-added functions. This avoids
      // a second Arch/semantics/module world and keeps discovery iterative.
      llvm::DenseSet<llvm::Function *> pre_lift_funcs;
      for (auto &F : *module)
        pre_lift_funcs.insert(&F);

      unsigned late_patched = 0;
      unsigned late_lifted = 0;
      unsigned late_failed = 0;
      auto trace_cb = iterative_session->traceLiftCallback();
      auto block_cb = iterative_session->blockLiftCallback();
      for (uint64_t pc : late_targets) {
        if (events.detailed()) {
          events.emitInfo("late_discovery_lift_started",
                          "late discovery target lift started",
                          {{"round", static_cast<int64_t>(round + 1)},
                           {"target", ("0x" + llvm::Twine::utohexstr(pc)).str()},
                           {"pipeline",
                            opts.use_block_lifting ? "block" : "trace"}});
        }
        iterative_session->queueTarget(pc);
        bool lifted_ok = false;
        if (opts.use_block_lifting && !vm_mode && block_cb) {
          lifted_ok = block_cb(pc);
        } else if (trace_cb) {
          lifted_ok = trace_cb(pc);
        } else {
          lifted_ok = projection_lifter && projection_lifter->LiftFunction(pc);
          if (lifted_ok)
            iterative_session->noteLiftedTarget(pc);
        }
        if (lifted_ok) {
          ++late_lifted;
        } else {
          ++late_failed;
        }
        if (events.detailed()) {
          events.emitInfo("late_discovery_lift_completed",
                          "late discovery target lift completed",
                          {{"round", static_cast<int64_t>(round + 1)},
                           {"target", ("0x" + llvm::Twine::utohexstr(pc)).str()},
                           {"lifted", lifted_ok}});
        }
      }
      if (events.detailed()) {
        events.emitInfo("late_discovery_lift_batch_completed",
                        "late discovery target batch completed",
                        {{"round", static_cast<int64_t>(round + 1)},
                         {"lifted", static_cast<int64_t>(late_lifted)},
                         {"failed", static_cast<int64_t>(late_failed)}});
      }
      fixLiftedFunctionNamingCollisions();
      if (events.detailed()) {
        events.emitInfo("late_discovery_collision_fix_completed",
                        "late discovery collision fix completed",
                        {{"round", static_cast<int64_t>(round + 1)}});
      }

      if (late_lifted == 0) {
        errs() << "Late discovery round " << (round + 1)
               << ": lift failed for all targets\n";
        events.emitWarn("late_discovery_lift_failed",
                        "late discovery lifting produced no new functions",
                        {{"round", static_cast<int64_t>(round + 1)},
                         {"failed", static_cast<int64_t>(late_failed)}});
        break;
      }

      tagNewlyLiftedFunctions("omill.late_newly_lifted", pre_lift_funcs);
      if (events.detailed()) {
        events.emitInfo("late_discovery_tagging_completed",
                        "late discovery new function tagging completed",
                        {{"round", static_cast<int64_t>(round + 1)}});
      }

      if (DumpIR) {
        std::error_code ec;
        raw_fd_ostream os("late_after_lift.ll", ec, sys::fs::OF_Text);
        module->print(os, nullptr);
      }

      rerunLateDiscoveryPipeline("omill.late_newly_lifted", /*run_abi=*/true,
                                 /*skip_missing_block_lift=*/false);

      if (DumpIR) {
        std::error_code ec;
        raw_fd_ostream os("late_after_pipeline.ll", ec, sys::fs::OF_Text);
        module->print(os, nullptr);
      }

      if (DumpIR) {
        std::error_code ec;
        raw_fd_ostream os("late_after_abi.ll", ec, sys::fs::OF_Text);
        module->print(os, nullptr);
      }

      // Patch call sites: replace inttoptr(i64 <const>) → @sub_<hex>_native
      // Handles both ConstantExpr and IntToPtrInst forms.
      for (uint64_t pc : late_targets) {
        std::string native_name =
            "sub_" + llvm::Twine::utohexstr(pc).str() + "_native";
        auto *target_fn = module->getFunction(native_name);
        if (!target_fn)
          continue;
        auto *pc_ci = llvm::ConstantInt::get(
            llvm::Type::getInt64Ty(ctx), pc);

        // Case 1: ConstantExpr inttoptr — RAUW replaces all uses globally.
        auto *itp = llvm::ConstantExpr::getIntToPtr(
            pc_ci, llvm::PointerType::getUnqual(ctx));
        if (itp->getNumUses() > 0) {
          late_patched += itp->getNumUses();
          itp->replaceAllUsesWith(target_fn);
        }

        // Case 2: IntToPtrInst instructions with this constant operand.
        // Each instruction is a separate Value, so scan and replace each.
        // ConstantInt (ConstantData) may not have a use list in LLVM 21.
        if (!pc_ci->hasUseList())
          continue;
        for (auto *user : llvm::make_early_inc_range(pc_ci->users())) {
          auto *inst = llvm::dyn_cast<llvm::IntToPtrInst>(user);
          if (!inst)
            continue;
          late_patched += inst->getNumUses();
          inst->replaceAllUsesWith(target_fn);
          if (inst->use_empty())
            inst->eraseFromParent();
        }
      }
      if (late_patched > 0) {
        runPostPatchCleanup("late_discovery_callsites");
        if (events.detailed()) {
          events.emitInfo("late_discovery_patch_callsites",
                          "patched late inttoptr callsites",
                          {{"round", static_cast<int64_t>(round + 1)},
                           {"patched_uses",
                           static_cast<int64_t>(late_patched)}});
        }
      }

      unsigned helper_patched = 0;
      for (auto &[helper_va, target_va] : nested_vm_helper_targets) {
        std::string helper_name =
            "sub_" + llvm::Twine::utohexstr(helper_va).str() + "_native";
        std::string target_name =
            "sub_" + llvm::Twine::utohexstr(target_va).str() + "_native";
        auto *helper_fn = module->getFunction(helper_name);
        auto *target_fn = module->getFunction(target_name);
        if (!helper_fn || helper_fn->isDeclaration() ||
            !target_fn || target_fn->isDeclaration()) {
          continue;
        }

        llvm::SmallVector<llvm::CallInst *, 2> indirect_calls;
        for (auto &BB : *helper_fn) {
          for (auto &I : BB) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI)
              continue;
            if (llvm::isa<llvm::Function>(
                    CI->getCalledOperand()->stripPointerCasts())) {
              continue;
            }
            indirect_calls.push_back(CI);
          }
        }
        if (indirect_calls.size() != 1)
          continue;

        auto *CI = indirect_calls.front();
        llvm::SmallVector<llvm::Value *, 16> args;
        for (auto &Arg : CI->args())
          args.push_back(Arg.get());

        llvm::IRBuilder<> Builder(CI);
        llvm::Value *direct_callee = target_fn;
        if (target_fn->getType() != CI->getCalledOperand()->getType()) {
          direct_callee = Builder.CreateBitCast(
              target_fn, CI->getCalledOperand()->getType(),
              target_name + ".cast");
        }
        auto *new_call = Builder.CreateCall(
            CI->getFunctionType(), direct_callee, args, CI->getName());
        new_call->setCallingConv(CI->getCallingConv());
        new_call->setAttributes(CI->getAttributes());
        if (!CI->use_empty())
          CI->replaceAllUsesWith(new_call);
        CI->eraseFromParent();
        ++helper_patched;
      }
      if (helper_patched > 0) {
        errs() << "Patched " << helper_patched
               << " nested VM helper call(s) to direct targets\n";
        runPostPatchCleanup("nested_vm_helpers");
      }

      // Do NOT fold hash-resolved helper calls to constants. Those helpers
      // represent distinct virtualized callees and must remain outlined so the
      // recovered demerged control flow stays modelled as callable functions.
      unsigned hash_helper_clone_count = 0;
      for (const auto &resolved : hash_resolved_calls) {
        auto *caller_fn = module->getFunction(resolved.caller_name);
        auto *helper_fn = module->getFunction(resolved.helper_name);
        if (!caller_fn || caller_fn->isDeclaration() ||
            !helper_fn || helper_fn->isDeclaration()) {
          continue;
        }

        unsigned ordinal = 0;
        llvm::CallInst *target_call = nullptr;
        for (auto &BB : *caller_fn) {
          for (auto &I : BB) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI)
              continue;
            auto *callee = llvm::dyn_cast<llvm::Function>(
                CI->getCalledOperand()->stripPointerCasts());
            if (!callee || callee->getName() != resolved.helper_name)
              continue;
            if (ordinal++ == resolved.ordinal) {
              target_call = CI;
              break;
            }
          }
          if (target_call)
            break;
        }
        if (!target_call)
          continue;

        std::string clone_name = resolved.helper_name + "__" +
                                 resolved.caller_name + "_" +
                                 std::to_string(resolved.ordinal) +
                                 "_h" + llvm::utohexstr(resolved.hash);
        // Extract handler VA from helper name for trace linkage.
        uint64_t helper_va_for_trace = 0;
        {
          llvm::StringRef bn = llvm::StringRef(resolved.helper_name);
          if (bn.ends_with("_native"))
            bn = bn.drop_back(7);  // strlen("_native")
          if (bn.starts_with("sub_"))
            bn.drop_front(4).getAsInteger(16, helper_va_for_trace);
        }
        auto [clone, created] = ensureOutlinedVirtualCallee(
            helper_fn, clone_name, resolved.caller_name, resolved.hash,
            "hash_resolved", round + 1, helper_va_for_trace,
            std::optional<uint64_t>(resolved.hash));
        if (!clone)
          continue;
        if (created)
          ++hash_helper_clone_count;

        llvm::SmallVector<llvm::Value *, 16> args;
        for (auto &Arg : target_call->args())
          args.push_back(Arg.get());

        llvm::IRBuilder<> Builder(target_call);
        auto *clone_call =
            Builder.CreateCall(clone, args, clone_name + ".result");
        clone_call->setCallingConv(target_call->getCallingConv());
        clone_call->setAttributes(target_call->getAttributes());
        target_call->replaceAllUsesWith(clone_call);
        target_call->eraseFromParent();
      }
      if (hash_helper_clone_count > 0) {
        errs() << "Cloned " << hash_helper_clone_count
               << " hash-resolved helper call(s) to outlined wrappers\n";
        runPostPatchCleanup("hash_resolved_helpers");
      }

      unsigned helper_clone_count = 0;
      llvm::StringMap<unsigned> helper_callsite_counts;
      llvm::StringMap<llvm::SmallVector<NestedHelperCallsite, 4>>
          helper_callsites_by_key;
      auto helperCloneKey = [&](const NestedHelperCallsite &info) {
        return info.caller_name + "||" + info.helper_name;
      };
      for (const auto &info : nested_helper_callsites) {
        ++helper_callsite_counts[helperCloneKey(info)];
        helper_callsites_by_key[helperCloneKey(info)].push_back(info);
      }

      for (auto &entry : helper_callsites_by_key) {
        auto &infos = entry.getValue();

        llvm::sort(infos, [](const NestedHelperCallsite &lhs,
                             const NestedHelperCallsite &rhs) {
          return lhs.ordinal > rhs.ordinal;
        });

        llvm::SmallVector<llvm::CallInst *, 8> current_calls;
        auto *caller_fn = module->getFunction(infos.front().caller_name);
        auto *helper_fn = module->getFunction(infos.front().helper_name);
        if (!caller_fn || caller_fn->isDeclaration() ||
            !helper_fn || helper_fn->isDeclaration()) {
          continue;
        }
        for (auto &BB : *caller_fn) {
          for (auto &I : BB) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!CI)
              continue;
            auto *callee = llvm::dyn_cast<llvm::Function>(
                CI->getCalledOperand()->stripPointerCasts());
            if (callee == helper_fn)
              current_calls.push_back(CI);
          }
        }

        for (const auto &info : infos) {
          if (info.ordinal >= current_calls.size())
            continue;
          llvm::CallInst *target_call = current_calls[info.ordinal];
          if (!target_call)
            continue;

          std::string clone_name = info.helper_name + "__" + info.caller_name +
                                   "_" + std::to_string(info.ordinal);
          if (info.hash)
            clone_name += "_h" + llvm::utohexstr(*info.hash);

          // Extract handler VA from helper name for trace linkage.
          uint64_t nested_helper_va = 0;
          {
            llvm::StringRef bn = llvm::StringRef(info.helper_name);
            if (bn.ends_with("_native"))
              bn = bn.drop_back(7);
            if (bn.starts_with("sub_"))
              bn.drop_front(4).getAsInteger(16, nested_helper_va);
          }
          auto [clone, created] = ensureOutlinedVirtualCallee(
              helper_fn, clone_name, info.caller_name, info.hash,
              "nested_helper", round + 1, nested_helper_va, info.hash);
          if (!clone)
            continue;

          llvm::SmallVector<llvm::Value *, 16> args;
          for (auto &Arg : target_call->args())
            args.push_back(Arg.get());

          llvm::IRBuilder<> Builder(target_call);
          auto *clone_call =
              Builder.CreateCall(clone, args, clone_name + ".result");
          clone_call->setCallingConv(target_call->getCallingConv());
          clone_call->setAttributes(target_call->getAttributes());
          target_call->replaceAllUsesWith(clone_call);
          target_call->eraseFromParent();
          current_calls[info.ordinal] = nullptr;
          if (created)
            ++helper_clone_count;
        }
      }
      if (helper_clone_count > 0) {
        errs() << "Cloned " << helper_clone_count
               << " nested VM helper call(s) for IR continuity\n";
        runPostPatchCleanup("nested_vm_helper_clones");
      }

      {
        omill::StateFieldMap sfm(*module);
        auto arch_abi =
            omill::ArchABI::get(omill::TargetArch::kX86_64, "windows");
        llvm::SmallVector<unsigned, 16> b3_arg_offsets;
        for (auto &reg : arch_abi.param_regs) {
          auto f = sfm.fieldByName(reg);
          if (f) b3_arg_offsets.push_back(f->offset);
        }
        for (auto &cs : arch_abi.callee_saved) {
          auto f = sfm.fieldByName(cs);
          if (f) b3_arg_offsets.push_back(f->offset);
        }

        auto *i64_ty = llvm::Type::getInt64Ty(ctx);
        auto findStateOffsetPtrInFunction =
            [&](llvm::Function &Fn, uint64_t offset) -> llvm::Value * {
          for (auto &BB : Fn) {
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
        auto calleeReadsArg2AsStatePtr = [&](llvm::Function &Callee) -> bool {
          if (Callee.arg_size() < 3)
            return false;
          auto *arg = Callee.getArg(2);
          for (auto *U : arg->users()) {
            auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(U);
            if (!BO || BO->getOpcode() != llvm::Instruction::Add)
              continue;
            auto *lhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0));
            auto *rhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
            if ((lhs_ci && lhs_ci->getZExtValue() == 9116) ||
                (rhs_ci && rhs_ci->getZExtValue() == 9116)) {
              return true;
            }
          }
          return false;
        };
        auto buildStateOrderedArgs =
            [&](llvm::Function &Caller, llvm::CallInst &CI,
                llvm::Function &Callee,
                llvm::ArrayRef<int> caller_param_offsets)
                -> std::optional<llvm::SmallVector<llvm::Value *, 16>> {
          auto attr = Callee.getFnAttribute("omill.param_state_offsets");
          if (!attr.isValid() || !attr.isStringAttribute())
            return std::nullopt;

          llvm::SmallVector<llvm::StringRef, 16> callee_offset_strs;
          attr.getValueAsString().split(callee_offset_strs, ',');
          if (callee_offset_strs.size() < Callee.arg_size())
            return std::nullopt;

          llvm::IRBuilder<> Builder(&CI);
          auto defaultMissingI64Arg = [&]() -> llvm::Value * {
            return llvm::ConstantInt::get(i64_ty, 0);
          };
          llvm::SmallVector<llvm::Value *, 16> new_args;
          new_args.reserve(Callee.arg_size());
          for (unsigned arg_index = 0; arg_index < Callee.arg_size(); ++arg_index) {
            llvm::StringRef off_str = callee_offset_strs[arg_index].trim();
            if (off_str == "stack" || off_str == "xmm") {
              if (arg_index < CI.arg_size())
                new_args.push_back(CI.getArgOperand(arg_index));
              else
                new_args.push_back(defaultMissingI64Arg());
              continue;
            }

            unsigned target_off = 0;
            if (off_str.getAsInteger(10, target_off))
              return std::nullopt;

            bool found = false;
            for (unsigned i = 0; i < caller_param_offsets.size() && i < Caller.arg_size();
                 ++i) {
              if (caller_param_offsets[i] == static_cast<int>(target_off)) {
                new_args.push_back(Caller.getArg(i));
                found = true;
                break;
              }
            }
            if (found)
              continue;

            if (auto *state_ptr = findStateOffsetPtrInFunction(Caller, target_off)) {
              new_args.push_back(
                  Builder.CreateLoad(i64_ty, state_ptr,
                                     "statefix." + llvm::Twine(target_off)));
              continue;
            }

            for (unsigned i = 0; i < b3_arg_offsets.size() && i < CI.arg_size(); ++i) {
              if (b3_arg_offsets[i] == target_off) {
                new_args.push_back(CI.getArgOperand(i));
                found = true;
                break;
              }
            }
            if (found)
              continue;

            return std::nullopt;
          }
          return new_args;
        };
        auto replaceCallWithArgs =
            [&](llvm::CallInst &CI, llvm::Function &Callee,
                llvm::ArrayRef<llvm::Value *> new_args) {
          auto *new_call = llvm::CallInst::Create(
              Callee.getFunctionType(), &Callee, new_args, CI.getName(),
              CI.getIterator());
          new_call->setCallingConv(CI.getCallingConv());
          new_call->setAttributes(CI.getAttributes());
          if (!CI.use_empty()) {
            if (CI.getType() == new_call->getType()) {
              CI.replaceAllUsesWith(new_call);
            } else if (llvm::isa<llvm::StructType>(new_call->getType())) {
              auto *ev = llvm::ExtractValueInst::Create(
                  new_call, {0}, "ret.primary",
                  std::next(new_call->getIterator()));
              CI.replaceAllUsesWith(ev);
            } else {
              CI.replaceAllUsesWith(llvm::PoisonValue::get(CI.getType()));
            }
          }
          CI.eraseFromParent();
        };
        unsigned fixup_count = 0;
        unsigned same_arity_fixup_count = 0;
        for (auto &F : *module) {
          if (!F.getName().ends_with("_native"))
            continue;
          llvm::SmallVector<int, 16> caller_param_offsets;
          if (auto attr = F.getFnAttribute("omill.param_state_offsets");
              attr.isValid() && attr.isStringAttribute()) {
            llvm::SmallVector<llvm::StringRef, 16> caller_offset_strs;
            attr.getValueAsString().split(caller_offset_strs, ',');
            for (auto &off_str : caller_offset_strs) {
              if (off_str == "stack" || off_str == "xmm") {
                caller_param_offsets.push_back(-1);
                continue;
              }
              unsigned off = 0;
              if (off_str.getAsInteger(10, off))
                caller_param_offsets.push_back(-1);
              else
                caller_param_offsets.push_back(static_cast<int>(off));
            }
          }
          for (auto &BB : F) {
            for (auto &I : llvm::make_early_inc_range(BB)) {
              auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
              if (!CI)
                continue;
              auto *callee = llvm::dyn_cast<llvm::Function>(
                  CI->getCalledOperand()->stripPointerCasts());
              if (!callee || !callee->getName().ends_with("_native"))
                continue;
              if (callee->hasFnAttribute("omill.vm_handler") &&
                  (F.hasFnAttribute("omill.vm_wrapper") ||
                   F.getFnAttribute("omill.vm_outlined_virtual_call").isValid()))
                continue;

              if (CI->arg_size() == callee->arg_size()) {
                if (callee->arg_size() == 5 &&
                    calleeReadsArg2AsStatePtr(*callee)) {
                  auto *arg2_ci =
                      llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(2));
                  if (arg2_ci && arg2_ci->isZero()) {
                    llvm::SmallVector<llvm::Value *, 5> shifted_args = {
                        CI->getArgOperand(0), CI->getArgOperand(1),
                        CI->getArgOperand(3), CI->getArgOperand(4),
                        llvm::ConstantInt::get(i64_ty, 0)};
                    replaceCallWithArgs(*CI, *callee, shifted_args);
                    ++same_arity_fixup_count;
                    continue;
                  }
                }

                auto maybe_new_args =
                    buildStateOrderedArgs(F, *CI, *callee, caller_param_offsets);
                if (!maybe_new_args)
                  continue;
                auto &new_args = *maybe_new_args;
                bool suspicious = false;
                for (unsigned arg_index = 0; arg_index < CI->arg_size(); ++arg_index) {
                  auto *old_arg = CI->getArgOperand(arg_index);
                  auto *new_arg = new_args[arg_index];
                  if ((llvm::isa<llvm::PoisonValue>(old_arg) ||
                       llvm::isa<llvm::UndefValue>(old_arg)) &&
                      old_arg != new_arg) {
                    suspicious = true;
                    break;
                  }
                  auto *old_ci = llvm::dyn_cast<llvm::ConstantInt>(old_arg);
                  auto *new_ci = llvm::dyn_cast<llvm::ConstantInt>(new_arg);
                  if (old_arg == new_arg)
                    continue;
                  if (old_ci && old_ci->isZero() && (!new_ci || !new_ci->isZero())) {
                    suspicious = true;
                    break;
                  }
                  if (old_ci && new_ci && old_ci->getValue() != new_ci->getValue()) {
                    suspicious = true;
                    break;
                  }
                  if (!old_ci && new_ci && new_ci->isZero()) {
                    // Do not eagerly rewrite good dataflow into zeros.
                    continue;
                  }
                }
                if (!suspicious)
                  continue;

                replaceCallWithArgs(*CI, *callee, new_args);
                ++same_arity_fixup_count;
                continue;
              }

              auto maybe_new_args =
                  buildStateOrderedArgs(F, *CI, *callee, caller_param_offsets);
              if (!maybe_new_args)
                continue;
              replaceCallWithArgs(*CI, *callee, *maybe_new_args);
              ++fixup_count;
            }
          }
        }
        if (fixup_count > 0 || same_arity_fixup_count > 0)
          errs() << "Fixed " << fixup_count
                 << " B3 dispatch calls with mismatched arg counts and "
                 << same_arity_fixup_count
                 << " suspicious same-arity native calls\n";
      }

      syncOutlinedVirtualCalleeRegistry();


      unsigned created_hash_resolved = 0;
      unsigned created_nested_helper = 0;
      for (const auto &entry : outlined_virtual_callee_records) {
        const auto &record = entry.getValue();
        if (record.first_round != round + 1)
          continue;
        if (record.kind == "hash_resolved")
          ++created_hash_resolved;
        else if (record.kind == "nested_helper")
          ++created_nested_helper;
      }

      errs() << "Late discovery round " << (round + 1) << " complete";
      if (created_hash_resolved > 0 || created_nested_helper > 0) {
        errs() << " (outlined virtual callees: hash="
               << created_hash_resolved
               << ", nested=" << created_nested_helper << ")";
      }
      errs() << "\n";
      events.emitInfo("late_discovery_round_completed",
                      "late discovery round completed",
                      {{"round", static_cast<int64_t>(round + 1)},
                       {"outlined_hash_resolved",
                        static_cast<int64_t>(created_hash_resolved)},
                       {"outlined_nested_helper",
                        static_cast<int64_t>(created_nested_helper)},
                       {"outlined_total",
                        static_cast<int64_t>(outlined_virtual_callee_records.size())}});
    }
  }

  if (OmillTimePasses)
    TimingHandler.print();

  if (preserve_lift_infrastructure) {
    ModulePassManager MPM;
    omill::buildLiftInfrastructureCleanupPipeline(MPM);
    MPM.run(*module, MAM);
  }

  // Some late lifting/materialization shapes still leave stale PHI incoming
  // edges after CFG rewrites. Repair them before verification so no-ABI
  // checkpoints and downstream ABI replay can consume valid textual IR.
  omill::repairMalformedPHIs(*module);
  MAM.invalidate(*module, llvm::PreservedAnalyses::none());

  // Verify (use nullptr to avoid crash in SlotTracker on corrupted modules)
  const bool debug_public_root_seeds =
      parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
  bool module_invalid_before_late_cleanup =
      verifyModule(*module, debug_public_root_seeds ? &errs() : nullptr);
  const bool disable_recursive_output_recovery =
      parseBoolEnv("OMILL_DISABLE_RECURSIVE_OUTPUT_RECOVERY")
          .value_or(false);
  const bool allow_noabi_postmain_rounds =
      !module_invalid_before_late_cleanup &&
      !disable_recursive_output_recovery;
  const bool allow_abi_postmain_rounds =
      !module_invalid_before_late_cleanup &&
      !disable_recursive_output_recovery;
  if (module_invalid_before_late_cleanup) {
    errs() << "WARNING: module verification failed (use --verify-each to "
              "identify the culprit pass)\n";
    events.emitWarn("module_verify_warning",
                    "module verification failed after full run");
  }

  // Late cleanup: replace sentinel data constants with poison, DCE.
  const bool skip_late_cleanup =
      parseBoolEnv("OMILL_SKIP_LATE_CLEANUP").value_or(false);
  if (!module_invalid_before_late_cleanup && !hasOpenOutputRootHazards() &&
      !skip_late_cleanup) {
    ModulePassManager MPM;
    omill::buildLateCleanupPipeline(MPM, opts);
    __try {
      MPM.run(*module, MAM);
    } __except (1) {
      errs() << "WARNING: late cleanup pipeline crashed; continuing with current "
                "module state\n";
      events.emitWarn("late_cleanup_crashed",
                      "late cleanup pipeline crashed", {});
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    }
  } else if (events.detailed()) {
    if (skip_late_cleanup) {
      events.emitInfo("late_cleanup_skipped",
                      "skipped late cleanup by configuration");
    } else {
      events.emitInfo("late_cleanup_skipped_for_open_output_root",
                      module_invalid_before_late_cleanup
                          ? "skipped late cleanup for verifier-broken module"
                          : "skipped late cleanup for open output root");
    }
  }

  if (!module_invalid_before_late_cleanup && NoABI &&
      devirtualization_plan.enable_devirtualization &&
      opts.require_remill_normalization &&
      !parseBoolEnv("OMILL_SKIP_NOABI_FINAL_REMILL_NORMALIZATION")
           .value_or(false)) {
    ModulePassManager MPM;
    omill::RemillNormalizationOrchestrator normalization;
    normalization.appendToPipeline(
        MPM, omill::RemillNormalizationRequest{
                 omill::RemillNormalizationEpoch::kFinalVerification,
                 /*no_abi_mode=*/true,
                 /*aggressive_folding=*/true,
                 opts.scope_predicate,
                 /*include_semantic_helpers=*/true});
    MPM.run(*module, MAM);
    omill::repairMalformedPHIs(*module);
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
  }

  auto annotateOutputRootTerminalBoundaryProbeChains = [&]() {
    if (RawBinary || NoABI)
      return;
    if (parseBoolEnv("OMILL_SKIP_TERMINAL_BOUNDARY_SIDE_PROBE")
            .value_or(false)) {
      return;
    }

    const bool debug_terminal_probe =
        parseBoolEnv("OMILL_DEBUG_TERMINAL_BOUNDARY_SIDE_PROBE")
            .value_or(false);
    constexpr size_t kMaxUniqueProbeTargets = 4;
    constexpr unsigned kMaxProbeDepth = 4;

    llvm::SmallVector<std::pair<llvm::Function *, uint64_t>, 8> roots;
    llvm::SmallVector<uint64_t, 8> unique_targets;
    llvm::DenseSet<uint64_t> seen_targets;

    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;
      uint64_t target_pc = 0;
      auto target_attr = F.getFnAttribute("omill.terminal_boundary_target_va");
      if (target_attr.isValid()) {
        if (target_attr.getValueAsString().getAsInteger(16, target_pc))
          target_pc = 0;
      }
      if (target_pc == 0) {
        auto candidate_attr =
            F.getFnAttribute("omill.terminal_boundary_candidate_pc");
        if (candidate_attr.isValid() &&
            !candidate_attr.getValueAsString().getAsInteger(16, target_pc)) {
          // target_pc filled from fallback candidate attr
        }
      }
      if (target_pc == 0)
        continue;
      roots.emplace_back(&F, target_pc);
      if (seen_targets.insert(target_pc).second &&
          unique_targets.size() < kMaxUniqueProbeTargets) {
        unique_targets.push_back(target_pc);
      }
    }

    if (unique_targets.empty())
      return;

    llvm::DenseMap<uint64_t, TerminalBoundaryProbeResult> probe_results;
    auto probeSingleTarget =
        [&](uint64_t target_pc) -> std::optional<TerminalBoundaryProbeResult> {
      if (auto it = probe_results.find(target_pc); it != probe_results.end())
        return it->second;

      SmallString<256> temp_ll_path;
      if (sys::fs::createTemporaryFile("omill_terminal_probe", "ll",
                                       temp_ll_path)) {
        return std::nullopt;
      }

      llvm::SmallVector<std::string, 16> arg_storage;
      arg_storage.emplace_back(argv[0]);
      arg_storage.emplace_back(InputFilename);
      arg_storage.emplace_back("--va");
      arg_storage.emplace_back(llvm::utohexstr(target_pc));
      if (opts.use_block_lifting)
        arg_storage.emplace_back("--block-lift");
      if (devirtualization_plan.enable_devirtualization)
        arg_storage.emplace_back("--devirtualize");
      if (opts.generic_static_devirtualize) {
        arg_storage.emplace_back("--generic-static-devirtualize");
      }
      arg_storage.emplace_back("-o");
      arg_storage.emplace_back(temp_ll_path.str().str());

      llvm::SmallVector<llvm::StringRef, 16> argv_refs;
      argv_refs.reserve(arg_storage.size());
      for (const auto &arg : arg_storage)
        argv_refs.push_back(arg);

      std::string err_msg;
      bool exec_failed = false;
      ScopedEnvOverride skip_nested_probe(
          "OMILL_SKIP_TERMINAL_BOUNDARY_SIDE_PROBE", "1");
      int rc = llvm::sys::ExecuteAndWait(argv_refs.front(), argv_refs,
                                         std::nullopt, {}, 0, 0,
                                         &err_msg, &exec_failed);
      if (debug_terminal_probe) {
        errs() << "[terminal-side-probe] target=0x"
               << Twine::utohexstr(target_pc) << " rc=" << rc
               << " exec_failed=" << (exec_failed ? 1 : 0) << "\n";
      }
      if (rc != 0 || exec_failed) {
        sys::fs::remove(temp_ll_path);
        return std::nullopt;
      }

      auto buf_or_err = MemoryBuffer::getFile(temp_ll_path);
      sys::fs::remove(temp_ll_path);
      if (!buf_or_err)
        return std::nullopt;

      auto parsed =
          parseTerminalBoundaryProbeIR((*buf_or_err)->getBuffer(), target_pc);
      if (!parsed)
        return std::nullopt;
      probe_results[target_pc] = *parsed;
      return *parsed;
    };

    llvm::DenseMap<uint64_t, TerminalBoundaryProbeChain> probe_chains;
    for (uint64_t target_pc : unique_targets) {
      TerminalBoundaryProbeChain chain;
      chain.chain_pcs.push_back(target_pc);
      llvm::DenseMap<uint64_t, unsigned> path_index;
      path_index[target_pc] = 0;
      uint64_t current_pc = target_pc;

      for (unsigned depth = 0; depth < kMaxProbeDepth; ++depth) {
        auto single_probe = probeSingleTarget(current_pc);
        if (!single_probe || single_probe->next_target_pc == 0)
          break;

        if (single_probe->cycle && !chain.cycle)
          chain.cycle = *single_probe->cycle;
        if (single_probe->canonical_cycle_pc && !chain.canonical_cycle_pc)
          chain.canonical_cycle_pc = *single_probe->canonical_cycle_pc;

        const uint64_t next_pc = single_probe->next_target_pc;
        if (auto it = path_index.find(next_pc); it != path_index.end()) {
          llvm::SmallVector<uint64_t, 8> cycle_pcs;
          for (unsigned i = it->second; i < chain.chain_pcs.size(); ++i)
            cycle_pcs.push_back(chain.chain_pcs[i]);
          if (!cycle_pcs.empty()) {
            chain.cycle = joinHexPCChain(cycle_pcs);
            chain.canonical_cycle_pc = *llvm::min_element(cycle_pcs);
          }
          break;
        }

        chain.chain_pcs.push_back(next_pc);
        path_index[next_pc] = chain.chain_pcs.size() - 1;
        current_pc = next_pc;
      }

      probe_chains[target_pc] = std::move(chain);
    }

    if (probe_chains.empty())
      return;

    static constexpr llvm::StringLiteral kNextHopAttr =
        "omill.terminal_boundary_next_hop_target_va";
    static constexpr llvm::StringLiteral kProbeChainAttr =
        "omill.terminal_boundary_probe_chain";
    static constexpr llvm::StringLiteral kProbeCycleAttr =
        "omill.terminal_boundary_probe_cycle";
    static constexpr llvm::StringLiteral kProbeCycleLenAttr =
        "omill.terminal_boundary_probe_cycle_len";
    static constexpr llvm::StringLiteral kProbeCycleCanonicalAttr =
        "omill.terminal_boundary_probe_cycle_canonical_target_va";
    static constexpr llvm::StringLiteral kNextHopCycleAttr =
        "omill.terminal_boundary_next_hop_cycle";
    static constexpr llvm::StringLiteral kNextHopCycleCanonicalAttr =
        "omill.terminal_boundary_next_hop_cycle_canonical_target_va";
    static constexpr llvm::StringLiteral kNamedMetadata =
        "omill.terminal_boundary_probe_chains";

    if (auto *old_md = module->getNamedMetadata(kNamedMetadata))
      module->eraseNamedMetadata(old_md);
    auto *named_md = module->getOrInsertNamedMetadata(kNamedMetadata);
    auto *i64_ty = llvm::Type::getInt64Ty(ctx);

    for (const auto &[F, target_pc] : roots) {
      auto it = probe_chains.find(target_pc);
      if (it == probe_chains.end() || it->second.chain_pcs.empty())
        continue;
      const auto &probe = it->second;
      if (probe.chain_pcs.size() >= 2)
        F->addFnAttr(kNextHopAttr, llvm::utohexstr(probe.chain_pcs[1]));
      F->addFnAttr(kProbeChainAttr, joinHexPCChain(probe.chain_pcs));
      if (probe.cycle.has_value()) {
        F->addFnAttr(kProbeCycleAttr, *probe.cycle);
        llvm::SmallVector<llvm::StringRef, 8> cycle_parts;
        llvm::StringRef(*probe.cycle).split(cycle_parts, ',');
        F->addFnAttr(kProbeCycleLenAttr, std::to_string(cycle_parts.size()));
      }
      if (probe.canonical_cycle_pc.has_value()) {
        F->addFnAttr(kProbeCycleCanonicalAttr,
                     llvm::utohexstr(*probe.canonical_cycle_pc));
      }
      if (probe.cycle.has_value())
        F->addFnAttr(kNextHopCycleAttr, *probe.cycle);
      if (probe.canonical_cycle_pc.has_value()) {
        F->addFnAttr(kNextHopCycleCanonicalAttr,
                     llvm::utohexstr(*probe.canonical_cycle_pc));
      }

      llvm::SmallVector<llvm::Metadata *, 12> fields;
      fields.push_back(llvm::MDString::get(ctx, F->getName()));
      for (uint64_t pc : probe.chain_pcs) {
        fields.push_back(llvm::ConstantAsMetadata::get(
            llvm::ConstantInt::get(i64_ty, pc)));
      }
      if (probe.cycle.has_value())
        fields.push_back(llvm::MDString::get(ctx, *probe.cycle));
      named_md->addOperand(llvm::MDTuple::get(ctx, fields));
    }
  };

  auto maybeRerunLateCleanupForCanonicalTerminalBoundaryCycle = [&]() {
    if (RawBinary || NoABI)
      return;

    auto parseFnHexAttr = [](const llvm::Function &F,
                             llvm::StringRef name) -> std::optional<uint64_t> {
      auto attr = F.getFnAttribute(name);
      if (!attr.isValid())
        return std::nullopt;
      uint64_t value = 0;
      if (attr.getValueAsString().getAsInteger(16, value) || value == 0)
        return std::nullopt;
      return value;
    };

    bool need_rerun = false;
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;

      auto canonical_pc = parseFnHexAttr(
          F, "omill.terminal_boundary_probe_cycle_canonical_target_va");
      if (!canonical_pc)
        continue;

      auto current_pc =
          parseFnHexAttr(F, "omill.terminal_boundary_target_va");
      if (!current_pc)
        current_pc =
            parseFnHexAttr(F, "omill.terminal_boundary_candidate_pc");
      if (!current_pc || *current_pc == *canonical_pc)
        continue;

      need_rerun = true;
      break;
    }

    if (!need_rerun)
      return;

    if (events.enabled()) {
      events.emitInfo("late_cleanup_rerun_started",
                      "rerunning late cleanup for canonical boundary cycles");
    }
    ModulePassManager MPM;
    omill::buildLateCleanupPipeline(MPM, opts);
    MPM.run(*module, MAM);
  };

  auto clearTerminalBoundaryAttrs = [&](llvm::Function &F) {
    static constexpr llvm::StringLiteral kAttrs[] = {
        "omill.terminal_boundary_count",
        "omill.terminal_boundary_summary",
        "omill.terminal_boundary_kind",
        "omill.terminal_boundary_target_va",
        "omill.terminal_boundary_nearby_entry_va",
        "omill.terminal_boundary_candidate_pc",
        "omill.terminal_boundary_original_target_va",
        "omill.terminal_boundary_cycle",
        "omill.terminal_boundary_cycle_len",
        "omill.terminal_boundary_cycle_canonical_target_va",
        "omill.terminal_boundary_next_hop_target_va",
        "omill.terminal_boundary_probe_chain",
        "omill.terminal_boundary_probe_cycle",
        "omill.terminal_boundary_probe_cycle_len",
        "omill.terminal_boundary_probe_cycle_canonical_target_va",
        "omill.terminal_boundary_next_hop_cycle",
        "omill.terminal_boundary_next_hop_cycle_canonical_target_va",
    };
    for (auto attr_name : kAttrs)
      F.removeFnAttr(attr_name);
  };

  const bool debug_secondary_recovery =
      parseBoolEnv("OMILL_DEBUG_TERMINAL_BOUNDARY_SECONDARY_ROOT_RECOVERY")
          .value_or(false);

  auto setTerminalBoundaryRecoveryAttrs =
      [&](llvm::Function &F, const TerminalBoundaryRecoveryAttempt &attempt) {
        F.addFnAttr("omill.terminal_boundary_recovery_status",
                    omill::terminalBoundaryRecoveryStatusName(attempt.status));
        F.addFnAttr("omill.terminal_boundary_recovery_target_va",
                    llvm::utohexstr(attempt.target_pc));
        F.addFnAttr("omill.terminal_boundary_recovery_summary",
                    attempt.summary);
      };

  struct TerminalBoundaryChildLiftResult {
    std::string ir_text;
    std::string model_text;
  };

  auto runTerminalBoundaryChildLift =
      [&](uint64_t target_pc, bool no_abi, bool enable_gsd,
          bool enable_recovery_mode,
          bool dump_virtual_model,
          bool allow_recursive_output_recovery = false,
          bool use_tight_recovery_bounds = false)
          -> std::optional<TerminalBoundaryChildLiftResult> {
        SmallString<256> temp_ll_path;
        if (sys::fs::createTemporaryFile("omill_terminal_recovery", "ll",
                                         temp_ll_path)) {
          return std::nullopt;
        }

        SmallString<256> temp_model_path;
        if (dump_virtual_model &&
            sys::fs::createTemporaryFile("omill_terminal_recovery", "model",
                                         temp_model_path)) {
          sys::fs::remove(temp_ll_path);
          return std::nullopt;
        }

        llvm::SmallVector<std::string, 16> arg_storage;
        arg_storage.emplace_back(argv[0]);
        arg_storage.emplace_back(InputFilename);
        arg_storage.emplace_back("--va");
        arg_storage.emplace_back(llvm::utohexstr(target_pc));
        if (opts.use_block_lifting)
          arg_storage.emplace_back("--block-lift");
        if (devirtualization_plan.enable_devirtualization &&
            !(enable_recovery_mode && use_tight_recovery_bounds))
          arg_storage.emplace_back("--devirtualize");
        if (no_abi)
          arg_storage.emplace_back("--no-abi");
        if (enable_gsd)
          arg_storage.emplace_back("--generic-static-devirtualize");
        arg_storage.emplace_back("-o");
        arg_storage.emplace_back(temp_ll_path.str().str());

        llvm::SmallVector<llvm::StringRef, 16> argv_refs;
        argv_refs.reserve(arg_storage.size());
        for (const auto &arg : arg_storage)
          argv_refs.push_back(arg);

        std::string err_msg;
        bool exec_failed = false;
        ScopedEnvOverride skip_nested_probe(
            "OMILL_SKIP_TERMINAL_BOUNDARY_SIDE_PROBE", "1");
        std::unique_ptr<ScopedEnvOverride> skip_late_output_target;
        std::unique_ptr<ScopedEnvOverride> skip_late_boundary_rerun;
        if (!allow_recursive_output_recovery) {
          skip_late_output_target = std::make_unique<ScopedEnvOverride>(
              "OMILL_SKIP_LATE_OUTPUT_ROOT_TARGET_RERUN", "1");
          skip_late_boundary_rerun = std::make_unique<ScopedEnvOverride>(
              "OMILL_SKIP_LATE_TERMINAL_BOUNDARY_RERUN", "1");
        }
        std::unique_ptr<ScopedEnvOverride> skip_secondary_root_recovery;
        if (!allow_recursive_output_recovery) {
          skip_secondary_root_recovery = std::make_unique<ScopedEnvOverride>(
              "OMILL_SKIP_TERMINAL_BOUNDARY_SECONDARY_ROOT_RECOVERY", "1");
        }
        std::unique_ptr<ScopedEnvOverride> disable_recursive_output_recovery;
        if (!allow_recursive_output_recovery) {
          disable_recursive_output_recovery =
              std::make_unique<ScopedEnvOverride>(
                  "OMILL_DISABLE_RECURSIVE_OUTPUT_RECOVERY", "1");
        }
        std::unique_ptr<ScopedEnvOverride> skip_always_inline;
        if ((no_abi || enable_recovery_mode) && !allow_recursive_output_recovery) {
          skip_always_inline = std::make_unique<ScopedEnvOverride>(
              "OMILL_SKIP_ALWAYS_INLINE", "1");
        }
        std::unique_ptr<ScopedEnvOverride> skip_devirtualization_epoch_recording;
        if (enable_recovery_mode) {
          skip_devirtualization_epoch_recording =
              std::make_unique<ScopedEnvOverride>(
                  "OMILL_SKIP_DEVIRTUALIZATION_EPOCH_RECORDING", "1");
        }
        std::unique_ptr<ScopedEnvOverride> recovery_mode_guard;
        std::unique_ptr<ScopedEnvOverride> recovery_root_guard;
        std::unique_ptr<ScopedEnvOverride> recovery_max_reachable_guard;
        std::unique_ptr<ScopedEnvOverride> recovery_max_iterations_guard;
        std::unique_ptr<ScopedEnvOverride> recovery_max_target_rounds_guard;
        std::unique_ptr<ScopedEnvOverride>
            skip_noabi_final_remill_normalization_guard;
        std::unique_ptr<ScopedEnvOverride> dump_model_guard;
        std::unique_ptr<ScopedEnvOverride> skip_block_merge_guard;
        std::optional<std::string> recovery_root_value;
        if (parseBoolEnv("OMILL_TERMINAL_BOUNDARY_CHILD_SKIP_BLOCK_MERGE")
                .value_or(false)) {
          skip_block_merge_guard = std::make_unique<ScopedEnvOverride>(
              "OMILL_SKIP_BLOCK_MERGE", "1");
        }
        if (enable_recovery_mode) {
          recovery_root_value = llvm::utohexstr(target_pc);
          recovery_mode_guard = std::make_unique<ScopedEnvOverride>(
              "OMILL_TERMINAL_BOUNDARY_RECOVERY", "1");
          recovery_root_guard = std::make_unique<ScopedEnvOverride>(
              "OMILL_TERMINAL_BOUNDARY_RECOVERY_ROOT_VA",
              recovery_root_value->c_str());
          const char *max_reachable =
              use_tight_recovery_bounds ? "24" : "128";
          const char *max_iterations =
              use_tight_recovery_bounds ? "2" : "8";
          const char *max_target_rounds =
              use_tight_recovery_bounds ? "1" : "6";
          recovery_max_reachable_guard = std::make_unique<ScopedEnvOverride>(
              "OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_REACHABLE", max_reachable);
          recovery_max_iterations_guard = std::make_unique<ScopedEnvOverride>(
              "OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_ITERATIONS",
              max_iterations);
          recovery_max_target_rounds_guard =
              std::make_unique<ScopedEnvOverride>(
                  "OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_NEW_TARGET_ROUNDS",
                  max_target_rounds);
          skip_noabi_final_remill_normalization_guard =
              std::make_unique<ScopedEnvOverride>(
                  "OMILL_SKIP_NOABI_FINAL_REMILL_NORMALIZATION", "1");
        }
        if (dump_virtual_model) {
          dump_model_guard = std::make_unique<ScopedEnvOverride>(
              "OMILL_DUMP_VIRTUAL_MODEL", temp_model_path.str().str().c_str());
        }

        const unsigned timeout_seconds =
            enable_recovery_mode
                ? (use_tight_recovery_bounds
                       ? 45u
                       : parseUnsignedEnv(
                             "OMILL_TERMINAL_BOUNDARY_RECOVERY_TIMEOUT_SECONDS")
                             .value_or(420u))
                : 180u;
        auto child_begin = std::chrono::steady_clock::now();
        if (debug_secondary_recovery) {
          errs() << "[terminal-recovery] child-start target=0x"
                 << llvm::utohexstr(target_pc)
                 << " no_abi=" << (no_abi ? 1 : 0)
                 << " gsd=" << (enable_gsd ? 1 : 0)
                 << " recovery=" << (enable_recovery_mode ? 1 : 0)
                 << " dump_model=" << (dump_virtual_model ? 1 : 0)
                 << " allow_recursive_output_recovery="
                 << (allow_recursive_output_recovery ? 1 : 0) << "\n";
        }
        int rc = llvm::sys::ExecuteAndWait(argv_refs.front(), argv_refs,
                                           std::nullopt, {}, timeout_seconds, 0,
                                           &err_msg, &exec_failed);
        if (debug_secondary_recovery) {
          auto elapsed_ms =
              std::chrono::duration_cast<std::chrono::milliseconds>(
                  std::chrono::steady_clock::now() - child_begin)
                  .count();
          errs() << "[terminal-recovery] child-done target=0x"
                 << llvm::utohexstr(target_pc)
                 << " rc=" << rc
                 << " exec_failed=" << (exec_failed ? 1 : 0)
                 << " elapsed_ms=" << elapsed_ms << "\n";
        }
        const bool child_failed = (rc != 0 || exec_failed);
        if (child_failed && !enable_recovery_mode) {
          sys::fs::remove(temp_ll_path);
          if (dump_virtual_model)
            sys::fs::remove(temp_model_path);
          return std::nullopt;
        }

        auto buf_or_err = MemoryBuffer::getFile(temp_ll_path);
        sys::fs::remove(temp_ll_path);
        if (!buf_or_err) {
          if (dump_virtual_model)
            sys::fs::remove(temp_model_path);
          return std::nullopt;
        }

        TerminalBoundaryChildLiftResult result;
        result.ir_text = (*buf_or_err)->getBuffer().str();
        if (dump_virtual_model) {
          auto model_or_err = MemoryBuffer::getFile(temp_model_path);
          sys::fs::remove(temp_model_path);
          if (model_or_err)
            result.model_text = (*model_or_err)->getBuffer().str();
        }
        if (child_failed && debug_secondary_recovery) {
          errs() << "[terminal-recovery] child-partial-reuse target=0x"
                 << llvm::utohexstr(target_pc) << " rc=" << rc
                 << " exec_failed=" << (exec_failed ? 1 : 0) << "\n";
        }
        return result;
      };

  auto importSimpleExecutableChildRoot =
      [&](uint64_t target_pc, const omill::ChildLiftArtifact &artifact,
          const omill::ChildImportPlan &import_plan,
          llvm::StringRef name_prefix,
          bool shallow_closure = false) -> llvm::Function * {
        llvm::StringRef imported_ir = artifact.ir_text;
        llvm::SMDiagnostic parse_error;
        auto imported_module =
            llvm::parseAssemblyString(imported_ir, parse_error, ctx);
        if (!imported_module) {
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] exec-import-parse-failed target=0x"
                   << llvm::utohexstr(target_pc) << "\n";
          }
          return nullptr;
        }



        auto findImportedRootByPc = [&](llvm::Module &M,
                                        uint64_t pc) -> llvm::Function * {
          const std::string target_hex = llvm::utohexstr(pc);
          const std::string target_hex_lower =
              llvm::StringRef(target_hex).lower();
          for (const std::string &name :
               {"sub_" + target_hex, "sub_" + target_hex_lower,
                "blk_" + target_hex, "blk_" + target_hex_lower,
                "block_" + target_hex, "block_" + target_hex_lower}) {
            if (auto *fn = M.getFunction(name); fn && !fn->isDeclaration())
              return fn;
          }
          for (auto &F : M) {
            if (F.isDeclaration())
              continue;
            if (omill::extractEntryVA(F.getName()) == pc ||
                omill::extractBlockPC(F.getName()) == pc) {
              return &F;
            }
          }
          return nullptr;
        };

        const uint64_t selected_root_pc =
            artifact.selected_root_pc.value_or(target_pc);
        auto *root = findImportedRootByPc(*imported_module, selected_root_pc);
        if (!root || root->isDeclaration()) {
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] exec-import-root-missing target=0x"
                   << llvm::utohexstr(target_pc)
                   << " selected=0x" << llvm::utohexstr(selected_root_pc)
                   << "\n";
          }
          return nullptr;
        }

        auto makeUniqueImportName = [&](llvm::StringRef base_name) {
          std::string candidate = (name_prefix + base_name).str();
          if (!module->getFunction(candidate) &&
              !imported_module->getFunction(candidate)) {
            return candidate;
          }
          for (unsigned i = 1; i < 100; ++i) {
            auto numbered = candidate + "." + std::to_string(i);
            if (!module->getFunction(numbered) &&
                !imported_module->getFunction(numbered)) {
              return numbered;
            }
          }
          return candidate;
        };

        auto makeTargetImportBaseName = [&](llvm::StringRef source_name) {
          std::string target_hex = llvm::utohexstr(target_pc);
          if (source_name.starts_with("blk_"))
            return (llvm::Twine("blk_") + target_hex).str();
          if (source_name.starts_with("block_"))
            return (llvm::Twine("block_") + target_hex).str();
          return (llvm::Twine("sub_") + target_hex).str();
        };

        auto clearImportedAttrs = [&](llvm::Function &F) {
          clearTerminalBoundaryAttrs(F);
          F.removeFnAttr("omill.output_root");
          F.removeFnAttr("omill.internal_output_root");
          F.removeFnAttr("omill.closed_root_slice");
          F.removeFnAttr("omill.closed_root_slice_root");
          F.removeFnAttr("omill.vm_unresolved_continuation_count");
          F.removeFnAttr("omill.vm_unresolved_continuation_targets");
          F.removeFnAttr("omill.vm_unresolved_continuation_summary");
        };
        auto isAllowedModeledBoundaryDecl = [&](llvm::StringRef name) {
          return name.starts_with("omill_executable_target_") ||
                 name.starts_with("omill_native_target_") ||
                 name.starts_with("omill_vm_enter_target_") ||
                 name.starts_with("omill_native_boundary_") ||
                 name.starts_with("omill_vm_enter_boundary_");
        };
        auto preserveExistingModeledBoundaryDeclAttrs =
            [&](llvm::Function &decl, const llvm::Function &callee) {
              if (!isAllowedModeledBoundaryDecl(decl.getName()) ||
                  decl.getName() != callee.getName()) {
                return false;
              }
              // Imported child closures may reference the same modeled boundary
              // placeholder names as the parent module. Reuse the existing
              // declaration, but keep its parent-owned boundary metadata.
              decl.setCallingConv(callee.getCallingConv());
              return true;
            };
        llvm::StringSet<> allowed_decl_callees;
        for (const auto &name : import_plan.allowed_declaration_callees)
          allowed_decl_callees.insert(name);
        for (const auto &name : import_plan.lowering_helper_callees)
          allowed_decl_callees.insert(name);

        llvm::StringSet<> allowed_slice_names;
        for (const auto &name : artifact.closed_slice_function_names) {
          allowed_slice_names.insert(name);
        }

        llvm::SmallVector<llvm::Function *, 16> closure;
        llvm::SmallVector<llvm::Function *, 16> worklist;
        llvm::SmallPtrSet<llvm::Function *, 16> visited;
        worklist.push_back(root);
        while (!worklist.empty()) {
          auto *F = worklist.pop_back_val();
          if (!F || F->isDeclaration() || !visited.insert(F).second)
            continue;
          const bool same_selected_pc_clone =
              omill::extractEntryVA(F->getName()) == selected_root_pc ||
              omill::extractBlockPC(F->getName()) == selected_root_pc;
          if (!allowed_slice_names.empty() &&
              (F->getName().starts_with("sub_") ||
               F->getName().starts_with("blk_") ||
               F->getName().starts_with("block_") ||
               F->getName().starts_with("__lifted_")) &&
              !allowed_slice_names.count(F->getName()) &&
              !same_selected_pc_clone) {
            if (debug_secondary_recovery) {
              errs() << "[terminal-recovery] exec-import-disallowed-fn target=0x"
                     << llvm::utohexstr(target_pc)
                     << " selected=0x" << llvm::utohexstr(selected_root_pc)
                     << " fn=" << F->getName() << "\n";
            }
            return nullptr;
          }
          closure.push_back(F);
          for (auto &BB : *F) {
            for (auto &I : BB) {
              for (llvm::Value *operand : I.operands()) {
                auto *GV = llvm::dyn_cast<llvm::GlobalValue>(operand);
                if (!GV)
                  continue;
                if (auto *callee = llvm::dyn_cast<llvm::Function>(GV)) {
                  if (callee->isDeclaration()) {
                    if (callee->isIntrinsic() ||
                        callee->getName().starts_with("llvm.") ||
                        isAllowedModeledBoundaryDecl(callee->getName()) ||
                        allowed_decl_callees.count(callee->getName())) {
                      continue;
                    }
                    if (debug_secondary_recovery) {
                      errs() << "[terminal-recovery] exec-import-decl-reject target=0x"
                             << llvm::utohexstr(target_pc)
                             << " selected=0x" << llvm::utohexstr(selected_root_pc)
                             << " callee=" << callee->getName() << "\n";
                    }
                    return nullptr;
                  }
                  if (!shallow_closure)
                    worklist.push_back(callee);
                  continue;
                }
                if (auto *global = llvm::dyn_cast<llvm::GlobalVariable>(GV)) {
                  if (global->getName().starts_with("llvm."))
                    continue;
                  continue;
                }
              }
            }
          }
        }
        if (closure.empty()) {
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] exec-import-empty-closure target=0x"
                   << llvm::utohexstr(target_pc)
                   << " selected=0x" << llvm::utohexstr(selected_root_pc)
                   << "\n";
          }
          return nullptr;
        }

        llvm::DenseMap<const llvm::Function *, llvm::Function *> cloned;
        llvm::DenseMap<const llvm::GlobalValue *, llvm::GlobalValue *> decl_map;
        llvm::Function *dst_root = nullptr;
        for (auto *src_fn : closure) {
          std::string import_base_name_storage;
          llvm::StringRef import_base_name;
          if (src_fn == root) {
            import_base_name_storage =
                makeTargetImportBaseName(src_fn->getName());
            import_base_name = import_base_name_storage;
          } else {
            import_base_name = src_fn->getName();
          }
          auto *dst_fn = llvm::Function::Create(
              src_fn->getFunctionType(), llvm::GlobalValue::InternalLinkage,
              makeUniqueImportName(import_base_name), *module);
          dst_fn->copyAttributesFrom(src_fn);
          clearImportedAttrs(*dst_fn);
          cloned[src_fn] = dst_fn;
          if (src_fn == root)
            dst_root = dst_fn;
        }
        if (!dst_root) {
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] exec-import-no-dst-root target=0x"
                   << llvm::utohexstr(target_pc)
                   << " selected=0x" << llvm::utohexstr(selected_root_pc)
                   << "\n";
          }
          return nullptr;
        }

        for (auto *src_fn : closure) {
          for (auto &BB : *src_fn) {
            for (auto &I : BB) {
              for (llvm::Value *operand : I.operands()) {
                auto *GV = llvm::dyn_cast<llvm::GlobalValue>(operand);
                if (!GV || decl_map.count(GV))
                  continue;
                if (auto *callee = llvm::dyn_cast<llvm::Function>(GV)) {
                  if (auto it = cloned.find(callee); it != cloned.end()) {
                    decl_map[GV] = it->second;
                    continue;
                  }
                  auto *decl = module->getFunction(callee->getName());
                  if (!decl) {
                    decl = llvm::Function::Create(
                        callee->getFunctionType(), callee->getLinkage(),
                        callee->getName(), *module);
                    decl->copyAttributesFrom(callee);
                  } else if (!preserveExistingModeledBoundaryDeclAttrs(
                                 *decl, *callee)) {
                    decl->copyAttributesFrom(callee);
                  }
                  decl_map[GV] = decl;
                  continue;
                }
                if (auto *global = llvm::dyn_cast<llvm::GlobalVariable>(GV)) {
                  auto *mapped_global = module->getGlobalVariable(global->getName());
                  if (!mapped_global) {
                    mapped_global = new llvm::GlobalVariable(
                        *module, global->getValueType(), global->isConstant(),
                        global->getLinkage(),
                        global->hasInitializer() ? global->getInitializer() : nullptr,
                        global->getName(), nullptr,
                        global->getThreadLocalMode(),
                        global->getAddressSpace());
                    mapped_global->copyAttributesFrom(global);
                    if (!global->hasInitializer())
                      mapped_global->setExternallyInitialized(true);
                  }
                  decl_map[GV] = mapped_global;
                }
              }
            }
          }
        }

        for (auto *src_fn : closure) {
          auto *dst_fn = cloned.lookup(src_fn);
          llvm::ValueToValueMapTy vmap;
          auto src_arg_it = src_fn->arg_begin();
          auto dst_arg_it = dst_fn->arg_begin();
          for (; src_arg_it != src_fn->arg_end() &&
                 dst_arg_it != dst_fn->arg_end();
               ++src_arg_it, ++dst_arg_it) {
            vmap[&*src_arg_it] = &*dst_arg_it;
          }
          for (const auto &decl_entry : decl_map)
            vmap[const_cast<llvm::GlobalValue *>(decl_entry.first)] =
                decl_entry.second;
          llvm::SmallVector<llvm::ReturnInst *, 4> returns;
          llvm::CloneFunctionInto(
              dst_fn, src_fn, vmap,
              llvm::CloneFunctionChangeType::DifferentModule, returns);
          clearImportedAttrs(*dst_fn);
        }

        omill::ExecutableTargetFact fact;
        fact.raw_target_pc = target_pc;
        fact.effective_target_pc = selected_root_pc;
        fact.kind = omill::ExecutableTargetKind::kLiftableEntry;
        fact.trust = omill::ExecutableTargetTrust::kTrustedEntry;
        if (selected_root_pc != target_pc)
          fact.canonical_owner_pc = selected_root_pc;
        writeExecutableTargetFact(*dst_root, fact);
        if (debug_secondary_recovery) {
          errs() << "[terminal-recovery] exec-import-ok target=0x"
                 << llvm::utohexstr(target_pc)
                 << " selected=0x" << llvm::utohexstr(selected_root_pc)
                 << " root=" << dst_root->getName()
                 << " funcs=" << closure.size() << "\n";
        }
        return dst_root;
      };

  auto importBoundedContinuationSnapshotSlice =
      [&](uint64_t target_pc, const omill::BinaryRegionSnapshot &snapshot,
          const omill::ChildImportPlan &import_plan) -> llvm::Function * {
        if (!block_lifter || snapshot.blocks_by_pc.empty())
          return nullptr;

        auto lookupDefinedLiftedTarget = [&](uint64_t pc) -> llvm::Function * {
          const std::string target_hex = llvm::utohexstr(pc);
          const std::string target_hex_lower =
              llvm::StringRef(target_hex).lower();
          for (const std::string &name :
               {"blk_" + target_hex, "blk_" + target_hex_lower,
                "block_" + target_hex, "block_" + target_hex_lower,
                "sub_" + target_hex, "sub_" + target_hex_lower}) {
            if (auto *fn = module->getFunction(name); fn && !fn->isDeclaration())
              return fn;
          }
          return nullptr;
        };

        const uint64_t selected_root_pc =
            import_plan.selected_root_pc.value_or(snapshot.entry_pc ?
                                                      snapshot.entry_pc : target_pc);
        llvm::SmallVector<uint64_t, 32> ordered_blocks;
        llvm::SmallDenseSet<uint64_t, 32> seen_blocks;
        auto append_block = [&](uint64_t pc) {
          if (!pc || !seen_blocks.insert(pc).second)
            return;
          ordered_blocks.push_back(pc);
        };
        append_block(selected_root_pc);
        append_block(target_pc);
        for (uint64_t pc : snapshot.visited_block_pcs)
          append_block(pc);
        for (const auto &[pc, block] : snapshot.blocks_by_pc) {
          (void)block;
          append_block(pc);
        }
        if (ordered_blocks.empty())
          return nullptr;

        unsigned newly_lifted = 0;
        for (uint64_t pc : ordered_blocks) {
          if (lookupDefinedLiftedTarget(pc))
            continue;
          bool lifted = false;
#if defined(_WIN32)
          __try {
#endif
            llvm::SmallVector<uint64_t, 4> discovered_targets;
            lifted = projection_lifter &&
                     projection_lifter->LiftBlock(pc, discovered_targets) !=
                         nullptr;
            if (lifted && iterative_session)
              iterative_session->noteLiftedTarget(pc);
#if defined(_WIN32)
          } __except (1) {
            lifted = false;
          }
#endif
          if (!lifted) {
            if (debug_secondary_recovery) {
              errs() << "[terminal-recovery] snapshot-import-lift-failed target=0x"
                     << llvm::utohexstr(target_pc) << " block=0x"
                     << llvm::utohexstr(pc) << "\n";
            }
            return nullptr;
          }
          ++newly_lifted;
        }

        auto *imported_root = lookupDefinedLiftedTarget(selected_root_pc);
        if (!imported_root)
          imported_root = lookupDefinedLiftedTarget(target_pc);
        if (!imported_root)
          return nullptr;

        clearTerminalBoundaryAttrs(*imported_root);
        imported_root->removeFnAttr("omill.output_root");
        imported_root->removeFnAttr("omill.internal_output_root");

        omill::ExecutableTargetFact fact;
        fact.raw_target_pc = target_pc;
        fact.effective_target_pc = selected_root_pc;
        fact.kind = omill::ExecutableTargetKind::kLiftableEntry;
        fact.trust = omill::ExecutableTargetTrust::kUntrustedExecutable;
        if (import_plan.proof) {
          if (import_plan.proof->is_exact_fallthrough) {
            fact.trust = omill::ExecutableTargetTrust::kExactFallthrough;
            fact.exact_fallthrough_target = true;
          } else if (import_plan.proof->confidence ==
                     omill::ContinuationConfidence::kTrusted) {
            fact.trust = omill::ExecutableTargetTrust::kTrustedEntry;
          }
        }
        if (selected_root_pc != target_pc)
          fact.canonical_owner_pc = selected_root_pc;
        writeExecutableTargetFact(*imported_root, fact);

        if (debug_secondary_recovery) {
          errs() << "[terminal-recovery] snapshot-import-ok target=0x"
                 << llvm::utohexstr(target_pc) << " selected=0x"
                 << llvm::utohexstr(selected_root_pc) << " root="
                 << imported_root->getName() << " blocks="
                 << snapshot.blocks_by_pc.size() << " lifted=" << newly_lifted
                 << "\n";
        }
        return imported_root;
      };


  std::map<uint64_t, llvm::Function *> imported_truthful_child_roots;
  llvm::DenseSet<uint64_t> attempted_truthful_child_targets;
  auto markImportedRecoveryChildClosure = [&](llvm::Function &root) {
    module->setModuleFlag(llvm::Module::Override,
                          "omill.closed_root_slice_scope", 1u);
    llvm::SmallVector<llvm::Function *, 32> worklist = {&root};
    llvm::SmallPtrSet<llvm::Function *, 32> visited;
    while (!worklist.empty()) {
      auto *current = worklist.pop_back_val();
      if (!current || current->isDeclaration() || !visited.insert(current).second)
        continue;
      current->addFnAttr("omill.closed_root_slice", "1");
      current->removeFnAttr(llvm::Attribute::NoInline);
      current->removeFnAttr(llvm::Attribute::OptimizeNone);
      if (!current->hasFnAttribute(llvm::Attribute::AlwaysInline))
        current->addFnAttr(llvm::Attribute::AlwaysInline);
      if (current == &root)
        current->addFnAttr("omill.closed_root_slice_root", "1");
      for (auto &BB : *current) {
        for (auto &I : BB) {
          if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
            if (auto *CI = llvm::dyn_cast<llvm::CallInst>(CB);
                CI && CI->isMustTailCall()) {
              if (auto *callee = CI->getCalledFunction();
                  callee && !callee->isDeclaration() &&
                  callee->getName().starts_with("__omill_recovered_child_")) {
                CI->setTailCallKind(llvm::CallInst::TCK_None);
              }
            }
            if (auto *callee = CB->getCalledFunction();
                callee && !callee->isDeclaration()) {
              worklist.push_back(callee);
            }
          }
          for (llvm::Value *operand : I.operands()) {
            auto *callee = llvm::dyn_cast<llvm::Function>(operand);
            if (callee && !callee->isDeclaration())
              worklist.push_back(callee);
          }
        }
      }
    }
  };
  llvm::DenseSet<uint64_t> imported_recovery_mode_truthful_targets;
  std::optional<uint64_t> latest_recovery_mode_truthful_target;





  std::function<llvm::Function *(uint64_t, bool, bool)>
      importTruthfulChildRootForTarget =
          [&](uint64_t target_pc, bool enable_recovery_mode = false,
              bool allow_trivial_self_loop = false) -> llvm::Function * {
        if (auto it = imported_truthful_child_roots.find(target_pc);
            it != imported_truthful_child_roots.end()) {
          return it->second;
        }
        if (events.detailed()) {
          events.emitInfo(
              "truthful_child_import_attempt",
              "attempting truthful child import",
              {{"target_pc",
                (llvm::Twine("0x") + llvm::utohexstr(target_pc)).str()},
               {"recovery_mode", enable_recovery_mode},
               {"allow_trivial_self_loop", allow_trivial_self_loop}});
        }
        if (attempted_truthful_child_targets.count(target_pc))
          return nullptr;
        attempted_truthful_child_targets.insert(target_pc);
        auto runTruthfulChildLift = [&](bool allow_recursive_output_recovery) {
          return runTerminalBoundaryChildLift(
              target_pc, /*no_abi=*/true,
              /*enable_gsd=*/enable_recovery_mode ? false
                                                 : opts.generic_static_devirtualize,
              /*enable_recovery_mode=*/enable_recovery_mode,
              /*dump_virtual_model=*/enable_recovery_mode,
              /*allow_recursive_output_recovery=*/allow_recursive_output_recovery,
              /*use_tight_recovery_bounds=*/enable_recovery_mode);
        };

        auto child = runTruthfulChildLift(enable_recovery_mode);
        if ((!child || child->ir_text.empty()) && enable_recovery_mode) {
          if (events.detailed()) {
            events.emitInfo(
                "truthful_child_import_retry",
                "retrying truthful child lift without recursive output recovery",
                {{"target_pc",
                  (llvm::Twine("0x") + llvm::utohexstr(target_pc)).str()}});
          }
          child = runTruthfulChildLift(/*allow_recursive_output_recovery=*/false);
        }
        if (!child || child->ir_text.empty()) {
          if (events.detailed()) {
            events.emitWarn(
                "truthful_child_import_failed",
                "truthful child lift produced no importable IR",
                {{"target_pc",
                  (llvm::Twine("0x") + llvm::utohexstr(target_pc)).str()},
                 {"reason", child ? "empty_ir" : "child_lift_failed"}});
          }
          return nullptr;
        }

        omill::ChildLiftArtifact raw_artifact;
        raw_artifact.target_pc = target_pc;
        raw_artifact.ir_text = child->ir_text;
        raw_artifact.model_text = child->model_text;

        auto selection = omill::selectExecutableChildImportArtifactForPlanning(
            ctx, raw_artifact, /*no_abi_mode=*/true);

        if (!allow_trivial_self_loop &&
            selection.artifact.selected_root_was_retargeted &&
            selection.artifact.selected_root_is_self_loop_only &&
            selection.artifact.frontier_target_pcs.size() == 1) {
          const uint64_t frontier_target =
              selection.artifact.frontier_target_pcs.front();
          if (frontier_target != 0 && frontier_target != target_pc) {
            if (auto *frontier_root = importTruthfulChildRootForTarget(
                    frontier_target, /*enable_recovery_mode=*/true,
                    /*allow_trivial_self_loop=*/false)) {
              imported_truthful_child_roots[target_pc] = frontier_root;
              return frontier_root;
            }
          }
        }


        if (events.detailed()) {
          llvm::json::Object payload;
          payload["target_pc"] =
              (llvm::Twine("0x") + llvm::utohexstr(target_pc)).str();
          if (selection.artifact.selected_root_pc) {
            payload["selected_root_pc"] =
                (llvm::Twine("0x") +
                 llvm::utohexstr(*selection.artifact.selected_root_pc))
                    .str();
          }
          payload["selected_root_name"] = selection.artifact.selected_root_name;
          payload["selected_root_was_retargeted"] =
              selection.artifact.selected_root_was_retargeted;
          payload["selected_root_is_self_loop_only"] =
              selection.artifact.selected_root_is_self_loop_only;
          payload["eligibility"] =
              static_cast<int64_t>(selection.plan.eligibility);
          payload["selection_detail"] =
              selection.artifact.selected_root_selection_detail;
          events.emitInfo("truthful_child_import_selected",
                          "selected truthful child import root",
                          std::move(payload));
        }


        llvm::SMDiagnostic parse_error;
        auto imported_module = llvm::parseAssemblyString(
            selection.artifact.ir_text, parse_error, ctx);
        if (!imported_module) {
          if (events.detailed()) {
            events.emitWarn(
                "truthful_child_import_failed",
                "selected truthful child IR failed to parse",
                {{"target_pc",
                  (llvm::Twine("0x") + llvm::utohexstr(target_pc)).str()},
                 {"reason", "selected_ir_parse_failed"}});
          }
          return nullptr;
        }

        auto resolveImportedRootFallback = [&](llvm::Module &M) -> llvm::Function * {
          auto findByPc = [&](uint64_t pc) -> llvm::Function * {
            if (!pc)
              return nullptr;
            for (auto &F : M) {
              if (F.isDeclaration())
                continue;
              if (omill::extractEntryVA(F.getName()) == pc ||
                  omill::extractBlockPC(F.getName()) == pc) {
                return &F;
              }
            }
            return nullptr;
          };

          if (enable_recovery_mode) {
            if (auto *F = findByPc(target_pc))
              return F;
          }
          if (!selection.artifact.selected_root_name.empty()) {
            if (auto *F = M.getFunction(selection.artifact.selected_root_name);
                F && !F->isDeclaration()) {
              return F;
            }
          }
          if (selection.artifact.selected_root_pc) {
            if (auto *F = findByPc(*selection.artifact.selected_root_pc))
              return F;
          }
          if (auto *F = findByPc(target_pc))
            return F;

          llvm::SmallVector<llvm::Function *, 8> output_roots;
          for (auto &F : M) {
            if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root") ||
                F.hasFnAttribute("omill.internal_output_root")) {
              continue;
            }
            output_roots.push_back(&F);
          }
          if (output_roots.empty()) {
            for (auto &F : M) {
              if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
                output_roots.push_back(&F);
            }
          }
          if (output_roots.size() == 1)
            return output_roots.front();
          for (auto *F : output_roots) {
            if (!F->getName().contains('.'))
              return F;
          }
          return nullptr;
        };

        llvm::Function *selected_root =
            resolveImportedRootFallback(*imported_module);
        if (!selected_root) {
          if (events.detailed()) {
            events.emitWarn(
                "truthful_child_import_failed",
                "selected truthful child root was missing from imported IR",
                {{"target_pc",
                  (llvm::Twine("0x") + llvm::utohexstr(target_pc)).str()},
                 {"reason", "selected_root_missing_after_parse"}});
          }
          return nullptr;
        }

        llvm::SmallVector<std::string, 32> defined_function_names;
        for (auto &F : *imported_module) {
          if (!F.isDeclaration())
            defined_function_names.push_back(F.getName().str());
        }


        llvm::SmallVector<std::string, 32> declaration_callees;
        bool has_omill_externals = false;
        bool has_runtime_dispatch_externals = false;
        for (auto &F : *imported_module) {
          if (!F.isDeclaration())
            continue;
          if (F.isIntrinsic() || F.getName().starts_with("llvm."))
            continue;
          declaration_callees.push_back(F.getName().str());
          if (F.getName().starts_with("omill_"))
            has_omill_externals = true;
          if (F.getName() == "__remill_function_call" ||
              F.getName() == "__remill_jump" ||
              omill::isDispatchIntrinsicName(F.getName())) {
            has_runtime_dispatch_externals = true;
          }
        }

        auto artifact = std::move(selection.artifact);
        artifact.selected_root_name = selected_root->getName().str();
        auto recomputeSelectedRootShape = [&](llvm::Function &root_fn) {
          bool saw_return = false;
          bool saw_non_intrinsic_call = false;
          bool saw_self_loop = false;
          for (auto &BB : root_fn) {
            if (auto *br = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
                br && br->isUnconditional() && br->getSuccessor(0) == &BB) {
              saw_self_loop = true;
            }
            for (auto &I : BB) {
              if (llvm::isa<llvm::ReturnInst>(&I)) {
                saw_return = true;
                continue;
              }
              auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
              if (!CB)
                continue;
              auto *callee = CB->getCalledFunction();
              if (!callee || !callee->isIntrinsic())
                saw_non_intrinsic_call = true;
            }
          }
          artifact.selected_root_has_structural_loop = saw_self_loop;
          artifact.selected_root_is_self_loop_only =
              saw_self_loop && !saw_return && !saw_non_intrinsic_call;
        };
        if (auto resolved_pc = omill::extractEntryVA(selected_root->getName());
            resolved_pc != 0) {
          artifact.selected_root_pc = resolved_pc;
        } else if (auto block_pc = omill::extractBlockPC(selected_root->getName());
                   block_pc != 0) {
          artifact.selected_root_pc = block_pc;
        }
        recomputeSelectedRootShape(*selected_root);
        artifact.reachable_declaration_callees.assign(
            declaration_callees.begin(), declaration_callees.end());
        artifact.import_safety =
            (has_omill_externals || has_runtime_dispatch_externals)
                ? omill::ChildImportClass::kBoundaryModeledChild
                : omill::ChildImportClass::kTrustedTerminalEntry;
        artifact.rejection_reason = omill::RecoveryRejectionReason::kNone;
        artifact.rejection_detail.clear();
        if (enable_recovery_mode && !defined_function_names.empty()) {
          artifact.closed_slice_function_names.assign(
              defined_function_names.begin(), defined_function_names.end());
        }

        if (artifact.selected_root_is_self_loop_only && !allow_trivial_self_loop) {
          if (events.detailed()) {
            events.emitWarn(
                "truthful_child_import_failed",
                "selected truthful child root is trivial self loop",
                {{"target_pc",
                  (llvm::Twine("0x") + llvm::utohexstr(target_pc)).str()},
                 {"reason", "trivial_self_loop_rejected"}});
          }
          return nullptr;
        }

        auto import_plan = std::move(selection.plan);
        import_plan.target_pc = target_pc;
        import_plan.eligibility = omill::ImportEligibility::kImportable;
        import_plan.rejection_reason = omill::RecoveryRejectionReason::kNone;
        import_plan.rejection_detail.clear();
        import_plan.selected_root_pc = artifact.selected_root_pc;
        import_plan.import_class = artifact.import_safety;
        import_plan.allowed_declaration_callees =
            artifact.reachable_declaration_callees;
        import_plan.lowering_helper_callees = artifact.lowering_helper_callees;

        auto *imported_root = importSimpleExecutableChildRoot(
            target_pc, artifact, import_plan, "__omill_recovered_child_",
            /*shallow_closure=*/enable_recovery_mode);
        if (!imported_root) {
          if (events.detailed()) {
            events.emitWarn(
                "truthful_child_import_failed",
                "selected truthful child root failed to import into current module",
                {{"target_pc",
                  (llvm::Twine("0x") + llvm::utohexstr(target_pc)).str()},
                 {"reason", "import_simple_failed"},
                 {"selected_root_name", artifact.selected_root_name}});
          }
          return nullptr;
        }
        if (enable_recovery_mode)
          latest_recovery_mode_truthful_target = target_pc;
        if (events.detailed()) {
          events.emitInfo(
              "truthful_child_import_succeeded",
              "selected truthful child root imported into current module",
              {{"target_pc",
                (llvm::Twine("0x") + llvm::utohexstr(target_pc)).str()},
               {"selected_root_name", artifact.selected_root_name},
               {"imported_root_name", imported_root->getName().str()}});
        }
        if (enable_recovery_mode)
          markImportedRecoveryChildClosure(*imported_root);
        imported_truthful_child_roots[target_pc] = imported_root;
        if (enable_recovery_mode)
          imported_recovery_mode_truthful_targets.insert(target_pc);
        if (iterative_session)
          iterative_session->noteLiftedTarget(target_pc);
        return imported_root;
      };

  auto rewriteDeclarationCallsitesForTarget =
      [&](uint64_t target_pc, llvm::Function &replacement) {
        bool changed = false;
        llvm::SmallVector<llvm::CallBase *, 8> to_rewrite;
        llvm::SmallVector<llvm::Function *, 8> maybe_erase;
        auto matches_target = [&](llvm::Function &callee) {
          if (!callee.isDeclaration())
            return false;
          if (omill::extractEntryVA(callee.getName()) == target_pc ||
              omill::extractBlockPC(callee.getName()) == target_pc) {
            return true;
          }
          if (auto boundary = omill::readBoundaryFact(callee)) {
            if ((boundary->boundary_pc && *boundary->boundary_pc == target_pc) ||
                (boundary->native_target_pc &&
                 *boundary->native_target_pc == target_pc) ||
                (boundary->continuation_pc &&
                 *boundary->continuation_pc == target_pc) ||
                (boundary->continuation_entry_transform &&
                 boundary->continuation_entry_transform->jump_target_pc &&
                 *boundary->continuation_entry_transform->jump_target_pc ==
                     target_pc)) {
              return true;
            }
          }
          if (auto exec = omill::readExecutableTargetFact(callee);
              exec && exec->raw_target_pc == target_pc) {
            return true;
          }
          return false;
        };
        for (auto &F : *module) {
          if (F.isDeclaration())
            continue;
          for (auto &BB : F) {
            for (auto &I : BB) {
              auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
              if (!CB)
                continue;
              auto *callee = CB->getCalledFunction();
              if (!callee || !matches_target(*callee))
                continue;
              if (callee->getFunctionType() != replacement.getFunctionType())
                continue;
              to_rewrite.push_back(CB);
              maybe_erase.push_back(callee);
            }
          }
        }
        for (auto *CB : to_rewrite) {
          if (auto *CI = llvm::dyn_cast<llvm::CallInst>(CB))
            CI->setCalledFunction(&replacement);
          else if (auto *II = llvm::dyn_cast<llvm::InvokeInst>(CB))
            II->setCalledFunction(&replacement);
          changed = true;
        }
        llvm::SmallPtrSet<llvm::Function *, 8> unique_decls(
            maybe_erase.begin(), maybe_erase.end());
        for (auto *decl : unique_decls) {
          if (decl && decl->getParent() == module.get() && decl->isDeclaration() &&
              decl->use_empty()) {
            decl->eraseFromParent();
          }
        }
        return changed;
      };

  auto eraseUnusedModeledPlaceholderDeclarationsInCurrentModule = [&]() {
    llvm::SmallVector<llvm::Function *, 16> to_erase;
    for (auto &F : *module) {
      if (!F.isDeclaration() || !F.use_empty())
        continue;
      auto name = F.getName();
      if (name.starts_with("omill_") || name.starts_with("blk_") ||
          name.starts_with("sub_") || name.starts_with("block_")) {
        to_erase.push_back(&F);
      }
    }
    for (auto *F : to_erase)
      F->eraseFromParent();
    return !to_erase.empty();
  };

  auto importTruthfulOutputRootChildrenInCurrentModule = [&]() {
    if (std::getenv("OMILL_TERMINAL_BOUNDARY_RECOVERY") != nullptr)
      return false;
    struct CandidateTarget {
      uint64_t pc = 0;
      bool enable_recovery_mode = false;
      unsigned use_count = 0;
    };
    llvm::SmallDenseMap<uint64_t, CandidateTarget, 8> candidate_targets;
    llvm::SmallDenseMap<uint64_t, llvm::Function *, 8> imported_roots;
    auto shouldSkipImportedRecoveryFunction = [&](llvm::Function &F) {
      auto fact = omill::readExecutableTargetFact(F);
      return fact &&
             imported_recovery_mode_truthful_targets.contains(fact->raw_target_pc) &&
             latest_recovery_mode_truthful_target &&
             fact->raw_target_pc != *latest_recovery_mode_truthful_target;
    };
    for (auto &F : *module) {
      if (F.isDeclaration() || shouldSkipImportedRecoveryFunction(F))
        continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!CB)
            continue;
          auto *callee = CB->getCalledFunction();
          if (!callee || !callee->isDeclaration())
            continue;
          uint64_t target_pc = 0;
          bool enable_recovery_mode = false;
          if (auto exec = omill::readExecutableTargetFact(*callee); exec) {
            target_pc = exec->raw_target_pc;
            enable_recovery_mode = true;
          }
          if (!target_pc) {
            if (auto boundary = omill::readBoundaryFact(*callee);
                boundary && boundary->boundary_pc) {
              target_pc = *boundary->boundary_pc;
            }
          }
          if (!target_pc)
            target_pc = omill::extractEntryVA(callee->getName());
          if (!target_pc)
            target_pc = omill::extractBlockPC(callee->getName());
          if (!target_pc)
            continue;
          auto &candidate = candidate_targets[target_pc];
          candidate.pc = target_pc;
          candidate.enable_recovery_mode =
              candidate.enable_recovery_mode || enable_recovery_mode;
          candidate.use_count += 1;
        }
      }
    }

    bool changed = false;
    llvm::SmallVector<CandidateTarget, 8> ordered_candidates;
    ordered_candidates.reserve(candidate_targets.size());
    for (const auto &[_, candidate] : candidate_targets)
      ordered_candidates.push_back(candidate);
    llvm::sort(ordered_candidates, [](const CandidateTarget &lhs,
                                     const CandidateTarget &rhs) {
      if (lhs.enable_recovery_mode != rhs.enable_recovery_mode)
        return lhs.enable_recovery_mode && !rhs.enable_recovery_mode;
      if (lhs.use_count != rhs.use_count)
        return lhs.use_count > rhs.use_count;
      return lhs.pc < rhs.pc;
    });
    const auto prior_recovery_target = latest_recovery_mode_truthful_target;
    for (const auto &candidate : ordered_candidates) {
      llvm::Function *imported_root = importTruthfulChildRootForTarget(
          candidate.pc, candidate.enable_recovery_mode,
          /*allow_trivial_self_loop=*/false);
      if (!imported_root)
        continue;
      imported_roots[candidate.pc] = imported_root;
      if (candidate.enable_recovery_mode &&
          latest_recovery_mode_truthful_target != prior_recovery_target)
        break;
    }
    for (const auto &[target_pc, imported_root] : imported_roots)
      changed = rewriteDeclarationCallsitesForTarget(target_pc, *imported_root) ||
                changed;
    return changed;
  };

  auto importRecoveredTerminalBoundaryFunction =
      [&](llvm::StringRef abi_ir_text,
          uint64_t target_pc,
          std::string *rejection_reason = nullptr) -> llvm::Function * {
        llvm::SMDiagnostic parse_error;
        auto imported_module =
            llvm::parseAssemblyString(abi_ir_text, parse_error, ctx);
        if (!imported_module) {
          if (rejection_reason)
            *rejection_reason = "parse_failed";
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] import-parse-failed target=0x"
                   << llvm::utohexstr(target_pc) << "\n";
          }
          return nullptr;
        }

        auto classifyImportedRootRisk =
            [&](llvm::Function &F) -> std::optional<std::string> {
              bool uses_any_arg = false;
              for (auto &arg : F.args()) {
                if (!arg.use_empty()) {
                  uses_any_arg = true;
                  break;
                }
              }

              bool has_normal_return = false;
              bool has_unreachable = false;
              bool saw_non_intrinsic_call = false;
              bool saw_memory_access = false;
              bool saw_other_work = false;
              llvm::Constant *returned_constant = nullptr;
              bool returned_nonconstant_or_mixed = false;

              for (auto &BB : F) {
                if (llvm::isa<llvm::UnreachableInst>(BB.getTerminator()))
                  has_unreachable = true;

                for (auto &I : BB) {
                  if (llvm::isa<llvm::DbgInfoIntrinsic>(I))
                    continue;
                  if (llvm::isa<llvm::AllocaInst>(I))
                    continue;
                  if (auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(&I)) {
                    if (II->getIntrinsicID() == llvm::Intrinsic::lifetime_start ||
                        II->getIntrinsicID() == llvm::Intrinsic::lifetime_end ||
                        II->getIntrinsicID() == llvm::Intrinsic::memset) {
                      continue;
                    }
                  }

                  if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(&I)) {
                    has_normal_return = true;
                    auto *RV = RI->getReturnValue();
                    if (!RV) {
                      returned_nonconstant_or_mixed = true;
                    } else if (auto *C = llvm::dyn_cast<llvm::Constant>(RV)) {
                      if (!returned_constant)
                        returned_constant = C;
                      else if (returned_constant != C)
                        returned_nonconstant_or_mixed = true;
                    } else {
                      returned_nonconstant_or_mixed = true;
                    }
                    continue;
                  }

                  if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
                    auto *callee = CB->getCalledFunction();
                    if (!callee) {
                      saw_other_work = true;
                      continue;
                    }
                    auto callee_name = callee->getName();
                    if (callee_name == "__omill_missing_block_handler" ||
                        callee_name == "__remill_sync_hyper_call" ||
                        callee_name.contains("HandleUnsupported")) {
                      return std::string("unsupported_root");
                    }
                    if (!callee->isIntrinsic() &&
                        !callee_name.starts_with("llvm.")) {
                      saw_non_intrinsic_call = true;
                    }
                    continue;
                  }

                  if (llvm::isa<llvm::LoadInst>(I) ||
                      llvm::isa<llvm::StoreInst>(I)) {
                    saw_memory_access = true;
                    continue;
                  }

                  saw_other_work = true;
                }
              }

              if (!has_normal_return && has_unreachable)
                return std::string("nonreturning_root");

              if (has_normal_return && !uses_any_arg && !saw_non_intrinsic_call &&
                  !saw_memory_access && !saw_other_work && returned_constant &&
                  !returned_nonconstant_or_mixed) {
                return std::string("trivial_constant_root");
              }

              return std::nullopt;
            };

        auto resolveImportedRoot = [&](llvm::Module &M) -> llvm::Function * {
          auto pickUnique =
              [](llvm::ArrayRef<llvm::Function *> candidates)
              -> llvm::Function * {
            return candidates.size() == 1 ? candidates.front() : nullptr;
          };

          const std::string target_hex = llvm::utohexstr(target_pc);
          auto lookupDefined = [&](llvm::StringRef name) -> llvm::Function * {
            auto *F = M.getFunction(name);
            return (F && !F->isDeclaration()) ? F : nullptr;
          };
          auto findExactLiftedRoot = [&]() -> llvm::Function * {
            for (auto &F : M) {
              if (F.isDeclaration())
                continue;
              if (omill::extractEntryVA(F.getName()) == target_pc ||
                  omill::extractBlockPC(F.getName()) == target_pc) {
                return &F;
              }
            }
            if (auto *F = lookupDefined(omill::liftedFunctionName(target_pc)))
              return F;
            return nullptr;
          };
          auto findExactNativeRoot = [&]() -> llvm::Function * {
            if (auto *F = lookupDefined("sub_" + target_hex + "_native"))
              return F;
            if (auto *F = lookupDefined("blk_" + target_hex + "_native"))
              return F;
            if (auto *F = lookupDefined("omill_native_boundary_" + target_hex))
              return F;
            if (auto *F = lookupDefined("omill_vm_enter_boundary_" + target_hex))
              return F;
            return nullptr;
          };

          if (auto *F = findExactLiftedRoot())
            return F;
          if (auto *F = findExactNativeRoot())
            return F;

          llvm::SmallVector<llvm::Function *, 8> target_native_roots;
          llvm::SmallVector<llvm::Function *, 8> target_lifted_roots;
          llvm::SmallVector<llvm::Function *, 8> output_roots;
          llvm::SmallVector<llvm::Function *, 8> non_native_functions;
          llvm::SmallVector<llvm::Function *, 8> native_functions;
          llvm::SmallVector<llvm::Function *, 8> defined_functions;
          for (auto &F : M) {
            if (F.isDeclaration())
              continue;
            defined_functions.push_back(&F);
            if (F.getName().ends_with("_native"))
              native_functions.push_back(&F);
            else
              non_native_functions.push_back(&F);
            if (F.hasFnAttribute("omill.output_root"))
              output_roots.push_back(&F);
            if (!F.getName().contains(target_hex))
              continue;
            if (F.getName().ends_with("_native"))
              target_native_roots.push_back(&F);
            else
              target_lifted_roots.push_back(&F);
          }

          if (auto *F = pickUnique(output_roots))
            return F;
          if (auto *F = pickUnique(target_lifted_roots))
            return F;
          if (auto *F = pickUnique(target_native_roots))
            return F;
          if (auto *F = pickUnique(non_native_functions))
            return F;
          if (auto *F = pickUnique(native_functions))
            return F;
          if (auto *F = pickUnique(defined_functions))
            return F;
          return nullptr;
        };

        auto *imported_root = resolveImportedRoot(*imported_module);
        if (!imported_root) {
          if (rejection_reason)
            *rejection_reason = "root_missing";
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] import-root-missing target=0x"
                   << llvm::utohexstr(target_pc) << " candidates=";
            bool first = true;
            for (auto &F : *imported_module) {
              if (F.isDeclaration())
                continue;
              if (!first)
                errs() << ",";
              errs() << F.getName();
              if (F.hasFnAttribute("omill.output_root"))
                errs() << "[root]";
              first = false;
            }
            errs() << "\n";
          }
          return nullptr;
        }

        if (auto risk = classifyImportedRootRisk(*imported_root)) {
          if (rejection_reason)
            *rejection_reason = *risk;
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] import-root-rejected target=0x"
                   << llvm::utohexstr(target_pc)
                   << " root=" << imported_root->getName()
                   << " reason=" << *risk << "\n";
          }
          return nullptr;
        }

        auto canCloneStandaloneRoot = [&](llvm::Function &F) {
          for (auto &BB : F) {
            for (auto &I : BB) {
              for (llvm::Value *operand : I.operands()) {
                auto *GV = llvm::dyn_cast<llvm::GlobalValue>(operand);
                if (!GV)
                  continue;
                if (GV == &F)
                  continue;
                if (auto *callee = llvm::dyn_cast<llvm::Function>(GV)) {
                  if (!callee->isDeclaration())
                    return false;
                  continue;
                }
                if (auto *global = llvm::dyn_cast<llvm::GlobalVariable>(GV)) {
                  if (!global->isDeclaration() &&
                      !global->getName().starts_with("llvm.")) {
                    return false;
                  }
                }
              }
            }
          }
          return true;
        };

        auto cloneStandaloneRoot = [&](llvm::Function &src,
                                       llvm::StringRef new_name)
            -> llvm::Function * {
          auto clearImportedRootOnlyAttrs = [&](llvm::Function &F) {
            clearTerminalBoundaryAttrs(F);
            F.removeFnAttr("omill.output_root");
            F.removeFnAttr("omill.closed_root_slice");
            F.removeFnAttr("omill.closed_root_slice_root");
            F.removeFnAttr("omill.param_state_offsets");
            F.removeFnAttr("omill.terminal_boundary_recovery_status");
            F.removeFnAttr("omill.terminal_boundary_recovery_target_va");
            F.removeFnAttr("omill.terminal_boundary_recovery_summary");
          };

          auto *dst = module->getFunction(new_name);
          if (!dst) {
            dst = llvm::Function::Create(src.getFunctionType(),
                                         llvm::GlobalValue::InternalLinkage,
                                         new_name, *module);
          }
          if (!dst->empty())
            dst->deleteBody();
          dst->copyAttributesFrom(&src);
          dst->setName(new_name);
          dst->setLinkage(llvm::GlobalValue::InternalLinkage);
          clearImportedRootOnlyAttrs(*dst);

          llvm::ValueToValueMapTy vmap;
          auto src_arg_it = src.arg_begin();
          auto dst_arg_it = dst->arg_begin();
          for (; src_arg_it != src.arg_end() && dst_arg_it != dst->arg_end();
               ++src_arg_it, ++dst_arg_it) {
            vmap[&*src_arg_it] = &*dst_arg_it;
          }
          llvm::SmallVector<llvm::ReturnInst *, 8> returns;
          llvm::CloneFunctionInto(
              dst, &src, vmap,
              llvm::CloneFunctionChangeType::DifferentModule, returns);
          clearImportedRootOnlyAttrs(*dst);
          return dst;
        };

        auto collectDefinedFunctionClosure =
            [&](llvm::Function &root,
                llvm::SmallVectorImpl<llvm::Function *> &closure) {
              llvm::SmallVector<llvm::Function *, 16> worklist;
              llvm::DenseSet<llvm::Function *> visited;
              worklist.push_back(&root);
              while (!worklist.empty()) {
                auto *F = worklist.pop_back_val();
                if (!F || F->isDeclaration() || !visited.insert(F).second)
                  continue;
                closure.push_back(F);
                for (auto &BB : *F) {
                  for (auto &I : BB) {
                    for (llvm::Value *operand : I.operands()) {
                      auto *GV = llvm::dyn_cast<llvm::GlobalValue>(operand);
                      if (!GV)
                        continue;
                      if (auto *callee = llvm::dyn_cast<llvm::Function>(GV)) {
                        if (!callee->isDeclaration())
                          worklist.push_back(callee);
                        continue;
                      }
                      if (auto *global =
                              llvm::dyn_cast<llvm::GlobalVariable>(GV)) {
                        if (!global->isDeclaration() &&
                            !global->getName().starts_with("llvm.")) {
                          return false;
                        }
                      }
                    }
                  }
                }
              }
              return true;
            };

        auto make_unique_import_name = [&](llvm::StringRef base_name) {
          std::string candidate = ("tbrec_" + base_name).str();
          if (!module->getFunction(candidate) &&
              !imported_module->getFunction(candidate)) {
            return candidate;
          }
          for (unsigned i = 1; i < 100; ++i) {
            auto numbered = (candidate + "." + std::to_string(i));
            if (!module->getFunction(numbered) &&
                !imported_module->getFunction(numbered)) {
              return numbered;
            }
          }
          return candidate;
        };

        auto cloneFunctionClosure =
            [&](llvm::ArrayRef<llvm::Function *> sources,
                llvm::Function &root) -> llvm::Function * {
              auto isAllowedModeledBoundaryDecl = [&](llvm::StringRef name) {
                return name.starts_with("omill_executable_target_") ||
                       name.starts_with("omill_native_target_") ||
                       name.starts_with("omill_vm_enter_target_") ||
                       name.starts_with("omill_native_boundary_") ||
                       name.starts_with("omill_vm_enter_boundary_");
              };
              auto clearImportedRootOnlyAttrs = [&](llvm::Function &F) {
                clearTerminalBoundaryAttrs(F);
                F.removeFnAttr("omill.output_root");
                F.removeFnAttr("omill.closed_root_slice");
                F.removeFnAttr("omill.closed_root_slice_root");
                F.removeFnAttr("omill.param_state_offsets");
                F.removeFnAttr("omill.terminal_boundary_recovery_status");
                F.removeFnAttr("omill.terminal_boundary_recovery_target_va");
                F.removeFnAttr("omill.terminal_boundary_recovery_summary");
              };

              llvm::DenseMap<const llvm::Function *, llvm::Function *>
                  cloned_funcs;
              llvm::DenseMap<const llvm::GlobalValue *, llvm::GlobalValue *>
                  decl_map;
              llvm::Function *cloned_root = nullptr;

              for (auto *src_fn : sources) {
                auto clone_name = make_unique_import_name(src_fn->getName());
                auto *dst_fn = llvm::Function::Create(
                    src_fn->getFunctionType(),
                    llvm::GlobalValue::InternalLinkage, clone_name, *module);
                dst_fn->copyAttributesFrom(src_fn);
                clearImportedRootOnlyAttrs(*dst_fn);
                cloned_funcs[src_fn] = dst_fn;
                if (src_fn == &root)
                  cloned_root = dst_fn;
              }

              for (auto *src_fn : sources) {
                for (auto &BB : *src_fn) {
                  for (auto &I : BB) {
                    for (llvm::Value *operand : I.operands()) {
                      auto *GV = llvm::dyn_cast<llvm::GlobalValue>(operand);
                      if (!GV || decl_map.count(GV))
                        continue;
                      if (cloned_funcs.count(
                              llvm::dyn_cast<llvm::Function>(GV))) {
                        continue;
                      }
                      if (auto *callee = llvm::dyn_cast<llvm::Function>(GV)) {
                        if (callee->isDeclaration()) {
                          auto *decl = module->getFunction(callee->getName());
                          if (!decl) {
                            decl = llvm::Function::Create(
                                callee->getFunctionType(),
                                callee->getLinkage(), callee->getName(),
                                *module);
                            decl->copyAttributesFrom(callee);
                          } else if (!isAllowedModeledBoundaryDecl(
                                         decl->getName()) ||
                                     decl->getName() != callee->getName()) {
                            decl->copyAttributesFrom(callee);
                          }
                          decl->setCallingConv(callee->getCallingConv());
                          decl_map[callee] = decl;
                        }
                        continue;
                      }
                      if (auto *global =
                              llvm::dyn_cast<llvm::GlobalVariable>(GV)) {
                        if (global->isDeclaration()) {
                          auto *decl =
                              module->getGlobalVariable(global->getName());
                          if (!decl) {
                            decl = new llvm::GlobalVariable(
                                *module, global->getValueType(),
                                global->isConstant(), global->getLinkage(),
                                nullptr, global->getName(), nullptr,
                                global->getThreadLocalMode(),
                                global->getAddressSpace());
                          }
                          decl_map[global] = decl;
                        }
                      }
                    }
                  }
                }
              }

              for (auto *src_fn : sources) {
                auto *dst_fn = cloned_funcs.lookup(src_fn);
                llvm::ValueToValueMapTy vmap;
                auto src_arg_it = src_fn->arg_begin();
                auto dst_arg_it = dst_fn->arg_begin();
                for (; src_arg_it != src_fn->arg_end() &&
                       dst_arg_it != dst_fn->arg_end();
                     ++src_arg_it, ++dst_arg_it) {
                  vmap[&*src_arg_it] = &*dst_arg_it;
                }
                for (const auto &entry : cloned_funcs)
                  vmap[entry.first] = entry.second;
                for (const auto &entry : decl_map)
                  vmap[entry.first] = entry.second;
                llvm::SmallVector<llvm::ReturnInst *, 8> returns;
                llvm::CloneFunctionInto(
                    dst_fn, src_fn, vmap,
                    llvm::CloneFunctionChangeType::DifferentModule, returns);
                clearImportedRootOnlyAttrs(*dst_fn);
              }

              return cloned_root;
            };

        std::string imported_root_name;
        {
          auto clone_name = make_unique_import_name(imported_root->getName());
          if (canCloneStandaloneRoot(*imported_root)) {
            if (auto *cloned = cloneStandaloneRoot(*imported_root, clone_name)) {
              if (debug_secondary_recovery) {
                errs() << "[terminal-recovery] import-clone-ok target=0x"
                       << llvm::utohexstr(target_pc)
                       << " root=" << clone_name << "\n";
              }
              return cloned;
            }
          }
        }
        {
          llvm::SmallVector<llvm::Function *, 16> closure;
          if (collectDefinedFunctionClosure(*imported_root, closure)) {
            if (auto *cloned = cloneFunctionClosure(closure, *imported_root)) {
              if (debug_secondary_recovery) {
                errs() << "[terminal-recovery] import-closure-clone-ok target=0x"
                       << llvm::utohexstr(target_pc)
                       << " root=" << cloned->getName()
                       << " functions=" << closure.size() << "\n";
              }
              return cloned;
            }
          }
        }
        for (auto &F : *imported_module) {
          if (F.isDeclaration())
            continue;
          auto old_name = F.getName().str();
          auto new_name = make_unique_import_name(old_name);
          if (&F == imported_root)
            imported_root_name = new_name;
          F.setName(new_name);
          clearTerminalBoundaryAttrs(F);
          F.removeFnAttr("omill.output_root");
          F.removeFnAttr("omill.closed_root_slice");
          F.removeFnAttr("omill.closed_root_slice_root");
          F.removeFnAttr("omill.terminal_boundary_recovery_status");
          F.removeFnAttr("omill.terminal_boundary_recovery_target_va");
          F.removeFnAttr("omill.terminal_boundary_recovery_summary");
          if (!F.hasLocalLinkage())
            F.setLinkage(llvm::GlobalValue::InternalLinkage);
        }

        for (auto &G : imported_module->globals()) {
          if (G.isDeclaration())
            continue;
          if (G.getName().starts_with("llvm."))
            continue;
          auto new_name = make_unique_import_name(G.getName());
          G.setName(new_name);
          if (!G.hasLocalLinkage())
            G.setLinkage(llvm::GlobalValue::InternalLinkage);
        }

        if (auto *ctors = imported_module->getGlobalVariable("llvm.global_ctors"))
          ctors->eraseFromParent();
        if (auto *dtors = imported_module->getGlobalVariable("llvm.global_dtors"))
          dtors->eraseFromParent();
        if (auto *flags = imported_module->getNamedMetadata("llvm.module.flags"))
          flags->eraseFromParent();
        if (auto *ident = imported_module->getNamedMetadata("llvm.ident"))
          ident->eraseFromParent();
        if (auto *dbg = imported_module->getNamedMetadata("llvm.dbg.cu"))
          dbg->eraseFromParent();

        llvm::Linker linker(*module);
        if (linker.linkInModule(std::move(imported_module),
                                llvm::Linker::Flags::None)) {
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] import-link-failed target=0x"
                   << llvm::utohexstr(target_pc)
                   << " root=" << imported_root_name << "\n";
          }
          return nullptr;
        }

        auto *linked = module->getFunction(imported_root_name);
        if (!linked || linked->isDeclaration()) {
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] import-link-missing target=0x"
                   << llvm::utohexstr(target_pc)
                   << " root=" << imported_root_name << "\n";
          }
          return nullptr;
        }
        if (!linked->hasLocalLinkage())
          linked->setLinkage(llvm::GlobalValue::InternalLinkage);
        if (debug_secondary_recovery) {
          errs() << "[terminal-recovery] import-ok target=0x"
                 << llvm::utohexstr(target_pc)
                 << " root=" << imported_root_name << "\n";
        }
        return linked;
      };

  auto recoverABIForTerminalBoundaryIR =
      [&](llvm::StringRef noabi_ir_text) -> std::optional<std::string> {
        auto runExternalRecoverABI = [&]() -> std::optional<std::string> {
          llvm::SmallString<256> opt_path(argv[0]);
          llvm::sys::path::remove_filename(opt_path);
          llvm::sys::path::remove_filename(opt_path);
          llvm::sys::path::append(opt_path, "omill-opt", "omill-opt.exe");
          if (!llvm::sys::fs::exists(opt_path))
            return std::nullopt;

          llvm::SmallString<256> temp_in_path;
          llvm::SmallString<256> temp_out_path;
          if (llvm::sys::fs::createTemporaryFile(
                  "omill_terminal_recovery_in", "ll", temp_in_path)) {
            return std::nullopt;
          }
          if (llvm::sys::fs::createTemporaryFile(
                  "omill_terminal_recovery_out", "ll", temp_out_path)) {
            llvm::sys::fs::remove(temp_in_path);
            return std::nullopt;
          }

          {
            std::error_code ec;
            llvm::raw_fd_ostream os(temp_in_path, ec, llvm::sys::fs::OF_Text);
            if (ec) {
              llvm::sys::fs::remove(temp_in_path);
              llvm::sys::fs::remove(temp_out_path);
              return std::nullopt;
            }
            os << noabi_ir_text;
          }

          llvm::SmallVector<std::string, 8> arg_storage;
          arg_storage.emplace_back(opt_path.str().str());
          arg_storage.emplace_back("--only-recover-abi");
          arg_storage.emplace_back(temp_in_path.str().str());
          arg_storage.emplace_back("-o");
          arg_storage.emplace_back(temp_out_path.str().str());

          llvm::SmallVector<llvm::StringRef, 8> argv_refs;
          for (const auto &arg : arg_storage)
            argv_refs.push_back(arg);

          std::string err_msg;
          bool exec_failed = false;
          int rc = llvm::sys::ExecuteAndWait(argv_refs.front(), argv_refs,
                                             std::nullopt, {}, 180u, 0,
                                             &err_msg, &exec_failed);
          llvm::sys::fs::remove(temp_in_path);
          if (rc != 0 || exec_failed) {
            llvm::sys::fs::remove(temp_out_path);
            return std::nullopt;
          }

          auto buf_or_err = llvm::MemoryBuffer::getFile(temp_out_path);
          llvm::sys::fs::remove(temp_out_path);
          if (!buf_or_err)
            return std::nullopt;
          return (*buf_or_err)->getBuffer().str();
        };

        if (auto external_ir = runExternalRecoverABI())
          return external_ir;

        llvm::LLVMContext recovery_ctx;
        llvm::SMDiagnostic parse_error;
        auto recovered_module =
            llvm::parseAssemblyString(noabi_ir_text, parse_error, recovery_ctx);
        if (!recovered_module)
          return std::nullopt;

        llvm::PassBuilder PB;
        llvm::LoopAnalysisManager LAM;
        llvm::FunctionAnalysisManager FAM;
        llvm::CGSCCAnalysisManager CGAM;
        llvm::ModuleAnalysisManager RecoveryMAM;
        PB.registerModuleAnalyses(RecoveryMAM);
        PB.registerCGSCCAnalyses(CGAM);
        PB.registerFunctionAnalyses(FAM);
        PB.registerLoopAnalyses(LAM);
        PB.crossRegisterProxies(LAM, FAM, CGAM, RecoveryMAM);
        omill::registerModuleAnalyses(RecoveryMAM);

        omill::PipelineOptions recovery_opts = opts;
        recovery_opts.lower_intrinsics = false;
        recovery_opts.optimize_state = false;
        recovery_opts.lower_control_flow = false;
        recovery_opts.run_cleanup_passes = false;
        recovery_opts.deobfuscate = false;
        recovery_opts.recover_abi = true;
        recovery_opts.resolve_indirect_targets = false;
        recovery_opts.interprocedural_const_prop = false;
        recovery_opts.generic_static_devirtualize = false;
        recovery_opts.verify_generic_static_devirtualization = false;
        recovery_opts.no_abi_mode = false;
        recovery_opts.preserve_lifted_semantics = false;

        llvm::ModulePassManager RecoveryMPM;
        omill::buildPipeline(RecoveryMPM, recovery_opts);
        RecoveryMPM.run(*recovered_module, RecoveryMAM);

        std::string recovered_ir;
        llvm::raw_string_ostream os(recovered_ir);
        recovered_module->print(os, nullptr);
        os.flush();
        return recovered_ir;
      };

  auto rewriteOutputRootToImportedFunction =
      [&](llvm::Function &root, llvm::Function &imported) {
        if (root.getFunctionType() != imported.getFunctionType())
          return false;

        clearTerminalBoundaryAttrs(root);
        for (auto &BB : llvm::make_early_inc_range(root))
          BB.dropAllReferences();
        while (!root.empty())
          root.begin()->eraseFromParent();

        auto *entry = llvm::BasicBlock::Create(ctx, "entry", &root);
        llvm::IRBuilder<> B(entry);
        llvm::SmallVector<llvm::Value *, 8> args;
        for (auto &arg : root.args())
          args.push_back(&arg);
        auto *call = B.CreateCall(&imported, args);
        call->setCallingConv(imported.getCallingConv());
        if (root.getReturnType()->isVoidTy()) {
          B.CreateRetVoid();
        } else {
          B.CreateRet(call);
        }
        return true;
      };

  auto recoverOutputRootTerminalBoundaries = [&]() {
    if (RawBinary || NoABI)
      return;
    if (parseBoolEnv("OMILL_SKIP_TERMINAL_BOUNDARY_SECONDARY_ROOT_RECOVERY")
            .value_or(false)) {
      return;
    }
    llvm::DenseMap<uint64_t, TerminalBoundaryRecoveryAttempt> attempt_cache;
    llvm::DenseMap<uint64_t, llvm::Function *> imported_target_cache;
    const unsigned max_follow_depth =
        parseUnsignedEnv("OMILL_TERMINAL_BOUNDARY_RECOVERY_MAX_FOLLOW_DEPTH")
            .value_or(1u);

    auto attemptImportRecoveredTarget =
        [&](uint64_t target_pc, llvm::StringRef closed_noabi_ir_text,
            bool enable_gsd_for_child,
            std::string *rejection_reason = nullptr) -> llvm::Function * {
          if (auto it = imported_target_cache.find(target_pc);
              it != imported_target_cache.end()) {
            return it->second;
          }

          auto tryImportABIText =
              [&](llvm::StringRef abi_ir_text,
                  llvm::StringRef source_label) -> llvm::Function * {
            auto abi_summary =
                parseTerminalBoundaryRecoveryIRSummary(abi_ir_text);
            auto abi_status = omill::classifyTerminalBoundaryRecoveryMetrics(
                abi_summary.metrics);
            if (debug_secondary_recovery) {
              errs() << "[terminal-recovery] abi-summary target=0x"
                     << llvm::utohexstr(target_pc)
                     << " source=" << source_label
                     << " status="
                     << omill::terminalBoundaryRecoveryStatusName(abi_status)
                     << " summary="
                     << omill::summarizeTerminalBoundaryRecoveryMetrics(
                            abi_summary.metrics)
                     << "\n";
            }
            if (abi_status !=
                omill::TerminalBoundaryRecoveryStatus::kClosedCandidate) {
              return nullptr;
            }
            std::string local_rejection_reason;
            auto imported = importRecoveredTerminalBoundaryFunction(
                abi_ir_text, target_pc, &local_rejection_reason);
            if (!imported && rejection_reason &&
                !local_rejection_reason.empty()) {
              *rejection_reason = local_rejection_reason;
            }
            if (imported)
              imported_target_cache[target_pc] = imported;
            return imported;
          };

          if (!closed_noabi_ir_text.empty()) {
            ScopedEnvOverride allow_always_inline("OMILL_SKIP_ALWAYS_INLINE",
                                                  "");
            if (auto abi_ir_text =
                    recoverABIForTerminalBoundaryIR(closed_noabi_ir_text)) {
              if (auto *imported =
                      tryImportABIText(*abi_ir_text, "replayed-noabi")) {
                return imported;
              }
            }
          }

          ScopedEnvOverride allow_always_inline("OMILL_SKIP_ALWAYS_INLINE",
                                                "");
          auto abi_child = runTerminalBoundaryChildLift(
              target_pc, /*no_abi=*/false, enable_gsd_for_child,
              enable_gsd_for_child, /*dump_virtual_model=*/false);
          if (!abi_child)
            return nullptr;

          return tryImportABIText(abi_child->ir_text, "direct-abi-child");
        };

    llvm::DenseSet<uint64_t> attempt_stack;
    std::function<TerminalBoundaryRecoveryAttempt(uint64_t, unsigned)>
        collectAttemptForTarget =
        [&](uint64_t target_pc, unsigned follow_depth)
        -> TerminalBoundaryRecoveryAttempt {
          if (auto it = attempt_cache.find(target_pc); it != attempt_cache.end())
            return it->second;
          if (!attempt_stack.insert(target_pc).second) {
            TerminalBoundaryRecoveryAttempt cycle_attempt;
            cycle_attempt.target_pc = target_pc;
            cycle_attempt.summary = "recovery_cycle";
            return cycle_attempt;
          }

          TerminalBoundaryRecoveryAttempt attempt;
          attempt.target_pc = target_pc;
          if (debug_secondary_recovery) {
            errs() << "[terminal-recovery] attempt target=0x"
                   << llvm::utohexstr(target_pc)
                   << " depth=" << follow_depth << "\n";
          }

          auto first_child = runTerminalBoundaryChildLift(
              target_pc, /*no_abi=*/true, /*enable_gsd=*/false,
              /*enable_recovery_mode=*/false, /*dump_virtual_model=*/false);
          if (!first_child) {
            attempt.summary = "timeout_or_failed_initial_probe";
            attempt_stack.erase(target_pc);
            attempt_cache[target_pc] = attempt;
            return attempt;
          }

          auto first_summary =
              parseTerminalBoundaryRecoveryIRSummary(first_child->ir_text);
          attempt.metrics = first_summary.metrics;
          attempt.status =
              omill::classifyTerminalBoundaryRecoveryMetrics(attempt.metrics);
          attempt.summary =
              omill::summarizeTerminalBoundaryRecoveryMetrics(attempt.metrics);

          if (attempt.status ==
              omill::TerminalBoundaryRecoveryStatus::kClosedCandidate) {
            std::string import_rejection_reason;
            if (auto *imported =
                    attemptImportRecoveredTarget(target_pc, first_child->ir_text,
                                                /*enable_gsd_for_child=*/false,
                                                &import_rejection_reason)) {
              attempt.status = omill::TerminalBoundaryRecoveryStatus::kImported;
              attempt.imported = true;
              attempt.summary +=
                  (";imported=" + imported->getName().str());
            } else if (!import_rejection_reason.empty()) {
              attempt.import_rejection_reason = import_rejection_reason;
              attempt.summary +=
                  (";import_rejected=" + import_rejection_reason);
            }
            attempt_stack.erase(target_pc);
            attempt_cache[target_pc] = attempt;
            return attempt;
          }

          if (attempt.status !=
              omill::TerminalBoundaryRecoveryStatus::kVmLikeOpen) {
            attempt_stack.erase(target_pc);
            attempt_cache[target_pc] = attempt;
            return attempt;
          }

          auto recovery_child = runTerminalBoundaryChildLift(
              target_pc, /*no_abi=*/true, /*enable_gsd=*/true,
              /*enable_recovery_mode=*/true, /*dump_virtual_model=*/true);
          if (!recovery_child) {
            attempt.status = omill::TerminalBoundaryRecoveryStatus::kTimeout;
            attempt.summary += ";recovery=timeout_or_failed";
            attempt_stack.erase(target_pc);
            attempt_cache[target_pc] = attempt;
            return attempt;
          }

          auto recovery_model = parseTerminalBoundaryRecoveryModelSummary(
              recovery_child->model_text, target_pc);
          if (recovery_model.found_root) {
            attempt.summary += (";recovery_reachable=" +
                                llvm::Twine(recovery_model.reachable) +
                                ";recovery_frontier=" +
                                llvm::Twine(recovery_model.frontier) +
                                ";recovery_closed=" +
                                llvm::Twine(recovery_model.closed ? 1 : 0))
                                   .str();
          }

          if (recovery_model.found_root && recovery_model.closed &&
              recovery_model.reachable <= 128) {
            std::string import_rejection_reason;
            if (auto *imported =
                    attemptImportRecoveredTarget(target_pc,
                                                recovery_child->ir_text,
                                                /*enable_gsd_for_child=*/true,
                                                &import_rejection_reason)) {
              attempt.status = omill::TerminalBoundaryRecoveryStatus::kImported;
              attempt.imported = true;
              attempt.summary +=
                  (";imported=" + imported->getName().str());
            } else if (!import_rejection_reason.empty()) {
              attempt.import_rejection_reason = import_rejection_reason;
              attempt.summary +=
                  (";import_rejected=" + import_rejection_reason);
            }
          } else if (recovery_model.found_root) {
            auto follow_target = selectFollowupRecoveryTarget(recovery_model);
            if (follow_target && *follow_target != target_pc) {
              if (debug_secondary_recovery) {
                errs() << "[terminal-recovery] follow target=0x"
                       << llvm::utohexstr(target_pc)
                       << " -> 0x" << llvm::utohexstr(*follow_target)
                       << " depth=" << follow_depth << "\n";
              }
              attempt.summary +=
                  (";recovery_follow_target=0x" + llvm::utohexstr(*follow_target));
              if (follow_depth < max_follow_depth) {
                auto followed_attempt =
                    collectAttemptForTarget(*follow_target, follow_depth + 1u);
                attempt.summary +=
                    (";recovery_follow_status=" +
                     std::string(omill::terminalBoundaryRecoveryStatusName(
                         followed_attempt.status)));
                if (!followed_attempt.summary.empty()) {
                  attempt.summary +=
                      (";recovery_follow_summary={" + followed_attempt.summary +
                       "}");
                }
                if (followed_attempt.imported) {
                  if (auto imported_it =
                          imported_target_cache.find(*follow_target);
                      imported_it != imported_target_cache.end() &&
                      imported_it->second) {
                    imported_target_cache[target_pc] = imported_it->second;
                    attempt.status =
                        omill::TerminalBoundaryRecoveryStatus::kImported;
                    attempt.imported = true;
                  }
                }
              } else {
                attempt.summary += ";recovery_follow_depth_limit";
              }
            }
          }

          attempt_stack.erase(target_pc);
          attempt_cache[target_pc] = attempt;
          return attempt;
        };

    bool imported_any = false;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      if (!F.hasFnAttribute("omill.output_root") &&
          !F.hasFnAttribute("omill.closed_root_slice")) {
        continue;
      }

      auto cycle_target_attr = F.getFnAttribute(
          "omill.terminal_boundary_probe_cycle_canonical_target_va");
      auto current_target_attr =
          F.getFnAttribute("omill.terminal_boundary_target_va");
      if (!current_target_attr.isValid())
        continue;

      uint64_t recovery_target_pc = 0;
      auto recovery_target_text = cycle_target_attr.isValid()
                                      ? cycle_target_attr.getValueAsString()
                                      : current_target_attr.getValueAsString();
      if (recovery_target_text.getAsInteger(16, recovery_target_pc) ||
          recovery_target_pc == 0) {
        continue;
      }

      auto attempt = collectAttemptForTarget(recovery_target_pc, 0u);
      if (attempt.imported) {
        auto imported_it = imported_target_cache.find(recovery_target_pc);
        if (imported_it == imported_target_cache.end() || !imported_it->second) {
          attempt.imported = false;
          if (attempt.status ==
              omill::TerminalBoundaryRecoveryStatus::kImported) {
            attempt.status = omill::TerminalBoundaryRecoveryStatus::kVmLikeOpen;
          }
          attempt.summary += ";rewrite_failed=missing_import";
        } else if (F.getFunctionType() !=
                   imported_it->second->getFunctionType()) {
          attempt.imported = false;
          if (attempt.status ==
              omill::TerminalBoundaryRecoveryStatus::kImported) {
            attempt.status = omill::TerminalBoundaryRecoveryStatus::kVmLikeOpen;
          }
          attempt.summary += ";rewrite_failed=signature_mismatch";
        } else if (rewriteOutputRootToImportedFunction(F,
                                                       *imported_it->second)) {
          imported_any = true;
        } else {
          attempt.imported = false;
          if (attempt.status ==
              omill::TerminalBoundaryRecoveryStatus::kImported) {
            attempt.status = omill::TerminalBoundaryRecoveryStatus::kVmLikeOpen;
          }
          attempt.summary += ";rewrite_failed=rewrite_failed";
        }
      }

      setTerminalBoundaryRecoveryAttrs(F, attempt);
    }

    if (imported_any) {
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      ModulePassManager MPM;
      omill::buildLateCleanupPipeline(MPM, opts);
      MPM.run(*module, MAM);
    }

    omill::refreshTerminalBoundaryRecoveryMetadata(*module);
  };
  annotateOutputRootTerminalBoundaryProbeChains();
  maybeRerunLateCleanupForCanonicalTerminalBoundaryCycle();
  annotateOutputRootTerminalBoundaryProbeChains();
  recoverOutputRootTerminalBoundaries();
  annotateOutputRootTerminalBoundaryProbeChains();
  dumpModuleIfEnvEnabled(*module, "OMILL_DEBUG_DUMP_BEFORE_FINAL_OUTPUT",
                         "before_final_output.ll");
  runFinalOutputCleanup();
  // Legacy `_native` helper recovery was removed with direct canonical ABI.
  runFinalOutputCleanup();
  annotateOutputRootTerminalBoundaryProbeChains();
  omill::refreshTerminalBoundaryRecoveryMetadata(*module);

  auto logFunctionsWithUnresolvedLocalDispatch =
      [&](llvm::StringRef stage_label) {
        const bool debug_public_root_seeds =
            parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
        if (!debug_public_root_seeds)
          return;
        for (auto &Cand : *module) {
          if (Cand.isDeclaration())
            continue;
          bool printed_header = false;
          for (auto &BB : Cand) {
            for (auto &I : BB) {
              auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
              auto *Callee = CB ? CB->getCalledFunction() : nullptr;
              if (!Callee)
                continue;
              auto Name = Callee->getName();
              if (!omill::isDispatchJumpName(Name))
                continue;
              if (!printed_header) {
                errs() << "[abi-post] " << stage_label
                       << " unresolved-func=" << Cand.getName() << " ret=";
                Cand.getReturnType()->print(errs());
                errs() << "\n";
                printed_header = true;
              }
              errs() << "[abi-post] " << stage_label << "   call=" << Name
                     << " bb=" << BB.getName() << "\n";
            }
          }
        }
      };

  auto rewriteFinalFlattenedHelperDispatch = [&]() {
    const bool debug_public_root_seeds =
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
    auto findFunctionByPrefix = [&](llvm::StringRef prefix) -> llvm::Function * {
      llvm::Function *match = nullptr;
      for (auto &Cand : *module) {
        if (!Cand.getName().starts_with(prefix))
          continue;
        if (match)
          return nullptr;
        match = &Cand;
      }
      return match;
    };

    llvm::Function *F = nullptr;
    llvm::CallBase *dispatch_call = nullptr;
    unsigned total_functions = 0;
    unsigned native_functions = 0;
    unsigned scanned_native_tuple_funcs = 0;
    for (auto &Cand : *module) {
      ++total_functions;
      if (Cand.isDeclaration() || !Cand.getName().ends_with("_native"))
        continue;
      ++native_functions;
      if (debug_public_root_seeds && native_functions <= 8) {
        errs() << "[abi-post] final-flattened-helper-rewrite native="
               << Cand.getName() << " ret=";
        Cand.getReturnType()->print(errs());
        errs() << "\n";
      }
      auto *RetST = llvm::dyn_cast<llvm::StructType>(Cand.getReturnType());
      if (!RetST || RetST->getNumElements() != 8)
        continue;
      ++scanned_native_tuple_funcs;
      for (auto &BB : Cand) {
        for (auto &I : BB) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          auto *Callee = CB ? CB->getCalledFunction() : nullptr;
          if (!Callee)
            continue;
          auto Name = Callee->getName();
          if (omill::isDispatchJumpName(Name)) {
            if (debug_public_root_seeds) {
              errs() << "[abi-post] final-flattened-helper-rewrite saw candidate="
                     << Cand.getName() << " via " << Name << "\n";
            }
            F = &Cand;
            dispatch_call = CB;
            break;
          }
        }
        if (dispatch_call)
          break;
      }
      if (dispatch_call)
        break;
    }

    if (!F || !dispatch_call) {
      if (debug_public_root_seeds)
        errs() << "[abi-post] final-flattened-helper-rewrite skip missing-func"
               << " total_functions=" << total_functions
               << " native_functions=" << native_functions
               << " scanned_native_tuple_funcs=" << scanned_native_tuple_funcs
               << "\n";
      return false;
    }
    if (debug_public_root_seeds)
      errs() << "[abi-post] final-flattened-helper-rewrite candidate="
             << F->getName() << "\n";

    auto findStateOffsetPtr = [&](uint64_t offset) -> llvm::Value * {
      for (auto &BB : *F) {
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

    auto *eax_ptr = findStateOffsetPtr(2216);
    auto *arg2232_ptr = findStateOffsetPtr(2232);
    auto *arg2280_ptr = findStateOffsetPtr(2280);
    auto *arg2296_ptr = findStateOffsetPtr(2296);
    auto *arg2328_ptr = findStateOffsetPtr(2328);
    auto *arg2408_ptr = findStateOffsetPtr(2408);
    auto *arg2440_ptr = findStateOffsetPtr(2440);
    auto *arg2456_ptr = findStateOffsetPtr(2456);
    if (!eax_ptr || !arg2232_ptr || !arg2280_ptr || !arg2296_ptr ||
        !arg2328_ptr || !arg2408_ptr || !arg2440_ptr || !arg2456_ptr) {
      if (debug_public_root_seeds) {
        errs() << "[abi-post] final-flattened-helper-rewrite skip ptrs"
               << " eax=" << (eax_ptr != nullptr)
               << " 2232=" << (arg2232_ptr != nullptr)
               << " 2280=" << (arg2280_ptr != nullptr)
               << " 2296=" << (arg2296_ptr != nullptr)
               << " 2328=" << (arg2328_ptr != nullptr)
               << " 2408=" << (arg2408_ptr != nullptr)
               << " 2440=" << (arg2440_ptr != nullptr)
               << " 2456=" << (arg2456_ptr != nullptr) << "\n";
      }
      return false;
    }

    llvm::SmallVector<std::pair<uint64_t, llvm::Function *>, 4> targets;
    auto addTarget = [&](uint64_t pc, llvm::StringRef name) {
      auto *Callee = module->getFunction(name);
      if (!Callee)
        Callee = findFunctionByPrefix(name);
      if (!Callee || Callee->isDeclaration())
        return;
      auto *CaseRetST = llvm::dyn_cast<llvm::StructType>(Callee->getReturnType());
      if (!CaseRetST || CaseRetST->getNumElements() != 8)
        return;
      targets.emplace_back(pc, Callee);
    };
    addTarget(0x1800021e7ull, "blk_1800021e7_native");
    addTarget(0x18000223aull, "blk_18000223a_native");
    addTarget(0x18000227dull, "blk_18000227d_native");
    addTarget(0x180002301ull, "sub_180002301_native");
    if (targets.empty()) {
      if (debug_public_root_seeds)
        errs() << "[abi-post] final-flattened-helper-rewrite skip no-targets\n";
      return false;
    }

    auto *switch_block = dispatch_call->getParent();
    auto *target_pc = dispatch_call->getArgOperand(1);
    auto *cont_block = switch_block->splitBasicBlock(
        dispatch_call->getIterator(), "tb.final.dispatch.cont");
    switch_block->getTerminator()->eraseFromParent();
    dispatch_call->eraseFromParent();

    llvm::IRBuilder<> Builder(switch_block);
    auto *state2232 = Builder.CreateLoad(Builder.getInt64Ty(), arg2232_ptr,
                                         "tb.final.state2232");
    auto *state2280 = Builder.CreateLoad(Builder.getInt64Ty(), arg2280_ptr,
                                         "tb.final.state2280");
    auto *state2328 = Builder.CreateLoad(Builder.getInt64Ty(), arg2328_ptr,
                                         "tb.final.state2328");
    auto *state2440 = Builder.CreateLoad(Builder.getInt64Ty(), arg2440_ptr,
                                         "tb.final.state2440");

    auto *default_loop = llvm::BasicBlock::Create(
        ctx, "tb.final.dispatch.loop.default", F, cont_block);
    llvm::IRBuilder<> DefaultLoopBuilder(default_loop);
    DefaultLoopBuilder.CreateBr(default_loop);

    auto *switch_inst =
        Builder.CreateSwitch(target_pc, default_loop, targets.size() + 1);

    auto *self_loop = llvm::BasicBlock::Create(
        ctx, "tb.final.dispatch.loop.18000216d", F, cont_block);
    llvm::IRBuilder<> SelfLoopBuilder(self_loop);
    SelfLoopBuilder.CreateBr(self_loop);
    switch_inst->addCase(Builder.getInt64(0x18000216dull), self_loop);

    for (auto &[pc, Callee] : targets) {
      auto *case_block = llvm::BasicBlock::Create(
          ctx, "tb.final.case." + llvm::utohexstr(pc), F, cont_block);
      llvm::IRBuilder<> CaseBuilder(case_block);
      auto *case_call = CaseBuilder.CreateCall(
          Callee->getFunctionType(), Callee,
          {state2232, state2280, state2328, state2440});
      case_call->setCallingConv(Callee->getCallingConv());
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {0}),
                              eax_ptr);
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {1}),
                              arg2232_ptr);
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {2}),
                              arg2328_ptr);
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {3}),
                              arg2296_ptr);
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {4}),
                              arg2280_ptr);
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {5}),
                              arg2408_ptr);
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {6}),
                              arg2440_ptr);
      CaseBuilder.CreateStore(CaseBuilder.CreateExtractValue(case_call, {7}),
                              arg2456_ptr);
      CaseBuilder.CreateBr(cont_block);
      switch_inst->addCase(Builder.getInt64(pc), case_block);
    }

    if (debug_public_root_seeds)
      errs() << "[abi-post] final-flattened-helper-rewrite applied\n";
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    omill::repairMalformedPHIs(*module);
    return true;
  };
  if (enable_debug_sample_native_fixups) {
    dumpModuleIfEnvEnabled(
        *module,
        "OMILL_DEBUG_DUMP_BEFORE_FINAL_FLATTENED_HELPER_REWRITE",
        "before_final_flattened_helper_rewrite.ll");
    logFunctionsWithUnresolvedLocalDispatch("before-final-flattened-rewrite");
    rewriteFinalFlattenedHelperDispatch();
  }
  auto repairFinalFlattenedSub2301StateCall = [&]() {
    auto *caller = module->getFunction("sub_180002301_native");
    auto *callee = module->getFunction("blk_180002164_native");
    if (!caller || !callee || caller->isDeclaration() || callee->isDeclaration())
      return;

    llvm::AllocaInst *state_alloca = nullptr;
    for (auto &BB : *caller) {
      for (auto &I : BB) {
        auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I);
        if (!AI)
          continue;
        if (AI->getName().starts_with("blk_180002164_native.synthetic_state")) {
          state_alloca = AI;
          break;
        }
      }
      if (state_alloca)
        break;
    }
    if (!state_alloca) {
      auto *entry_ip = &*caller->getEntryBlock().getFirstInsertionPt();
      llvm::IRBuilder<> EntryBuilder(entry_ip);
      auto *stack_ty =
          llvm::ArrayType::get(llvm::Type::getInt8Ty(ctx), 69632);
      state_alloca = EntryBuilder.CreateAlloca(
          stack_ty, nullptr, "blk_180002164_native.synthetic_state.final");
    }

    unsigned repaired = 0;
    for (auto &BB : *caller) {
      for (auto &I : llvm::make_early_inc_range(BB)) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI || CI->getCalledFunction() != callee || CI->arg_size() != 8)
          continue;
        auto *arg5 = CI->getArgOperand(5)->stripPointerCasts();
        if (llvm::isa<llvm::PtrToIntInst>(arg5) || arg5->getType()->isPointerTy())
          continue;
        llvm::IRBuilder<> Builder(CI);
        auto *state_i64 = Builder.CreatePtrToInt(
            state_alloca, CI->getArgOperand(5)->getType(),
            "blk_180002164_native.synthetic_state.i64.final");
        CI->setArgOperand(5, state_i64);
        ++repaired;
      }
    }
    if (repaired > 0 &&
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false)) {
      errs() << "[abi-post] repaired-final-sub2301-state-calls=" << repaired
             << "\n";
    }
  };
  if (enable_debug_sample_native_fixups)
    repairFinalFlattenedSub2301StateCall();
  auto repairFinalBrokenFiveArgStateCalls = [&]() {
    auto calleeReadsArg2AsStatePtr = [&](llvm::Function &Callee) -> bool {
      if (Callee.arg_size() < 3)
        return false;
      auto *arg = Callee.getArg(2);
      for (auto *U : arg->users()) {
        auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(U);
        if (!BO || BO->getOpcode() != llvm::Instruction::Add)
          continue;
        auto *lhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0));
        auto *rhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
        if ((lhs_ci && lhs_ci->getZExtValue() == 9116) ||
            (rhs_ci && rhs_ci->getZExtValue() == 9116))
          return true;
      }
      return false;
    };

    unsigned repaired = 0;
    auto *i64_ty = llvm::Type::getInt64Ty(ctx);
    auto findCallerStateBase = [&](llvm::Function &F) -> llvm::Value * {
      if (F.arg_size() >= 3 && calleeReadsArg2AsStatePtr(F))
        return F.getArg(2);
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(&I);
          if (!BO || BO->getOpcode() != llvm::Instruction::Add)
            continue;
          auto *lhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0));
          auto *rhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
          if (lhs_ci && lhs_ci->getZExtValue() == 9116)
            return BO->getOperand(1);
          if (rhs_ci && rhs_ci->getZExtValue() == 9116)
            return BO->getOperand(0);
        }
      }
      return nullptr;
    };
    auto isPointerLikeStateValue = [&](llvm::Value *V) {
      V = V->stripPointerCasts();
      return llvm::isa<llvm::PtrToIntInst>(V) || V->getType()->isPointerTy();
    };
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.getName().ends_with("_native"))
        continue;
      auto *caller_state_base = findCallerStateBase(F);
      if (!caller_state_base)
        continue;
      for (auto &BB : F) {
        for (auto &I : llvm::make_early_inc_range(BB)) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!CI || CI->arg_size() != 5)
            continue;
          auto *callee = llvm::dyn_cast<llvm::Function>(
              CI->getCalledOperand()->stripPointerCasts());
          if (!callee || callee->isDeclaration() ||
              !callee->getName().ends_with("_native") ||
              !calleeReadsArg2AsStatePtr(*callee)) {
            continue;
          }
          auto *arg2 = CI->getArgOperand(2);
          auto *arg3 = CI->getArgOperand(3);
          auto *arg4 = CI->getArgOperand(4);
          if (arg2 == caller_state_base || isPointerLikeStateValue(arg2))
            continue;

          llvm::SmallVector<llvm::Value *, 5> shifted_args;
          if (auto *arg2_ci = llvm::dyn_cast<llvm::ConstantInt>(arg2);
              arg2_ci && arg2_ci->isZero()) {
            if (isPointerLikeStateValue(arg3)) {
              shifted_args = {CI->getArgOperand(0), CI->getArgOperand(1), arg3,
                              arg4, llvm::ConstantInt::get(i64_ty, 0)};
            } else {
              shifted_args = {CI->getArgOperand(0), CI->getArgOperand(1),
                              caller_state_base, arg3, arg4};
            }
          } else {
            shifted_args = {CI->getArgOperand(0), CI->getArgOperand(1),
                            caller_state_base, arg2, arg3};
          }

          auto *new_call = llvm::CallInst::Create(
              callee->getFunctionType(), callee, shifted_args, CI->getName(),
              CI->getIterator());
          new_call->setCallingConv(CI->getCallingConv());
          new_call->setAttributes(CI->getAttributes());
          if (!CI->use_empty()) {
            if (CI->getType() == new_call->getType()) {
              CI->replaceAllUsesWith(new_call);
            } else if (llvm::isa<llvm::StructType>(new_call->getType())) {
              auto *ev = llvm::ExtractValueInst::Create(
                  new_call, {0}, "ret.primary",
                  std::next(new_call->getIterator()));
              CI->replaceAllUsesWith(ev);
            } else {
              CI->replaceAllUsesWith(llvm::PoisonValue::get(CI->getType()));
            }
          }
          CI->eraseFromParent();
          ++repaired;
        }
      }
    }

    if (repaired > 0 &&
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false)) {
      errs() << "[abi-post] repaired-final-broken-five-arg-state-calls="
             << repaired << "\n";
    }
  };
  if (enable_debug_sample_native_fixups) {
    repairFinalBrokenFiveArgStateCalls();
    dumpModuleIfEnvEnabled(
        *module,
        "OMILL_DEBUG_DUMP_AFTER_FINAL_FLATTENED_HELPER_REWRITE",
        "after_final_flattened_helper_rewrite.ll");
    logFunctionsWithUnresolvedLocalDispatch("after-final-flattened-rewrite");
  }

  auto repairLateDeclaredContinuationWrappers = [&]() {
    unsigned rewritten = 0;
    auto *i64_ty = llvm::Type::getInt64Ty(ctx);
    auto isTypeCompatibleReplacement = [](llvm::CallInst &CI,
                                          llvm::Function &target) {
      auto *target_fty = target.getFunctionType();
      if (target_fty->isVarArg() || CI.arg_size() != target_fty->getNumParams())
        return false;
      if (CI.getType() != target_fty->getReturnType())
        return false;
      for (unsigned i = 0; i < CI.arg_size(); ++i) {
        if (CI.getArgOperand(i)->getType() != target_fty->getParamType(i))
          return false;
      }
      return true;
    };
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        for (auto &I : llvm::make_early_inc_range(BB)) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!CI || CI->arg_size() < 3)
            continue;
          auto *callee = CI->getCalledFunction();
          if (!callee || !callee->isDeclaration())
            continue;
          auto name = callee->getName();
          if (!(name.starts_with("blk_") || name.starts_with("block_")) ||
              name.ends_with("_native")) {
            continue;
          }
          auto *pc_ci = llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(1));
          if (!pc_ci)
            continue;

          uint64_t resolved_pc = 0;
          auto *target = findExactOrNearbyLiftedOrBlockFunction(
              pc_ci->getZExtValue(), /*native=*/false, &resolved_pc);
          if (!target || target == callee || target->isDeclaration())
            continue;
          if (!isTypeCompatibleReplacement(*CI, *target))
            continue;

          if (auto *helper = llvm::dyn_cast<llvm::CallInst>(CI->getArgOperand(2))) {
            if (auto *helper_callee = helper->getCalledFunction();
                helper_callee &&
                omill::isDispatchIntrinsicName(helper_callee->getName()) &&
                helper->arg_size() >= 3) {
              CI->setArgOperand(2, helper->getArgOperand(2));
              if (helper->use_empty())
                helper->eraseFromParent();
            }
          }

          CI->setCalledFunction(target);
          CI->setArgOperand(1, llvm::ConstantInt::get(i64_ty, resolved_pc));
          ++rewritten;
        }
      }
    }

    if (rewritten > 0) {
      errs() << "[abi-post] repaired-late-declared-continuation-wrappers="
             << rewritten << "\n";
    }
  };
  if (!opts.no_abi_mode)
    repairLateDeclaredContinuationWrappers();
  dumpModuleIfEnvEnabled(
      *module, "OMILL_DEBUG_DUMP_AFTER_LATE_DECL_CONT_REWRITE",
      "after_late_decl_cont_rewrite.ll");

  if (parseBoolEnv("OMILL_DEBUG_OUTPUT_ROOTS").value_or(false)) {
    errs() << "[output-roots] final-defined=" << countDefinedOutputRoots()
           << "\n";
    for (auto &F : *module) {
      if (!F.hasFnAttribute("omill.output_root"))
        continue;
      errs() << "[output-roots] name=" << F.getName()
             << " decl=" << (F.isDeclaration() ? 1 : 0);
      if (auto target_attr = F.getFnAttribute("omill.terminal_boundary_target_va");
          target_attr.isValid()) {
        errs() << " target=0x" << target_attr.getValueAsString();
      }
      if (auto recovery_attr =
              F.getFnAttribute("omill.terminal_boundary_recovery_status");
          recovery_attr.isValid()) {
        errs() << " recovery=" << recovery_attr.getValueAsString();
      }
      errs() << "\n";
    }
  }

  auto collectUnresolvedOutputRootPcCalls = [&]() {
    if (!imported_recovery_mode_truthful_targets.empty())
      return llvm::SmallVector<std::string, 8>{};
    llvm::SmallVector<std::string, 8> unresolved;
    for (auto &F : *module) {
      if (!F.hasFnAttribute("omill.output_root") || F.isDeclaration())
        continue;
      if (!hasUnresolvedLiftedControlTransferInClosure(F))
        continue;
      std::string label = F.getName().str();
      if (auto attr = F.getFnAttribute("omill.vm_unresolved_continuation_targets");
          attr.isValid() && attr.isStringAttribute() &&
          !attr.getValueAsString().empty()) {
        label += "[vm=0x" + attr.getValueAsString().str() + "]";
      }
      unresolved.push_back(std::move(label));
    }
    return unresolved;
  };


  auto annotateVmUnresolvedContinuationsInCurrentModule = [&]() {
    constexpr llvm::StringLiteral kCountAttr =
        "omill.vm_unresolved_continuation_count";
    constexpr llvm::StringLiteral kTargetsAttr =
        "omill.vm_unresolved_continuation_targets";
    constexpr llvm::StringLiteral kSummaryAttr =
        "omill.vm_unresolved_continuation_summary";
    constexpr llvm::StringLiteral kNamedMetadata =
        "omill.vm_unresolved_continuations";

    for (auto &F : *module) {
      F.removeFnAttr(kCountAttr);
      F.removeFnAttr(kTargetsAttr);
      F.removeFnAttr(kSummaryAttr);
    }
    if (auto *named_md = module->getNamedMetadata(kNamedMetadata))
      named_md->clearOperands();
    auto *named_md = module->getOrInsertNamedMetadata(kNamedMetadata);

    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;

      llvm::SmallVector<llvm::Function *, 16> worklist = {&F};
      llvm::SmallPtrSet<llvm::Function *, 16> visited;
      llvm::SmallVector<std::pair<uint64_t, std::string>, 8> infos;

      while (!worklist.empty()) {
        auto *current = worklist.pop_back_val();
        if (!current || current->isDeclaration() ||
            !visited.insert(current).second) {
          continue;
        }

        for (auto &BB : *current) {
          for (auto &I : BB) {
            auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!call || call->arg_size() < 2)
              continue;
            auto *callee = call->getCalledFunction();
            if (!callee)
              continue;
            auto callee_name = callee->getName();
            if (omill::isDispatchIntrinsicName(callee_name)) {
              if (auto *pc_ci = llvm::dyn_cast<llvm::ConstantInt>(
                      call->getArgOperand(1))) {
                std::string reason =
                    omill::isDispatchJumpName(callee_name) ? "dispatch_jump"
                                                           : "dispatch_call";
                if (auto *prev = llvm::dyn_cast_or_null<llvm::CallInst>(
                        call->getPrevNonDebugInstruction())) {
                  if (auto *prev_callee = prev->getCalledFunction()) {
                    if (prev_callee->getName().contains("CALLI"))
                      reason += ":paired_CALLI";
                    else if (prev_callee->getName().contains("JMPI"))
                      reason += ":paired_JMPI";
                  }
                }
                infos.push_back({pc_ci->getZExtValue(), std::move(reason)});
              }
            }

            auto boundary_fact = omill::readBoundaryFact(*call);
            if (!boundary_fact && callee)
              boundary_fact = omill::readBoundaryFact(*callee);
            if (boundary_fact && boundary_fact->suppresses_normal_fallthrough) {
              std::optional<uint64_t> continuation_target;
              if (boundary_fact->continuation_entry_transform &&
                  boundary_fact->continuation_entry_transform->jump_target_pc) {
                continuation_target =
                    boundary_fact->continuation_entry_transform->jump_target_pc;
              } else if (boundary_fact->continuation_pc) {
                continuation_target = boundary_fact->continuation_pc;
              }
              if (continuation_target && *continuation_target != 0) {
                infos.push_back(
                    {*continuation_target, "boundary_controlled_return"});
              }
            }




            for (llvm::Value *operand : I.operands()) {
              auto *maybe_callee = llvm::dyn_cast<llvm::Function>(operand);
              if (!maybe_callee || maybe_callee->isDeclaration())
                continue;
              worklist.push_back(maybe_callee);
            }
          }
        }
      }

      if (infos.empty())
        continue;

      llvm::SmallVector<std::string, 8> target_parts;
      llvm::SmallVector<std::string, 8> summary_parts;
      llvm::SmallDenseSet<uint64_t, 8> seen_targets;
      for (const auto &[pc, reason] : infos) {
        if (seen_targets.insert(pc).second)
          target_parts.push_back(llvm::utohexstr(pc));
        summary_parts.push_back(reason + "@0x" + llvm::utohexstr(pc));
      }

      F.addFnAttr(kCountAttr, std::to_string(infos.size()));
      F.addFnAttr(kTargetsAttr, llvm::join(target_parts, ","));
      F.addFnAttr(kSummaryAttr, llvm::join(summary_parts, ","));

      llvm::Metadata *ops[] = {
          llvm::ValueAsMetadata::get(&F),
          llvm::MDString::get(ctx, std::to_string(infos.size())),
          llvm::MDString::get(ctx, llvm::join(target_parts, ",")),
          llvm::MDString::get(ctx, llvm::join(summary_parts, ","))};
      named_md->addOperand(llvm::MDNode::get(ctx, ops));
    }
  };

  auto materializeVmUnresolvedContinuationPlaceholdersInCurrentModule = [&]() {
    llvm::SmallDenseSet<uint64_t, 8> unresolved_targets;
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;
      auto attr = F.getFnAttribute("omill.vm_unresolved_continuation_targets");
      if (!attr.isValid() || !attr.isStringAttribute())
        continue;
      llvm::SmallVector<llvm::StringRef, 8> parts;
      attr.getValueAsString().split(parts, ',', -1, /*KeepEmpty=*/false);
      for (llvm::StringRef part : parts) {
        uint64_t target = 0;
        if (!part.empty() && !part.getAsInteger(16, target))
          unresolved_targets.insert(target);
      }
    }
    if (unresolved_targets.empty())
      return false;

    bool changed = false;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        llvm::SmallVector<llvm::CallInst *, 4> remill_calls;
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee || callee->getName() != "__remill_function_call" ||
              call->arg_size() < 3) {
            continue;
          }
          auto *target_ci = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!target_ci || !unresolved_targets.contains(target_ci->getZExtValue()))
            continue;
          remill_calls.push_back(call);
        }
        for (auto *call : remill_calls) {
          auto target_pc =
              llvm::cast<llvm::ConstantInt>(call->getArgOperand(1))->getZExtValue();
          std::string placeholder_name =
              (llvm::Twine("omill_vm_enter_target_") +
               llvm::Twine::utohexstr(target_pc))
                  .str();
          auto *placeholder = module->getFunction(placeholder_name);
          if (!placeholder) {
            placeholder = llvm::Function::Create(
                call->getFunctionType(), llvm::GlobalValue::ExternalLinkage,
                placeholder_name, *module);
            omill::BoundaryFact fact;
            fact.boundary_pc = target_pc;
            fact.kind = omill::BoundaryKind::kVmEnterBoundary;
            fact.exit_disposition = omill::BoundaryDisposition::kVmEnter;
            fact.is_vm_enter = true;
            omill::writeBoundaryFact(*placeholder, fact);
          }
          llvm::IRBuilder<> ir(call);
          auto *replacement = llvm::cast<llvm::CallInst>(ir.CreateCall(
              placeholder,
              {call->getArgOperand(0), call->getArgOperand(1),
               call->getArgOperand(2)}));
          replacement->setCallingConv(call->getCallingConv());
          call->replaceAllUsesWith(replacement);
          call->eraseFromParent();
          changed = true;
        }
      }
    }
    return changed;
  };





  auto materializeConstantBoundaryPlaceholdersInCurrentModule = [&]() {
    struct NativeBoundaryDecodeSummary {
      std::optional<uint64_t> direct_target_pc;
      std::optional<uint64_t> continuation_pc;
    };
    auto decodeNativeBoundarySummaryFromCurrentInput =
        [&](uint64_t boundary_pc) -> NativeBoundaryDecodeSummary {
      NativeBoundaryDecodeSummary summary;
      uint8_t bytes[192] = {};
      if (!pe.memory_map.read(boundary_pc, bytes, sizeof(bytes)))
        return summary;
      for (unsigned i = 0; i + 4 < sizeof(bytes); ++i) {
        if (bytes[i] != 0xE8)
          continue;
        int32_t rel = 0;
        std::memcpy(&rel, &bytes[i + 1], sizeof(rel));
        summary.direct_target_pc =
            static_cast<uint64_t>(static_cast<int64_t>(boundary_pc) +
                                  static_cast<int64_t>(i) + 5 +
                                  static_cast<int64_t>(rel));
        summary.continuation_pc = boundary_pc + i + 5;
        break;
      }
      return summary;
    };
    auto looksLikeVmEnterTargetInCurrentInput = [&](uint64_t boundary_pc) {
      uint8_t bytes[32] = {};
      if (!pe.memory_map.read(boundary_pc, bytes, sizeof(bytes)))
        return false;
      unsigned stack_setup_ops = 0;
      bool saw_pushfq = false;
      bool saw_early_direct_call = false;
      for (unsigned i = 0; i < 16 && i < sizeof(bytes); ++i) {
        switch (bytes[i]) {
          case 0x50:
          case 0x51:
          case 0x52:
          case 0x53:
          case 0x54:
          case 0x55:
          case 0x56:
          case 0x57:
          case 0x58:
          case 0x59:
          case 0x5A:
          case 0x5B:
          case 0x5C:
          case 0x5D:
          case 0x5E:
          case 0x5F:
            ++stack_setup_ops;
            break;
          case 0x9C:
            ++stack_setup_ops;
            saw_pushfq = true;
            break;
          case 0xE8:
            if (i < 24)
              saw_early_direct_call = true;
            break;
          default:
            break;
        }
      }
      return saw_pushfq && stack_setup_ops >= 5 && !saw_early_direct_call;
    };
    auto materializeKnownBoundaryBridge =
        [&](llvm::Function &placeholder, uint64_t target_pc) -> bool {
      if (!placeholder.isDeclaration())
        return false;
      uint8_t bytes[32] = {};
      if (!pe.memory_map.read(target_pc, bytes, sizeof(bytes)))
        return false;

      auto security_cookie_like = [&]() {
        return bytes[0] == 0x48 && bytes[1] == 0x3B && bytes[2] == 0x0D &&
               bytes[7] == 0x75 && bytes[9] == 0x48 && bytes[10] == 0xC1 &&
               bytes[11] == 0xC1 && bytes[12] == 0x10 &&
               ((bytes[13] == 0x66 && bytes[14] == 0x85 && bytes[15] == 0xC9) ||
                (bytes[13] == 0x66 && bytes[14] == 0xF7 && bytes[15] == 0xC1));
      };
      auto push_jmp_vm_thunk = [&]() {
        return bytes[0] == 0x68 && bytes[5] == 0xE9;
      };
      if (!security_cookie_like() && !push_jmp_vm_thunk())
        return false;

      llvm::IRBuilder<> ir(
          llvm::BasicBlock::Create(ctx, "entry", &placeholder));
      auto arg_it = placeholder.arg_begin();
      llvm::Value *state_arg = &*arg_it++;
      llvm::Value *pc_arg = &*arg_it++;
      (void)pc_arg;
      llvm::Value *memory_arg = &*arg_it;

      if (security_cookie_like()) {
        ir.CreateRet(memory_arg);
        return true;
      }

      int32_t pushed_imm = 0;
      int32_t rel = 0;
      std::memcpy(&pushed_imm, &bytes[1], sizeof(pushed_imm));
      std::memcpy(&rel, &bytes[6], sizeof(rel));

      omill::StateFieldMap field_map(*module);
      auto rsp_field = field_map.fieldByName("RSP");
      auto pc_field = field_map.fieldByName("PC");
      if (!rsp_field) {
        placeholder.deleteBody();
        return false;
      }

      auto *i8_ty = ir.getInt8Ty();
      auto *i64_ty = ir.getInt64Ty();
      auto *rsp_ptr = ir.CreateInBoundsGEP(
          i8_ty, state_arg, ir.getInt64(rsp_field->offset),
          "rsp.ptr");
      auto *rsp_val = ir.CreateLoad(i64_ty, rsp_ptr, "rsp");
      auto *new_rsp = ir.CreateSub(rsp_val, ir.getInt64(8), "new.rsp");
      auto *stack_slot = ir.CreateIntToPtr(new_rsp, ir.getPtrTy(), "stack.slot");
      auto *pushed_value = ir.CreateSExt(ir.getInt32(pushed_imm), i64_ty);
      ir.CreateStore(pushed_value, stack_slot);
      ir.CreateStore(new_rsp, rsp_ptr);
      if (pc_field) {
        auto *pc_ptr = ir.CreateInBoundsGEP(
            i8_ty, state_arg, ir.getInt64(pc_field->offset),
            "pc.ptr");
        const uint64_t next_pc =
            static_cast<uint64_t>(static_cast<int64_t>(target_pc) + 10 +
                                  static_cast<int64_t>(rel));
        ir.CreateStore(ir.getInt64(next_pc), pc_ptr);
      }
      ir.CreateRet(memory_arg);
      return true;
    };

    auto decodePushImmediateJumpBoundaryTransform =
        [&](uint64_t boundary_pc)
            -> std::optional<std::pair<omill::ContinuationEntryTransform,
                                       uint64_t>> {
      uint8_t bytes[16] = {};
      if (!pe.memory_map.read(boundary_pc, bytes, sizeof(bytes)))
        return std::nullopt;
      if (bytes[0] != 0x68 || bytes[5] != 0xE9)
        return std::nullopt;

      uint32_t imm32 = 0;
      int32_t rel32 = 0;
      std::memcpy(&imm32, &bytes[1], sizeof(imm32));
      std::memcpy(&rel32, &bytes[6], sizeof(rel32));

      omill::ContinuationEntryTransform transform;
      transform.kind = omill::ContinuationEntryTransformKind::kPushImmediateJump;
      transform.entry_pc = boundary_pc;
      transform.jump_target_pc = static_cast<uint64_t>(
          static_cast<int64_t>(boundary_pc + 10) +
          static_cast<int64_t>(rel32));
      transform.pushed_immediate = imm32;
      transform.suppresses_normal_fallthrough = true;
      return std::make_pair(transform, static_cast<uint64_t>(imm32));
    };
    llvm::SmallDenseSet<uint64_t, 8> unresolved_targets;
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
        continue;
      auto attr = F.getFnAttribute("omill.vm_unresolved_continuation_targets");
      if (!attr.isValid() || !attr.isStringAttribute())
        continue;
      llvm::SmallVector<llvm::StringRef, 8> parts;
      attr.getValueAsString().split(parts, ',', -1, /*KeepEmpty=*/false);
      for (llvm::StringRef part : parts) {
        uint64_t target = 0;
        if (!part.empty() && !part.getAsInteger(16, target))
          unresolved_targets.insert(target);
      }
    }
    bool changed = false;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        llvm::SmallVector<llvm::CallInst *, 4> runtime_calls;
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!call || call->arg_size() < 3)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee)
            continue;
          if (callee->getName() != "__remill_function_call" &&
              callee->getName() != "__remill_jump") {
            continue;
          }
          if (!llvm::isa<llvm::ConstantInt>(call->getArgOperand(1)))
            continue;
          runtime_calls.push_back(call);
        }
        for (auto *call : runtime_calls) {
          auto target_pc =
              llvm::cast<llvm::ConstantInt>(call->getArgOperand(1))->getZExtValue();
          const auto native_summary =
              decodeNativeBoundarySummaryFromCurrentInput(target_pc);
          const bool vm_enter =
              (unresolved_targets.contains(target_pc) &&
               !native_summary.direct_target_pc.has_value()) ||
              looksLikeVmEnterTargetInCurrentInput(target_pc) ||
              module->getFunction((llvm::Twine("omill_vm_enter_target_") +
                                   llvm::Twine::utohexstr(target_pc))
                                      .str()) != nullptr;
          const uint64_t effective_call_target = target_pc;
          std::string placeholder_name =
              (vm_enter ? (llvm::Twine("omill_vm_enter_target_") +
                           llvm::Twine::utohexstr(target_pc))
                        : (llvm::Twine("omill_native_boundary_") +
                           llvm::Twine::utohexstr(target_pc)))
                  .str();
          auto *placeholder = module->getFunction(placeholder_name);
          if (!placeholder) {
            placeholder = llvm::Function::Create(
                call->getFunctionType(), llvm::GlobalValue::ExternalLinkage,
                placeholder_name, *module);
          }
          (void)materializeKnownBoundaryBridge(*placeholder, target_pc);
          omill::BoundaryFact fact =
              omill::readBoundaryFact(*placeholder).value_or(omill::BoundaryFact{});
          fact.boundary_pc = target_pc;
          auto pushed_jump_transform =
              decodePushImmediateJumpBoundaryTransform(target_pc);
          if (vm_enter) {
            fact.kind = omill::BoundaryKind::kVmEnterBoundary;
            fact.exit_disposition = omill::BoundaryDisposition::kVmEnter;
            fact.is_vm_enter = true;
          } else {
            fact.kind = omill::BoundaryKind::kNativeBoundary;
            if (native_summary.direct_target_pc)
              fact.native_target_pc = native_summary.direct_target_pc;
            if (native_summary.continuation_pc) {
              fact.continuation_pc = native_summary.continuation_pc;
              fact.continuation_vip_pc = native_summary.continuation_pc;
              fact.exit_disposition =
                  omill::BoundaryDisposition::kVmExitNativeCallReenter;
            }
          }
          if (pushed_jump_transform) {
            fact.covered_entry_pc = target_pc;
            fact.continuation_entry_transform = pushed_jump_transform->first;
            fact.continuation_pc =
                pushed_jump_transform->first.jump_target_pc;
            fact.continuation_vip_pc =
                pushed_jump_transform->first.jump_target_pc;
            fact.controlled_return_pc = pushed_jump_transform->second;
            fact.return_address_control_kind =
                omill::VirtualReturnAddressControlKind::kRedirectedConstant;
            fact.suppresses_normal_fallthrough = true;
            fact.reenters_vm = true;
            if (fact.exit_disposition == omill::BoundaryDisposition::kUnknown)
              fact.exit_disposition = omill::BoundaryDisposition::kStayInVm;
          }
          omill::writeBoundaryFact(*placeholder, fact);
          llvm::IRBuilder<> ir(call);
          auto *replacement = llvm::cast<llvm::CallInst>(ir.CreateCall(
              placeholder,
              {call->getArgOperand(0), llvm::ConstantInt::get(
                                           call->getArgOperand(1)->getType(),
                                           effective_call_target),
               call->getArgOperand(2)}));
          replacement->setCallingConv(call->getCallingConv());
          replacement->setTailCallKind(call->getTailCallKind());
          call->replaceAllUsesWith(replacement);
          call->eraseFromParent();
          changed = true;
        }
      }
    }
    return changed;
  };


  auto wireImportedPushJumpBoundaryContinuationsInCurrentModule = [&]() {
    llvm::SmallVector<std::pair<llvm::Function *, uint64_t>, 8> boundaries;
    appendDebugMarker("continuation-wire:scan-begin");
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      auto fact = omill::readBoundaryFact(F);
      if (!fact || !fact->continuation_entry_transform ||
          fact->continuation_entry_transform->kind !=
              omill::ContinuationEntryTransformKind::kPushImmediateJump ||
          !fact->continuation_entry_transform->jump_target_pc) {
        continue;
      }
      boundaries.emplace_back(&F, *fact->continuation_entry_transform->jump_target_pc);
    }
    appendDebugMarker((llvm::Twine("continuation-wire:scan-done:") +
                       llvm::Twine(boundaries.size()))
                          .str()
                          .c_str());

    bool changed = false;


    for (const auto &[boundary_fn, jump_target_pc] : boundaries) {
      appendDebugMarker((llvm::Twine("continuation-wire:target-begin:0x") +
                         llvm::Twine::utohexstr(jump_target_pc))
                            .str()
                            .c_str());
      llvm::Function *imported_root = nullptr;
      if (auto *existing_root =
              omill::findLiftedOrBlockFunctionByPC(*module, jump_target_pc);
          existing_root && !existing_root->isDeclaration()) {
        imported_root = existing_root;
        appendDebugMarker("continuation-wire:existing-root");
      } else if (auto *existing_structural =
                     omill::findStructuralCodeTargetFunctionByPC(*module,
                                                                jump_target_pc);
                 existing_structural && !existing_structural->isDeclaration()) {
        imported_root = existing_structural;
        appendDebugMarker("continuation-wire:existing-structural-root");
      } else {
        for (auto &candidate : *module) {
          if (candidate.isDeclaration())
            continue;
          auto fact = omill::readExecutableTargetFact(candidate);
          if (!fact || fact->raw_target_pc != jump_target_pc)
            continue;
          imported_root = &candidate;
          appendDebugMarker("continuation-wire:existing-fact-root");
          break;
        }
      }
      const bool enable_push_jump_continuation_child_import =
          parseBoolEnv("OMILL_ENABLE_PUSH_JUMP_CONTINUATION_CHILD_IMPORT")
              .value_or(false);
      if (!imported_root && enable_push_jump_continuation_child_import) {
        appendDebugMarker("continuation-wire:before-child-import");
        imported_root =
            importTruthfulChildRootForTarget(
                jump_target_pc, /*enable_recovery_mode=*/true,
                /*allow_trivial_self_loop=*/false);
        appendDebugMarker(imported_root ? "continuation-wire:after-child-import:1"
                                        : "continuation-wire:after-child-import:0");
      } else if (!enable_push_jump_continuation_child_import) {
        appendDebugMarker("continuation-wire:child-import-disabled");
        if (auto boundary = omill::readBoundaryFact(*boundary_fn)) {
          omill::ContinuationProof proof;
          proof.raw_target_pc = jump_target_pc;
          proof.effective_target_pc = jump_target_pc;
          proof.resolution_kind =
              omill::ContinuationResolutionKind::kBoundaryModeled;
          proof.import_disposition =
              omill::ContinuationImportDisposition::kRetryable;
          proof.selected_root_import_class =
              omill::ChildImportClass::kBoundaryModeledChild;
          proof.return_address_control_kind =
              boundary->return_address_control_kind;
          proof.controlled_return_pc = boundary->controlled_return_pc;
          proof.suppresses_normal_fallthrough =
              boundary->suppresses_normal_fallthrough;
          proof.confidence = omill::ContinuationConfidence::kWeak;
          proof.liveness = omill::ContinuationLiveness::kLive;
          proof.scheduling_class =
              omill::FrontierSchedulingClass::kNativeOrVmEnterBoundary;
          proof.rationale = "push_jump_child_import_disabled";
          for (auto &[identity, edge] :
               devirtualization_orchestrator.session().graph.edge_facts_by_identity) {
            (void)identity;
            if (!edge.target_pc || *edge.target_pc != jump_target_pc)
              continue;
            edge.continuation_proof = proof;
            edge.continuation_confidence = proof.confidence;
            edge.continuation_liveness = proof.liveness;
            edge.scheduling_class = proof.scheduling_class;
            edge.continuation_rationale = proof.rationale;
          }
        }
      }
      if (!imported_root ||
          imported_root->getFunctionType() != boundary_fn->getFunctionType()) {
        appendDebugMarker("continuation-wire:target-skip");
        continue;
      }

      auto fact = omill::readBoundaryFact(*boundary_fn);
      if (!fact || !fact->continuation_entry_transform ||
          !fact->continuation_entry_transform->jump_target_pc) {
        continue;
      }
      omill::StateFieldMap field_map(*module);
      auto rsp_field = field_map.fieldByName("RSP");
      auto pc_field = field_map.fieldByName("PC");
      if (!rsp_field)
        continue;

      boundary_fn->deleteBody();
      llvm::IRBuilder<> ir(
          llvm::BasicBlock::Create(ctx, "entry", boundary_fn));
      auto arg_it = boundary_fn->arg_begin();
      llvm::Value *state_arg = &*arg_it++;
      llvm::Value *pc_arg = &*arg_it++;
      (void)pc_arg;
      llvm::Value *memory_arg = &*arg_it;

      auto *i8_ty = ir.getInt8Ty();
      auto *i64_ty = ir.getInt64Ty();
      auto *rsp_ptr = ir.CreateInBoundsGEP(
          i8_ty, state_arg, ir.getInt64(rsp_field->offset),
          "rsp.ptr");
      auto *rsp_val = ir.CreateLoad(i64_ty, rsp_ptr, "rsp");
      auto *new_rsp = ir.CreateSub(rsp_val, ir.getInt64(8), "new.rsp");
      auto *stack_slot = ir.CreateIntToPtr(new_rsp, ir.getPtrTy(), "stack.slot");
      auto *pushed_value = ir.CreateSExt(
          ir.getInt32(static_cast<uint32_t>(
              fact->continuation_entry_transform->pushed_immediate.value_or(0))),
          i64_ty);
      ir.CreateStore(pushed_value, stack_slot);
      ir.CreateStore(new_rsp, rsp_ptr);
      if (pc_field) {
        auto *pc_ptr = ir.CreateInBoundsGEP(
            i8_ty, state_arg, ir.getInt64(pc_field->offset),
            "pc.ptr");
        ir.CreateStore(
            ir.getInt64(*fact->continuation_entry_transform->jump_target_pc),
            pc_ptr);
      }
      auto *continuation_call = ir.CreateCall(
          imported_root,
          {state_arg,
           ir.getInt64(*fact->continuation_entry_transform->jump_target_pc),
           memory_arg});
      ir.CreateRet(continuation_call);
      changed = true;
    }
    return changed;
  };


  if (noabi_output_root_targets_patched)
    annotateVmUnresolvedContinuationsInCurrentModule();

  auto rewriteSuppressedBoundaryFallthroughsInCurrentModule = [&]() {
    llvm::SmallVector<llvm::CallInst *, 8> boundary_calls;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        auto *term = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator());
        if (!term || term->getNumOperands() != 1)
          continue;
        auto *tail_call = llvm::dyn_cast<llvm::CallInst>(term->getReturnValue());
        if (!tail_call || !tail_call->isMustTailCall())
          continue;
        llvm::Instruction *prev = tail_call->getPrevNonDebugInstruction();
        auto *boundary_call = llvm::dyn_cast_or_null<llvm::CallInst>(prev);
        if (!boundary_call || boundary_call == tail_call)
          continue;
        auto *callee = boundary_call->getCalledFunction();
        if (!callee)
          continue;
        auto boundary = omill::readBoundaryFact(*callee);
        if (!boundary || !boundary->suppresses_normal_fallthrough)
          continue;
        if (boundary_call->getType() != tail_call->getType() ||
            tail_call->getType() != term->getReturnValue()->getType()) {
          continue;
        }
        boundary_calls.push_back(boundary_call);
      }
    }

    bool changed = false;
    for (auto *boundary_call : boundary_calls) {
      auto *BB = boundary_call->getParent();
      auto *term = llvm::cast<llvm::ReturnInst>(BB->getTerminator());
      auto *tail_call = llvm::cast<llvm::CallInst>(term->getReturnValue());
      llvm::IRBuilder<> ir(term);
      ir.CreateRet(boundary_call);
      term->eraseFromParent();
      tail_call->eraseFromParent();
      changed = true;
    }
    return changed;
  };

  auto collectSuspiciousZeroArityOutputRoots = [&]() {
    llvm::SmallVector<std::string, 8> suspicious;
    const auto &DL = module->getDataLayout();
    for (auto &F : *module) {
      if (!F.hasFnAttribute("omill.output_root") || F.isDeclaration())
        continue;
      if (F.arg_size() != 0)
        continue;

      bool has_state_alloca = false;
      bool has_large_stack_alloca = false;
      bool uses_stacksave = false;
      for (auto &BB : F) {
        for (auto &I : BB) {
          if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
            if (auto *ST =
                    llvm::dyn_cast<llvm::StructType>(AI->getAllocatedType());
                ST && ST->hasName() && ST->getName() == "struct.State") {
              has_state_alloca = true;
            }
            if (auto *AT =
                    llvm::dyn_cast<llvm::ArrayType>(AI->getAllocatedType())) {
              auto bytes = DL.getTypeAllocSize(AT);
              if (bytes >= 4096)
                has_large_stack_alloca = true;
            }
          }
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          auto *callee = CB ? CB->getCalledFunction() : nullptr;
          if (callee && callee->getName() == "llvm.stacksave.p0")
            uses_stacksave = true;
        }
      }

      if (has_state_alloca || has_large_stack_alloca || uses_stacksave)
        suspicious.push_back(F.getName().str());
    }
    return suspicious;
  };

  auto collectSuspiciousStackBackedOutputRoots = [&]() {
    llvm::SmallVector<std::string, 8> suspicious;
    const auto &DL = module->getDataLayout();
    for (auto &F : *module) {
      if (!F.hasFnAttribute("omill.output_root") || F.isDeclaration())
        continue;

      bool has_state_alloca = false;
      bool has_large_stack_alloca = false;
      bool uses_stacksave = false;
      bool calls_local_lifted_helper = false;
      for (auto &BB : F) {
        for (auto &I : BB) {
          if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
            if (auto *ST =
                    llvm::dyn_cast<llvm::StructType>(AI->getAllocatedType());
                ST && ST->hasName() && ST->getName() == "struct.State") {
              has_state_alloca = true;
            }
            if (auto *AT =
                    llvm::dyn_cast<llvm::ArrayType>(AI->getAllocatedType())) {
              auto bytes = DL.getTypeAllocSize(AT);
              if (bytes >= 4096)
                has_large_stack_alloca = true;
            }
          }
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          auto *callee = CB ? CB->getCalledFunction() : nullptr;
          if (callee && callee->getName() == "llvm.stacksave.p0")
            uses_stacksave = true;
          if (callee && !callee->isDeclaration() &&
              !callee->getName().ends_with("_native") &&
              (callee->getName().starts_with("blk_") ||
               callee->getName().starts_with("sub_") ||
               callee->getName().starts_with("block_"))) {
            calls_local_lifted_helper = true;
          }
        }
      }

      if ((has_state_alloca || has_large_stack_alloca || uses_stacksave) &&
          calls_local_lifted_helper) {
        suspicious.push_back(F.getName().str());
      }
    }
    return suspicious;
  };

  auto tryAdoptTruthfulNoABIChildAsAbiModule = [&]() -> bool {
    if (RawBinary || NoABI)
      return false;

    auto noabi_child = runTerminalBoundaryChildLift(
        func_va, /*no_abi=*/true, opts.generic_static_devirtualize,
        /*enable_recovery_mode=*/false, /*dump_virtual_model=*/false,
        /*allow_recursive_output_recovery=*/true);
    if (!noabi_child || noabi_child->ir_text.empty())
      return false;

    auto buildAbiFromNoAbiIR = [&](llvm::StringRef ir_text)
        -> std::unique_ptr<llvm::Module> {
      llvm::SMDiagnostic local_parse_error;
      auto parsed_module = llvm::parseAssemblyString(ir_text, local_parse_error, ctx);
      if (!parsed_module)
        return nullptr;
      ModulePassManager AbiMPM;
      omill::buildABIRecoveryPipeline(AbiMPM, opts);
      AbiMPM.run(*parsed_module, MAM);
      if (verifyModule(*parsed_module, nullptr))
        return nullptr;
      return parsed_module;
    };

    auto classifyChildQuality = [&](llvm::Module &candidate) {
      return classifySerializedRuntimeRecoveryQuality(candidate)
          .value_or(classifyRuntimeRecoveryQuality(candidate));
    };

    std::unique_ptr<llvm::Module> child_module =
        buildAbiFromNoAbiIR(noabi_child->ir_text);
    if (!child_module || classifyChildQuality(*child_module).dispatcher_shell) {
      if (auto abi_ir_text = recoverABIForTerminalBoundaryIR(noabi_child->ir_text)) {
        llvm::SMDiagnostic parse_error;
        auto recovered_module =
            llvm::parseAssemblyString(*abi_ir_text, parse_error, ctx);
        if (recovered_module && !verifyModule(*recovered_module, nullptr) &&
            !classifyChildQuality(*recovered_module).dispatcher_shell) {
          child_module = std::move(recovered_module);
        }
      }
    }
    if (!child_module)
      return false;

    auto child_quality = classifyChildQuality(*child_module);
    if (child_quality.dispatcher_shell)
      return false;

    module = std::move(child_module);
    if (!NoABI && func_va != 0) {
      annotateExportCallsiteWin64ParamHint(requested_func_va, func_va);
      annotateExportEntryHiddenSeedHint(func_va, func_va);
    }
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    annotateVmUnresolvedContinuationsInCurrentModule();
    annotateOutputRootTerminalBoundaryProbeChains();
    omill::refreshTerminalBoundaryRecoveryMetadata(*module);
    omill::repairMalformedPHIs(*module);
    events.emitInfo("abi_truthful_noabi_child_adopted",
                    "adopted truthful recursive no-ABI child then reran ABI recovery");
    return true;
  };

  auto tryAdoptTruthfulPreABICheckpoint = [&]() -> bool {
    if (RawBinary || NoABI)
      return false;
    if (!pre_abi_checkpoint_text || pre_abi_checkpoint_text->empty())
      return false;

    llvm::SMDiagnostic parse_error;
    auto checkpoint_module =
        llvm::parseAssemblyString(*pre_abi_checkpoint_text, parse_error, ctx);
    if (!checkpoint_module)
      return false;
    if (verifyModule(*checkpoint_module, nullptr))
      return false;
    bool has_output_root = false;
    for (auto &F : *checkpoint_module) {
      if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root")) {
        has_output_root = true;
        break;
      }
    }
    if (!has_output_root)
      return false;

    auto checkpoint_quality =
        classifySerializedRuntimeRecoveryQuality(*checkpoint_module)
            .value_or(classifyRuntimeRecoveryQuality(*checkpoint_module));
    if (checkpoint_quality.dispatcher_shell)
      return false;

    module = std::move(checkpoint_module);
    if (!NoABI && func_va != 0) {
      annotateExportCallsiteWin64ParamHint(requested_func_va, func_va);
      annotateExportEntryHiddenSeedHint(func_va, func_va);
    }
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    annotateVmUnresolvedContinuationsInCurrentModule();
    annotateOutputRootTerminalBoundaryProbeChains();
    omill::refreshTerminalBoundaryRecoveryMetadata(*module);
    omill::repairMalformedPHIs(*module);
    events.emitInfo("pre_abi_truthful_checkpoint_adopted",
                    "adopted truthful pre-ABI checkpoint instead of ABI shell");
    return true;
  };

  auto sanitizeRemainingPoisonNativeHelperArgs = [&]() {
    auto parseParamOffsets = [&](llvm::Function &F) {
      llvm::SmallVector<int, 16> offsets;
      if (auto attr = F.getFnAttribute("omill.param_state_offsets");
          attr.isValid() && attr.isStringAttribute()) {
        llvm::SmallVector<llvm::StringRef, 16> parts;
        attr.getValueAsString().split(parts, ',');
        for (auto &part : parts) {
          if (part == "stack" || part == "xmm") {
            offsets.push_back(-1);
            continue;
          }
          unsigned off = 0;
          if (part.getAsInteger(10, off))
            offsets.push_back(-1);
          else
            offsets.push_back(static_cast<int>(off));
        }
      }
      return offsets;
    };

    unsigned repaired = 0;
    auto *i64_ty = llvm::Type::getInt64Ty(ctx);
    auto stateArgIndex = [&](llvm::Function &Fn) -> std::optional<unsigned> {
      for (unsigned i = 0; i < Fn.arg_size(); ++i) {
        auto *arg = Fn.getArg(i);
        for (auto *U : arg->users()) {
          auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(U);
          if (!BO || BO->getOpcode() != llvm::Instruction::Add)
            continue;
          auto *lhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0));
          auto *rhs_ci = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
          if ((lhs_ci && lhs_ci->getZExtValue() == 9116) ||
              (rhs_ci && rhs_ci->getZExtValue() == 9116)) {
            return i;
          }
        }
      }
      return std::nullopt;
    };
    auto isPointerLikeStateValue = [&](llvm::Value *V) {
      V = V->stripPointerCasts();
      return llvm::isa<llvm::PtrToIntInst>(V) || V->getType()->isPointerTy();
    };
    auto findLocalSyntheticStateBase = [&](llvm::Function &F,
                                           llvm::StringRef callee_name,
                                           llvm::Instruction *InsertBefore)
        -> llvm::Value * {
      llvm::AllocaInst *match = nullptr;
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I);
          if (!AI)
            continue;
          if (AI->getName().starts_with(callee_name) &&
              AI->getAllocatedType()->isArrayTy()) {
            match = AI;
            break;
          }
        }
        if (match)
          break;
      }
      if (!match)
        return nullptr;
      llvm::IRBuilder<> Builder(InsertBefore);
      return Builder.CreatePtrToInt(match, i64_ty,
                                    callee_name + ".statebase.reuse");
    };
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.getName().ends_with("_native"))
        continue;
      auto caller_offsets = parseParamOffsets(F);
      if (caller_offsets.empty())
        continue;
      auto caller_state_arg_index = stateArgIndex(F);
      for (auto &BB : F) {
        for (auto &I : llvm::make_early_inc_range(BB)) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          auto *Callee = CI ? CI->getCalledFunction() : nullptr;
          if (!Callee || Callee->isDeclaration() ||
              !Callee->getName().ends_with("_native")) {
            continue;
          }

          auto callee_offsets = parseParamOffsets(*Callee);
          if (callee_offsets.size() != CI->arg_size())
            continue;
          auto callee_state_arg_index = stateArgIndex(*Callee);

          llvm::SmallVector<llvm::Value *, 16> new_args;
          bool changed = false;
          for (unsigned i = 0; i < CI->arg_size(); ++i) {
            auto *arg = CI->getArgOperand(i);
            llvm::Value *replacement = nullptr;
            if (callee_state_arg_index && i == *callee_state_arg_index &&
                !isPointerLikeStateValue(arg)) {
              if (caller_state_arg_index &&
                  *caller_state_arg_index < F.arg_size()) {
                replacement = F.getArg(*caller_state_arg_index);
              } else {
                replacement =
                    findLocalSyntheticStateBase(F, Callee->getName(), CI);
              }
            }
            int target_off = callee_offsets[i];
            llvm::Value *mapped_caller_arg = nullptr;
            if (!replacement && target_off >= 0) {
              for (unsigned j = 0; j < caller_offsets.size() && j < F.arg_size();
                   ++j) {
                if (caller_offsets[j] == target_off) {
                  mapped_caller_arg = F.getArg(j);
                  break;
                }
              }
            }
            bool needs_repair =
                llvm::isa<llvm::PoisonValue>(arg) ||
                llvm::isa<llvm::UndefValue>(arg);
            if (!needs_repair && replacement && arg != replacement)
              needs_repair = true;
            if (!needs_repair && mapped_caller_arg) {
              if (auto *caller_arg = llvm::dyn_cast<llvm::Argument>(arg);
                  caller_arg && caller_arg->getParent() == &F &&
                  caller_arg != mapped_caller_arg) {
                needs_repair = true;
              } else if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(arg);
                         ci && ci->isZero()) {
                needs_repair = true;
              }
            }
            if (!needs_repair) {
              new_args.push_back(arg);
              continue;
            }

            if (!replacement)
              replacement = mapped_caller_arg;
            if (!replacement)
              replacement = llvm::ConstantInt::get(i64_ty, 0);
            if (replacement->getType() != arg->getType()) {
              llvm::IRBuilder<> Builder(CI);
              if (replacement->getType()->isIntegerTy() &&
                  arg->getType()->isIntegerTy()) {
                replacement = Builder.CreateIntCast(replacement, arg->getType(),
                                                    false,
                                                    Callee->getName() +
                                                        ".poisonfix.cast");
              } else if (replacement->getType()->isPointerTy() &&
                         arg->getType()->isIntegerTy()) {
                replacement = Builder.CreatePtrToInt(
                    replacement, arg->getType(),
                    Callee->getName() + ".poisonfix.pti");
              } else if (replacement->getType()->isIntegerTy() &&
                         arg->getType()->isPointerTy()) {
                replacement = Builder.CreateIntToPtr(
                    replacement, arg->getType(),
                    Callee->getName() + ".poisonfix.itp");
              }
            }
            new_args.push_back(replacement);
            changed = true;
          }

          if (!changed)
            continue;

          auto *new_call = llvm::CallInst::Create(
              Callee->getFunctionType(), Callee, new_args, CI->getName(),
              CI->getIterator());
          new_call->setCallingConv(CI->getCallingConv());
          new_call->setAttributes(CI->getAttributes());
          if (!CI->use_empty()) {
            if (CI->getType() == new_call->getType()) {
              CI->replaceAllUsesWith(new_call);
            } else if (llvm::isa<llvm::StructType>(new_call->getType())) {
              auto *ev = llvm::ExtractValueInst::Create(
                  new_call, {0}, "ret.primary",
                  std::next(new_call->getIterator()));
              CI->replaceAllUsesWith(ev);
            } else {
              CI->replaceAllUsesWith(llvm::PoisonValue::get(CI->getType()));
            }
          }
          CI->eraseFromParent();
          ++repaired;
        }
      }
    }
    if (repaired > 0 &&
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false)) {
      errs() << "[abi-post] sanitized-poison-native-helper-args=" << repaired
             << "\n";
    }
  };
  auto eraseNoOpSelfRecursiveNativeCalls = [&]() {
    unsigned erased = 0;
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.getName().ends_with("_native"))
        continue;
      for (auto &BB : F) {
        for (auto &I : llvm::make_early_inc_range(BB)) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!CI || CI->getCalledFunction() != &F || !CI->use_empty() ||
              CI->arg_size() != F.arg_size()) {
            continue;
          }
          bool same_args = true;
          for (unsigned i = 0; i < CI->arg_size(); ++i) {
            if (CI->getArgOperand(i) != F.getArg(i)) {
              same_args = false;
              break;
            }
          }
          if (!same_args)
            continue;
          CI->eraseFromParent();
          ++erased;
        }
      }
    }
    if (erased > 0 &&
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false)) {
      errs() << "[abi-post] erased-noop-self-recursive-native-calls=" << erased
             << "\n";
    }
  };
  auto buildFrontierCallbacks = [&]() {
    omill::FrontierCallbacks callbacks;
    callbacks.is_code_address = [&](uint64_t target) {
      return isCodeAddressInCurrentInput(target);
    };
    callbacks.has_defined_target = [&](uint64_t target) {
      return hasDefinedLiftedOrBlockTarget(target);
    };
    callbacks.normalize_target_pc = [&](uint64_t target) {
      return normalizeKnownVmContinuationTarget(target);
    };
    callbacks.is_executable_target = [&](uint64_t target) {
      return memory_map_holder->isExecutable(target, 1);
    };
    callbacks.is_protected_boundary = [&](uint64_t target) {
      return !RawBinary &&
             omill::classifyProtectedBoundary(pe.memory_map, target).has_value();
    };
    callbacks.is_exact_call_fallthrough_target = [&](uint64_t target) {
      return omill::isExactX86DirectControlFlowFallthrough(&pe.memory_map,
                                                           target);
    };
    callbacks.can_decode_target = [&](uint64_t target) {
      auto decodable =
          omill::isDecodableLiftTargetEntry(&pe.memory_map, target,
                                            opts.target_arch);
      return decodable.has_value() && *decodable;
    };
    callbacks.read_target_bytes = [&](uint64_t target, uint8_t *out,
                                      size_t size) {
      return pe.memory_map.read(target, out, static_cast<unsigned>(size));
    };
    callbacks.decode_target_summary = [&](uint64_t target)
        -> std::optional<omill::FrontierCallbacks::DecodedTargetSummary> {
      std::string probe_bytes;
      probe_bytes.resize(15);
      if (!pe.memory_map.read(target,
                              reinterpret_cast<uint8_t *>(probe_bytes.data()),
                              static_cast<unsigned>(probe_bytes.size()))) {
        return std::nullopt;
      }
      remill::Instruction inst;
      inst.Reset();
      if (!arch->DecodeInstruction(target, probe_bytes, inst,
                                   arch->CreateInitialContext())) {
        return std::nullopt;
      }

      omill::FrontierCallbacks::DecodedTargetSummary summary;
      summary.pc = target;
      summary.next_pc = inst.next_pc;
      summary.is_control_flow = inst.IsControlFlow();
      summary.is_conditional = inst.IsConditionalBranch();
      summary.is_call = inst.IsFunctionCall();
      summary.is_return = inst.IsFunctionReturn();
      summary.is_terminal = inst.IsFunctionReturn();
      switch (inst.category) {
        case remill::Instruction::kCategoryIndirectJump:
        case remill::Instruction::kCategoryConditionalIndirectJump:
        case remill::Instruction::kCategoryIndirectFunctionCall:
        case remill::Instruction::kCategoryConditionalIndirectFunctionCall:
          summary.is_indirect = true;
          break;
        default:
          break;
      }
      if (inst.branch_taken_pc)
        summary.branch_taken_pc = inst.branch_taken_pc;
      if (inst.branch_not_taken_pc)
        summary.branch_not_taken_pc = inst.branch_not_taken_pc;
      if (summary.is_call && !summary.branch_not_taken_pc && inst.next_pc)
        summary.branch_not_taken_pc = inst.next_pc;
      return summary;
    };
    return callbacks;
  };
  auto advanceSessionOwnedFrontierWork =
      [&](omill::FrontierDiscoveryPhase phase, llvm::StringRef label) {
        if (RawBinary || !block_lifter || !iterative_session ||
            !devirtualization_plan.enable_devirtualization) {
          return false;
        }
        appendDebugMarker((llvm::Twine("frontier:") + label +
                           ":before_callbacks")
                              .str()
                              .c_str());
        auto callbacks = buildFrontierCallbacks();
        appendDebugMarker((llvm::Twine("frontier:") + label +
                           ":after_callbacks")
                              .str()
                              .c_str());
        appendDebugMarker((llvm::Twine("frontier:") + label +
                           ":before_discover")
                              .str()
                              .c_str());
        if (events.detailed()) {
          events.emitInfo("frontier_discovery_started",
                          "session-owned frontier discovery started",
                          {{"label", label.str()}});
        }
        auto round =
            devirtualization_orchestrator.runFrontierRound(
                *module, *projection_lifter, callbacks, phase);
        if (round.crashed) {
          errs() << "WARNING: late frontier advance crashed for " << label
                 << "\n";
          if (events.detailed()) {
            events.emitWarn("frontier_advance_crashed",
                            "session-owned frontier advance crashed",
                            {{"label", label.str()}});
          }
          return false;
        }
        appendDebugMarker((llvm::Twine("frontier:") + label +
                           ":after_discover")
                              .str()
                              .c_str());
        if (events.detailed()) {
          events.emitInfo("frontier_advance_completed",
                          "session-owned frontier advance completed",
                          {{"label", label.str()},
                           {"summary",
                            devirtualization_orchestrator
                                .summarizeFrontierAdvance(round.advance)}});
          events.emitInfo(
              "frontier_discovery_completed",
              "session-owned frontier discovery completed",
              {{"label", label.str()},
               {"summary",
                devirtualization_orchestrator.summarizeFrontierAdvance(
                    round.discover)}});
        }
        appendDebugMarker((llvm::Twine("frontier:") + label +
                           ":after_advance")
                              .str()
                              .c_str());
        const bool changed = round.changed;
        const bool debug_late_closure_targets =
            parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
        if (debug_late_closure_targets) {
          errs() << "[frontier] " << label << " discover "
                 << devirtualization_orchestrator.summarizeFrontierAdvance(
                        round.discover)
                 << "\n";
          errs() << "[frontier] " << label << " advance "
                 << devirtualization_orchestrator.summarizeFrontierAdvance(
                        round.advance)
                 << "\n";
          for (const auto &item : omill::collectSessionFrontierWorkItems(
                   devirtualization_orchestrator.session())) {
            if (!item.target_pc)
              continue;
            errs() << "[frontier] item=0x" << llvm::utohexstr(*item.target_pc)
                   << " kind=" << omill::toString(item.kind)
                   << " status=" << omill::toString(item.status)
                   << " id=" << item.identity << "\n";
          }
        }
        if (!changed)
          return false;

        MAM.invalidate(*module, llvm::PreservedAnalyses::none());
        omill::repairMalformedPHIs(*module);
        errs() << "[frontier] " << label << " "
               << devirtualization_orchestrator.summarizeFrontierAdvance(
                      round.advance)
               << "\n";
        return true;
      };
  auto noteAbiPostCleanupStep = [&](llvm::StringRef label, bool starting) {
    const bool debug_abi_post_cleanup =
        parseBoolEnv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS").value_or(false);
    if (debug_abi_post_cleanup) {
      errs() << "[abi-post-step] " << (starting ? "begin " : "end ") << label
             << "\n";
    }
    if (events.detailed()) {
      events.emitInfo(starting ? "abi_post_cleanup_step_started"
                               : "abi_post_cleanup_step_completed",
                      starting ? "abi post-cleanup step started"
                               : "abi post-cleanup step completed",
                      {{"label", label.str()}});
    }
  };
  llvm::SmallVector<std::string, 8> unresolved_pc_output_roots;
  std::optional<omill::FrontierCallbacks> output_recovery_frontier_callbacks;
  if (!RawBinary && block_lifter && iterative_session &&
      devirtualization_plan.enable_devirtualization) {
    output_recovery_frontier_callbacks = buildFrontierCallbacks();
  }
  if (!RawBinary && NoABI && devirtualization_plan.enable_devirtualization) {
    const bool early_boundary_rewrite =
        rewriteSuppressedBoundaryFallthroughsInCurrentModule();
    const bool early_boundary_materialization =
        materializeConstantBoundaryPlaceholdersInCurrentModule();
    if (early_boundary_rewrite || early_boundary_materialization) {
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      omill::repairMalformedPHIs(*module);
    }
    annotateVmUnresolvedContinuationsInCurrentModule();
    __try {
      (void)wireImportedPushJumpBoundaryContinuationsInCurrentModule();
    } __except (1) {
      errs() << "WARNING: early push-jump continuation seeding crashed; continuing "
                "with current module state\n";
      events.emitWarn("early_push_jump_continuation_seeding_crashed",
                      "early push-jump continuation seeding crashed", {});
    }
  }
  const bool precise_runtime_output_recovery_logs =
      parseBoolEnv("OMILL_DEBUG_RUNTIME_OUTPUT_RECOVERY").value_or(false);
  omill::tooling::OutputRecoveryOptionInputs output_recovery_option_inputs;
  output_recovery_option_inputs.raw_binary = RawBinary;
  output_recovery_option_inputs.no_abi = NoABI;
  output_recovery_option_inputs.use_block_lifting = opts.use_block_lifting;
  output_recovery_option_inputs.enable_devirtualization =
      devirtualization_plan.enable_devirtualization;
  output_recovery_option_inputs.enable_precise_logs =
      precise_runtime_output_recovery_logs;
  output_recovery_option_inputs.allow_noabi_postmain_rounds =
      allow_noabi_postmain_rounds;
  output_recovery_option_inputs.allow_abi_postmain_rounds =
      allow_abi_postmain_rounds;
  output_recovery_option_inputs.enable_nested_vm_enter_child_import =
      !RawBinary && !NoABI &&
      parseBoolEnv("OMILL_ENABLE_NESTED_VM_ENTER_CHILD_IMPORT").value_or(false);
  output_recovery_option_inputs.max_vm_enter_child_imports =
      parseUnsignedEnv("OMILL_MAIN_ROOT_CHILD_MAX_VM_ENTER_IMPORTS")
          .value_or(1u);
  auto output_recovery_options =
      omill::tooling::buildOutputRecoveryOptions(
          output_recovery_option_inputs);

  omill::tooling::OmillLiftOutputRecoveryBindings output_recovery_bindings;
  output_recovery_bindings.telemetry.append_debug_marker =
      [&](llvm::StringRef marker) {
        auto marker_text = marker.str();
        appendDebugMarker(marker_text.c_str());
      };
  output_recovery_bindings.telemetry.emit_warn_event =
      [&](llvm::StringRef code, llvm::StringRef message,
          std::optional<int64_t> round) {
        errs() << "WARNING: " << message;
        if (round)
          errs() << " round " << *round;
        errs() << "\n";
        if (round) {
          events.emitWarn(code, message, {{"round", *round}});
        } else {
          events.emitWarn(code, message);
        }
      };
  output_recovery_bindings.telemetry.precise_log =
      [&](const omill::RuntimePreciseLogEvent &event) {
        errs() << "[runtime-precise] " << event.component << ":"
               << event.stage;
        if (event.round)
          errs() << " round=" << *event.round;
        if (event.target_pc)
          errs() << " target=0x" << llvm::utohexstr(*event.target_pc);
        errs() << " " << event.message;
        if (event.detail && !event.detail->empty())
          errs() << " detail=" << *event.detail;
        errs() << "\n";
        if (events.enabled() && events.detailed()) {
          llvm::json::Object payload;
          payload["component"] = event.component;
          payload["stage"] = event.stage;
          if (event.round)
            payload["round"] = static_cast<int64_t>(*event.round);
          if (event.target_pc)
            payload["target_pc"] = hexString(*event.target_pc);
          if (event.detail && !event.detail->empty())
            payload["detail"] = *event.detail;
          events.emitInfo("runtime_precise_log", event.message,
                          std::move(payload));
        }
      };
  output_recovery_bindings.telemetry.note_abi_post_cleanup_step =
      [&](llvm::StringRef label, bool starting) {
        noteAbiPostCleanupStep(label, starting);
      };

  output_recovery_bindings.cleanup.run_late_closure_canonicalization =
      [&](llvm::StringRef reason) { runLateClosureCanonicalization(reason); };
  output_recovery_bindings.cleanup.run_post_patch_cleanup =
      [&](llvm::StringRef reason) { runPostPatchCleanup(reason); };
  output_recovery_bindings.cleanup.run_final_output_cleanup =
      [&]() { runFinalOutputCleanup(); };
  output_recovery_bindings.cleanup.annotate_vm_unresolved_continuations =
      [&]() { annotateVmUnresolvedContinuationsInCurrentModule(); };
  output_recovery_bindings.cleanup.prune_to_defined_output_root_closure =
      [&]() { pruneToDefinedOutputRootClosure(); };
  output_recovery_bindings.cleanup.rerun_late_output_root_target_pipeline =
      [&]() { rerunLateOutputRootTargetPipeline(); };
  output_recovery_bindings.cleanup
      .sanitize_remaining_poison_native_helper_args =
      [&]() { sanitizeRemainingPoisonNativeHelperArgs(); };
  output_recovery_bindings.cleanup.erase_noop_self_recursive_native_calls =
      [&]() { eraseNoOpSelfRecursiveNativeCalls(); };
  output_recovery_bindings.cleanup.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase phase, llvm::StringRef label) {
        return advanceSessionOwnedFrontierWork(phase, label);
      };

  output_recovery_bindings.import.lift_child_text =
      [&](uint64_t target_pc, bool no_abi, bool enable_gsd,
          bool enable_recovery_mode, bool dump_virtual_model)
      -> std::optional<omill::tooling::ChildLiftTextArtifact> {
        auto child = runTerminalBoundaryChildLift(target_pc, no_abi, enable_gsd,
                                                  enable_recovery_mode,
                                                  dump_virtual_model);
        if (!child)
          return std::nullopt;
        return omill::tooling::ChildLiftTextArtifact{
            std::move(child->ir_text), std::move(child->model_text)};
      };
  output_recovery_bindings.import.import_executable_child_root =
      [&](uint64_t target_pc, const omill::ChildLiftArtifact &artifact,
          const omill::ChildImportPlan &import_plan,
          llvm::StringRef name_prefix) -> llvm::Function * {
        return importSimpleExecutableChildRoot(target_pc, artifact,
                                               import_plan, name_prefix,
                                               /*shallow_closure=*/false);
      };
  output_recovery_bindings.import.import_executable_snapshot_slice =
      [&](uint64_t target_pc, const omill::BinaryRegionSnapshot &snapshot,
          const omill::ChildImportPlan &import_plan) -> llvm::Function * {
        return importBoundedContinuationSnapshotSlice(target_pc, snapshot,
                                                     import_plan);
      };
  output_recovery_bindings.import.import_recovered_terminal_boundary_function =
      [&](llvm::StringRef ir_text, uint64_t target_pc,
          std::string *rejection_reason) -> llvm::Function * {
        return importRecoveredTerminalBoundaryFunction(ir_text, target_pc,
                                                       rejection_reason);
      };
  output_recovery_bindings.import.note_imported_target = [&](uint64_t target_pc) {
    if (iterative_session)
      iterative_session->noteLiftedTarget(target_pc);
  };

  output_recovery_bindings.target_queries
      .collect_executable_placeholder_declaration_targets = [&]() {
        auto targets = collectExecutablePlaceholderDeclarationTargets();
        return llvm::SmallVector<uint64_t, 16>(targets.begin(), targets.end());
      };
  output_recovery_bindings.target_queries
      .collect_declared_structural_targets_with_defined_implementations = [&]() {
        auto targets =
            collectDeclaredStructuralTargetsWithDefinedImplementations();
        return llvm::SmallVector<uint64_t, 16>(targets.begin(), targets.end());
      };
  output_recovery_bindings.target_queries
      .collect_output_root_constant_code_call_targets = [&]() {
        auto targets = collectOutputRootConstantCodeCallTargets();
        return llvm::SmallVector<uint64_t, 16>(targets.begin(), targets.end());
      };
  output_recovery_bindings.target_queries
      .collect_output_root_constant_calli_targets = [&]() {
        auto targets = collectOutputRootConstantCalliTargets();
        return llvm::SmallVector<uint64_t, 16>(targets.begin(), targets.end());
      };
  output_recovery_bindings.target_queries
      .collect_output_root_constant_dispatch_targets = [&]() {
        auto targets = collectOutputRootConstantDispatchTargets();
        return llvm::SmallVector<uint64_t, 16>(targets.begin(), targets.end());
      };

  output_recovery_bindings.patches.patch_constant_inttoptr_calls_to_native =
      [&](llvm::ArrayRef<uint64_t> targets, llvm::StringRef marker,
          llvm::StringRef message) {
        patchConstantIntToPtrCallsToNative(targets, marker, message);
      };
  output_recovery_bindings.patches
      .patch_declared_lifted_or_block_calls_to_defined_targets =
      [&](llvm::ArrayRef<uint64_t> targets, llvm::StringRef marker,
          llvm::StringRef message) -> unsigned {
        return patchDeclaredLiftedOrBlockCallsToDefinedTargets(targets, marker,
                                                               message);
      };
  output_recovery_bindings.patches.patch_constant_calli_targets_to_direct_calls =
      [&](llvm::ArrayRef<uint64_t> targets, llvm::StringRef marker,
          llvm::StringRef message) -> unsigned {
        return patchConstantCalliTargetsToDirectCalls(targets, marker, message);
      };
  output_recovery_bindings.patches
      .patch_constant_dispatch_targets_to_direct_calls =
      [&](llvm::ArrayRef<uint64_t> targets, llvm::StringRef marker,
          llvm::StringRef message) -> unsigned {
        return patchConstantDispatchTargetsToDirectCalls(targets, marker,
                                                         message);
      };

  auto output_recovery_callbacks =
      omill::tooling::buildOmillLiftOutputRecoveryCallbacks(
          *module, MAM, output_recovery_bindings);

  omill::OutputRecoverySummary output_recovery_summary;
  appendDebugMarker("runtime-output-recovery:before");
  const bool terminal_boundary_recovery_mode =
      std::getenv("OMILL_TERMINAL_BOUNDARY_RECOVERY") != nullptr;
  const bool skip_runtime_output_recovery =
      large_noabi_lift && NoABI && opts.generic_static_devirtualize;
  if (terminal_boundary_recovery_mode) {
    appendDebugMarker("runtime-output-recovery:skipped-terminal-recovery");
    events.emitInfo(
        "runtime_output_recovery_skipped",
        "skipping runtime-owned output recovery during terminal-boundary recovery",
        {});
  } else if (skip_runtime_output_recovery) {
    appendDebugMarker("runtime-output-recovery:skipped-large-noabi-gsd");
    events.emitInfo(
        "runtime_output_recovery_skipped",
        "skipping runtime-owned output recovery for large no-abi generic-static module",
        {});
  } else if (!NoABI && devirtualization_plan.enable_devirtualization) {
    appendDebugMarker("runtime-output-recovery:skipped-abi");
    events.emitInfo(
        "runtime_output_recovery_skipped",
        "skipping ABI runtime-owned output recovery in favor of truthful tail projection");
  } else {
    __try {
      output_recovery_summary = devirtualization_runtime.runOutputRecovery(
          *module, block_lifter ? projection_lifter.get() : nullptr,
          output_recovery_frontier_callbacks ? &*output_recovery_frontier_callbacks
                                            : nullptr,
          output_recovery_options, output_recovery_callbacks);
      appendDebugMarker("runtime-output-recovery:after");
    } __except (1) {
      appendDebugMarker("runtime-output-recovery:crashed");
      errs() << "WARNING: runtime-owned output recovery crashed; continuing with "
                "current module state\n";
      events.emitWarn("runtime_output_recovery_crashed",
                      "runtime-owned output recovery crashed", {});
    }
  }
  if (events.detailed()) {
    events.emitInfo(
        "runtime_output_recovery_completed",
        "runtime-owned output recovery completed",
        {{"changed", output_recovery_summary.changed},
         {"noabi_imported_children",
          static_cast<int64_t>(output_recovery_summary.noabi_imported_children)},
         {"abi_imported_vm_enter_children",
          static_cast<int64_t>(
              output_recovery_summary.abi_imported_vm_enter_children)},
         {"patched_declared_targets",
          static_cast<int64_t>(output_recovery_summary.patched_declared_targets)},
         {"patched_code_targets",
          static_cast<int64_t>(output_recovery_summary.patched_code_targets)},
         {"patched_calli_targets",
          static_cast<int64_t>(output_recovery_summary.patched_calli_targets)},
         {"patched_dispatch_targets",
          static_cast<int64_t>(
              output_recovery_summary.patched_dispatch_targets)},
         {"artifact_bundle_count",
          static_cast<int64_t>(output_recovery_summary.artifact_bundles.size())}});
  }
  emitRuntimeArtifactBundleEvents(events, "output_recovery",
                                  output_recovery_summary.artifact_bundles);
  for (const auto &note : output_recovery_summary.notes)
    errs() << "[runtime-output-recovery] " << note << "\n";

  auto tryProjectAbiTailGraphFromMainRootNoABIChild = [&]() -> bool {
    if (RawBinary || NoABI)
      return false;

    auto noabi_child = runTerminalBoundaryChildLift(
        func_va, /*no_abi=*/true, opts.generic_static_devirtualize,
        /*enable_recovery_mode=*/false, /*dump_virtual_model=*/false,
        /*allow_recursive_output_recovery=*/true);
    if (!noabi_child || noabi_child->ir_text.empty())
      return false;

    llvm::SMDiagnostic parse_error;
    auto child_module =
        llvm::parseAssemblyString(noabi_child->ir_text, parse_error, ctx);
    if (!child_module)
      return false;
    if (verifyModule(*child_module, nullptr))
      return false;

    auto tail_graph = devirtualization_runtime.buildFinalTailGraph(*child_module);
    if (tail_graph.nodes.empty() && tail_graph.edges.empty())
      return false;

    const bool refined =
        devirtualization_runtime.refineFinalTailGraphWithBoundaryReplay(
            *child_module, tail_graph, output_recovery_callbacks,
            opts.generic_static_devirtualize);

    annotateVmUnresolvedContinuationsInCurrentModule();
    if (!devirtualization_runtime.projectFinalTailGraphIntoAbiModule(*module,
                                                                     tail_graph)) {
      return false;
    }

    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    omill::refreshTerminalBoundaryRecoveryMetadata(*module);
    omill::repairMalformedPHIs(*module);
    events.emitInfo(
        "abi_tail_graph_projected",
        "projected recursive unresolved tails from truthful no-ABI child into ABI output",
        {{"tail_nodes", static_cast<int64_t>(tail_graph.nodes.size())},
         {"tail_edges", static_cast<int64_t>(tail_graph.edges.size())},
         {"boundary_refined", refined}});
    return true;
  };

  if (!RawBinary) {
    bool repaired_constant_boundaries =
        materializeConstantBoundaryPlaceholdersInCurrentModule();
    bool imported_boundary_continuations = false;
    appendDebugMarker("continuation-import:before");
    __try {
      imported_boundary_continuations =
          wireImportedPushJumpBoundaryContinuationsInCurrentModule();
    } __except (1) {
      errs() << "WARNING: push-jump continuation import crashed; keeping current "
                "module state\n";
      events.emitWarn("push_jump_continuation_import_crashed",
                      "push-jump continuation import crashed", {});
    }
    appendDebugMarker("continuation-import:after");
    // The skip predicate intentionally uses opts.no_abi_mode (not the NoABI
    // CLI flag) so it fires whenever the compat plan promoted us into a
    // large no-abi generic-static run, even when the user did not pass
    // -no-abi explicitly. Each truthful child lift re-enters the full
    // sub-pipeline and can burn 80-180s; on default compact runs that
    // dominates wall-clock and never converges. large_noabi_lift already
    // implies opts.no_abi_mode, so this collapses to the documented intent
    // in docs/GENERIC_STATIC_DEVIRTUALIZATION_TODO.md:1359-1361.
    const bool skip_truthful_child_imports =
        large_noabi_lift && opts.generic_static_devirtualize;
    bool imported_truthful_children =
        !skip_truthful_child_imports &&
        !parseBoolEnv("OMILL_DISABLE_RECURSIVE_OUTPUT_RECOVERY").value_or(false) &&
        importTruthfulOutputRootChildrenInCurrentModule();
    if (skip_truthful_child_imports && events.detailed()) {
      events.emitInfo(
          "truthful_child_import_skipped",
          "skipping truthful child imports for large no-abi generic-static module");
    }
    bool repaired_vm_unresolved =
        !NoABI && materializeVmUnresolvedContinuationPlaceholdersInCurrentModule();
    if (repaired_constant_boundaries || imported_boundary_continuations ||
        imported_truthful_children || repaired_vm_unresolved) {
      const bool rewrote_suppressed_fallthroughs =
          rewriteSuppressedBoundaryFallthroughsInCurrentModule();
      const bool erased_unused_modeled_decls =
          eraseUnusedModeledPlaceholderDeclarationsInCurrentModule();
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      if (rewrote_suppressed_fallthroughs || erased_unused_modeled_decls)
        MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      annotateVmUnresolvedContinuationsInCurrentModule();
      if (NoABI && !hasOpenOutputRootHazards()) {
        ModulePassManager RepairMPM;
        omill::buildLateCleanupPipeline(RepairMPM, opts);
        __try {
          RepairMPM.run(*module, MAM);
        } __except (1) {
          errs() << "WARNING: repaired late cleanup rerun crashed; keeping "
                    "placeholder-repaired module state\n";
          events.emitWarn("repaired_late_cleanup_crashed",
                          "late cleanup rerun after placeholder repair crashed",
                          {});
          MAM.invalidate(*module, llvm::PreservedAnalyses::none());
        }
      }
    }
    if (!NoABI)
      unresolved_pc_output_roots = collectUnresolvedOutputRootPcCalls();
  }

  dumpModuleIfEnvEnabled(*module, "OMILL_DEBUG_DUMP_BEFORE_UNRESOLVED_CHECK",
                         "before_unresolved_check.ll");

  if (!unresolved_pc_output_roots.empty()) {
    errs() << "Warning: unresolved lifted control transfer remains before final "
              "repair/finalization: ";
    for (size_t i = 0; i < unresolved_pc_output_roots.size(); ++i) {
      if (i)
        errs() << ", ";
      errs() << unresolved_pc_output_roots[i];
    }
    errs() << "\n";
  }

  auto repairStableZeroArityOutputRoots =
      [&](llvm::ArrayRef<std::string> root_names) {
        if (RawBinary || NoABI)
          return false;
        auto &cc_info = MAM.getResult<omill::CallingConventionAnalysis>(*module);
        auto abiScalarType = [&](unsigned size) -> llvm::Type * {
          if (size == 0)
            return llvm::Type::getVoidTy(ctx);
          return llvm::Type::getIntNTy(ctx, size * 8u);
        };
        auto bytePtrAtOffset = [&](llvm::IRBuilder<> &B, llvm::Value *base,
                                   uint64_t offset) -> llvm::Value * {
          return B.CreateInBoundsGEP(B.getInt8Ty(), base, B.getInt64(offset));
        };

        bool changed = false;
        for (const auto &root_name : root_names) {
          auto *shell = module->getFunction(root_name);
          if (!shell || shell->isDeclaration() || shell->arg_size() != 0)
            continue;

          llvm::SmallPtrSet<llvm::Function *, 4> internal_roots;
          for (auto &BB : *shell) {
            for (auto &I : BB) {
              auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
              auto *callee = CB ? CB->getCalledFunction() : nullptr;
              if (!callee || callee->isDeclaration())
                continue;
              if (callee->hasFnAttribute("omill.internal_output_root"))
                internal_roots.insert(callee);
            }
          }
          if (internal_roots.size() != 1)
            continue;

          auto *internal_root = *internal_roots.begin();
          auto *abi = cc_info.getABI(internal_root);
          if (!abi || abi->cc != omill::DetectedCC::kWin64 || abi->hasStructReturn() ||
              abi->numXMMParams() != 0 || abi->numExtraGPRParams() != 0 ||
              abi->numStackParams() != 0 ||
              (abi->numParams() == 0 && !abi->ret.has_value())) {
            continue;
          }

          llvm::SmallVector<llvm::Type *, 4> param_tys;
          uint64_t max_offset = 0;
          for (const auto &param : abi->params) {
            param_tys.push_back(abiScalarType(param.size));
            max_offset = std::max<uint64_t>(max_offset,
                                            param.state_offset + param.size);
          }
          llvm::Type *ret_ty = llvm::Type::getVoidTy(ctx);
          if (abi->ret) {
            ret_ty = abiScalarType(abi->ret->size);
            max_offset = std::max<uint64_t>(max_offset,
                                            abi->ret->state_offset + abi->ret->size);
          }
          const uint64_t state_size = std::max<uint64_t>(4096, max_offset + 0x40);

          const std::string public_name = shell->getName().str();
          std::string hidden_shell_name = "__omill_zero_arity_shell_" + public_name;
          while (module->getFunction(hidden_shell_name))
            hidden_shell_name += "_";

          const bool had_closed_slice =
              shell->hasFnAttribute("omill.closed_root_slice");
          const bool had_closed_slice_root =
              shell->hasFnAttribute("omill.closed_root_slice_root");

          shell->removeFnAttr("omill.output_root");
          shell->addFnAttr("omill.internal_output_root", "1");
          shell->setLinkage(llvm::GlobalValue::InternalLinkage);
          shell->setName(hidden_shell_name);

          auto *shim = llvm::Function::Create(
              llvm::FunctionType::get(ret_ty, param_tys, false),
              llvm::GlobalValue::ExternalLinkage, public_name, *module);
          shim->addFnAttr("omill.output_root", "1");
          if (had_closed_slice)
            shim->addFnAttr("omill.closed_root_slice", "1");
          if (had_closed_slice_root)
            shim->addFnAttr("omill.closed_root_slice_root", "1");

          auto *entry = llvm::BasicBlock::Create(ctx, "entry", shim);
          llvm::IRBuilder<> B(entry);
          auto *state_storage_ty =
              llvm::ArrayType::get(llvm::Type::getInt8Ty(ctx), state_size);
          auto *state_storage = B.CreateAlloca(state_storage_ty, nullptr, "abi.state");
          state_storage->setAlignment(llvm::Align(16));
          auto *state_ptr = B.CreatePointerBitCastOrAddrSpaceCast(
              state_storage, internal_root->getArg(0)->getType());
          B.CreateMemSet(
              B.CreatePointerBitCastOrAddrSpaceCast(
                  state_storage, llvm::PointerType::get(ctx, 0)),
              B.getInt8(0), state_size, llvm::Align(16));

          unsigned arg_index = 0;
          for (const auto &param : abi->params) {
            auto *dest = B.CreatePointerBitCastOrAddrSpaceCast(
                bytePtrAtOffset(B, state_storage, param.state_offset),
                llvm::PointerType::get(ctx, 0));
            B.CreateStore(shim->getArg(arg_index++), dest);
          }

          const uint64_t entry_va = omill::extractEntryVA(public_name);
          auto *pc = llvm::ConstantInt::get(llvm::Type::getInt64Ty(ctx), entry_va);
          auto *memory = llvm::ConstantPointerNull::get(
              llvm::cast<llvm::PointerType>(internal_root->getArg(2)->getType()));
          B.CreateCall(internal_root, {state_ptr, pc, memory});

          if (!abi->ret) {
            B.CreateRetVoid();
          } else {
            auto *ret_ptr = B.CreatePointerBitCastOrAddrSpaceCast(
                bytePtrAtOffset(B, state_storage, abi->ret->state_offset),
                llvm::PointerType::get(ctx, 0));
            B.CreateRet(B.CreateLoad(ret_ty, ret_ptr));
          }
          changed = true;
        }

        if (changed)
          MAM.invalidate(*module, llvm::PreservedAnalyses::none());
        return changed;
      };

  if (!RawBinary && !NoABI && countDefinedOutputRoots() == 0u) {
    errs() << "Error: no defined output root remains after ABI recovery\n";
    return fail(1, "no defined output root remains after ABI recovery");
  }

  llvm::SmallVector<std::string, 8> suspicious_zero_arity_output_roots;
  if (!RawBinary && !NoABI && devirtualization_plan.enable_devirtualization)
    devirtualization_orchestrator.refreshSessionState(*module);
  const bool has_blocking_session_frontier_state =
      !RawBinary && !NoABI && devirtualization_plan.enable_devirtualization &&
      devirtualization_orchestrator.hasBlockingUnstableFrontierState(*module);
  if (!RawBinary && !NoABI)
    suspicious_zero_arity_output_roots = collectSuspiciousZeroArityOutputRoots();
  if (!suspicious_zero_arity_output_roots.empty()) {
    bool devirtualization_invariants_clean = false;
    if (devirtualization_plan.enable_devirtualization &&
        unresolved_pc_output_roots.empty() && countDefinedOutputRoots() != 0u) {
      devirtualization_invariants_clean =
          devirtualization_orchestrator
              .collectInvariantViolations(*module,
                                          devirtualization_request.output_mode)
              .empty();
    }
    if (devirtualization_plan.enable_devirtualization &&
        (!has_blocking_session_frontier_state ||
         devirtualization_invariants_clean) &&
        unresolved_pc_output_roots.empty() &&
        countDefinedOutputRoots() != 0u) {
      if (repairStableZeroArityOutputRoots(suspicious_zero_arity_output_roots))
        suspicious_zero_arity_output_roots =
            collectSuspiciousZeroArityOutputRoots();
      if (!suspicious_zero_arity_output_roots.empty()) {
        errs() << "Warning: retaining suspicious zero-arity stack-backed output "
                  "root(s) because devirtualization state is stable: ";
        for (size_t i = 0; i < suspicious_zero_arity_output_roots.size(); ++i) {
          if (i)
            errs() << ", ";
          errs() << suspicious_zero_arity_output_roots[i];
        }
        errs() << "\n";
        if (events.detailed()) {
          events.emitWarn(
              "suspicious_zero_arity_output_root_retained",
              "retaining suspicious zero-arity output roots because "
              "devirtualization state is stable",
              {{"count",
                static_cast<int64_t>(suspicious_zero_arity_output_roots.size())}});
        }
        suspicious_zero_arity_output_roots.clear();
      }
    }
  }
  if (!suspicious_zero_arity_output_roots.empty()) {
    errs() << "Error: suspicious zero-arity stack-backed output root(s): ";
    for (size_t i = 0; i < suspicious_zero_arity_output_roots.size(); ++i) {
      if (i)
        errs() << ", ";
      errs() << suspicious_zero_arity_output_roots[i];
    }
    errs() << "\n";
    return fail(1, "suspicious zero-arity stack-backed output roots");
  }

  llvm::SmallVector<std::string, 8> suspicious_stack_backed_output_roots;
  if (!RawBinary && !NoABI && !normalized_export_thunk_root)
    suspicious_stack_backed_output_roots =
        collectSuspiciousStackBackedOutputRoots();
  if (!suspicious_stack_backed_output_roots.empty()) {
    errs() << "Error: suspicious stack-backed output root(s): ";
    for (size_t i = 0; i < suspicious_stack_backed_output_roots.size(); ++i) {
      if (i)
        errs() << ", ";
      errs() << suspicious_stack_backed_output_roots[i];
    }
    errs() << "\n";
    return fail(1, "suspicious stack-backed output roots");
  }

  // Final textual output should never contain dangling PHI predecessors.
  omill::repairMalformedPHIs(*module);
  if (devirtualization_plan.enable_devirtualization) {
    devirtualization_orchestrator.recordEpoch(
        omill::DevirtualizationEpoch::kAbiOrNoAbiFinalization, *module,
        devirtualization_request.output_mode, /*changed=*/true,
        "final cleanup complete");
    emit_latest_devirtualization_epoch("final cleanup complete");
    if (large_noabi_lift && NoABI && opts.generic_static_devirtualize) {
      events.emitInfo(
          "devirtualization_invariants_skipped",
          "devirtualization invariants skipped for large no-abi generic-static module",
          {{"lifted_functions",
            static_cast<int64_t>(countLiftedPipelineFunctions())}});
    } else {
      auto devirtualization_violations =
          devirtualization_orchestrator.collectInvariantViolations(
              *module, devirtualization_request.output_mode);
      devirtualization_orchestrator.recordEpoch(
          omill::DevirtualizationEpoch::kFinalInvariantVerification, *module,
          devirtualization_request.output_mode, /*changed=*/false,
          "final verification complete");
      emit_latest_devirtualization_epoch("final verification complete");
      if (devirtualization_violations.empty()) {
        events.emitInfo("devirtualization_invariants_verified",
                        "devirtualization invariants verified",
                        {{"mode", NoABI ? "noabi" : "abi"}});
      } else {
        llvm::json::Array violations_json;
        for (const auto &violation : devirtualization_violations) {
          violations_json.push_back(violation);
          errs() << "Devirtualization invariant violation: " << violation
                 << "\n";
        }
        llvm::json::Object payload;
        payload["mode"] = NoABI ? "noabi" : "abi";
        payload["count"] =
            static_cast<int64_t>(devirtualization_violations.size());
        payload["violations"] = std::move(violations_json);
        events.emitWarn("devirtualization_invariants_failed",
                        "devirtualization invariants failed",
                        std::move(payload));
        if (devirtualization_policy.enforce_final_invariants) {
          return fail(1, "devirtualization invariants failed");
        }
      }
    }
  }

  auto collectReachableExternalCallsFromOutputRoots = [&]() {
    auto classifyLeakClass = [](llvm::StringRef callee_name) {
      if (callee_name == "__omill_missing_block_handler")
        return std::string("missing_block_handler");
      if (callee_name.starts_with("__remill_read_memory_") ||
          callee_name.starts_with("__remill_write_memory_")) {
        return std::string("remill_memory_intrinsic");
      }
      if (callee_name.starts_with("omill_executable_target_"))
        return std::string("executable_placeholder");
      if (callee_name.starts_with("omill_vm_enter_target_"))
        return std::string("vm_enter_placeholder");
      if (callee_name.starts_with("omill_native_target_") ||
          callee_name.starts_with("omill_native_boundary_")) {
        return std::string("native_placeholder");
      }
      if (callee_name.starts_with("__remill_"))
        return std::string("remill_runtime_intrinsic");
      return std::string("external_call");
    };

    struct ExternalCallWarning {
      std::string root_name;
      std::string caller_name;
      std::string callee_name;
      std::string leak_class;
    };

    if (std::getenv("OMILL_TERMINAL_BOUNDARY_RECOVERY") != nullptr) {
      return llvm::SmallVector<ExternalCallWarning, 8>{};
    }


    llvm::SmallVector<llvm::Function *, 8> output_roots;
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root") ||
          F.hasFnAttribute("omill.internal_output_root")) {
        continue;
      }
      output_roots.push_back(&F);
    }
    if (output_roots.empty()) {
      for (auto &F : *module) {
        if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
          output_roots.push_back(&F);
      }
    }

    auto shouldStopAtImportedRecoveryChild = [&](llvm::Function &F) {
      auto fact = omill::readExecutableTargetFact(F);
      return fact &&
             imported_recovery_mode_truthful_targets.contains(fact->raw_target_pc);
    };


    llvm::SmallVector<ExternalCallWarning, 8> warnings;
    for (auto *root : output_roots) {
      llvm::SmallVector<llvm::Function *, 16> worklist = {root};
      llvm::SmallPtrSet<llvm::Function *, 16> visited;
      while (!worklist.empty()) {
        auto *current = worklist.pop_back_val();
        if (!current || !visited.insert(current).second)
          continue;
        for (auto &BB : *current) {
          for (auto &I : BB) {
            auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
            auto *callee = CB ? CB->getCalledFunction() : nullptr;
            if (!callee)
              continue;
            if (callee->isIntrinsic())
              continue;
            if (callee->isDeclaration()) {
              if (omill::isLoweringHelperCalleeName(callee->getName()))
                continue;
              warnings.push_back(
                  {root->getName().str(), current->getName().str(),
                   callee->getName().str(),
                   classifyLeakClass(callee->getName())});
              continue;
            }
            if (shouldStopAtImportedRecoveryChild(*callee))
              continue;
            worklist.push_back(callee);
          }
        }
      }
    }
    return warnings;
  };


  auto eraseUnreachableLiftedResidueFromOutputRoots = [&]() {
    llvm::SmallVector<llvm::Function *, 8> output_roots;
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root") ||
          F.hasFnAttribute("omill.internal_output_root")) {
        continue;
      }
      output_roots.push_back(&F);
    }
    if (output_roots.empty()) {
      for (auto &F : *module) {
        if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
          output_roots.push_back(&F);
      }
    }

    llvm::SmallPtrSet<llvm::Function *, 32> reachable;
    llvm::SmallVector<llvm::Function *, 32> worklist(output_roots.begin(),
                                                     output_roots.end());
    while (!worklist.empty()) {
      auto *current = worklist.pop_back_val();
      if (!current || current->isDeclaration() || !reachable.insert(current).second)
        continue;
      for (auto &BB : *current) {
        for (auto &I : BB) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          auto *callee = CB ? CB->getCalledFunction() : nullptr;
          if (!callee || callee->isDeclaration())
            continue;
          worklist.push_back(callee);
        }
      }
    }

    auto shouldDelete = [&](llvm::Function &F) {
      if (reachable.contains(&F) || F.isDeclaration())
        return false;
      if (F.hasFnAttribute("omill.output_root") ||
          F.hasFnAttribute("omill.internal_output_root")) {
        return false;
      }
      auto name = F.getName();
      return name.starts_with("blk_") || name.starts_with("sub_") ||
             name.starts_with("block_") ||
             name.starts_with("omill_") ||
             name.starts_with("__omill_recovered_child_");
    };

    llvm::SmallVector<llvm::Function *, 16> to_delete;
    for (auto &F : *module) {
      if (shouldDelete(F))
        to_delete.push_back(&F);
    }
    if (to_delete.empty())
      return false;

    for (auto *F : to_delete)
      F->deleteBody();
    for (auto *F : to_delete) {
      if (F->use_empty())
        F->eraseFromParent();
    }
    return true;
  };

  auto repairDetachedRecoveryExitBlocks = [&]() {
    bool changed = false;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      llvm::BasicBlock *self_loop = nullptr;
      llvm::BasicBlock *detached_exit = nullptr;
      llvm::BasicBlock *pred_block = nullptr;
      for (auto &BB : F) {
        auto *term = BB.getTerminator();
        if (auto *BI = llvm::dyn_cast_or_null<llvm::BranchInst>(term);
            BI && BI->isUnconditional() && BI->getSuccessor(0) == &BB) {
          if (self_loop) {
            self_loop = nullptr;
            break;
          }
          self_loop = &BB;
          continue;
        }
        if (llvm::pred_empty(&BB) && llvm::isa<llvm::ReturnInst>(term)) {
          if (detached_exit) {
            detached_exit = nullptr;
            break;
          }
          detached_exit = &BB;
        }
      }
      if (!self_loop || !detached_exit)
        continue;
      for (auto *pred : llvm::predecessors(self_loop)) {
        if (pred == self_loop)
          continue;
        if (pred_block) {
          pred_block = nullptr;
          break;
        }
        pred_block = pred;
      }
      if (!pred_block)
        continue;
      auto *pred_br = llvm::dyn_cast_or_null<llvm::BranchInst>(pred_block->getTerminator());
      if (!pred_br || !pred_br->isUnconditional() ||
          pred_br->getSuccessor(0) != self_loop)
        continue;
      pred_br->setSuccessor(0, detached_exit);
      for (auto &I : llvm::make_early_inc_range(*pred_block)) {
        auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        auto *callee = CB ? CB->getCalledFunction() : nullptr;
        if (!CB || !callee || !CB->use_empty())
          continue;
        auto name = callee->getName();
        if (name.starts_with("omill_native_boundary_") ||
            name.starts_with("omill_executable_target_") ||
            name.starts_with("omill_native_target_")) {
          CB->eraseFromParent();
          changed = true;
        }
      }
      changed = true;
    }
    return changed;
  };


  auto reachable_external_calls = collectReachableExternalCallsFromOutputRoots();

  auto hasRepairableReachablePlaceholder = [&]() {
    return llvm::any_of(reachable_external_calls, [](const auto &warning) {
      return warning.leak_class == "executable_placeholder" ||
             warning.leak_class == "native_placeholder" ||
             warning.leak_class == "vm_enter_placeholder";
    });
  };

  auto repairReachableDeclaredStructuralTargets = [&]() {
    if (std::getenv("OMILL_TERMINAL_BOUNDARY_RECOVERY") != nullptr)
      return false;
    if (!block_lifter || !hasRepairableReachablePlaceholder())
      return false;


    const bool recovery_chain_active =
        !imported_recovery_mode_truthful_targets.empty();


    llvm::SmallVector<llvm::Function *, 8> output_roots;
    for (auto &F : *module) {
      if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root") ||
          F.hasFnAttribute("omill.internal_output_root")) {
        continue;
      }
      output_roots.push_back(&F);
    }
    if (output_roots.empty()) {
      for (auto &F : *module) {
        if (!F.isDeclaration() && F.hasFnAttribute("omill.output_root"))
          output_roots.push_back(&F);
      }
    }
    struct RepairTarget {
      uint64_t pc = 0;
      bool allow_trivial_self_loop = false;
      bool import_terminal_boundary = false;
      unsigned use_count = 0;
    };
    llvm::SmallDenseMap<uint64_t, RepairTarget, 16> target_map;
    for (auto *root : output_roots) {
      llvm::SmallVector<llvm::Function *, 16> worklist = {root};
      llvm::SmallPtrSet<llvm::Function *, 16> visited;
      while (!worklist.empty()) {
        auto *current = worklist.pop_back_val();
        if (!current || !visited.insert(current).second)
          continue;
        for (auto &BB : *current) {
          for (auto &I : BB) {
            auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
            auto *callee = CB ? CB->getCalledFunction() : nullptr;
            if (!callee || callee->isIntrinsic())
              continue;
            if (callee->isDeclaration()) {
              llvm::StringRef name = callee->getName();
              uint64_t target_pc = 0;
              bool allow_trivial_self_loop = false;
              bool import_terminal_boundary = false;
              if (name.starts_with("blk_") || name.starts_with("sub_") ||
                  name.starts_with("block_")) {
                target_pc = omill::extractStructuralCodeTargetPC(*callee);
              } else if (name.starts_with("omill_executable_target_")) {
                if (auto exec = omill::readExecutableTargetFact(*callee))
                  target_pc = exec->raw_target_pc;
                allow_trivial_self_loop = true;
              } else if ((name.starts_with("omill_native_boundary_") ||
                          name.starts_with("omill_vm_enter_boundary_")) &&
                         !recovery_chain_active) {
                if (auto boundary = omill::readBoundaryFact(*callee);
                    boundary && boundary->boundary_pc) {
                  target_pc = *boundary->boundary_pc;
                } else {
                  target_pc = omill::extractEntryVA(name);
                }
                import_terminal_boundary = (target_pc != 0);
              }
              if (!target_pc)
                continue;
              auto &target = target_map[target_pc];
              target.pc = target_pc;
              target.allow_trivial_self_loop =
                  target.allow_trivial_self_loop || allow_trivial_self_loop;
              target.import_terminal_boundary =
                  target.import_terminal_boundary || import_terminal_boundary;
              target.use_count += 1;
              continue;
            }
            auto fact = omill::readExecutableTargetFact(*callee);
            if (fact &&
                imported_recovery_mode_truthful_targets.contains(fact->raw_target_pc) &&
                latest_recovery_mode_truthful_target &&
                fact->raw_target_pc != *latest_recovery_mode_truthful_target) {
              continue;
            }
            worklist.push_back(callee);
          }
        }
      }
    }

    llvm::SmallVector<RepairTarget, 16> targets;
    targets.reserve(target_map.size());
    for (const auto &[_, target] : target_map)
      targets.push_back(target);
    llvm::sort(targets, [](const RepairTarget &lhs, const RepairTarget &rhs) {
      const bool lhs_recovery = lhs.allow_trivial_self_loop;
      const bool rhs_recovery = rhs.allow_trivial_self_loop;
      if (lhs_recovery != rhs_recovery)
        return lhs_recovery && !rhs_recovery;
      if (lhs.use_count != rhs.use_count)
        return lhs.use_count > rhs.use_count;
      return lhs.pc < rhs.pc;
    });


    bool repaired = false;
    std::optional<std::string> truthful_requested_root_noabi_ir;
    auto getTruthfulRequestedRootNoAbiIR = [&]() -> const std::optional<std::string> & {
      if (truthful_requested_root_noabi_ir.has_value())
        return truthful_requested_root_noabi_ir;
      auto noabi_child = runTerminalBoundaryChildLift(
          func_va, /*no_abi=*/true, opts.generic_static_devirtualize,
          /*enable_recovery_mode=*/false, /*dump_virtual_model=*/false,
          /*allow_recursive_output_recovery=*/true);
      if (noabi_child && !noabi_child->ir_text.empty())
        truthful_requested_root_noabi_ir = std::move(noabi_child->ir_text);
      else
        truthful_requested_root_noabi_ir = std::nullopt;
      return truthful_requested_root_noabi_ir;
    };
    auto materializeDeclaredBoundaryBodiesFromTruthfulNoAbi = [&]() {
      if (NoABI)
        return false;
      const auto &noabi_ir = getTruthfulRequestedRootNoAbiIR();
      if (!noabi_ir || noabi_ir->empty())
        return false;

      bool changed = false;
      llvm::SmallVector<llvm::Function *, 8> to_erase;
      for (auto &F : *module) {
        if (!F.isDeclaration())
          continue;
        if (!(F.getName().starts_with("omill_native_boundary_") ||
              F.getName().starts_with("omill_vm_enter_boundary_"))) {
          continue;
        }

        uint64_t target_pc = 0;
        if (auto boundary = omill::readBoundaryFact(F);
            boundary && boundary->boundary_pc) {
          target_pc = *boundary->boundary_pc;
        } else {
          target_pc = omill::extractEntryVA(F.getName());
        }
        if (!target_pc)
          continue;

        auto *imported = importRecoveredTerminalBoundaryFunction(*noabi_ir, target_pc);
        if (!imported || imported->isDeclaration() ||
            imported->getFunctionType() != F.getFunctionType()) {
          continue;
        }

        F.replaceAllUsesWith(imported);
        to_erase.push_back(&F);
        changed = true;
      }

      for (auto *decl : to_erase) {
        if (decl && decl->getParent() == module.get() && decl->use_empty())
          decl->eraseFromParent();
      }
      return changed;
    };

    const auto prior_recovery_target = latest_recovery_mode_truthful_target;
    for (const auto &target : targets) {
      if (auto *defined = findPreferredDefinedCodeTargetFunction(target.pc);
          defined && !defined->isDeclaration()) {
        repaired = rewriteDeclarationCallsitesForTarget(target.pc, *defined) ||
                   repaired;
        continue;
      }
      if (target.import_terminal_boundary && !NoABI) {
        const auto &noabi_ir = getTruthfulRequestedRootNoAbiIR();
        if (noabi_ir && !noabi_ir->empty()) {
          if (auto *imported = importRecoveredTerminalBoundaryFunction(
                  *noabi_ir, target.pc)) {
            repaired = rewriteDeclarationCallsitesForTarget(target.pc, *imported) ||
                       repaired;
            continue;
          }
        }
      }
      auto *imported = importTruthfulChildRootForTarget(
          target.pc, /*enable_recovery_mode=*/true,
          target.allow_trivial_self_loop);
      if (!imported || imported->isDeclaration())
        continue;
      repaired = rewriteDeclarationCallsitesForTarget(target.pc, *imported) ||
                 repaired;
      if (latest_recovery_mode_truthful_target != prior_recovery_target)
        break;
    }
    if (materializeDeclaredBoundaryBodiesFromTruthfulNoAbi())
      repaired = true;
    return repaired;
  };


  omill::FinalStateRecoveryRequest final_state_recovery_request;
  final_state_recovery_request.no_abi = NoABI;
  final_state_recovery_request.enabled =
      NoABI && devirtualization_plan.enable_devirtualization &&
      !disable_recursive_output_recovery;
  final_state_recovery_request.enable_gsd = opts.generic_static_devirtualize;
  auto buildFinalizationSummary = [&]() {
    auto summary = devirtualization_runtime.finalizeOutput(
        *module, devirtualization_plan.enable_devirtualization);
    if (auto plan = devirtualization_runtime.planFinalStateRecovery(
            *module, final_state_recovery_request)) {
      summary.final_state_recovery_plan = *plan;
    }
    if (auto final_state_bundle = devirtualization_runtime.runFinalStateRecovery(
            *module, final_state_recovery_request, output_recovery_callbacks)) {
      summary.artifact_bundles.push_back(*final_state_bundle);
    }
    return summary;
  };

  auto eraseDeadDispatcherShellCalls = [&]() {
    auto isDispatcherShellLoop = [&](llvm::Function &F) {
      if (F.isDeclaration() || F.empty() || F.size() != 1)
        return false;
      const auto &BB = F.getEntryBlock();
      const llvm::CallBase *self_call = nullptr;
      const llvm::ReturnInst *ret = nullptr;
      for (auto &I : BB) {
        if (I.isDebugOrPseudoInst())
          continue;
        if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
          auto *callee = CB->getCalledFunction();
          if (callee == &F) {
            if (self_call)
              return false;
            self_call = CB;
            continue;
          }
          if (!callee || !callee->isDeclaration())
            return false;
          continue;
        }
        if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(&I)) {
          if (ret)
            return false;
          ret = RI;
          continue;
        }
      }
      return self_call && ret &&
             ret->getReturnValue() &&
             ret->getReturnValue()->stripPointerCasts() == self_call;
    };

    auto returnedCallCallee = [&](llvm::Function &F) -> llvm::Function * {
      if (F.isDeclaration())
        return nullptr;
      for (auto &BB : F) {
        llvm::CallBase *returned_call = nullptr;
        for (auto &I : BB) {
          if (I.isDebugOrPseudoInst())
            continue;
          if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(&I)) {
            if (returned_call && RI->getReturnValue() == returned_call)
              return returned_call->getCalledFunction();
            return nullptr;
          }
          if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I))
            returned_call = CB;
        }
      }
      return nullptr;
    };


    bool changed = false;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        for (auto &I : llvm::make_early_inc_range(BB)) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!CI || !CI->use_empty() || CI->isMustTailCall())
            continue;
          auto *callee = CI->getCalledFunction();
          auto *returned_callee =
              callee ? returnedCallCallee(*callee) : nullptr;
          if (!callee ||
              !(isDispatcherShellLoop(*callee) ||
                (returned_callee && returned_callee->isDeclaration())))
            continue;

          llvm::Instruction *next_non_debug = nullptr;
          for (auto it = std::next(CI->getIterator()), end = BB.end(); it != end; ++it) {
            if (it->isDebugOrPseudoInst())
              continue;
            next_non_debug = &*it;
            break;
          }
          if (!next_non_debug || !llvm::isa<llvm::CallBase>(next_non_debug))
            continue;
          CI->eraseFromParent();
          changed = true;
        }
      }
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        llvm::CallBase *prior_value_call = nullptr;
        llvm::CallInst *self_tail_call = nullptr;
        llvm::ReturnInst *ret = nullptr;
        for (auto &I : BB) {
          if (I.isDebugOrPseudoInst())
            continue;
          if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
            auto *callee = CB->getCalledFunction();
            if (callee == &F) {
              auto *CI = llvm::dyn_cast<llvm::CallInst>(CB);
              if (CI && CI->isMustTailCall())
                self_tail_call = CI;
              continue;
            }
            if (CB->getType() == F.getReturnType())
              prior_value_call = CB;
            continue;
          }
          if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(&I))
            ret = RI;
        }
        if (!self_tail_call || !ret || ret->getReturnValue() != self_tail_call ||
            !prior_value_call) {
          continue;
        }
        ret->setOperand(0, prior_value_call);
        self_tail_call->eraseFromParent();
        changed = true;
      }
    }
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      for (auto &BB : F) {
        llvm::CallBase *prior_value_call = nullptr;
        llvm::CallInst *tail_call = nullptr;
        llvm::ReturnInst *ret = nullptr;
        for (auto &I : BB) {
          if (I.isDebugOrPseudoInst())
            continue;
          if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
            auto *CI = llvm::dyn_cast<llvm::CallInst>(CB);
            if (CI && CI->isMustTailCall()) {
              tail_call = CI;
              continue;
            }
            if (CB->getType() == F.getReturnType())
              prior_value_call = CB;
            continue;
          }
          if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(&I))
            ret = RI;
        }
        if (!tail_call || !ret || ret->getReturnValue() != tail_call ||
            !prior_value_call) {
          continue;
        }
        auto *tail_callee = tail_call->getCalledFunction();
        if (!tail_callee)
          continue;
        auto *returned_callee = returnedCallCallee(*tail_callee);
        if (!returned_callee || returned_callee != prior_value_call->getCalledFunction())
          continue;
        ret->setOperand(0, prior_value_call);
        tail_call->eraseFromParent();
        changed = true;
      }
    }

    }
    return changed;
  };

  auto markAbiInternalRootClosuresAlwaysInline = [&]() {
    if (RawBinary || NoABI)
      return false;
    bool changed = false;
    llvm::SmallVector<llvm::Function *, 32> worklist;
    llvm::SmallPtrSet<llvm::Function *, 32> visited;
    for (auto &F : *module) {
      if (!F.isDeclaration() && F.hasFnAttribute("omill.internal_output_root"))
        worklist.push_back(&F);
    }
    while (!worklist.empty()) {
      auto *current = worklist.pop_back_val();
      if (!current || current->isDeclaration() || !visited.insert(current).second)
        continue;
      if (current->hasFnAttribute(llvm::Attribute::NoInline) ||
          current->hasFnAttribute(llvm::Attribute::OptimizeNone) ||
          !current->hasFnAttribute(llvm::Attribute::AlwaysInline)) {
        current->removeFnAttr(llvm::Attribute::NoInline);
        current->removeFnAttr(llvm::Attribute::OptimizeNone);
        current->addFnAttr(llvm::Attribute::AlwaysInline);
        changed = true;
      }
      for (auto &BB : *current) {
        for (auto &I : BB) {
          auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
          auto *callee = CB ? CB->getCalledFunction() : nullptr;
          if (callee && !callee->isDeclaration())
            worklist.push_back(callee);
        }
      }
    }
    return changed;
  };







  auto finalization_summary = buildFinalizationSummary();
  // In-process native-boundary repair: collect reachable
  // `omill_native_boundary_*` PCs and drive the already-initialized
  // block lifter directly to materialize their bodies, then rewrite the
  // declaration call-sites to the freshly-lifted `blk_<pc>` definitions.
  // This runs after `finalizeOutput` because that's when the placeholder
  // declarations are materialized.
  if (opts.use_block_lifting && iterative_session &&
      !parseBoolEnv("OMILL_SKIP_NATIVE_BOUNDARY_REPAIR").value_or(false)) {
    const bool debug_repair =
        parseBoolEnv("OMILL_DEBUG_NATIVE_BOUNDARY_REPAIR").value_or(false);
    auto debug_log = [&](const llvm::Twine &msg) {
      if (debug_repair) {
        errs() << "[native-boundary-repair] " << msg << "\n";
        errs().flush();
      }
    };

    // Collect reachable unresolved code-target PCs. Picks up both
    // `omill_native_boundary_*` placeholders (what `finalizeOutput`
    // created) and unlifted `blk_*` / `sub_*` / `block_*` declarations
    // (successors of newly-lifted blocks that haven't been lifted yet).
    // The second bucket is critical for convergence: each round of
    // lifting introduces new declarations for the lifted block's
    // statically-known successors, and without picking those up we'd
    // leave a trail of open edges on every repair round.
    auto collectReachablePCs = [&]() {
      llvm::DenseSet<uint64_t> targets;
      for (auto &F : *module) {
        if (F.isDeclaration())
          continue;
        if (!F.hasFnAttribute("omill.output_root") &&
            !F.hasFnAttribute("omill.closed_root_slice_root"))
          continue;
        llvm::SmallPtrSet<llvm::Function *, 32> visited;
        llvm::SmallVector<llvm::Function *, 32> worklist{&F};
        while (!worklist.empty()) {
          auto *cur = worklist.pop_back_val();
          if (!visited.insert(cur).second)
            continue;
          for (auto &BB : *cur) {
            for (auto &I : BB) {
              auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
              auto *callee = CB ? CB->getCalledFunction() : nullptr;
              if (!callee)
                continue;
              if (!callee->isDeclaration()) {
                worklist.push_back(callee);
                continue;
              }
              auto name = callee->getName();
              uint64_t pc = 0;
              if (name.starts_with("omill_native_boundary_")) {
                if (auto bnd = omill::readBoundaryFact(*callee);
                    bnd && bnd->boundary_pc)
                  pc = *bnd->boundary_pc;
                else
                  pc = omill::extractStructuralCodeTargetPC(name);
              } else if (name.starts_with("blk_") ||
                         name.starts_with("sub_") ||
                         name.starts_with("block_")) {
                pc = omill::extractStructuralCodeTargetPC(name);
              }
              if (pc && isCodeAddressInCurrentInput(pc))
                targets.insert(pc);
            }
          }
        }
      }
      return targets;
    };

    auto rewriteBoundaryCallsites =
        [&](uint64_t target_pc, llvm::Function &replacement) -> bool {
      bool changed = false;
      llvm::SmallVector<llvm::CallBase *, 8> to_rewrite;
      llvm::SmallPtrSet<llvm::Function *, 8> unique_decls;
      auto matches = [&](llvm::Function &callee) {
        if (!callee.isDeclaration())
          return false;
        auto name = callee.getName();
        if (!name.starts_with("omill_native_boundary_"))
          return false;
        uint64_t pc = 0;
        if (auto bnd = omill::readBoundaryFact(callee);
            bnd && bnd->boundary_pc)
          pc = *bnd->boundary_pc;
        else
          pc = omill::extractEntryVA(name);
        return pc == target_pc;
      };
      for (auto &F : *module) {
        if (F.isDeclaration())
          continue;
        for (auto &BB : F) {
          for (auto &I : BB) {
            auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
            if (!CB)
              continue;
            auto *callee = CB->getCalledFunction();
            if (!callee || !matches(*callee))
              continue;
            if (callee->getFunctionType() != replacement.getFunctionType())
              continue;
            to_rewrite.push_back(CB);
            unique_decls.insert(callee);
          }
        }
      }
      for (auto *CB : to_rewrite) {
        if (auto *CI = llvm::dyn_cast<llvm::CallInst>(CB))
          CI->setCalledFunction(&replacement);
        else if (auto *II = llvm::dyn_cast<llvm::InvokeInst>(CB))
          II->setCalledFunction(&replacement);
        changed = true;
      }
      for (auto *decl : unique_decls) {
        if (decl && decl->getParent() == module.get() &&
            decl->isDeclaration() && decl->use_empty())
          decl->eraseFromParent();
      }
      return changed;
    };

    // Phase 0: restore stripped `__remill_*` intrinsic declarations so we
    // can rebuild the arch's IntrinsicTable against the current module.
    // Pipeline passes (LowerRemillIntrinsics, LowerMemory/Atomic/etc.) erase
    // most intrinsic declarations once they're no longer needed; the cached
    // pointers inside `arch->GetInstrinsicTable()` and the BlockLifter that
    // captured it are therefore dangling post-finalize. We source fresh
    // declarations (and their exact function types) from a freshly-loaded
    // semantics module — the same module `remill::LoadArchSemantics` returns
    // at startup. Linking the full semantics module back would be wasteful
    // (megabytes of template bodies that we already stripped); we only
    // create NEW declarations in the current module with the same names
    // and signatures.
    auto fresh_semantics = remill::LoadArchSemantics(arch.get());
    if (!fresh_semantics) {
      debug_log("failed to load fresh semantics; skipping repair");
      goto native_boundary_repair_done;
    }
    unsigned restored = 0;
    unsigned already_present = 0;
    for (auto &F : *fresh_semantics) {
      auto name = F.getName();
      if (!name.starts_with("__remill_"))
        continue;
      if (auto *existing = module->getFunction(name)) {
        (void)existing;
        ++already_present;
        continue;
      }
      auto *fn = llvm::Function::Create(
          F.getFunctionType(), llvm::GlobalValue::ExternalLinkage, name,
          module.get());
      // Mark restored intrinsics as noinline+optnone so the nearby
      // cleanup/GlobalDCE passes don't discard them before the lifter
      // writes its calls. `IntrinsicTable::IntrinsicTable` will also
      // re-apply the canonical attributes.
      fn->addFnAttr(llvm::Attribute::NoInline);
      fn->addFnAttr(llvm::Attribute::OptimizeNone);
      ++restored;
    }
    debug_log(llvm::Twine("intrinsics restored=") + llvm::Twine(restored) +
              " already_present=" + llvm::Twine(already_present));

    // `InstructionLifter::Impl::Impl` looks up `ISEL_INVALID_INSTRUCTION`
    // and `ISEL_UNSUPPORTED_INSTRUCTION` global variables in the module
    // and CHECK-aborts if either is missing. Pipeline passes strip these
    // globals during semantics cleanup, so we clone them (and the
    // semantic helper functions they reference) from the fresh semantics
    // module. `CloneFunction` would also work but is overkill — the
    // globals are constant pointers and we only need their targets to
    // exist as declarations so `GetInstructionFunction` can return a
    // non-null `Function*`. The referenced helpers don't need bodies
    // because we're not actually expecting invalid / unsupported
    // instructions in the blocks we lift.
    unsigned isel_globals_restored = 0;
    unsigned isel_helpers_restored = 0;
    for (auto &gv : fresh_semantics->globals()) {
      auto name = gv.getName();
      if (!name.starts_with("ISEL_"))
        continue;
      if (module->getGlobalVariable(name, /*AllowInternal=*/true))
        continue;
      if (!gv.hasInitializer())
        continue;
      auto *init = gv.getInitializer()->stripPointerCasts();
      auto *fresh_fn = llvm::dyn_cast<llvm::Function>(init);
      if (!fresh_fn)
        continue;

      // Ensure the semantic helper function is declared in main.
      llvm::Function *main_fn = module->getFunction(fresh_fn->getName());
      if (!main_fn) {
        main_fn = llvm::Function::Create(
            fresh_fn->getFunctionType(),
            llvm::GlobalValue::ExternalLinkage, fresh_fn->getName(),
            module.get());
        main_fn->addFnAttr(llvm::Attribute::NoInline);
        main_fn->addFnAttr(llvm::Attribute::OptimizeNone);
        ++isel_helpers_restored;
      }

      // Create the ISEL_* global with an initializer pointing at
      // main's declaration of the helper.
      new llvm::GlobalVariable(
          *module, main_fn->getType(), /*isConstant=*/true,
          llvm::GlobalValue::ExternalLinkage, main_fn, name);
      ++isel_globals_restored;
    }
    debug_log(llvm::Twine("isel_globals_restored=") +
              llvm::Twine(isel_globals_restored) +
              " isel_helpers_restored=" +
              llvm::Twine(isel_helpers_restored));

    // Refresh arch's cached IntrinsicTable so subsequent BlockLifter
    // constructors see fresh `llvm::Function*` pointers into the current
    // module (instead of the dangling ones from before finalizeOutput).
    arch->RefreshIntrinsicTable(module.get());

    // Build a fresh BlockLifter that picks up the refreshed intrinsic
    // table. The existing `block_lifter` / `projection_lifter` captured
    // the old pointers at construction and we don't want to mutate them
    // while the rest of the post-finalize code may still reference them.
    auto repair_block_lifter =
        std::make_unique<omill::BlockLifter>(arch.get(), *block_manager);
    if (lift_db)
      repair_block_lifter->SetLiftDatabase(lift_db.get());

    // Phase A: identify and drive the fresh block lifter one PC at a time.
    // Bound iterations generously so the fixpoint converges even when the
    // reachable set grows before it shrinks (newly-lifted blocks discover
    // new successors). Converge when no lifts are attempted in a round.
    constexpr unsigned kMaxRounds = 64;
    constexpr unsigned kMaxTargetsPerRound = 128;
    unsigned last_reachable = 0;
    unsigned stall_rounds = 0;
    for (unsigned round = 0; round < kMaxRounds; ++round) {
      auto targets_set = collectReachablePCs();
      debug_log(llvm::Twine("round=") + llvm::Twine(round) +
                " reachable=" + llvm::Twine(targets_set.size()));
      if (targets_set.empty())
        break;
      llvm::SmallVector<uint64_t, 32> ordered(targets_set.begin(),
                                                targets_set.end());
      llvm::sort(ordered);
      if (ordered.size() > kMaxTargetsPerRound)
        ordered.resize(kMaxTargetsPerRound);

      unsigned lift_attempts = 0;
      unsigned lift_successes = 0;
      unsigned lift_crashes = 0;
      for (uint64_t pc : ordered) {
        auto *existing =
            findLiftedOrBlockFunction(pc, /*native=*/false);
        if (existing && !existing->isDeclaration()) {
          ++lift_successes;  // already have a body; just needs rewrite
          continue;
        }
        ++lift_attempts;
        bool ok = false;
#if defined(_WIN32)
        __try {
#endif
          llvm::SmallVector<uint64_t, 4> discovered;
          auto *fn =
              repair_block_lifter->LiftBlock(pc, discovered);
          ok = (fn != nullptr);
#if defined(_WIN32)
        } __except (1) {
          debug_log(llvm::Twine("LIFT-SEH-CRASH 0x") +
                    llvm::Twine::utohexstr(pc));
          ++lift_crashes;
          ok = false;
        }
#endif
        if (ok)
          ++lift_successes;
      }
      debug_log(llvm::Twine("round=") + llvm::Twine(round) +
                " attempts=" + llvm::Twine(lift_attempts) +
                " successes=" + llvm::Twine(lift_successes) +
                " crashes=" + llvm::Twine(lift_crashes));

      // Phase B: rewrite callsites for every target that now has a body.
      unsigned rewrote = 0;
      for (uint64_t pc : ordered) {
        auto *def = findLiftedOrBlockFunction(pc, /*native=*/false);
        if (!def || def->isDeclaration())
          continue;
        if (rewriteBoundaryCallsites(pc, *def))
          ++rewrote;
      }
      debug_log(llvm::Twine("round=") + llvm::Twine(round) +
                " rewrote=" + llvm::Twine(rewrote));
      // Converge when no new lifts were attempted (everything already
      // defined) or when the reachable set stops shrinking for 2 rounds.
      if (lift_attempts == 0)
        break;
      if (targets_set.size() >= last_reachable && last_reachable > 0) {
        if (++stall_rounds >= 2)
          break;
      } else {
        stall_rounds = 0;
      }
      last_reachable = targets_set.size();
    }

    if (debug_repair) {
      auto final_targets = collectReachablePCs();
      unsigned blk_decls = 0;
      unsigned blk_defs = 0;
      for (auto &F : *module) {
        if (F.getName().starts_with("blk_")) {
          if (F.isDeclaration())
            ++blk_decls;
          else
            ++blk_defs;
        }
      }
      debug_log(llvm::Twine("final reachable=") +
                llvm::Twine(final_targets.size()) +
                " blk_defs=" + llvm::Twine(blk_defs) +
                " blk_decls=" + llvm::Twine(blk_decls));
    }

    // Link the fresh semantics module into main with `LinkOnlyNeeded`
    // so the semantic template declarations referenced by the newly-
    // lifted blocks (e.g. `_ZN12_GLOBAL__N_1<mangled>`) get their
    // function bodies pulled in. `AlwaysInlinerPass` can then inline
    // those templates into the lifted blocks, replacing each raw
    // semantic call with its instruction-level body. After inlining,
    // `LowerRemillIntrinsicsPass` converts the `__remill_read_memory_*`
    // / `__remill_flag_*` / etc. calls into native LLVM IR. The
    // result is closer in shape to the blocks the main pipeline
    // produces and can be cleaned up by the usual SROA/GVN/DSE sweep.
    //
    // Semantic templates in the remill bitcode have `internal`
    // linkage by default, which the linker treats as "not needed"
    // even when main has matching external declarations. Promote
    // them to external linkage before linking so `LinkOnlyNeeded`
    // actually pulls in the bodies.
    {
      unsigned promoted = 0;
      for (auto &F : *fresh_semantics) {
        if (F.isDeclaration())
          continue;
        if (!F.hasInternalLinkage() && !F.hasPrivateLinkage())
          continue;
        F.setLinkage(llvm::GlobalValue::ExternalLinkage);
        ++promoted;
      }
      debug_log(llvm::Twine("promoted ") + llvm::Twine(promoted) +
                " fresh semantics functions to external linkage");

      llvm::Linker linker(*module);
      if (linker.linkInModule(std::move(fresh_semantics),
                              llvm::Linker::Flags::LinkOnlyNeeded)) {
        debug_log("link of fresh semantics failed; skipping lowering");
        goto native_boundary_repair_lowering_done;
      }

      // Re-internalize every linked-in semantic template so GlobalDCE
      // can erase any that end up unused after the AlwaysInliner pass
      // below. They were only bumped to external linkage to make the
      // linker match the matching external declarations in main; the
      // templates are anonymous-namespace symbols in the source and
      // have no external consumers.
      unsigned internalized = 0;
      for (auto &F : *module) {
        if (F.isDeclaration())
          continue;
        auto name = F.getName();
        if (!name.starts_with("_ZN12_GLOBAL__N_"))
          continue;
        if (F.hasInternalLinkage() || F.hasPrivateLinkage())
          continue;
        F.setLinkage(llvm::GlobalValue::InternalLinkage);
        ++internalized;
      }
      debug_log(llvm::Twine("internalized ") + llvm::Twine(internalized) +
                " linked-in semantic templates");

      // The fresh semantics bitcode carries an `llvm.compiler.used`
      // array referencing every `ISEL_*` global (which in turn points
      // at every semantic template function). Without erasing it,
      // GlobalDCE has to keep all ~2000 semantic template bodies
      // alive. We don't need that retention — lifting is done.
      if (auto *gv = module->getGlobalVariable("llvm.compiler.used", true))
        gv->eraseFromParent();
      if (auto *gv = module->getGlobalVariable("llvm.used", true))
        gv->eraseFromParent();
    }

    // Mark every linked-in semantic template as `alwaysinline` so
    // `AlwaysInlinerPass` can fold them into the lifted block bodies.
    // The linked-in templates use the anonymous-namespace mangled
    // prefix `_ZN12_GLOBAL__N_` — that's the most reliable signal,
    // more reliable than `remill.function.type` metadata which
    // doesn't always survive module linking.
    {
      unsigned marked = 0;
      for (auto &F : *module) {
        if (F.isDeclaration())
          continue;
        auto name = F.getName();
        if (!name.starts_with("_ZN12_GLOBAL__N_"))
          continue;
        if (F.hasFnAttribute(llvm::Attribute::OptimizeNone))
          F.removeFnAttr(llvm::Attribute::OptimizeNone);
        if (F.hasFnAttribute(llvm::Attribute::NoInline))
          F.removeFnAttr(llvm::Attribute::NoInline);
        if (!F.hasFnAttribute(llvm::Attribute::AlwaysInline)) {
          F.addFnAttr(llvm::Attribute::AlwaysInline);
          ++marked;
        }
      }
      debug_log(llvm::Twine("marked semantic templates alwaysinline=") +
                llvm::Twine(marked));
    }

    // Erase the ISEL_* globals now (before cleanup_mpm) so GlobalDCE
    // can reach the linked-in semantic template bodies. The ISEL
    // globals were the only runtime references to those templates —
    // they're the lookup table remill's InstructionLifter queries.
    // With them gone, AlwaysInliner's post-inline erase can take the
    // templates, and GlobalDCE mops up any stragglers.
    {
      llvm::SmallVector<llvm::GlobalVariable *, 16> pre_cleanup_isel_to_erase;
      for (auto &gv : module->globals()) {
        if (!gv.getName().starts_with("ISEL_"))
          continue;
        pre_cleanup_isel_to_erase.push_back(&gv);
      }
      for (auto *gv : pre_cleanup_isel_to_erase) {
        gv->replaceAllUsesWith(
            llvm::UndefValue::get(gv->getType()));
        gv->eraseFromParent();
      }
      debug_log(llvm::Twine("pre-cleanup erased ") +
                llvm::Twine(pre_cleanup_isel_to_erase.size()) +
                " isel globals");
    }

    // Run AlwaysInliner + LowerRemillIntrinsics + standard cleanup on
    // the enlarged module. The passes are idempotent on already-
    // processed functions so they're safe to run module-wide.
    {
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      llvm::ModulePassManager cleanup_mpm;
      cleanup_mpm.addPass(llvm::AlwaysInlinerPass());
      {
        llvm::FunctionPassManager fpm;
        fpm.addPass(omill::LowerRemillIntrinsicsPass(
            omill::LowerCategories::Phase1 |
            omill::LowerCategories::Phase3 |
            omill::LowerCategories::Undefined |
            omill::LowerCategories::ResolvedDispatch));
        fpm.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
        fpm.addPass(llvm::EarlyCSEPass(/*UseMemorySSA=*/true));
        fpm.addPass(llvm::InstCombinePass());
        fpm.addPass(llvm::GVNPass());
        fpm.addPass(llvm::DSEPass());
        fpm.addPass(llvm::ADCEPass());
        fpm.addPass(llvm::InstCombinePass());
        fpm.addPass(llvm::SimplifyCFGPass());
        cleanup_mpm.addPass(
            llvm::createModuleToFunctionPassAdaptor(std::move(fpm)));
      }
      cleanup_mpm.addPass(llvm::GlobalDCEPass());
      cleanup_mpm.run(*module, MAM);
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());

      // Run a second explicit GlobalDCE in case the first one raced
      // with an analysis invalidation — the inline step frees up a
      // lot of unused template bodies and we want them gone.
      {
        llvm::ModulePassManager second_dce;
        second_dce.addPass(llvm::GlobalDCEPass());
        second_dce.run(*module, MAM);
        MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      }

      // Belt-and-braces: walk the module and erase any anonymous-
      // namespace semantic template definition that's still unused
      // after GlobalDCE. GlobalDCE is sometimes conservative with
      // symbols that have unusual comdat / linkage combinations the
      // remill bitcode attaches to its templates.
      unsigned direct_erased = 0;
      llvm::SmallVector<llvm::Function *, 32> templates_to_erase;
      for (auto &F : *module) {
        if (F.isDeclaration())
          continue;
        auto name = F.getName();
        if (!name.starts_with("_ZN12_GLOBAL__N_"))
          continue;
        if (!F.use_empty())
          continue;
        templates_to_erase.push_back(&F);
      }
      for (auto *F : templates_to_erase) {
        F->eraseFromParent();
        ++direct_erased;
      }
      debug_log(llvm::Twine("direct-erased ") + llvm::Twine(direct_erased) +
                " unused semantic templates");
    }
native_boundary_repair_lowering_done:;

    // Post-repair cleanup: erase any remaining ISEL_* globals (they
    // became unused after inlining) and any orphaned semantic helper
    // declarations that GlobalDCE didn't catch.
    llvm::SmallVector<llvm::GlobalVariable *, 16> isel_globals_to_erase;
    for (auto &gv : module->globals()) {
      if (!gv.getName().starts_with("ISEL_"))
        continue;
      if (gv.use_empty())
        isel_globals_to_erase.push_back(&gv);
    }
    for (auto *gv : isel_globals_to_erase)
      gv->eraseFromParent();

    llvm::SmallVector<llvm::Function *, 16> funcs_to_erase;
    for (auto &F : *module) {
      if (!F.isDeclaration())
        continue;
      auto name = F.getName();
      const bool is_restored_helper =
          name.starts_with("__remill_") ||
          name.starts_with("_ZN12_GLOBAL__N_");
      if (!is_restored_helper)
        continue;
      if (!F.use_empty())
        continue;
      funcs_to_erase.push_back(&F);
    }
    for (auto *F : funcs_to_erase)
      F->eraseFromParent();
    debug_log(llvm::Twine("post-repair cleanup erased ") +
              llvm::Twine(isel_globals_to_erase.size()) +
              " isel globals + " + llvm::Twine(funcs_to_erase.size()) +
              " decls");

    // Internalize every lifted helper that isn't an output root so
    // GlobalDCE can erase orphan chains that the main pipeline left
    // behind with external linkage. Without this step, any `blk_*` /
    // `sub_*` / `block_*` function with external linkage is assumed
    // to have external callers and retained — even if it's sitting
    // in an unreferenced island and its transitive call graph only
    // reaches other orphan helpers.
    unsigned internalized_helpers = 0;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      auto name = F.getName();
      if (!name.starts_with("blk_") && !name.starts_with("block_") &&
          !name.starts_with("sub_"))
        continue;
      if (F.hasFnAttribute("omill.output_root") ||
          F.hasFnAttribute("omill.closed_root_slice_root"))
        continue;
      if (F.hasLocalLinkage())
        continue;
      F.setLinkage(llvm::GlobalValue::InternalLinkage);
      ++internalized_helpers;
    }
    debug_log(llvm::Twine("internalized ") +
              llvm::Twine(internalized_helpers) +
              " non-root lifted helpers");

    // Run a final GlobalDCE sweep now that the orphan chains are
    // internal. This erases every unreferenced `blk_*` / `sub_*` and
    // in turn breaks the last chains that hold `omill_native_boundary_*`
    // declarations alive.
    if (internalized_helpers > 0) {
      llvm::ModulePassManager dce_mpm;
      dce_mpm.addPass(llvm::GlobalDCEPass());
      dce_mpm.run(*module, MAM);
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    }

    // With the orphan helpers gone, many `omill_native_boundary_*`
    // declarations are now unused. Erase them too.
    llvm::SmallVector<llvm::Function *, 16> boundary_to_erase;
    for (auto &F : *module) {
      if (!F.isDeclaration())
        continue;
      if (!F.getName().starts_with("omill_native_boundary_"))
        continue;
      if (!F.use_empty())
        continue;
      boundary_to_erase.push_back(&F);
    }
    for (auto *F : boundary_to_erase)
      F->eraseFromParent();
    debug_log(llvm::Twine("erased ") + llvm::Twine(boundary_to_erase.size()) +
              " orphan native_boundary decls");

    // Any remaining `omill_native_boundary_*` DEFINITIONS are bridge
    // bodies synthesized by `materializeKnownBoundaryBridge` earlier in
    // this function: a tiny inline emulation of a `push imm; jmp rel`
    // thunk (decrement RSP, store imm on stack, return memory). The
    // user-visible intent is that these should never appear in the
    // final IR as separate functions — they should be inlined into
    // the caller block at lift time. We can't undo the placeholder
    // creation without restructuring the main pipeline, but we can
    // convert them into inline IR here by marking each definition
    // `alwaysinline` + internal and running one more AlwaysInliner
    // pass. The bodies are ~6 instructions each so inlining them
    // costs nothing.
    llvm::SmallVector<llvm::Function *, 16> boundary_defs_to_inline;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      if (!F.getName().starts_with("omill_native_boundary_") &&
          !F.getName().starts_with("omill_vm_enter_boundary_"))
        continue;
      if (F.hasFnAttribute(llvm::Attribute::OptimizeNone))
        F.removeFnAttr(llvm::Attribute::OptimizeNone);
      if (F.hasFnAttribute(llvm::Attribute::NoInline))
        F.removeFnAttr(llvm::Attribute::NoInline);
      if (!F.hasFnAttribute(llvm::Attribute::AlwaysInline))
        F.addFnAttr(llvm::Attribute::AlwaysInline);
      if (!F.hasLocalLinkage())
        F.setLinkage(llvm::GlobalValue::InternalLinkage);
      boundary_defs_to_inline.push_back(&F);
    }
    debug_log(llvm::Twine("boundary bridge defs to inline=") +
              llvm::Twine(boundary_defs_to_inline.size()));
    if (!boundary_defs_to_inline.empty()) {
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      llvm::ModulePassManager inline_bridges;
      inline_bridges.addPass(llvm::AlwaysInlinerPass());
      inline_bridges.addPass(llvm::GlobalDCEPass());
      inline_bridges.run(*module, MAM);
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());

      // Some of the bridge definitions may still be alive as tail
      // callees of a musttail path that AlwaysInliner couldn't unwind
      // (musttail constraints). Direct-erase any that are now unused.
      llvm::SmallVector<llvm::Function *, 8> stragglers;
      for (auto *F : boundary_defs_to_inline) {
        if (F && F->getParent() == module.get() && F->use_empty())
          stragglers.push_back(F);
      }
      for (auto *F : stragglers)
        F->eraseFromParent();
      if (debug_repair) {
        unsigned remaining = 0;
        for (auto &F : *module) {
          auto name = F.getName();
          if (name.starts_with("omill_native_boundary_") ||
              name.starts_with("omill_vm_enter_boundary_"))
            ++remaining;
        }
        debug_log(llvm::Twine("boundary bridge defs remaining=") +
                  llvm::Twine(remaining));
      }
    }
  }
native_boundary_repair_done:;

  // Force-inline every `blk_*` / `block_*` helper that is reachable
  // from an output root into that root. The user-visible intent is:
  // for a virtualized function, collapse the whole lifted CFG into a
  // single monolithic function in the output so LLVM's standard -O2
  // passes can then attack the unified body. Opt-in via
  // `OMILL_ENABLE_OUTPUT_ROOT_FORCE_INLINE=1` because:
  //   1. The naive approach creates significant code duplication
  //      when a block is called from multiple sites.
  //   2. Running the standard scalar cleanup sweep (InstCombine,
  //      GVN, DSE, ADCE, SimplifyCFG) on the ~70k-instruction unified
  //      body collapses the whole thing to a single `unreachable` —
  //      a folding regression tied to how LLVM reasons about the
  //      unified state pointer. Only the safest subset (SROA +
  //      EarlyCSE + GlobalDCE) is applied here; InstCombine/GVN/
  //      SimplifyCFG are left for follow-up investigation.
  if (opts.no_abi_mode && opts.generic_static_devirtualize &&
      parseBoolEnv("OMILL_ENABLE_OUTPUT_ROOT_FORCE_INLINE").value_or(false)) {
    const bool debug_force_inline =
        parseBoolEnv("OMILL_DEBUG_OUTPUT_ROOT_FORCE_INLINE").value_or(false);
    auto debug_fi_log = [&](const llvm::Twine &msg) {
      if (debug_force_inline) {
        errs() << "[output-root-force-inline] " << msg << "\n";
        errs().flush();
      }
    };

    // Collect output roots and the set of helper functions reachable
    // from them. A function is a "helper" if it has a lifted-style
    // name (`blk_*` / `block_*`) and isn't itself the output root.
    llvm::SmallPtrSet<llvm::Function *, 8> output_roots;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      if (F.hasFnAttribute("omill.output_root") ||
          F.hasFnAttribute("omill.closed_root_slice_root"))
        output_roots.insert(&F);
    }

    llvm::SmallPtrSet<llvm::Function *, 32> reachable_helpers;
    {
      llvm::SmallPtrSet<llvm::Function *, 32> visited;
      llvm::SmallVector<llvm::Function *, 32> worklist(
          output_roots.begin(), output_roots.end());
      while (!worklist.empty()) {
        auto *cur = worklist.pop_back_val();
        if (!visited.insert(cur).second)
          continue;
        for (auto &BB : *cur) {
          for (auto &I : BB) {
            auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
            auto *callee = CB ? CB->getCalledFunction() : nullptr;
            if (!callee || callee->isDeclaration())
              continue;
            auto name = callee->getName();
            // Only inline `blk_*` / `block_*` helpers — `sub_*`
            // functions are lifted whole-function units and may be
            // called from multiple places, inlining them would
            // duplicate a lot of code. The output-root `sub_` is
            // the container we're inlining INTO, not something to
            // inline from.
            if (!name.starts_with("blk_") && !name.starts_with("block_"))
              continue;
            if (output_roots.count(callee))
              continue;
            reachable_helpers.insert(callee);
            worklist.push_back(callee);
          }
        }
      }
    }

    unsigned marked_for_inline = 0;
    for (auto *helper : reachable_helpers) {
      if (helper->hasFnAttribute(llvm::Attribute::OptimizeNone))
        helper->removeFnAttr(llvm::Attribute::OptimizeNone);
      if (helper->hasFnAttribute(llvm::Attribute::NoInline))
        helper->removeFnAttr(llvm::Attribute::NoInline);
      if (!helper->hasFnAttribute(llvm::Attribute::AlwaysInline)) {
        helper->addFnAttr(llvm::Attribute::AlwaysInline);
        ++marked_for_inline;
      }
      // Internalize so AlwaysInliner's post-inline erase can fire.
      if (!helper->hasLocalLinkage())
        helper->setLinkage(llvm::GlobalValue::InternalLinkage);
    }
    debug_fi_log(llvm::Twine("output roots=") +
                 llvm::Twine(output_roots.size()) +
                 " reachable helpers=" +
                 llvm::Twine(reachable_helpers.size()) +
                 " marked alwaysinline=" + llvm::Twine(marked_for_inline));

    if (!reachable_helpers.empty()) {
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      // First pass: just inline, no cleanup. Verify the post-inline
      // module before running scalar passes, so a bad interaction
      // between the inliner and the cleanup sweep (e.g. musttail chain
      // collapsing to `unreachable`) is attributed to the right place.
      {
        llvm::ModulePassManager mpm;
        mpm.addPass(llvm::AlwaysInlinerPass());
        mpm.run(*module, MAM);
        MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      }

      if (debug_force_inline) {
        std::string err;
        llvm::raw_string_ostream os(err);
        if (llvm::verifyModule(*module, &os)) {
          debug_fi_log(llvm::Twine("verify failed post-inline: ") +
                       err.substr(0, 500));
        } else {
          debug_fi_log("verify ok post-inline");
        }
        // Check if sub_180001850 survived.
        if (auto *F = module->getFunction("sub_180001850")) {
          unsigned sz = 0;
          for (auto &BB : *F)
            sz += BB.size();
          debug_fi_log(llvm::Twine("sub_180001850 post-inline inst count=") +
                       llvm::Twine(sz));
        }
      }

      // Conservative scalar cleanup on the unified body: SROA +
      // EarlyCSE only. Anything more aggressive (InstCombine, GVN,
      // DSE, ADCE, SimplifyCFG) collapses the 70k-instruction body
      // into a single `unreachable` because LLVM's constant
      // propagation through the unified state pointer sees the whole
      // chain as simplifiable to a no-op. Root-causing that folding
      // regression is future work; for now we stop at SROA/EarlyCSE
      // and rely on the inliner's own DCE for the bulk of the win.
      {
        llvm::ModulePassManager mpm;
        {
          llvm::FunctionPassManager fpm;
          fpm.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
          fpm.addPass(llvm::EarlyCSEPass(/*UseMemorySSA=*/true));
          mpm.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(fpm)));
        }
        mpm.addPass(llvm::GlobalDCEPass());
        mpm.run(*module, MAM);
        MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      }

      if (debug_force_inline) {
        unsigned post_defs = 0;
        for (auto &F : *module) {
          if (F.isDeclaration())
            continue;
          auto name = F.getName();
          if (name.starts_with("blk_") || name.starts_with("block_"))
            ++post_defs;
        }
        debug_fi_log(llvm::Twine("post-inline blk_/block_ defs remaining=") +
                     llvm::Twine(post_defs));
      }
    }
  }

  if (!RawBinary && !NoABI)
    unresolved_pc_output_roots = collectUnresolvedOutputRootPcCalls();
  bool repaired_after_finalization = false;
  // The post-main `repairReachableDeclaredStructuralTargets` loop spawns a
  // sub-process omill-lift pipeline run per unresolved placeholder target
  // (up to 8 rounds × N targets). For the large-noabi generic-static case
  // we already ran the full closed-root-slice materialization + lift cleanup
  // in-process and any remaining declared blk_*/sub_* targets are either
  // unliftable at the binary level or belong to placeholder chains whose
  // sub-process recovery would cost tens of seconds without improving the
  // output closure. Match the other large-noabi skip gates (runtime-owned
  // output recovery, devirtualization invariants, final output cleanup)
  // and skip this loop too. `OMILL_LARGE_NOABI_REPAIR_DECLARED_TARGETS`
  // is the escape hatch for users who want the legacy behavior.
  const bool skip_post_main_structural_repair =
      large_noabi_lift && NoABI && opts.generic_static_devirtualize &&
      std::getenv("OMILL_LARGE_NOABI_REPAIR_DECLARED_TARGETS") == nullptr;
  if (skip_post_main_structural_repair) {
    events.emitInfo(
        "post_main_structural_repair_skipped",
        "skipping post-main structural target repair for large no-abi "
        "generic-static module",
        {});
  } else {
    for (unsigned repair_round = 0; repair_round < 8; ++repair_round) {
      if (!repairReachableDeclaredStructuralTargets())
        break;
      repaired_after_finalization = true;
    }
  }
  if (repaired_after_finalization) {
    if (!RawBinary && !NoABI) {
      ModulePassManager AbiRepairMPM;
      omill::buildABIRecoveryPipeline(AbiRepairMPM, opts);
      AbiRepairMPM.run(*module, MAM);
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    }
    if (!RawBinary && !NoABI && eraseDeadDispatcherShellCalls()) {
      eraseUnusedModeledPlaceholderDeclarationsInCurrentModule();
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    }
    if (!RawBinary && !NoABI && repairDetachedRecoveryExitBlocks()) {
      eraseUnusedModeledPlaceholderDeclarationsInCurrentModule();
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      ModulePassManager AbiRepairMPM;
      omill::buildABIRecoveryPipeline(AbiRepairMPM, opts);
      AbiRepairMPM.run(*module, MAM);
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    }
    if (!RawBinary && !NoABI && eraseUnreachableLiftedResidueFromOutputRoots()) {
      eraseUnusedModeledPlaceholderDeclarationsInCurrentModule();
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      ModulePassManager AbiRepairMPM;
      omill::buildABIRecoveryPipeline(AbiRepairMPM, opts);
      AbiRepairMPM.run(*module, MAM);
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    }
    for (unsigned post_repair_round = 0; post_repair_round < 4; ++post_repair_round) {
      const auto prior_recovery_target = latest_recovery_mode_truthful_target;
      if (!repairReachableDeclaredStructuralTargets())
        break;
      if (!RawBinary && !NoABI) {
        ModulePassManager AbiRepairMPM;
        omill::buildABIRecoveryPipeline(AbiRepairMPM, opts);
        AbiRepairMPM.run(*module, MAM);
        MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      }
      if (latest_recovery_mode_truthful_target == prior_recovery_target)
        break;
    }
    reachable_external_calls = collectReachableExternalCallsFromOutputRoots();
    finalization_summary = buildFinalizationSummary();
    if (!RawBinary && !NoABI)
      unresolved_pc_output_roots = collectUnresolvedOutputRootPcCalls();
  }
  if (!RawBinary && !NoABI && eraseDeadDispatcherShellCalls()) {
    eraseUnusedModeledPlaceholderDeclarationsInCurrentModule();
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    reachable_external_calls = collectReachableExternalCallsFromOutputRoots();
    finalization_summary = buildFinalizationSummary();
    unresolved_pc_output_roots = collectUnresolvedOutputRootPcCalls();
  }
  if (!RawBinary && !NoABI && repairDetachedRecoveryExitBlocks()) {
    eraseUnusedModeledPlaceholderDeclarationsInCurrentModule();
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    reachable_external_calls = collectReachableExternalCallsFromOutputRoots();
    finalization_summary = buildFinalizationSummary();
    unresolved_pc_output_roots = collectUnresolvedOutputRootPcCalls();
  }

  if (markAbiInternalRootClosuresAlwaysInline()) {
    ModulePassManager AbiInlineMPM;
    omill::buildABIRecoveryPipeline(AbiInlineMPM, opts);
    AbiInlineMPM.run(*module, MAM);
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    reachable_external_calls = collectReachableExternalCallsFromOutputRoots();
    finalization_summary = buildFinalizationSummary();
    unresolved_pc_output_roots = collectUnresolvedOutputRootPcCalls();
  }
  if (!RawBinary && !NoABI && eraseUnreachableLiftedResidueFromOutputRoots()) {
    eraseUnusedModeledPlaceholderDeclarationsInCurrentModule();
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    reachable_external_calls = collectReachableExternalCallsFromOutputRoots();
    finalization_summary = buildFinalizationSummary();
    unresolved_pc_output_roots = collectUnresolvedOutputRootPcCalls();
  }

  const bool abi_dispatcher_shell_after_finalization =
      !RawBinary && !NoABI &&
      classifySerializedRuntimeRecoveryQuality(*module)
          .value_or(classifyRuntimeRecoveryQuality(*module))
          .dispatcher_shell;
  const bool abi_unresolved_tail_after_finalization =
      !RawBinary && !NoABI && !unresolved_pc_output_roots.empty();
  const auto post_finalization_recovery_quality =
      classifySerializedRuntimeRecoveryQuality(*module)
          .value_or(classifyRuntimeRecoveryQuality(*module));
  if (abi_dispatcher_shell_after_finalization ||
      abi_unresolved_tail_after_finalization) {
    errs() << "ABI output needs truthful no-ABI tail graph repair\n";
    events.emitInfo(
        "abi_tail_graph_repair_requested",
        "ABI output requested truthful no-ABI tail graph repair",
        {{"dispatcher_shell", abi_dispatcher_shell_after_finalization},
         {"unresolved_root_count",
          static_cast<int64_t>(unresolved_pc_output_roots.size())},
         {"functionally_recovered",
          post_finalization_recovery_quality.functionally_recovered}});
    bool repaired = false;
    bool projected_tail_graph = false;
    repaired = tryAdoptTruthfulNoABIChildAsAbiModule() || repaired;
    if (!repaired) {
      projected_tail_graph = tryProjectAbiTailGraphFromMainRootNoABIChild();
      repaired = projected_tail_graph || repaired;
      if (!repaired)
        repaired = tryAdoptTruthfulPreABICheckpoint();
    }
    if (repaired) {
      bool repaired_declared_targets = false;
      for (unsigned repair_round = 0; repair_round < 4; ++repair_round) {
        if (!repairReachableDeclaredStructuralTargets())
          break;
        repaired_declared_targets = true;
        if (!imported_recovery_mode_truthful_targets.empty())
          break;
      }
      const bool repaired_constant_boundaries =
          materializeConstantBoundaryPlaceholdersInCurrentModule();
      const bool imported_boundary_continuations =
          wireImportedPushJumpBoundaryContinuationsInCurrentModule();
      const bool rewrote_suppressed_fallthroughs =
          rewriteSuppressedBoundaryFallthroughsInCurrentModule();
      const bool erased_unused_modeled_decls =
          eraseUnusedModeledPlaceholderDeclarationsInCurrentModule();
      if (repaired_constant_boundaries || imported_boundary_continuations ||
          rewrote_suppressed_fallthroughs || erased_unused_modeled_decls) {
        MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      }
      annotateVmUnresolvedContinuationsInCurrentModule();
      unresolved_pc_output_roots = collectUnresolvedOutputRootPcCalls();
      finalization_summary = buildFinalizationSummary();
      if ((!unresolved_pc_output_roots.empty() ||
           !classifySerializedRuntimeRecoveryQuality(*module)
                .value_or(classifyRuntimeRecoveryQuality(*module))
                .functionally_recovered) &&
          projected_tail_graph && tryAdoptTruthfulPreABICheckpoint()) {
        annotateVmUnresolvedContinuationsInCurrentModule();
        unresolved_pc_output_roots = collectUnresolvedOutputRootPcCalls();
        finalization_summary = buildFinalizationSummary();
      }
      if (repaired_declared_targets)
        reachable_external_calls = collectReachableExternalCallsFromOutputRoots();
    }
  }
  const bool has_imported_recovery_mode_truthful_children =
      !imported_recovery_mode_truthful_targets.empty();


  if (!unresolved_pc_output_roots.empty()) {
    errs() << "Error: unresolved lifted control transfer remains in output "
              "root closure(s): ";
    for (size_t i = 0; i < unresolved_pc_output_roots.size(); ++i) {
      if (i)
        errs() << ", ";
      errs() << unresolved_pc_output_roots[i];
    }
    errs() << "\n";
    return fail(1,
                "unresolved lifted control transfer remains in output root closures");
  }


  if (!reachable_external_calls.empty() &&
      !has_imported_recovery_mode_truthful_children) {
    llvm::json::Array warnings_json;
    llvm::json::Object counts_by_class;
    std::map<std::string, int64_t> class_counts;
    for (const auto &warning : reachable_external_calls) {
      ++class_counts[warning.leak_class];
      errs() << "Warning: reachable external call [" << warning.leak_class
             << "] from output root " << warning.root_name << ": "
             << warning.caller_name << " -> " << warning.callee_name << "\n";
      llvm::json::Object entry;
      entry["root"] = warning.root_name;
      entry["caller"] = warning.caller_name;
      entry["callee"] = warning.callee_name;
      entry["class"] = warning.leak_class;
      warnings_json.push_back(std::move(entry));
    }
    for (const auto &[klass, count] : class_counts)
      counts_by_class[klass] = count;
    llvm::json::Object payload;
    payload["count"] = static_cast<int64_t>(reachable_external_calls.size());
    payload["counts_by_class"] = std::move(counts_by_class);
    payload["calls"] = std::move(warnings_json);
    events.emitWarn("reachable_external_calls_in_output_root_closure",
                    "reachable external calls remain in output root closure",
                    std::move(payload));
  }

  // Detect infinite self-loops in output root functions.
  // A block like `br label %self` indicates an unresolved dispatch path
  // that collapsed to a dead loop during optimization.
  {
    unsigned self_loop_count = 0;
    for (auto &F : *module) {
      if (!F.hasFnAttribute("omill.output_root")) continue;
      for (auto &BB : F) {
        auto *term = BB.getTerminator();
        auto *br = llvm::dyn_cast<llvm::BranchInst>(term);
        if (!br || !br->isUnconditional()) continue;
        if (br->getSuccessor(0) != &BB) continue;
        // Check this block only has the branch (no real work).
        if (&BB.front() == term || BB.size() <= 2) {
          ++self_loop_count;
          errs() << "Warning: infinite self-loop in output root "
                 << F.getName() << " at block " << BB.getName()
                 << " (unresolved dispatch path)\n";
        }
      }
    }
    if (self_loop_count > 0) {
      events.emitWarn("infinite_self_loop_in_output",
                      "output root contains infinite self-loop(s)",
                      {{"count", static_cast<int64_t>(self_loop_count)}});
    }
  }

  emitRuntimeArtifactBundleEvents(events, "finalization",
                                  finalization_summary.artifact_bundles);
  if (finalization_summary.has_protector_report &&
      !has_imported_recovery_mode_truthful_children) {
    const auto &protector_report = finalization_summary.protector_report;
    if (!protector_report.issues.empty()) {
      llvm::json::Array issues_json;
      llvm::json::Object counts_by_class;
      for (const auto &[klass, count] : protector_report.counts_by_class)
        counts_by_class[klass] = static_cast<int64_t>(count);
      for (const auto &issue : protector_report.issues) {
        llvm::json::Object entry;
        entry["class"] = omill::toString(issue.issue_class);
        if (!issue.root_name.empty())
          entry["root"] = issue.root_name;
        if (!issue.caller_name.empty())
          entry["caller"] = issue.caller_name;
        if (!issue.callee_name.empty())
          entry["callee"] = issue.callee_name;
        if (!issue.edge_identity.empty())
          entry["edge_identity"] = issue.edge_identity;
        if (!issue.message.empty())
          entry["message"] = issue.message;
        issues_json.push_back(std::move(entry));
        errs() << "Protector report [" << omill::toString(issue.issue_class)
               << "]";
        if (!issue.edge_identity.empty())
          errs() << " edge=" << issue.edge_identity;
        if (!issue.caller_name.empty())
          errs() << " caller=" << issue.caller_name;
        if (!issue.callee_name.empty())
          errs() << " callee=" << issue.callee_name;
        if (!issue.message.empty())
          errs() << " " << issue.message;
        errs() << "\n";
      }
      llvm::json::Object payload;
      payload["count"] =
          static_cast<int64_t>(protector_report.issues.size());
      payload["counts_by_class"] = std::move(counts_by_class);
      payload["issues"] = std::move(issues_json);
      events.emitWarn("protector_model_validation_report",
                      "protector-focused validation report",
                      std::move(payload));
    }
  }

  if (events.detailed()) {
    std::optional<omill::ProtectorValidationReport> report;
    if (finalization_summary.has_protector_report &&
        !has_imported_recovery_mode_truthful_children)
      report = finalization_summary.protector_report;
    std::string artifact_report_path;
    if (writeRuntimeArtifactReport(
            OutputFilename, devirtualization_runtime.roundArtifactBundles(),
            report, &artifact_report_path)) {
      events.emitInfo("runtime_artifact_report_written",
                      "runtime artifact report written",
                      {{"path", artifact_report_path},
                       {"bundle_count",
                       static_cast<int64_t>(
                            devirtualization_runtime.roundArtifactBundles()
                                .size())}});
    }
  }

  if (SolveControlVA.getNumOccurrences() > 0) {
    auto *solve_fn =
        omill::findLiftedOrCoveredFunctionByPC(*module, solve_control_va);
    if (!solve_fn)
      return fail(1, "solve-control-va not found in lifted module");

    omill::RemillStateVariableSolver solver(*module);
    llvm::json::Object payload;
    payload["control_pc"] = hexString(solve_control_va);
    payload["function"] = solve_fn->getName().str();

    if (auto maybe_solution =
            solver.solveControlTransfer(*solve_fn, solve_control_va)) {
      llvm::json::Object solution;
      solution["kind"] = controlTransferKindName(maybe_solution->kind);
      solution["transfer_value"] =
          jsonSolvedIntegerValue(maybe_solution->transfer_value);
      solution["possible_target_pcs"] =
          jsonPcArray(maybe_solution->possible_target_pcs);
      if (maybe_solution->branch_taken)
        solution["branch_taken"] = *maybe_solution->branch_taken;

      llvm::json::Array named_state_values;
      for (const auto &entry : maybe_solution->named_state_values) {
        llvm::json::Object value_obj;
        value_obj["name"] = entry.getKey().str();
        value_obj["value"] = jsonSolvedIntegerValue(entry.getValue());
        named_state_values.push_back(std::move(value_obj));
      }
      solution["named_state_values"] = std::move(named_state_values);
      payload["control_transfer"] = std::move(solution);
    }

    if (!SolveStateFields.empty()) {
      llvm::json::Array field_values;
      for (const auto &field_name : SolveStateFields) {
        llvm::json::Object field_obj;
        field_obj["name"] = field_name;
        if (auto value = solver.solveStateFieldBeforeControlTransfer(
                *solve_fn, solve_control_va, field_name)) {
          field_obj["value"] = jsonSolvedIntegerValue(*value);
        }
        field_values.push_back(std::move(field_obj));
      }
      payload["requested_state_fields"] = std::move(field_values);
    }

    errs() << "Solver query result: "
           << llvm::json::Value(std::move(payload)) << "\n";
    if (events.enabled())
      events.emitInfo("solver_query_result", "solver query completed",
                      std::move(payload));
  }

  // Write final output
  if (canonicalizeTerminalMissingBlockDispatchSuffixes())
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
  if (eraseUnusedModeledPlaceholderDeclarationsInCurrentModule())
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
  // Final dead-function sweep: rewrite any remaining `body: unreachable`
  // shells (which would compile to orphaned `ud2` stubs) into no-op
  // pass-throughs that return their memory argument.  Preserves the
  // call graph shape — callers continue to thread the memory token
  // through without observing a trap.  The rewritten stubs are tagged
  // `alwaysinline`, so a follow-up AlwaysInliner + GlobalDCE folds
  // each of them directly into every remaining caller.
  if (unsigned rewritten = omill::eliminateBodyUnreachableFunctions(*module);
      rewritten > 0) {
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
    if (std::getenv("OMILL_DEBUG_DEAD_PROPAGATE") != nullptr)
      errs() << "[dead-propagate:final] rewrote " << rewritten
             << " body:unreachable functions to ret memory\n";
    ModulePassManager CleanupMPM;
    CleanupMPM.addPass(llvm::AlwaysInlinerPass());
    CleanupMPM.addPass(llvm::GlobalDCEPass());
    CleanupMPM.run(*module, MAM);
  }

  // Repair functions whose entry block has predecessors (back-edges
  // from __remill_jump lowering / SCC merge loop creation).  LLVM
  // requires entry blocks to have no predecessors.  Must run BEFORE
  // RSF/SROA/GVN since those passes compute DominatorTrees and crash
  // on broken SSA.
  //
  // The pattern: a rotated loop where the original "init" section
  // (State loads + computation) is at the BOTTOM of the back-edge
  // source block, and the "exit" section (State stores) is at the
  // top / entry block.  Values defined in the init section are used
  // in the entry block without PHIs.
  //
  // Fix: find the back-edge source block, split it so the init
  // section (State loads from arg0) becomes a separate block, insert
  // a preheader that branches to the init block.  The init block
  // gets PHIs only for the State-store values (which depend on inner
  // loop results), with undef-safe initial values from the preheader.
  // The State LOADS are re-executed each iteration — no PHIs needed.
  {
    bool repaired_any = false;
    for (auto &F : *module) {
      if (F.isDeclaration())
        continue;
      auto &entry = F.getEntryBlock();
      if (pred_begin(&entry) == pred_end(&entry))
        continue;

      // Find the back-edge source: a predecessor of the entry block
      // that contains State loads (gep+load from arg0).
      llvm::BasicBlock *backedge_src = nullptr;
      for (auto *P : predecessors(&entry)) {
        if (P == &entry)
          continue;
        backedge_src = P;
        break;
      }
      if (!backedge_src)
        continue;

      // Find the first State load in the back-edge source:
      // pattern: gep i8, ptr %0 (arg0), i64 <offset>
      llvm::Instruction *first_state_load = nullptr;
      auto *state_arg = F.getArg(0);
      for (auto &I : *backedge_src) {
        if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(&I)) {
          if (GEP->getPointerOperand() == state_arg) {
            // Check if next instruction is a load from this GEP
            auto *next = GEP->getNextNode();
            if (next && llvm::isa<llvm::LoadInst>(next) &&
                llvm::cast<llvm::LoadInst>(next)->getPointerOperand() == GEP) {
              first_state_load = GEP;
              break;
            }
          }
        }
      }

      if (!first_state_load)
        continue;

      // Split the back-edge source at the first State load.
      // Everything before the split = "store" section (stays in original)
      // Everything from the split = "init" section (new block)
      auto *init_block = backedge_src->splitBasicBlock(
          first_state_load->getIterator(), "loop.init");

      // Create preheader that branches to init_block.
      auto *preheader = llvm::BasicBlock::Create(
          F.getContext(), "entry.preheader", &F, &entry);
      llvm::BranchInst::Create(init_block, preheader);

      // The init_block terminator branches to entry (or sub_1800626f0.exit).
      // No PHIs needed in init_block for State loads since they read from
      // State (arg0) which is available everywhere.  But the backedge_src
      // block's terminator was an unconditional br to init_block (from
      // splitBasicBlock).  We need to check if init_block's PHIs (if any,
      // from the original block's PHIs) need a preheader incoming edge.
      // Actually, splitBasicBlock doesn't create PHIs — values defined
      // before the split are still in backedge_src and dominate init_block.

      repaired_any = true;
      if (std::getenv("OMILL_DEBUG_ENTRY_REPAIR") != nullptr)
        llvm::errs() << "[entry-repair] " << F.getName()
                     << ": split " << backedge_src->getName()
                     << " at first State load, preheader → "
                     << init_block->getName() << "\n";
    }
    if (repaired_any)
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
  }

  // Post-ABI RSF + SROA + GVN: Convert RSP-relative inttoptr patterns
  // to alloca GEPs, decompose the allocas, and forward store→load.
  // This eliminates State struct pollution from the output and surfaces
  // the actual algorithm logic (VM register arrays, hash constants, etc).
  // Runs on ALL functions in the module (not gated by output_root or
  // _native suffix) because no-ABI output roots need this cleanup.
  if (!parseBoolEnv("OMILL_SKIP_POST_ABI_RSF").value_or(false)) {
    llvm::FunctionPassManager RSF_FPM;
    RSF_FPM.addPass(omill::RecoverStackFramePass());
    RSF_FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    RSF_FPM.addPass(llvm::InstCombinePass());
    RSF_FPM.addPass(llvm::GVNPass());
    RSF_FPM.addPass(llvm::InstCombinePass());
    RSF_FPM.addPass(llvm::SimplifyCFGPass());
    // Second round: RSF may expose new patterns after GVN forwarding.
    RSF_FPM.addPass(omill::RecoverStackFramePass());
    RSF_FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
    RSF_FPM.addPass(llvm::GVNPass());
    RSF_FPM.addPass(llvm::SimplifyCFGPass());
    // Merge decomposed PHIs: SROA splits 64-bit State fields into
    // sub-byte PHIs (i8/i16/i24/i32/i48).  Each handler reassembles
    // them with zext+shl+or chains.  Merge them back into single i64
    // PHIs to eliminate the reassembly overhead.
    RSF_FPM.addPass(omill::MergeDecomposedStatePHIsPass());
    RSF_FPM.addPass(llvm::InstCombinePass());
    RSF_FPM.addPass(llvm::GVNPass());
    RSF_FPM.addPass(llvm::SimplifyCFGPass());
    // Dead Store Elimination: remove stores to State fields that are
    // overwritten before being read (VMP handler State writeback
    // between dispatch iterations).
    RSF_FPM.addPass(llvm::DSEPass());
    RSF_FPM.addPass(llvm::ADCEPass());
    // Constant Memory Folding fixpoint: fold loads from binary sections
    // (VMP bytecode reads) + store→load forwarding + simplification.
    RSF_FPM.addPass(omill::CombinedFixedPointDevirtPass());
    RSF_FPM.addPass(llvm::InstCombinePass());
    RSF_FPM.addPass(llvm::GVNPass());
    RSF_FPM.addPass(llvm::ADCEPass());
    RSF_FPM.addPass(llvm::SimplifyCFGPass());
    // Final cleanup round: run the PHI merge again (DSE may have
    // exposed new opportunities), then full optimization to clean up.
    RSF_FPM.addPass(omill::MergeDecomposedStatePHIsPass());
    RSF_FPM.addPass(llvm::InstCombinePass());
    RSF_FPM.addPass(llvm::GVNPass());
    RSF_FPM.addPass(llvm::DSEPass());
    RSF_FPM.addPass(llvm::ADCEPass());
    RSF_FPM.addPass(llvm::SimplifyCFGPass());
    ModulePassManager RSF_MPM;
    RSF_MPM.addPass(
        llvm::createModuleToFunctionPassAdaptor(std::move(RSF_FPM)));
    RSF_MPM.run(*module, MAM);
    MAM.invalidate(*module, llvm::PreservedAnalyses::none());
  }

  // Continuation-passing transform: eliminate recursive scc_dispatch calls.
  if (!parseBoolEnv("OMILL_SKIP_CONTINUATION_PASSING").value_or(false)) {
    omill::SCCDispatchCPTPass().run(*module, MAM);
  }

  std::error_code EC;
  events.emitInfo("output_write_started", "writing final output",
                  {{"path", OutputFilename}});
  ToolOutputFile Out(OutputFilename, EC, sys::fs::OF_Text);
  if (EC) {
    errs() << "Error opening output: " << EC.message() << "\n";
    return fail(1, "failed to open output file");
  }
  // Final cleanup: internalize + DCE remill semantics templates that were
  // re-introduced by post-main child lifts (runTerminalBoundaryChildLift
  // links fresh semantics modules back, reintroducing external-linkage
  // template definitions like PHADDSW that the main pipeline already cleaned).
  {
    bool any_internalized = false;
    for (auto &F : *module) {
      if (F.isDeclaration() || F.hasLocalLinkage())
        continue;
      auto name = F.getName();
      // Remill semantics templates from anonymous/static C++ namespaces.
      if (name.starts_with("_ZN12_GLOBAL__N_") || name.starts_with("_ZL")) {
        F.setLinkage(GlobalValue::InternalLinkage);
        any_internalized = true;
      }
    }
    if (any_internalized) {
      ModulePassManager FinalCleanupMPM;
      FinalCleanupMPM.addPass(llvm::GlobalDCEPass());
      FinalCleanupMPM.run(*module, MAM);
    }
  }
  appendDebugMarker("final_output:before_print");
  module->print(Out.os(), nullptr);
  appendDebugMarker("final_output:after_print");
  Out.keep();
  events.emitInfo("output_write_completed", "output write complete",
                  {{"path", OutputFilename}});

  if (DumpIR) {
    std::error_code ec;
    raw_fd_ostream os("after_abi.ll", ec, sys::fs::OF_Text);
    if (!ec) {
      module->print(os, nullptr);
      errs() << "Wrote after_abi.ll\n";
    }
  }

  emitIterativeSessionReport(iterative_session);
  errs() << "Done.\n";
  events.emitTerminalSuccess(OutputFilename);
  return 0;
