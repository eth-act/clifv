# Full original #140 gap map

The remaining work is general Stock semantics and completeness across the original domain. It is not another consumer rewrite.
The original objective and active plan remain unchanged.
This inspection ran no builds and changed no source,cache,worktree,plan,or PR.

## Inspection boundary

Actual main is3a6719b44b0e6b38e24cd0de82655f93b78272a9.
Published #892 is90c51c880b9d614f7c5f9730b8363a6321c840de. It remained open during inspection.
Main differs from77088aba only through #894. All supplied changed lines across294files are import lines.
I read23current-main modules through GitHub and five published892modules locally.
`module-evidence.json` records exact source hashes,declaration names,and line positions.
`actual-main-delta.json` and `inspection-boundary.json` retain the reviewed boundary.
Import-only drift still invalidates an assumed source-context match. Reconcile before reusing kernel evidence.

## Established proofs and remaining gaps

1. **Aliases and register values.**
   `StockSourceAliasRecords.stock_lower_final_source_chain_noCycle` proves actual final source paths cannot cycle.
   `StockRecordFinalAlias.stock_lower_record_finalAliasEntry` and `StockFreshRecordValues.stock_lower_record_fresh_result` bind actual retained definitions and fresh results.
   `StockCoverageDriver.lower_noOpportunity` already derives whole-driver empty remembered state from `LowerScope`.
   `StockAliasSemantics.ValuesHeld.resolvedResult_frame` provides the write-based frame rule.
   Remaining work must derive value production and write exclusions through every effect,call,and terminator record.
   Alias termination and transport of an already-held value do not establish that execution produced the value.

2. **Root families and effects.**
   `StockScopeRoots.stock_excluded_root_match` and `stock_selected_source_root_closure` already justify current mapped-scope exclusions and closure membership.
   Existing scalar dispatch,value,source,and production proofs must be reused. Landed #767 supplies production selection witnesses.
   A root count or ledger status does not prove execution,retained binding,source transfer,composition,or completeness.
   Concrete remaining classes include result-bearing calls,indirect/GOT/TLS paths,atomics,and general address/effect mixtures.
   This inspection did not complete an exhaustive517-root audit. Record unknown rows instead of crediting them as proved.

3. **Omissions,sinking,and first traps.**
   `StockScanSemantics.ScansSpec.fall_refines` composes actual records but requires each local semantic obligation.
   `StockScanTrapSemantics.ScansSpec.local_trap_refines` composes normal prefixes through the first trap.
   `StockBodyScanRefines.stock_lower_select_omitted_body_fall_refines` discharges a specific concrete family partition.
   `StockProtectedSinkDriver.stock_lower_store_unsunk` and the protected-slot lemmas already constrain real sinking.
   Remaining work must discharge local obligations for every actual source mixture and carry the deferred-effect invariant.
   Stores before a trap must occur. Effects after the first trap must not occur.

4. **Source,block,node,and whole-driver simulation.**
   `Scalar.Domain`, `DomainAt`, and `CodeDomain` provide reusable universal source contracts.
   Concrete scalar,memory,and ranked CFG families derive these contracts.
   `CodeDomain` states correctness for the actual emitted code. It does not make every emitted code correct.
   `Domain` fields remain internal proof-composition obligations. They cannot become new accepted-input premises.
   The full original-domain Stock simulation remains distinct from the existing finite source classes.

5. **Control flow and joins.**
   `StockParameterArgsDomain.domainAt_of_args_parameter_leaf_cfg` covers ranked parameter CFGs with family and original-order premises.
   Per-successor domains and `PerEdgePrepareSound.prep_sound` already provide split-edge transport.
   A owns critical-edge extensions in open #884/#885/#886,CodeDomain integration,and later loops.
   Raw route22 exists. #892 still selects the route21 provider chain; it does not activate route22.
   General loop/table induction and arbitrary argument-carrying joins need Stock source semantics and completeness.
   Do not duplicate A's work or treat a strict ranking premise as coverage of cyclic loops.

6. **Calls and ABI results.**
   The current `StockVoidCallCheck.sourceData?` accepts one direct call with no source results.
   `sourceB` requires empty explicit returns and at most eight argument entries.
   `SretCopyCapturedExec.captured_exec_bytes` already proves the complete linked caller/callee copy for arbitrary symbolic bytes in both cleanup modes.
   The missing next case is a nonempty call result that the original caller consumes.
   General caller mixtures,live values across calls,stack arguments,indirect/GOT calls,and exception payloads remain separate obligations.
   The existing captured internal-call execution is real progress. Do not rebuild its program/binary infrastructure.

7. **Lowering success and admission completeness.**
   Kev's `IselPrgDriver.lowerFunction_ok_input` already proves baseline input-only totality.
   `StockPrgContext.stock_pinv` and `stock_stmtProg` transfer baseline progress infrastructure to the mapped Stock context.
   Landed #792 proves `StockScalarLowerOk.stock_lower_scalar_ok`; scalar lowering success is already done for that classifier.
   Its ABI read-check obligation remains separate. General calls,loads,sinks,and CFG traversal need broader progress invariants.
   Prove actual Stock success and required check acceptance from the original inputs. Fallback acceptance does not establish Stock-only completeness.

8. **Production consumers and typed modes.**
   Landed #887–#891 already provide binary,executable,original-source,route,checker,and generated-proof adapters.
   #892 adds default admission/fallback and raw/cleanup typed compiler modes.
   `TypedCompilerWith.attempt_correct`, `_depth`, and `_peak` require a successful checked attempt.
   Their source variants preserve the original source and peak premises.
   These are correctness results for success. They do not prove input-only attempt success or complete Stock selection.
   `ReturnPinProduction.returnPinModeB` and whole-file retry preserve compatibility; passing admission is not whole-driver completeness.

## Reuse Kev's and A's infrastructure

- Use `LowerSim.driver_correct`, the ABI variants,and `LowerSimUAbi.driver_correctU_abi` when lifting Stock transitions.
- Use `IselAtomic.load_acquire_ok`, `store_release_ok`, `atomic_rmw_loop_ok`, and `atomic_cas_loop_ok` for actual atomic helper projections.
- Use `IselCtlCallInd`, the call-control helpers,per-edge preparation,and the baseline loop proofs for their existing semantic work.
- Reuse A's scalar completeness,selection witnesses,and ranked argument CFG proofs. Coordinate only concrete shared constructors and routes.
- Preserve Kev's pending #843 boundary. Its source-aware stage migration is not landed and may change actual stage and checker premises.
- Reuse Parithosh's module locks,normal-key scheduler,and import pruning. Do not repeat stale source-context validation blindly.

The original integer `LowerScope` uses `Compile.functionE`:i8–i64,without float/i128/vector roots or `return_call`.
`StockFloatCheckDomain.buildCtx_functionE_domain` proves the float rejection preserves that original scope.
Use real current exclusions. Do not invent work outside that scope or silently delete any accepted typed,tail-call,opt,or unwind variant.
Each retained theorem variant must keep its own original conditions and guarantees.

## Ordered coherent next units

1. Land #892 through its scoped source,one direct cheap review,exact-head CI,and tree gates. Do not wait for unrelated union validation.
2. Complete the active result-bearing direct-call unit. Derive result binding,source return/trap semantics,and admission from actual retained records.
   Its complete program must consume the call result in arithmetic or memory. Execute both cleanup modes through compiler,checker,linkers,and generated proofs.
   Reuse actual allocator answers and the existing return-pin cache. Add no execution certificate,heap guard,or new source condition.
3. Extend that call composition to live values,memory effects,multiple calls,and the original stack-argument layouts.
   Then cover indirect/GOT/TLS call paths and ordinary/exceptional return payloads using Kev's existing helpers.
4. In parallel,A completes argument-carrying critical edges and then general control-flow composition.
   Integrate the proved route and CodeDomain consumers once. Extend to tables and loops through source-fuel induction.
5. Complete mixed-effect and first-trap composition. Lift atomic/address helpers into actual Stock records,then body,block,node,and whole-driver contracts.
6. Generalize Stock-only progress and prove all semantic/ABI/pipeline checks complete under the original conditions.
   Derive input-only compiler success and whole-program simulation/completeness. Retain ordinary,source,depth,peak,typed,and unwind variants.
7. Execute the shared current-head full gate after the protected owner releases its view.
   Continue the remaining captured functions and every original family/effect obligation. Do not stop at the first new class.

Each implementation unit includes proofs,nonvacuity,axiom audit,real consumer execution,and a substantive delivery where eligible.
These units are an execution order. They do not reduce the original goal or replace its completion criteria.

## Mandatory validation and unknowns

The broad current-head gate remains unrun. The healthy frozen gate uses an older source snapshot.
Require normal FV/FVTest/Corpus,all tools,crate proofs,all audits,retained runtime matrices,filetests,encoder,and unwind executions.
Require actual final CLI/linker/checker/generated-proof execution,including typed mixed programs and both cleanup modes.
Preserve the1302official input hashes,4501stage identities,all1633previous exact filetest tuples,and every accepted E2E identity and successful stage.
Measure both raw Stock and actual configured production output. Measure real crate byte parity separately from native behavior.
Exit10means a completed measurement with gaps. Green comparison CI is not full validation or equivalence.
Preserve exact old axiom sets. Generic correctness uses only propext,Classical.choice,and Quot.sound; existing marked fixed roots retain their required native sets.

The full ledger audit,remaining captured-function denominator,and universal theorem closure are unknown in this inspection.
Resolve them from the preserved original inventory and concrete proofs. Do not infer completeness from filenames,root counts,admission guards,or fixed witnesses.
The gap map does not own #513 publication. Its existing controller remains exclusively owned by the execution coordinator.
