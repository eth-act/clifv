import FV.E2E.LinkScopeTotalTF
import FV.E2E.LinkScopeInputT3
import FVTest.E2E.EmitCondsTWitness
import FVTest.E2E.PoolLoadWitness

-- #1002 part 1: the typed scopes' prepared code has no literal-pool load, so the literal loads'
-- reach `poolReachB` is a theorem there (it was a premise `hpool` and a run-time conjunct
-- `poolReachInB` since #955)

-- constant-pool entries in ISLE values: the extern helpers and the driver's data
#print axioms Backend.Proof.Pool.amode_const_pool
#print axioms Backend.Proof.Pool.ofV_pool
#print axioms Backend.Proof.Pool.externCtor_pool
#print axioms Backend.Proof.Pool.externExtract_pool
#print axioms Backend.Proof.Pool.ctor_noPool
#print axioms Backend.Proof.Pool.instData_poolIn
#print axioms Backend.Proof.Pool.termData_poolIn
#print axioms Backend.Proof.Pool.tryCallData_poolIn
#print axioms Backend.Proof.Pool.dataP_of_build
-- the pool-free term set and the uniform invariant; `constant_f64` and rule 585 by hand
#print axioms Backend.Proof.Pool.poolTab_closedB
#print axioms Backend.Proof.Pool.poolTab_const
#print axioms Backend.Proof.Pool.poolRootS_ok
#print axioms Backend.Proof.Pool.poolRootB_ok
#print axioms Backend.Proof.Pool.poolRootF_ok
#print axioms Backend.Proof.Pool.internal_first
#print axioms Backend.Proof.Pool.constant_f64_noPool
#print axioms Backend.Proof.Pool.f64const_rhs_noPool
#print axioms Backend.Proof.Pool.stmt_noPool
#print axioms Backend.Proof.Pool.branch_noPool
#print axioms Backend.Proof.Pool.termCall_noPool
#print axioms Backend.Proof.Pool.tryCall_noPool
-- the prepared VCode: no literal-pool load, the reach, two-way coverage
#print axioms E2E.lower_noLitTF
#print axioms E2E.noPoolB_of_prepare
#print axioms E2E.noPoolB_lowerTF
#print axioms E2E.noPoolB_cleanup_lowerTF
#print axioms E2E.poolReachB_lowerTF
#print axioms E2E.poolReachB_cleanup_lowerTF
#print axioms E2E.noPoolB_lowerT
#print axioms E2E.noPoolB_cleanup_lowerT
#print axioms E2E.poolReachB_lowerT
#print axioms E2E.poolReachB_cleanup_lowerT
#print axioms Backend.Proof.Driver.formsCovered2_completeT
#print axioms Backend.Proof.Driver.formsCovered2_completeTF
-- the ten statements restored to their pre-#955 form (no `hpool`)
#print axioms E2E.spillSizeOkB_of_sizeOkBT
#print axioms E2E.spillSizeOkB_cleanup_of_sizeOkBT
#print axioms E2E.spillSizeOkB_of_sizeOkBTF
#print axioms E2E.spillSizeOkB_cleanup_of_sizeOkBTF
#print axioms E2E.emitConds_lowerT
#print axioms E2E.emitConds_cleanup_lowerT
#print axioms E2E.emitConds_lowerTF
#print axioms E2E.emitConds_cleanup_lowerTF
#print axioms E2E.LinkCheck.emitCondsB_of_T2
#print axioms E2E.LinkCheck.emitCondsB_cleanup_of_T2
-- the input scopes without the `poolReachInB` conjunct
#print axioms E2E.LinkCheck.fnScopeInT3_parts
#print axioms E2E.LinkCheck.poolReachB_of_T3
#print axioms E2E.LinkCheck.poolReachIn_of_T3
#print axioms E2E.LinkCheck.lowerOutTB_of_T3
#print axioms E2E.LinkCheck.fnScopeInTB2_of_T3
#print axioms E2E.LinkCheck.emitCondsB_of_T3
#print axioms E2E.LinkCheck.fnScopeInT3F_parts
#print axioms E2E.LinkCheck.poolReachB_of_T3F
#print axioms E2E.LinkCheck.poolReachIn_of_T3F
#print axioms E2E.LinkCheck.pipeCleanupT_okT3F
-- witnesses: a typed function with an `f64const`; a pooled constant is outside the scope
#print axioms EmitCondsTWitness.fW_f64const -- witness: native_decide
#print axioms EmitCondsTWitness.fW_const_code -- witness: native_decide
#print axioms EmitCondsTWitness.fW_poolReach -- witness: native_decide
#print axioms EmitCondsTWitness.fW_covered2 -- witness: native_decide
#print axioms EmitCondsTWitness.fW_spillSize -- witness: native_decide
#print axioms EmitCondsTWitness.fW_emitConds -- witness: native_decide
#print axioms EmitCondsTWitness.fW_emitConds_cleanup -- witness: native_decide
#print axioms PoolLoadWitness.fLit_outside -- witness: native_decide
