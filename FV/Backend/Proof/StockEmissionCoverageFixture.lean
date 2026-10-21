import FV.Backend.Proof.StockEmissionCoverageKernel

namespace Backend.Stock.Proof.EmissionCoverageFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private def original (branch : Bool) : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx (function branch)).toOption.getD (sinkCtx,#[],default)
private theorem original_build (branch : Bool) : Backend.buildCtx (function branch) = .ok (original branch) := by
  cases branch <;> rfl

private theorem source_dominated (branch : Bool) : Dominated (function branch) := by
  constructor
  · cases branch <;> decide +kernel
  · intro ctx ranges st build bi b found
    cases branch
    · have bound : bi < 1 := by have h := lt_of_getElem? found; simpa [function] using h
      have same : bi = 0 := by omega
      subst bi
      simp [function] at found
      subst b
      constructor
      · intro j stm atStmt x member
        have zero : j = 0 := by have h := lt_of_getElem? atStmt; simp at h; omega
        subst j
        cases atStmt
        cases member
      · intro x member
        simp [abiTerm,Driver.termArgs,sretRet,sigRets,function] at member
        subst x
        simp [availOf,function,defsBefore,defsFrom]
    · have bound : bi < 3 := by have h := lt_of_getElem? found; simpa [function] using h
      have cases : bi = 0 ∨ bi = 1 ∨ bi = 2 := by omega
      rcases cases with rfl | rfl | rfl
      all_goals
        simp [function] at found
        subst b
        constructor
        · intro j stm atStmt x member
          first
          | (solve | simp at atStmt)
          | have zero : j = 0 := by have h := lt_of_getElem? atStmt; simp at h; omega
            subst j
            cases atStmt
            change x ∈ ([7,13] : List Nat) at member
            simp only [List.mem_cons,List.not_mem_nil,or_false] at member
            rcases member with rfl | rfl <;> simp [availOf,function,defsBefore,defsFrom]
        · intro x member
          simp [abiTerm,Driver.termArgs,sretRet,sigRets,function] at member
          first
          | (subst x; simp [availOf,function,defsBefore,defsFrom])
          | (rcases member with rfl | rfl <;> simp [availOf,function,defsBefore,defsFrom])
  · intro ctx ranges st build tl x available notLocal y member
    have context : ctx = (original branch).1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans (original_build branch)))
    rw [context] at member
    have fixed := (inFix_fixOk (f := function branch) (ctx := ctx) (gn := id)).cand tl x available
    cases branch
    · have same : x = 7 := by simpa [valueDefs,function] using fixed.2.2.2.1
      subst x
      change y ∈ ([] : List Nat) at member
      cases member
    · have values : x = 7 ∨ x = 13 ∨ x = 17 ∨ x = 31 ∨ x = 47 := by
        simpa [valueDefs,function] using fixed.2.2.2.1
      rcases values with rfl | rfl | rfl | rfl | rfl
      all_goals first
        | change y ∈ ([] : List Nat) at member; cases member
        | skip
      change y ∈ ([7,13] : List Nat) at member
      have choices : y = 7 ∨ y = 13 := by simpa using member
      have notEntry : tl ≠ 0 := by intro same; subst tl; exact notLocal (by decide +kernel)
      rcases tl with _ | _ | _ | tl
      · exact False.elim (notEntry rfl)
      all_goals rcases choices with rfl | rfl <;> simp [parsOf,function]

/-- Cached complete actual source/pipeline and nonempty ordinary emitted code
for both real named roots. Used by downstream non-vacuity proofs. -/
structure Output (branch : Bool) where
  result : Result
  prepared : EdgeVCode
  rf : RFunc
  af : AFunc
  out : Backend.V
  after : State
  trace : List Isle.RuleId
  lowered : Stock.lower (function branch) = .ok result
  scope : LowerScope (function branch)
  dominated : Dominated (function branch)
  arity : ArityOk (function branch)
  prepare : prepareAt result.code result.edgeArgs = .ok prepared
  fallback : rf = spillAllocAt prepared.code prepared.edges
  accepted : checkAllocAt prepared.code prepared.edges rf = .ok ()
  physical : lowerRFunc prepared.code rf = .ok af
  root : Stock.runTerm (rootCtx branch result.ctx) (rootName branch) (rootArgs branch) result.initial =
    .ok (some out,after,trace)
  initialEmpty : result.initial.base.emitted = #[]
  ordinary : after.base.emitted.any (fun i => !i.isCtl) = true

/-- Both complete sources have original scope/dominance/arity, actual raw and
checked fallback/physical success, and a real non-control named-root emission. -/
theorem emission_fixture (branch : Bool) : Nonempty (Output branch) := by
  have actual := emission_observed branch
  unfold Observed at actual
  cases run : pipeline branch with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok q =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    unfold pipeline at run
    obtain ⟨result,lowered,h⟩ := Except.bind_ok run
    obtain ⟨prepared,prepare,h⟩ := Except.bind_ok h
    obtain ⟨rf,selected,h⟩ := Except.bind_ok h
    obtain ⟨af,physical,h⟩ := Except.bind_ok h
    obtain ⟨⟨out,after,trace⟩,root,h⟩ := Except.bind_ok h
    cases out with
    | none => cases h
    | some out =>
      cases h
      have accepted := PerEdge.allocResultAt_checked selected
      have fallback : rf = spillAllocAt prepared.code prepared.edges := by
        unfold allocResultAt checkedSpillAt at selected
        simp only [bind,Except.bind] at selected
        split at selected <;> cases selected
        rfl
      have scope : LowerScope (function branch) := by cases branch <;> exact lowerScope_of (by decide +kernel)
      have dominated := source_dominated branch
      have arity : ArityOk (function branch) := by cases branch <;> exact arityOk_of (by decide +kernel)
      exact ⟨⟨result,prepared,rf,af,out,after,trace,lowered,scope,dominated,arity,prepare,fallback,accepted,physical,root,actual.1,actual.2⟩⟩

end Backend.Stock.Proof.EmissionCoverageFixture
