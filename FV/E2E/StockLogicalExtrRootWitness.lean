import FV.E2E.StockLogicalExtrWitness
import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockLogicalExtrMatchedValues
import FV.Backend.Proof.StockLogicalExtrSelectedValues
import FV.Backend.Proof.StockLogicalExtrSourceTransfer


namespace E2E.StockLogicalExtrWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0 Backend.Stock.Proof
open Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def rootBuilt (config : Configuration) (mirrored : Bool) : Ctx × Array (Nat × Nat) × Stock.State :=
  (Stock.buildCtx (function config mirrored)).toOption.getD (sinkCtx,#[],sinkState)
private def sourceFrame (config : Configuration) (mirrored : Bool) (a b : CV) : Clif.Frame :=
  let ty := valueType config
  {
   func := function config mirrored
   regs := fun x => if x = 1 then some ⟨ty,a.setWidth ty.width⟩
     else if x = 8 then some ⟨ty,b.setWidth ty.width⟩
     else if x = 9 then some (.ofInt ty (ty.width-1 : Nat))
     else if x = 10 then some (.ofInt ty 1)
     else if x = 11 then some ⟨ty,a.setWidth ty.width <<< (ty.width-1)⟩
     else if x = 12 then some ⟨ty,b.setWidth ty.width >>> 1⟩ else none
   slots := []
   body := []
   term := .ret [13] }
/-- The real looked-through shifts and literals are source-available while
being absent from the machine register file in the fused EXTR witness. -/
private theorem sourceDFG (config : Configuration) (mirrored : Bool) (a b : CV) :
    DFGCons (rootBuilt config mirrored).1 (sourceFrame config mirrored a b) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases h1 : x = 1
    · subst x
      have absent : (rootBuilt config mirrored).1.defInst? 1 = none := by
        cases config <;> cases mirrored <;> rfl
      rw [absent] at defined
      cases defined
    ·
      by_cases h8 : x = 8
      · subst x
        have absent : (rootBuilt config mirrored).1.defInst? 8 = none := by
          cases config <;> cases mirrored <;> rfl
        rw [absent] at defined
        cases defined
      ·
        by_cases h9 : x = 9
        · subst x
          cases config <;> cases mirrored
          all_goals
            change some 0 = some j at defined
            cases defined
            obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
            subst info
            cases original
            cases lookup
            exact ⟨[_],fun cm => rfl,rfl⟩
        ·
          by_cases h10 : x = 10
          · subst x
            cases config <;> cases mirrored
            all_goals
              change some 1 = some j at defined
              cases defined
              obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
              subst info
              cases original
              cases lookup
              exact ⟨[_],fun cm => rfl,rfl⟩
          ·
            by_cases h11 : x = 11
            · subst x
              cases config <;> cases mirrored
              all_goals
                change some 2 = some j at defined
                cases defined
                obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
                subst info
                cases original
                cases lookup
                exact ⟨[_],fun cm => rfl,rfl⟩
            ·
              by_cases h12 : x = 12
              · subst x
                cases config <;> cases mirrored
                all_goals
                  change some 3 = some j at defined
                  cases defined
                  obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
                  subst info
                  cases original
                  cases lookup
                  exact ⟨[_],fun cm => rfl,rfl⟩
              · simp [sourceFrame,h1,h8,h9,h10,h11,h12] at lookup
  · intro x t v typed lookup
    by_cases present : x = 1 ∨ x = 8 ∨ x = 9 ∨ x = 10 ∨ x = 11 ∨ x = 12
    · rcases present with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        cases config <;> cases mirrored
        all_goals first
        | (change some (.int 32) = some t at typed; cases typed; cases lookup; rfl)
        | (change some (.int 64) = some t at typed; cases typed; cases lookup; rfl)
    · simp only [not_or] at present
      simp [sourceFrame,present.1,present.2.1,present.2.2.1,present.2.2.2.1,
        present.2.2.2.2.1,present.2.2.2.2.2] at lookup

end E2E.StockLogicalExtrWitness

namespace E2E.StockLogicalExtrWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0 Backend.Stock.Proof
open Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def rootRF (a b : CV) : Nat → CV := fun n => if n = 193 then a else if n = 200 then b else 0
private def rootAfter (config : Configuration) (mirrored : Bool) : Stock.State :=
  let st := (rootBuilt config mirrored).2.2
  { (st.mark 1).mark 8 with base := (st.base.fresh .int).2.emit (.aluRRRShift .extr
      (szOf (valueType config).width) (st.base.fresh .int).1 (.vreg 193 .int) (.vreg 200 .int)
      (LogicalExtr.shiftFor (valueType config).width 1)) }

private theorem root_match (config : Configuration) (mirrored : Bool) :
    let ctx := (rootBuilt config mirrored).1
    let st := (rootBuilt config mirrored).2.2
    let ty := valueType config
    (matchRule program (Stock.sem ctx) {} 20 (LogicalExtr.extrRule mirrored) [.inst 4]).run (st,#[]) =
      .ok (some (LogicalExtr.extrEnv mirrored ty.width 1 (ty.width-1 : Nat) 8 1),st,#[]) := by
  dsimp only
  cases config with
  | defaultI32 =>
    cases mirrored with
    | false =>
      apply LogicalExtr.match_forward_1501 data_program (rootBuilt .defaultI32 false).1 (rootBuilt .defaultI32 false).2.2 #[] 0 (cfg := {}) (i := 4) (a := 11) (b := 12) (x := 1) (y := 8) (c1 := 9) (c2 := 10) (j1 := 2) (j2 := 0) (j3 := 3) (j4 := 1) (w := 32) (kx := 31) (ky := 1)
        (info := (rootBuilt .defaultI32 false).1.insts[4]!) (info1 := (rootBuilt .defaultI32 false).1.insts[2]!) (info2 := (rootBuilt .defaultI32 false).1.insts[0]!) (info3 := (rootBuilt .defaultI32 false).1.insts[3]!) (info4 := (rootBuilt .defaultI32 false).1.insts[1]!)
      all_goals first | rfl | decide +kernel | (unfold ExtrOk; decide +kernel)
    | true =>
      apply LogicalExtr.match_forward_1507 data_program (rootBuilt .defaultI32 true).1 (rootBuilt .defaultI32 true).2.2 #[] 0 (cfg := {}) (i := 4) (a := 12) (b := 11) (x := 1) (y := 8) (c1 := 10) (c2 := 9) (j1 := 3) (j2 := 1) (j3 := 2) (j4 := 0) (w := 32) (kx := 31) (ky := 1)
        (info := (rootBuilt .defaultI32 true).1.insts[4]!) (info1 := (rootBuilt .defaultI32 true).1.insts[3]!) (info2 := (rootBuilt .defaultI32 true).1.insts[1]!) (info3 := (rootBuilt .defaultI32 true).1.insts[2]!) (info4 := (rootBuilt .defaultI32 true).1.insts[0]!)
      all_goals first | rfl | decide +kernel | (unfold ExtrOk; decide +kernel)
  | systemVI32 =>
    cases mirrored with
    | false =>
      apply LogicalExtr.match_forward_1501 data_program (rootBuilt .systemVI32 false).1 (rootBuilt .systemVI32 false).2.2 #[] 0 (cfg := {}) (i := 4) (a := 11) (b := 12) (x := 1) (y := 8) (c1 := 9) (c2 := 10) (j1 := 2) (j2 := 0) (j3 := 3) (j4 := 1) (w := 32) (kx := 31) (ky := 1)
        (info := (rootBuilt .systemVI32 false).1.insts[4]!) (info1 := (rootBuilt .systemVI32 false).1.insts[2]!) (info2 := (rootBuilt .systemVI32 false).1.insts[0]!) (info3 := (rootBuilt .systemVI32 false).1.insts[3]!) (info4 := (rootBuilt .systemVI32 false).1.insts[1]!)
      all_goals first | rfl | decide +kernel | (unfold ExtrOk; decide +kernel)
    | true =>
      apply LogicalExtr.match_forward_1507 data_program (rootBuilt .systemVI32 true).1 (rootBuilt .systemVI32 true).2.2 #[] 0 (cfg := {}) (i := 4) (a := 12) (b := 11) (x := 1) (y := 8) (c1 := 10) (c2 := 9) (j1 := 3) (j2 := 1) (j3 := 2) (j4 := 0) (w := 32) (kx := 31) (ky := 1)
        (info := (rootBuilt .systemVI32 true).1.insts[4]!) (info1 := (rootBuilt .systemVI32 true).1.insts[3]!) (info2 := (rootBuilt .systemVI32 true).1.insts[1]!) (info3 := (rootBuilt .systemVI32 true).1.insts[2]!) (info4 := (rootBuilt .systemVI32 true).1.insts[0]!)
      all_goals first | rfl | decide +kernel | (unfold ExtrOk; decide +kernel)
  | fastI32 =>
    cases mirrored with
    | false =>
      apply LogicalExtr.match_forward_1501 data_program (rootBuilt .fastI32 false).1 (rootBuilt .fastI32 false).2.2 #[] 0 (cfg := {}) (i := 4) (a := 11) (b := 12) (x := 1) (y := 8) (c1 := 9) (c2 := 10) (j1 := 2) (j2 := 0) (j3 := 3) (j4 := 1) (w := 32) (kx := 31) (ky := 1)
        (info := (rootBuilt .fastI32 false).1.insts[4]!) (info1 := (rootBuilt .fastI32 false).1.insts[2]!) (info2 := (rootBuilt .fastI32 false).1.insts[0]!) (info3 := (rootBuilt .fastI32 false).1.insts[3]!) (info4 := (rootBuilt .fastI32 false).1.insts[1]!)
      all_goals first | rfl | decide +kernel | (unfold ExtrOk; decide +kernel)
    | true =>
      apply LogicalExtr.match_forward_1507 data_program (rootBuilt .fastI32 true).1 (rootBuilt .fastI32 true).2.2 #[] 0 (cfg := {}) (i := 4) (a := 12) (b := 11) (x := 1) (y := 8) (c1 := 10) (c2 := 9) (j1 := 3) (j2 := 1) (j3 := 2) (j4 := 0) (w := 32) (kx := 31) (ky := 1)
        (info := (rootBuilt .fastI32 true).1.insts[4]!) (info1 := (rootBuilt .fastI32 true).1.insts[3]!) (info2 := (rootBuilt .fastI32 true).1.insts[1]!) (info3 := (rootBuilt .fastI32 true).1.insts[2]!) (info4 := (rootBuilt .fastI32 true).1.insts[0]!)
      all_goals first | rfl | decide +kernel | (unfold ExtrOk; decide +kernel)
  | defaultI64 =>
    cases mirrored with
    | false =>
      apply LogicalExtr.match_forward_1501 data_program (rootBuilt .defaultI64 false).1 (rootBuilt .defaultI64 false).2.2 #[] 0 (cfg := {}) (i := 4) (a := 11) (b := 12) (x := 1) (y := 8) (c1 := 9) (c2 := 10) (j1 := 2) (j2 := 0) (j3 := 3) (j4 := 1) (w := 64) (kx := 63) (ky := 1)
        (info := (rootBuilt .defaultI64 false).1.insts[4]!) (info1 := (rootBuilt .defaultI64 false).1.insts[2]!) (info2 := (rootBuilt .defaultI64 false).1.insts[0]!) (info3 := (rootBuilt .defaultI64 false).1.insts[3]!) (info4 := (rootBuilt .defaultI64 false).1.insts[1]!)
      all_goals first | rfl | decide +kernel | (unfold ExtrOk; decide +kernel)
    | true =>
      apply LogicalExtr.match_forward_1507 data_program (rootBuilt .defaultI64 true).1 (rootBuilt .defaultI64 true).2.2 #[] 0 (cfg := {}) (i := 4) (a := 12) (b := 11) (x := 1) (y := 8) (c1 := 10) (c2 := 9) (j1 := 3) (j2 := 1) (j3 := 2) (j4 := 0) (w := 64) (kx := 63) (ky := 1)
        (info := (rootBuilt .defaultI64 true).1.insts[4]!) (info1 := (rootBuilt .defaultI64 true).1.insts[3]!) (info2 := (rootBuilt .defaultI64 true).1.insts[1]!) (info3 := (rootBuilt .defaultI64 true).1.insts[2]!) (info4 := (rootBuilt .defaultI64 true).1.insts[0]!)
      all_goals first | rfl | decide +kernel | (unfold ExtrOk; decide +kernel)
  | systemVI64 =>
    cases mirrored with
    | false =>
      apply LogicalExtr.match_forward_1501 data_program (rootBuilt .systemVI64 false).1 (rootBuilt .systemVI64 false).2.2 #[] 0 (cfg := {}) (i := 4) (a := 11) (b := 12) (x := 1) (y := 8) (c1 := 9) (c2 := 10) (j1 := 2) (j2 := 0) (j3 := 3) (j4 := 1) (w := 64) (kx := 63) (ky := 1)
        (info := (rootBuilt .systemVI64 false).1.insts[4]!) (info1 := (rootBuilt .systemVI64 false).1.insts[2]!) (info2 := (rootBuilt .systemVI64 false).1.insts[0]!) (info3 := (rootBuilt .systemVI64 false).1.insts[3]!) (info4 := (rootBuilt .systemVI64 false).1.insts[1]!)
      all_goals first | rfl | decide +kernel | (unfold ExtrOk; decide +kernel)
    | true =>
      apply LogicalExtr.match_forward_1507 data_program (rootBuilt .systemVI64 true).1 (rootBuilt .systemVI64 true).2.2 #[] 0 (cfg := {}) (i := 4) (a := 12) (b := 11) (x := 1) (y := 8) (c1 := 10) (c2 := 9) (j1 := 3) (j2 := 1) (j3 := 2) (j4 := 0) (w := 64) (kx := 63) (ky := 1)
        (info := (rootBuilt .systemVI64 true).1.insts[4]!) (info1 := (rootBuilt .systemVI64 true).1.insts[3]!) (info2 := (rootBuilt .systemVI64 true).1.insts[1]!) (info3 := (rootBuilt .systemVI64 true).1.insts[2]!) (info4 := (rootBuilt .systemVI64 true).1.insts[0]!)
      all_goals first | rfl | decide +kernel | (unfold ExtrOk; decide +kernel)
  | fastI64 =>
    cases mirrored with
    | false =>
      apply LogicalExtr.match_forward_1501 data_program (rootBuilt .fastI64 false).1 (rootBuilt .fastI64 false).2.2 #[] 0 (cfg := {}) (i := 4) (a := 11) (b := 12) (x := 1) (y := 8) (c1 := 9) (c2 := 10) (j1 := 2) (j2 := 0) (j3 := 3) (j4 := 1) (w := 64) (kx := 63) (ky := 1)
        (info := (rootBuilt .fastI64 false).1.insts[4]!) (info1 := (rootBuilt .fastI64 false).1.insts[2]!) (info2 := (rootBuilt .fastI64 false).1.insts[0]!) (info3 := (rootBuilt .fastI64 false).1.insts[3]!) (info4 := (rootBuilt .fastI64 false).1.insts[1]!)
      all_goals first | rfl | decide +kernel | (unfold ExtrOk; decide +kernel)
    | true =>
      apply LogicalExtr.match_forward_1507 data_program (rootBuilt .fastI64 true).1 (rootBuilt .fastI64 true).2.2 #[] 0 (cfg := {}) (i := 4) (a := 12) (b := 11) (x := 1) (y := 8) (c1 := 10) (c2 := 9) (j1 := 3) (j2 := 1) (j3 := 2) (j4 := 0) (w := 64) (kx := 63) (ky := 1)
        (info := (rootBuilt .fastI64 true).1.insts[4]!) (info1 := (rootBuilt .fastI64 true).1.insts[3]!) (info2 := (rootBuilt .fastI64 true).1.insts[1]!) (info3 := (rootBuilt .fastI64 true).1.insts[2]!) (info4 := (rootBuilt .fastI64 true).1.insts[0]!)
      all_goals first | rfl | decide +kernel | (unfold ExtrOk; decide +kernel)

private theorem rootHeld (config : Configuration) (mirrored : Bool) (a b : CV) :
    ValuesHeld (Demanded (rootAfter config mirrored)) (rootBuilt config mirrored).1
      (sourceFrame config mirrored a b) (fun n => rootRF a b (aliasNum #[] n)) := by
  let st := (rootBuilt config mirrored).2.2
  have bound1 : 1 < st.demand.size := by cases config <;> cases mirrored <;> decide +kernel
  have bound8 : 8 < (st.mark 1).demand.size := by cases config <;> cases mirrored <;> decide +kernel
  have initialZero : st.demand = Array.replicate 15 0 := by cases config <;> cases mirrored <;> rfl
  intro x needed value found
  change Demanded ((st.mark 1).mark 8) x at needed
  rw [demanded_mark_iff _ _ _ bound8,demanded_mark_iff _ _ _ bound1] at needed
  rcases needed with rfl | rfl | old
  · cases found
    exact ⟨200,by cases config <;> cases mirrored <;> rfl,by rfl⟩
  · cases found
    exact ⟨193,by cases config <;> cases mirrored <;> rfl,by rfl⟩
  · rw [Demanded,initialZero] at old
    by_cases hx : x < 15 <;> simp [getElem!_def,Array.getElem?_replicate,hx] at old

/-- The complete actual root match and RHS inhabit original-source EXTR value
semantics for arbitrary independent words in all ABI/width and mirror cases.
Only the two underlying parameters are held; fused intermediate values remain
available in the original source frame without materialized machine registers. -/
theorem root_values_witness (config : Configuration) (mirrored : Bool) (a b : CV) :
    let ctx := (rootBuilt config mirrored).1
    let st := (rootBuilt config mirrored).2.2
    let ty := valueType config
    let fr := sourceFrame config mirrored a b
    ∃ trace,
      (matchRule program (Stock.sem ctx) {} 20 (LogicalExtr.extrRule mirrored) [.inst 4]).run (st,#[]) =
        .ok (some (LogicalExtr.extrEnv mirrored ty.width 1 (ty.width-1 : Nat) 8 1),st,#[]) ∧
      (evalExpr program (Stock.sem ctx) {} 60 (LogicalExtr.extrRule mirrored).rhs
        (LogicalExtr.extrEnv mirrored ty.width 1 (ty.width-1 : Nat) 8 1)).run (st,#[]) =
        .ok (some (.regsVec [[(st.base.fresh .int).1]]),rootAfter config mirrored,trace) ∧
      ∃ (mi : MInst) (ρ' : Nat → CV),
        (.regsVec [[(st.base.fresh .int).1]] : V) = .regsVec [[.vreg st.base.nextVreg .int]] ∧
        (rootAfter config mirrored).base = (st.base.fresh .int).2.emit mi ∧
        PRun (fun _ => True) ispec [mi.mapRegs (Backend.lowerFunction.resolve #[] 1)] (rootRF a b) ρ' ∧
        VHolds ⟨ty,Clif.Sem.binary .bor
          (if mirrored then b.setWidth ty.width >>> 1 else a.setWidth ty.width <<< (ty.width-1))
          (if mirrored then a.setWidth ty.width <<< (ty.width-1) else b.setWidth ty.width >>> 1)⟩
          (ρ' st.base.nextVreg) ∧
        ∀ z,z ≠ st.base.nextVreg → ρ' z = rootRF a b z := by
  dsimp only
  let ctx := (rootBuilt config mirrored).1
  let st := (rootBuilt config mirrored).2.2
  let ty := valueType config
  have width : ty.width = 32 ∨ ty.width = 64 := by cases config <;> simp [ty,valueType,Clif.Ty.width]
  have mx : ctx.valueReg? 1 = some (.vreg 193 .int) := by cases config <;> cases mirrored <;> rfl
  have my : ctx.valueReg? 8 = some (.vreg 200 .int) := by cases config <;> cases mirrored <;> rfl
  have safeX : DemandAllowed ctx st 1 := by
    intro i found
    have absent : ctx.defInst? 1 = none := by cases config <;> cases mirrored <;> rfl
    rw [absent] at found
    cases found
  have safeY : DemandAllowed ctx st 8 := by
    intro i found
    have absent : ctx.defInst? 8 = none := by cases config <;> cases mirrored <;> rfl
    rw [absent] at found
    cases found
  obtain ⟨trace,rhs⟩ := LogicalExtr.rhs_forward data_program ctx mirrored mx my width (by decide)
    st safeX safeY #[] 0 (X := (ty.width-1 : Nat)) (Y := 1)
  refine ⟨trace,root_match config mirrored,rhs,?_⟩
  have scope : LowerScope (function config mirrored) := lowerScope_of (by cases config <;> cases mirrored <;> decide +kernel)
  have build : Stock.buildCtx (function config mirrored) = .ok (rootBuilt config mirrored) := by
    cases config <;> cases mirrored <;> rfl
  have inv := buildCtx_mappedInv scope build
  have source : ctx.insts[4]? = some ctx.insts[4]! := by cases config <;> cases mirrored <;> rfl
  have clif : ctx.insts[4]!.clif = some (.binary .bor ty
      (if mirrored then 12 else 11) (if mirrored then 11 else 12)) := by
    cases config <;> cases mirrored <;> rfl
  have getterX : (sourceFrame config mirrored a b).getAs (if mirrored then 12 else 11) ty =
      .ok (if mirrored then b.setWidth ty.width >>> 1 else a.setWidth ty.width <<< (ty.width-1)) := by
    cases config <;> cases mirrored <;> rfl
  have getterY : (sourceFrame config mirrored a b).getAs (if mirrored then 11 else 12) ty =
      .ok (if mirrored then a.setWidth ty.width <<< (ty.width-1) else b.setWidth ty.width >>> 1) := by
    cases config <;> cases mirrored <;> rfl
  have extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size := by
    intro z r mapped
    have size : st.demand.size = ctx.valReg.size := by cases config <;> cases mirrored <;> rfl
    rw [size]
    by_cases small : z < ctx.valReg.size
    · exact small
    · rw [Ctx.valueReg?,Array.getElem?_eq_none (Nat.le_of_not_lt small)] at mapped
      cases mapped
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  exact LogicalExtr.matched_values data_program inv mirrored source clif self (sourceDFG config mirrored a b)
    getterX getterY (aliases := #[]) (ρ := rootRF a b) (by simp) extent (rootHeld config mirrored a b)
    (m := 0) (n := 0) (root_match config mirrored) rhs
private def selectedRootChecks (config : Configuration) (mirrored : Bool) : Bool :=
  let ctx := (rootBuilt config mirrored).1
  let st := (rootBuilt config mirrored).2.2
  match Stock.runTerm ctx "lower" [.inst 4] st with
  | .ok (some _, next, fired) =>
      decide (fired.getLast? = some (LogicalExtr.extrRule mirrored).id) &&
      decide (next.demand = (rootAfter config mirrored).demand)
  | _ => false

-- witness: native_decide (twelve fixed actual first-match lower calls only)
private theorem selectedRootChecks_true : configurations.all (fun config =>
    [false,true].all (selectedRootChecks config)) = true := by native_decide

private theorem selected_inputs (config : Configuration) (mirrored : Bool) :
    let ctx := (rootBuilt config mirrored).1
    let st := (rootBuilt config mirrored).2.2
    ∃ out next fired, ∃ selected : LowerSelection ctx 4 st out next fired,
      selected.rule = LogicalExtr.extrRule mirrored ∧
      next.demand = (rootAfter config mirrored).demand := by
  have allConfig := List.all_eq_true.mp selectedRootChecks_true config
    (by cases config <;> simp [configurations])
  have checked := List.all_eq_true.mp allConfig mirrored (by cases mirrored <;> simp)
  dsimp only
  unfold selectedRootChecks at checked
  cases run : Stock.runTerm (rootBuilt config mirrored).1 "lower" [.inst 4]
      (rootBuilt config mirrored).2.2 with
  | error message => simp [run] at checked
  | ok value =>
    obtain ⟨output,next,fired⟩ := value
    cases output with
    | none => simp [run] at checked
    | some output =>
      simp only [run,Bool.and_eq_true,decide_eq_true_eq] at checked
      obtain ⟨last,demand⟩ := checked
      obtain ⟨selected⟩ := stock_named_lower_selection run
      have member : LogicalExtr.extrRule mirrored ∈ program.rulesOf T.lower.id := by
        cases mirrored <;> rw [show T.lower.id = 686 from rfl,data_program.r686] <;>
          decide +kernel
      have idEq := Option.some.inj (selected.last_rule.symm.trans last)
      exact ⟨output,next,fired,selected,
        eq_of_mem_of_id lower_ids_nodup selected.rule_mem member idEq,demand⟩

/-- Complete actual first-match execution inhabits the selected-root theorem
in every ABI and mirror case for arbitrary independent input words. Only the
underlying parameters are held; looked-through shifts remain unmaterialized. -/
theorem selected_root_values_witness (config : Configuration) (mirrored : Bool) (a b : CV) :
    let ctx := (rootBuilt config mirrored).1
    let st := (rootBuilt config mirrored).2.2
    let ty := valueType config
    ∃ out next fired, ∃ selected : LowerSelection ctx 4 st out next fired,
      selected.rule = LogicalExtr.extrRule mirrored ∧
      ∃ (mi : MInst) (ρ' : Nat → CV),
        out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
        next.base = (st.base.fresh .int).2.emit mi ∧
        PRun (fun _ => True) ispec [mi.mapRegs (Backend.lowerFunction.resolve #[] 1)]
          (rootRF a b) ρ' ∧
        VHolds ⟨ty,Clif.Sem.binary .bor
          (if mirrored then b.setWidth ty.width >>> 1 else a.setWidth ty.width <<< (ty.width-1))
          (if mirrored then a.setWidth ty.width <<< (ty.width-1) else b.setWidth ty.width >>> 1)⟩
          (ρ' st.base.nextVreg) ∧
        ∀ z, z ≠ st.base.nextVreg → ρ' z = rootRF a b z := by
  dsimp only
  obtain ⟨output,next,fired,selected,chosen,demand⟩ := selected_inputs config mirrored
  refine ⟨output,next,fired,selected,chosen,?_⟩
  let ctx := (rootBuilt config mirrored).1
  let st := (rootBuilt config mirrored).2.2
  let ty := valueType config
  have scope : LowerScope (function config mirrored) :=
    lowerScope_of (by cases config <;> cases mirrored <;> decide +kernel)
  have build : Stock.buildCtx (function config mirrored) = .ok (rootBuilt config mirrored) := by
    cases config <;> cases mirrored <;> rfl
  have inv := buildCtx_mappedInv scope build
  have source : ctx.insts[4]? = some ctx.insts[4]! := by
    cases config <;> cases mirrored <;> rfl
  have clif : ctx.insts[4]!.clif = some (.binary .bor ty
      (if mirrored then 12 else 11) (if mirrored then 11 else 12)) := by
    cases config <;> cases mirrored <;> rfl
  have getterX : (sourceFrame config mirrored a b).getAs (if mirrored then 12 else 11) ty =
      .ok (if mirrored then b.setWidth ty.width >>> 1 else a.setWidth ty.width <<< (ty.width-1)) := by
    cases config <;> cases mirrored <;> rfl
  have getterY : (sourceFrame config mirrored a b).getAs (if mirrored then 11 else 12) ty =
      .ok (if mirrored then a.setWidth ty.width <<< (ty.width-1) else b.setWidth ty.width >>> 1) := by
    cases config <;> cases mirrored <;> rfl
  have extent : ∀ z r, ctx.valueReg? z = some r → z < st.demand.size := by
    intro z r mapped
    have size : st.demand.size = ctx.valReg.size := by
      cases config <;> cases mirrored <;> rfl
    rw [size]
    by_cases small : z < ctx.valReg.size
    · exact small
    · rw [Ctx.valueReg?,Array.getElem?_eq_none (Nat.le_of_not_lt small)] at mapped
      cases mapped
  have held : ValuesHeld (Demanded next) ctx (sourceFrame config mirrored a b)
      (fun k => rootRF a b (aliasNum #[] k)) := by
    simpa only [ValuesHeld,Demanded,demand] using (rootHeld config mirrored a b)
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h =>
    ⟨w',h,SameWorld.refl _ _⟩
  exact LogicalExtr.selected_root_values inv mirrored source clif self
    (sourceDFG config mirrored a b) getterX getterY selected chosen
    (aliases := #[]) (ρ := rootRF a b) (by simp) extent held

private def recordFrame (config : Configuration) (mirrored : Bool) (a b : CV) : Clif.Frame :=
  { sourceFrame config mirrored a b with body :=
    [⟨[13],.binary .bor (valueType config) (if mirrored then 12 else 11) (if mirrored then 11 else 12)⟩] }
private def recordDemand (config : Configuration) (mirrored : Bool) : Array Nat :=
  (rootAfter config mirrored).demand.modify 13 (·+1)
private def sourceKey (info : IInfo) := (info.clif,info.results)
private def ctxKey (ctx : Ctx) := (ctx.insts.map sourceKey,ctx.valTy,ctx.valDef,ctx.valReg)
private theorem dfg_transport {a b : Ctx} {fr : Clif.Frame}
    (insts : a.insts.map sourceKey = b.insts.map sourceKey)
    (types : a.valTy = b.valTy) (defs : a.valDef = b.valDef) (dfg : DFGCons b fr) : DFGCons a fr := by
  constructor
  · intro x j info cl v defined found original pure lookup
    have view : (b.insts[j]?).map sourceKey = some (sourceKey info) := by
      rw [← Array.getElem?_map,← insts,Array.getElem?_map,found]
      rfl
    obtain ⟨info',found',same⟩ := Option.map_eq_some_iff.mp view
    have clifEq := congrArg Prod.fst same
    have resultsEq := congrArg Prod.snd same
    change info'.clif = info.clif at clifEq
    change info'.results = info.results at resultsEq
    obtain ⟨vals,evaluated,written⟩ := dfg.1 x j info' cl v
      (by simpa only [Ctx.defInst?,defs] using defined) found' (clifEq.trans original) pure lookup
    exact ⟨vals,evaluated,by rw [← resultsEq]; exact written⟩
  · simpa only [FrameTyped,Ctx.valueType?,types] using dfg.2

private def recordChecks (config : Configuration) (mirrored : Bool) : Bool :=
  match Stock.lower (function config mirrored) with
  | .error _ => false
  | .ok result =>
    decide (aliasNum result.final.alias 193 = 193) &&
    decide (aliasNum result.final.alias 200 = 200) &&
    result.blockScans.toList.any (fun event =>
      decide (ctxKey event.ctx = ctxKey (rootBuilt config mirrored).1) &&
      event.output.records.any (fun record =>
        record.inst == 4 && decide (record.output.state.demand = recordDemand config mirrored) &&
        record.output.step.any (fun step => step.decision == .emitted &&
          decide (step.rules.getLast? = some (LogicalExtr.extrRule mirrored).id))))
-- witness: native_decide (twelve fixed complete driver runs, not value semantics)
private theorem recordChecks_true : configurations.all (fun config =>
    [false,true].all (recordChecks config)) = true := by native_decide

private structure RecordInputs (config : Configuration) (mirrored : Bool) (a b : CV) where
  result : Stock.Result
  event : Stock.BlockScanEvent
  record : Stock.ScanRecord
  info : IInfo
  step : Stock.Step
  run : Stock.lower (function config mirrored) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = 4
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.binary .bor (valueType config)
    (if mirrored then 12 else 11) (if mirrored then 11 else 12))
  results : info.results = [13]
  mapped : event.ctx.valueReg? 13 = some (.vreg 205 .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some (LogicalExtr.extrRule mirrored).id
  dfg : DFGCons event.ctx (recordFrame config mirrored a b)
  held : ValuesHeld (Demanded record.output.state) event.ctx (recordFrame config mirrored a b)
    (fun n => rootRF a b (aliasNum result.final.alias n))

private theorem record_inputs (config : Configuration) (mirrored : Bool) (a b : CV) :
    Nonempty (RecordInputs config mirrored a b) := by
  have allConfig := List.all_eq_true.mp recordChecks_true config
    (by cases config <;> simp [configurations])
  have actual := List.all_eq_true.mp allConfig mirrored (by cases mirrored <;> simp)
  unfold recordChecks at actual
  cases run : Stock.lower (function config mirrored) with
  | error message => simp [run] at actual
  | ok result =>
    simp only [run,Bool.and_eq_true,List.any_eq_true,beq_iff_eq,decide_eq_true_eq,and_assoc] at actual
    obtain ⟨alias193,alias200,event,events,ctxEq,record,records,current,demand,stepData⟩ := actual
    simp only [ctxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
          step.rules.getLast? = some (LogicalExtr.extrRule mirrored).id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey =
        some (some (.binary .bor (valueType config)
          (if mirrored then 12 else 11) (if mirrored then 11 else 12)),[13]) := by
      rw [← Array.getElem?_map,insts,current,Array.getElem?_map]
      cases config <;> cases mirrored <;> rfl
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    have mapped : event.ctx.valueReg? 13 = some (.vreg 205 .int) := by
      simp only [Ctx.valueReg?,maps]
      cases config <;> cases mirrored <;> rfl
    have baseDFG := dfgCons_congr (ctx := (rootBuilt config mirrored).1)
      (fr := sourceFrame config mirrored a b) (fr' := recordFrame config mirrored a b)
      rfl rfl rfl (sourceDFG config mirrored a b)
    have actualDFG := dfg_transport insts types defs baseDFG
    have held : ValuesHeld (Demanded record.output.state) event.ctx (recordFrame config mirrored a b)
        (fun n => rootRF a b (aliasNum result.final.alias n)) := by
      intro x needed val lookup
      by_cases one : x = 1
      · subst x
        change some ⟨valueType config,a.setWidth (valueType config).width⟩ = some val at lookup
        cases lookup
        refine ⟨193,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]; cases config <;> cases mirrored <;> rfl
        · change VHolds _ (rootRF a b (aliasNum result.final.alias 193))
          rw [alias193]; rfl
      · by_cases eight : x = 8
        · subst x
          change some ⟨valueType config,b.setWidth (valueType config).width⟩ = some val at lookup
          cases lookup
          refine ⟨200,?_,?_⟩
          · simp only [Ctx.valueReg?,maps]; cases config <;> cases mirrored <;> rfl
          · change VHolds _ (rootRF a b (aliasNum result.final.alias 200))
            rw [alias200]; rfl
        · by_cases unmaterialized : x = 9 ∨ x = 10 ∨ x = 11 ∨ x = 12
          · rcases unmaterialized with rfl | rfl | rfl | rfl
            all_goals
              rw [Demanded,demand] at needed
              cases config <;> cases mirrored <;> change 0 ≠ 0 at needed <;> exact (needed rfl).elim
          · simp only [not_or] at unmaterialized
            simp [recordFrame,sourceFrame,one,eight,unmaterialized.1,unmaterialized.2.1,
              unmaterialized.2.2.1,unmaterialized.2.2.2] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,
      mapped,recorded,emitted,selectedId,actualDFG,held⟩⟩

/-- Complete retained EXTR records in every ABI and mirror case execute the
original OR of two shifted independent words, through actual final aliases. -/
theorem record_values_witness (config : Configuration) (mirrored : Bool) (a b : CV) :
    ∃ (result : Stock.Result) (event : Stock.BlockScanEvent) (record : Stock.ScanRecord) (ρ' : Nat → CV),
      Stock.lower (function config mirrored) = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (rootRF a b) ρ' ∧
      VHolds ⟨valueType config,Clif.Sem.binary .bor
        (a.setWidth (valueType config).width <<< ((valueType config).width-1))
        (b.setWidth (valueType config).width >>> 1)⟩ (ρ' record.input.base.nextVreg) ∧
      ∀ n, n ≠ record.input.base.nextVreg → ρ' n = rootRF a b n := by
  obtain ⟨input⟩ := record_inputs config mirrored a b
  have scope : LowerScope (function config mirrored) :=
    lowerScope_of (by cases config <;> cases mirrored <;> decide +kernel)
  have getX : (recordFrame config mirrored a b).getAs (if mirrored then 12 else 11) (valueType config) =
      .ok (if mirrored then b.setWidth (valueType config).width >>> 1
        else a.setWidth (valueType config).width <<< ((valueType config).width-1)) := by
    cases config <;> cases mirrored <;> rfl
  have getY : (recordFrame config mirrored a b).getAs (if mirrored then 11 else 12) (valueType config) =
      .ok (if mirrored then a.setWidth (valueType config).width <<< ((valueType config).width-1)
        else b.setWidth (valueType config).width >>> 1) := by
    cases config <;> cases mirrored <;> rfl
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨mi,ρ',outputs,code,upper,execution,value,kept⟩ := LogicalExtr.record_values
    input.run scope mirrored input.events input.records input.source input.clif input.results
    input.mapped input.recorded input.emitted input.selectedId self input.dfg input.held getX getY
  refine ⟨input.result,input.event,input.record,ρ',input.run,input.events,input.records,execution,?_,kept⟩
  cases mirrored <;> simpa only [Bool.false_eq_true,ite_false,ite_true,Clif.Sem.binary,Clif.Sem.bor,BitVec.or_comm] using value

private theorem record_frame_available (config : Configuration) (mirrored : Bool) (a b : CV) (ctx : Ctx) :
    (restrict (recordFrame config mirrored a b)
      (availOf (function config mirrored) (availIn (function config mirrored) ctx) 0 4)).regs =
      (recordFrame config mirrored a b).regs := by
  funext x
  by_cases present : x = 1 ∨ x = 8 ∨ x = 9 ∨ x = 10 ∨ x = 11 ∨ x = 12
  · rcases present with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      apply restrict_regs_of_mem
      simp [availOf,function,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,recordFrame,sourceFrame,present.1,present.2.1,present.2.2.1,
      present.2.2.2.1,present.2.2.2.2.1,present.2.2.2.2.2]

/-- The actual complete EXTR record also transfers the real original source
step under its original availability guard, including unmaterialized shifts. -/
theorem source_values_witness (config : Configuration) (mirrored : Bool) (a b : CV) :
    ∃ (result : Stock.Result) (event : Stock.BlockScanEvent) (record : Stock.ScanRecord)
      (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (function config mirrored) = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (recordFrame config mirrored a b,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (rootRF a b) ρ' ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf (function config mirrored) (availIn (function config mirrored) result.ctx) 0 5)
        event.ctx fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨input⟩ := record_inputs config mirrored a b
  obtain ⟨scope,dominated,_⟩ := compiled_exists config mirrored false
  have available := record_frame_available config mirrored a b input.result.ctx
  have restrictedDFG := dfgCons_congr (ctx := input.event.ctx)
    (fr := recordFrame config mirrored a b)
    (fr' := restrict (recordFrame config mirrored a b)
      (availOf (function config mirrored) (availIn (function config mirrored) input.result.ctx) 0 4))
    rfl rfl available input.dfg
  have guarded := input.held.mono (fun y (h : Demanded input.record.output.state y ∧ y ∈
    availOf (function config mirrored) (availIn (function config mirrored) input.result.ctx) 0 4) => h.1)
  have block : (function config mirrored).blocks[0]? = some ((function config mirrored).blocks[0]!) := rfl
  have statement : ((function config mirrored).blocks[0]!).body[4]? =
      some (⟨[13],.binary .bor (valueType config)
        (if mirrored then 12 else 11) (if mirrored then 11 else 12)⟩ : Clif.Stmt) := rfl
  have current : input.record.inst = blockStart (function config mirrored) 0 + 4 := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  let ty := valueType config
  let val : Clif.Val := ⟨ty,Clif.Sem.binary .bor
    (if mirrored then b.setWidth ty.width >>> 1 else a.setWidth ty.width <<< (ty.width-1))
    (if mirrored then a.setWidth ty.width <<< (ty.width-1) else b.setWidth ty.width >>> 1)⟩
  let fr' : Clif.Frame := {recordFrame config mirrored a b with
    regs := (recordFrame config mirrored a b).regs.set 13 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (recordFrame config mirrored a b) Clif.Mem.empty
      (.binary .bor ty (if mirrored then 12 else 11) (if mirrored then 11 else 12)) =
      .ok ([val],Clif.Mem.empty) := by
    cases config <;> cases mirrored <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (recordFrame config mirrored a b,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,.binary .bor ty (if mirrored then 12 else 11) (if mirrored then 11 else 12),
      [val],(recordFrame config mirrored a b).regs.set 13 val,[],input.source,input.clif,
      by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨u,v,ρ',getX,getY,execution,value,memory,kept,installed⟩ := LogicalExtr.source_from_step
    input.run scope dominated mirrored input.events input.records block statement current
    input.source input.clif input.results rfl input.mapped input.recorded input.emitted
    input.selectedId self restrictedDFG guarded sourceStep
  exact ⟨input.result,input.event,input.record,ρ',fr',input.run,input.events,input.records,
    sourceStep,execution,installed⟩

end E2E.StockLogicalExtrWitness
