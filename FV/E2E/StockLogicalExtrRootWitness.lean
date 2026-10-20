import FV.E2E.StockLogicalExtrWitness
import FV.Backend.Proof.StockLogicalExtrMatchedValues


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
end E2E.StockLogicalExtrWitness
