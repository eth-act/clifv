import FV.Backend.Proof.StockValues
import FV.Backend.Proof.LowerAlias
import FV.Backend.Proof.IselFamAluBIconst
import FV.Backend.Proof.IselLcf
import FV.Backend.Proof.CSemRename

/-! Alias-aware fragment semantics and availability for the reverse stock scan.
The frame property uses actual writes; allocation order need not agree with
source execution order. These are internal simulation lemmas, not new input checks.
-/

namespace Backend.Stock.Proof

open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

/-- Installing a resolved result preserves every other demanded value whose
resolved register is not written by the actual fragment. -/
theorem ValuesHeld.resolvedResult_frame {needed : Nat → Prop} {ctx : Ctx}
    {fr : Clif.Frame} {ρ ρ' : Nat → CV} {gn : Nat → Nat} {x n d : Nat}
    {v : Clif.Val} {ms : List MInst} {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (h : ValuesHeld needed ctx fr (fun k => ρ (gn k)))
    (hmap : ctx.valueReg? x = some (.vreg n .int)) (hresult : gn n = d)
    (hvalue : VHolds v (ρ' d))
    (hkeep : ∀ y m, needed y → y ≠ x → ctx.valueReg? y = some (.vreg m .int) →
      (fr.regs y).isSome = true → ∀ mi ∈ ms, gn m ∉ vdefs mi)
    (hrun : PRun F isem ms ρ ρ') :
    ValuesHeld needed ctx (withValue fr x v) (fun k => ρ' (gn k)) := by
  intro y hy value hv
  by_cases he : y = x
  · subst y
    simp only [withValue, eq_self, ite_true] at hv
    cases hv
    exact ⟨n, hmap, by change VHolds v (ρ' (gn n)); rw [hresult]; exact hvalue⟩
  · simp only [withValue, ite_eq_right he] at hv
    obtain ⟨m, hm, hold⟩ := h y hy value hv
    obtain ⟨w', hr, _⟩ := hrun Arm.ArmState.default
    have keep := seqRun_fall_frame (hkeep y m hy he hm (by rw [hv]; rfl)) hr
    exact ⟨m, hm, by change VHolds value (ρ' (gn m)); rw [keep]; exact hold⟩

/-- Reverse allocation may put an already materialized producer above the
current fragment's allocation interval. Both sides of that interval are safe. -/
theorem ValuesHeld.resolvedResult_interval {needed : Nat → Prop} {ctx : Ctx}
    {fr : Clif.Frame} {ρ ρ' : Nat → CV} {gn : Nat → Nat} {x n d lo hi : Nat}
    {v : Clif.Val} {ms : List MInst} {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (h : ValuesHeld needed ctx fr (fun k => ρ (gn k)))
    (hmap : ctx.valueReg? x = some (.vreg n .int)) (hresult : gn n = d)
    (hvalue : VHolds v (ρ' d))
    (houtside : ∀ y m, needed y → y ≠ x → ctx.valueReg? y = some (.vreg m .int) →
      (fr.regs y).isSome = true → gn m < lo ∨ hi ≤ gn m)
    (hdefs : ∀ mi ∈ ms, ∀ e ∈ vdefs mi, lo ≤ e ∧ e < hi)
    (hrun : PRun F isem ms ρ ρ') :
    ValuesHeld needed ctx (withValue fr x v) (fun k => ρ' (gn k)) := by
  apply h.resolvedResult_frame hmap hresult hvalue _ hrun
  intro y m hy hne hm hv mi hmi he
  have := houtside y m hy hne hm hv
  have := hdefs mi hmi _ he
  omega

/-- Numeric part of the actual final array resolver. -/
def aliasNum (a : Array (Option Nat)) (n : Nat) : Nat :=
  chaseF (fun k => (a[k]?).join) (a.size + 1) n

private theorem alias_renaming (a : Array (Option Nat)) :
    VRenaming (Backend.lowerFunction.resolve a (a.size + 1)) (aliasNum a) := by
  refine ⟨fun n c => resolve_vreg a _ n c, ?_⟩
  intro r hr
  cases r with
  | vreg n c => exact False.elim (hr n c rfl)
  | _ => simp [Backend.lowerFunction.resolve]

private theorem alias_fresh {a : Array (Option Nat)} {lo n : Nat}
    (ha : a.size ≤ lo) (hn : lo ≤ n) : aliasNum a n = n := by
  apply chaseF_none
  rw [Array.getElem?_eq_none (by omega)]
  rfl

private theorem renamed_defs (a : Array (Option Nat)) (m : MInst) :
    vdefs (m.mapRegs (Backend.lowerFunction.resolve a (a.size + 1))) =
      (vdefs m).map (aliasNum a) := by
  unfold vdefs
  rw [operands_mapRegs (alias_renaming a)]
  cases hm : m.operands with
  | error e => rfl
  | ok ops =>
    simp only [Except.map, Array.toList_map]
    rw [filter_map_rn _ Operand.isDef (fun _ => rfl)]
    simp only [List.map_map]
    rfl

/-- Semantic transport for a selected fragment with mapped source operands.
Fresh writes stay in [lo, hi); every pre-existing use resolves outside it. This
allows producers allocated later in the reverse scan to be read above hi. -/
theorem stock_alias_interval_prun {a : Array (Option Nat)} {lo hi : Nat}
    {ms : List MInst} {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    {ρ ρraw : Nat → CV} (ha : a.size ≤ lo)
    (hdefs : ∀ m ∈ ms, ∀ d ∈ vdefs m, lo ≤ d ∧ d < hi)
    (huses : ∀ m ∈ ms, ∀ u ∈ vuseNums m,
      (lo ≤ u ∧ u < hi) ∨ aliasNum a u < lo ∨ hi ≤ aliasNum a u)
    (hsem : ∀ i, isem (i.mapRegs (Backend.lowerFunction.resolve a (a.size + 1))) = isem i)
    (hrun : PRun F isem ms (fun n => ρ (aliasNum a n)) ρraw) :
    ∃ ρout, PRun F isem (ms.map (·.mapRegs
        (Backend.lowerFunction.resolve a (a.size + 1)))) ρ ρout ∧
      (∀ n, lo ≤ n → n < hi → ρout n = ρraw n) ∧
      (∀ n, n < lo ∨ hi ≤ n → ρout n = ρ n) := by
  let D : Nat → Prop := fun n => lo ≤ n ∧ n < hi
  have hfix : ∀ n, D n → aliasNum a n = n := fun n hn => alias_fresh ha hn.1
  have hrenDefs : ∀ m ∈ ms.map (·.mapRegs
      (Backend.lowerFunction.resolve a (a.size + 1))), ∀ n ∈ vdefs m, D n := by
    intro m hm n hn
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hm
    rw [renamed_defs] at hn
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hn
    rw [alias_fresh ha (hdefs raw hraw d hd).1]
    exact hdefs raw hraw d hd
  let ρout : Nat → CV := fun n => if D n then ρraw n else ρ n
  refine ⟨ρout, ?_, fun n hn hhi => ite_eq_left ⟨hn, hhi⟩,
    fun n hn => ite_eq_right (by dsimp [D]; omega)⟩
  intro w
  obtain ⟨w', hr, hw⟩ := hrun w
  have huse : ∀ m ∈ ms, ∀ u ∈ vuseNums m, D u ∨ ¬D (aliasNum a u) := by
    intro m hm u hu
    rcases huses m hm u hu with h | h
    · exact Or.inl h
    · exact Or.inr (by dsimp [D]; omega)
  obtain ⟨ρnew, hnew, hagree⟩ := (seqRun_rename (alias_renaming a) hsem hfix
    hdefs huse (fun _ _ => rfl)).1 hr
  have he : ρnew = ρout := by
    funext n
    by_cases hn : D n
    · have h := hagree n (Or.inl hn)
      rw [alias_fresh ha hn.1] at h
      exact h.symm.trans (ite_eq_left hn).symm
    · have hkeep := seqRun_fall_frame
        (fun m hm hd => hn (hrenDefs m hm _ hd)) hnew
      exact hkeep.trans (ite_eq_right hn).symm
  exact ⟨w', by simpa only [he] using hnew, hw⟩

/-- Fresh-only selected code (including constant materialization) executes after
the actual array alias renaming. Its result file is uniform over machine worlds;
registers below the fragment are retained from the incoming physical execution. -/
theorem stock_alias_fresh_prun {a : Array (Option Nat)} {lo : Nat}
    {ms : List MInst} {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    {ρ ρraw : Nat → CV} (ha : a.size ≤ lo)
    (hdefs : ∀ m ∈ ms, ∀ d ∈ vdefs m, lo ≤ d)
    (huses : ∀ m ∈ ms, ∀ u ∈ vuseNums m, lo ≤ u)
    (hsem : ∀ i, isem (i.mapRegs (Backend.lowerFunction.resolve a (a.size + 1))) = isem i)
    (hrun : PRun F isem ms (fun n => ρ (aliasNum a n)) ρraw) :
    ∃ ρout, PRun F isem (ms.map (·.mapRegs
        (Backend.lowerFunction.resolve a (a.size + 1)))) ρ ρout ∧
      (∀ n, lo ≤ n → ρout n = ρraw n) ∧ (∀ n, n < lo → ρout n = ρ n) := by
  let D : Nat → Prop := fun n => lo ≤ n
  have hfix : ∀ n, D n → aliasNum a n = n := fun n hn => alias_fresh ha hn
  have hrenDefs : ∀ m ∈ ms.map (·.mapRegs
      (Backend.lowerFunction.resolve a (a.size + 1))), ∀ n ∈ vdefs m, lo ≤ n := by
    intro m hm n hn
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hm
    rw [renamed_defs] at hn
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hn
    rw [alias_fresh ha (hdefs raw hraw d hd)]
    exact hdefs raw hraw d hd
  let ρout : Nat → CV := fun n => if lo ≤ n then ρraw n else ρ n
  refine ⟨ρout, ?_, fun n hn => ite_eq_left hn, fun n hn => ite_eq_right (by omega)⟩
  intro w
  obtain ⟨w', hr, hw⟩ := hrun w
  obtain ⟨ρnew, hnew, hagree⟩ := (seqRun_rename (alias_renaming a) hsem hfix
    hdefs (fun m hm u hu => Or.inl (huses m hm u hu)) (fun _ _ => rfl)).1 hr
  have he : ρnew = ρout := by
    funext n
    by_cases hn : lo ≤ n
    · have h := hagree n (Or.inl hn)
      rw [alias_fresh ha hn] at h
      exact h.symm.trans (ite_eq_left hn).symm
    · have hkeep := seqRun_fall_frame
        (fun m hm hd => Nat.not_le_of_lt (Nat.lt_of_not_ge hn) (hrenDefs m hm _ hd)) hnew
      exact hkeep.trans (ite_eq_right hn).symm
  exact ⟨w', by simpa only [he] using hnew, hw⟩

/-! The witnesses use actual constant materialization and the actual array
resolver. The other live value is in vreg 200, above the fragment [194, 195):
the earlier below-only availability lemma cannot cover this reverse-allocation case. -/

private def witnessAliases : Array (Option Nat) :=
  aliasStep (aliasStep #[] (192, 194)) (193, 200)

set_option maxRecDepth 2048 in
private theorem witness_alias_facts :
    witnessAliases.size = 194 ∧ aliasNum witnessAliases 192 = 194 ∧
      aliasNum witnessAliases 193 = 200 := by decide

private def witnessFrame : Clif.Frame := {
  func := sinkCtx.func
  regs := fun x => if x = 1 then some (.ofInt .i64 11) else none
  slots := [], body := [], term := .ret [0] }

private def witnessRF (n : Nat) : CV := if n = 200 then 11 else 0

private def witnessNeeded (x : Nat) : Prop := x = 0 ∨ x = 1

private theorem witness_held :
    ValuesHeld witnessNeeded sinkCtx witnessFrame
      (fun k => witnessRF (aliasNum witnessAliases k)) := by
  intro x _ v hv
  by_cases he : x = 1
  · subst x
    change some (Clif.Val.ofInt .i64 11) = some v at hv
    cases hv
    refine ⟨193, rfl, ?_⟩
    change VHolds (Clif.Val.ofInt .i64 11) (witnessRF (aliasNum witnessAliases 193))
    rw [witness_alias_facts.2.2]
    unfold VHolds witnessRF
    decide
  · simp [witnessFrame, he] at hv

private theorem witness_outside :
    ∀ y m, witnessNeeded y → y ≠ 0 → sinkCtx.valueReg? y = some (.vreg m .int) →
      (witnessFrame.regs y).isSome = true →
        aliasNum witnessAliases m < 194 ∨ 195 ≤ aliasNum witnessAliases m := by
  intro y m hy hne hm _
  rcases hy with hy | hy
  · exact False.elim (hne hy)
  · subst y
    change some (Reg.vreg 193 .int) = some (Reg.vreg m .int) at hm
    cases hm
    rw [witness_alias_facts.2.2]
    exact Or.inr (by decide)

private theorem witness_selfRefines : Refines (fun _ => True) ispec :=
  fun _ _ _ _ w' _ h => ⟨w', h, SameWorld.refl _ _⟩

private theorem witness_materialization (ρ : Nat → CV) :
    ∃ ms ρ', PRun (fun _ => True) ispec ms ρ ρ' ∧
      (∀ mi ∈ ms, ∀ e ∈ vdefs mi, 194 ≤ e ∧ e < 195) ∧
      (∀ mi ∈ ms, ∀ u ∈ vuseNums mi, 194 ≤ u) ∧
      VHolds (Clif.Val.ofInt .i8 9) (ρ' 194) ∧
      (∀ n, n < 194 ∨ 195 ≤ n → ρ' n = ρ n) := by
  have mat := imm_case_movz witness_selfRefines (w := 8) (i := 9)
    (mw := ⟨9, 0⟩) (Or.inl rfl) rfl sinkState.base
  obtain ⟨ms, d, hd, hshape, hrun⟩ := mat
  change V.reg (.vreg 194 .int) = V.reg (.vreg d .int) at hd
  cases hd
  obtain ⟨ρ', X, hr, hx, hX, _⟩ := hrun ρ
  have hdefs : ∀ mi ∈ ms, ∀ e ∈ vdefs mi, 194 ≤ e ∧ e < 195 :=
    fun mi hmi e he => hshape.defs mi hmi e he
  refine ⟨ms, ρ', hr, hdefs, ?_, ?_, ?_⟩
  · intro mi hmi u hu
    have h := hshape.uses mi hmi u hu
    change 194 ≤ u ∨ u = 194 at h
    omega
  · apply vholds_of_lo64 (by decide) hx
    exact hX
  · intro n hn
    obtain ⟨w', hs, _⟩ := hr Arm.ArmState.default
    apply seqRun_fall_frame _ hs
    intro mi hmi he
    have := hdefs mi hmi n he
    omega

theorem ValuesHeld.resolvedResult_frame_witness :
    ∃ ms ρ', PRun (fun _ => True) ispec ms witnessRF ρ' ∧
      ValuesHeld witnessNeeded sinkCtx (withValue witnessFrame 0 (.ofInt .i8 9))
        (fun k => ρ' (aliasNum witnessAliases k)) ∧
      ρ' 200 = 11 ∧ aliasNum witnessAliases 193 = 200 ∧
      ¬aliasNum witnessAliases 193 < 194 := by
  obtain ⟨ms, ρ', hr, hdefs, _, hv, hkeep⟩ := witness_materialization witnessRF
  have held := witness_held.resolvedResult_frame (x := 0) (n := 192)
    rfl witness_alias_facts.2.1 hv (by
      intro y m hy hne hm hh mi hmi he
      have := witness_outside y m hy hne hm hh
      have := hdefs mi hmi _ he
      omega) hr
  refine ⟨ms, ρ', hr, held, hkeep 200 (Or.inr (by decide)),
    witness_alias_facts.2.2, ?_⟩
  rw [witness_alias_facts.2.2]
  decide

theorem ValuesHeld.resolvedResult_interval_witness :
    ∃ ms ρ', PRun (fun _ => True) ispec ms witnessRF ρ' ∧
      ValuesHeld witnessNeeded sinkCtx (withValue witnessFrame 0 (.ofInt .i8 9))
        (fun k => ρ' (aliasNum witnessAliases k)) ∧
      VHolds (Clif.Val.ofInt .i8 9) (ρ' 194) ∧ ρ' 200 = 11 := by
  obtain ⟨ms, ρ', hr, hdefs, _, hv, hkeep⟩ := witness_materialization witnessRF
  exact ⟨ms, ρ', hr, witness_held.resolvedResult_interval (x := 0) (n := 192)
    rfl witness_alias_facts.2.1 hv witness_outside hdefs hr, hv,
    hkeep 200 (Or.inr (by decide))⟩

theorem stock_alias_fresh_prun_witness :
    ∃ (ms : List MInst) (ρ' : Nat → CV), PRun (fun _ => True) ispec
        (ms.map (·.mapRegs (Backend.lowerFunction.resolve witnessAliases
          (witnessAliases.size + 1)))) witnessRF ρ' ∧
      VHolds (Clif.Val.ofInt .i8 9) (ρ' 194) ∧ ρ' 200 = 11 ∧ ρ' 192 = 0 ∧
      aliasNum witnessAliases 192 = 194 ∧ aliasNum witnessAliases 193 = 200 := by
  obtain ⟨ms, ρraw, hr, hdefs, huses, hv, hkeep⟩ :=
    witness_materialization (fun n => witnessRF (aliasNum witnessAliases n))
  have hsem : ∀ i, ispec (i.mapRegs (Backend.lowerFunction.resolve witnessAliases
      (witnessAliases.size + 1))) = ispec i := by
    intro i
    funext us w
    exact ispec_mapRegs (alias_renaming witnessAliases) us w i
  obtain ⟨ρ', hrun, hfresh, hold⟩ := stock_alias_fresh_prun
    (lo := 194) (by rw [witness_alias_facts.1]; exact Nat.le_refl _)
    (fun mi hmi e he => (hdefs mi hmi e he).1) huses hsem hr
  refine ⟨ms, ρ', hrun, ?_, ?_, hold 192 (by decide),
    witness_alias_facts.2.1, witness_alias_facts.2.2⟩
  · rw [hfresh 194 (by decide)]
    exact hv
  · rw [hfresh 200 (by decide), hkeep 200 (Or.inr (by decide)),
      alias_fresh (a := witnessAliases) (lo := 194) (by rw [witness_alias_facts.1]; exact Nat.le_refl _)
        (by decide)]
    rfl

set_option maxRecDepth 2048 in
/-- A real ALU fragment reads source vreg 193 through alias 200 and writes
fresh vreg 194. This exercises renamed operands, not only register-free constants. -/
theorem stock_alias_interval_prun_witness :
    ∃ (ρ' : Nat → CV), PRun (fun _ => True) ispec
        [(MInst.aluRRImm12 .add .size64 (.vreg 194 .int) (.vreg 193 .int) ⟨1, false⟩).mapRegs
          (Backend.lowerFunction.resolve witnessAliases (witnessAliases.size + 1))]
        witnessRF ρ' ∧ ρ' 194 = 12 ∧ ρ' 200 = 11 ∧ ρ' 192 = 0 ∧
      aliasNum witnessAliases 193 = 200 := by
  let ρraw : Nat → CV := fun n => witnessRF (aliasNum witnessAliases n)
  have hr193 : ρraw 193 = 11 := by
    change witnessRF (aliasNum witnessAliases 193) = 11
    rw [witness_alias_facts.2.2]
    rfl
  have hrun : PRun (fun _ => True) ispec
      [.aluRRImm12 .add .size64 (.vreg 194 .int) (.vreg 193 .int) ⟨1, false⟩]
      ρraw (upd ρraw 194 12) := by
    apply prun_cons witness_selfRefines
      (ops := #[⟨194, .int, .def, .late, .reg⟩, ⟨193, .int, .use, .early, .reg⟩])
      (by rfl)
      (outs := [12])
    · intro w
      change ispec (.aluRRImm12 .add .size64 (.vreg 194 .int) (.vreg 193 .int) ⟨1, false⟩)
        [ρraw 193] w = some ([12], w, .next)
      rw [hr193]
      rfl
    · rfl
    · have hupd (ρ : Nat → CV) :
          vdefUpd #[⟨194, .int, .def, .late, .reg⟩, ⟨193, .int, .use, .early, .reg⟩]
            [12] ρ = upd ρ 194 12 := rfl
      rw [hupd]
      exact prun_nil _
  have hdefs : ∀ m ∈ [MInst.aluRRImm12 .add .size64 (.vreg 194 .int)
      (.vreg 193 .int) ⟨1, false⟩], ∀ d ∈ vdefs m, 194 ≤ d ∧ d < 195 := by
    intro m hm d hd
    simp only [List.mem_singleton] at hm
    subst m
    change d ∈ [194] at hd
    simp only [List.mem_singleton] at hd
    subst d
    decide
  have huses : ∀ m ∈ [MInst.aluRRImm12 .add .size64 (.vreg 194 .int)
      (.vreg 193 .int) ⟨1, false⟩], ∀ u ∈ vuseNums m,
      (194 ≤ u ∧ u < 195) ∨ aliasNum witnessAliases u < 194 ∨
        195 ≤ aliasNum witnessAliases u := by
    intro m hm u hu
    simp only [List.mem_singleton] at hm
    subst m
    change u ∈ [193] at hu
    simp only [List.mem_singleton] at hu
    subst u
    rw [witness_alias_facts.2.2]
    exact Or.inr (Or.inr (by decide))
  have hsem : ∀ i, ispec (i.mapRegs (Backend.lowerFunction.resolve witnessAliases
      (witnessAliases.size + 1))) = ispec i := by
    intro i
    funext us w
    exact ispec_mapRegs (alias_renaming witnessAliases) us w i
  obtain ⟨ρ', hr, hfresh, hkeep⟩ := stock_alias_interval_prun
    (by rw [witness_alias_facts.1]; exact Nat.le_refl _) hdefs huses hsem hrun
  exact ⟨ρ', hr, (hfresh 194 (by decide) (by decide)).trans (upd_same _ _ _),
    hkeep 200 (Or.inr (by decide)), hkeep 192 (Or.inl (by decide)),
    witness_alias_facts.2.2⟩

end Backend.Stock.Proof
