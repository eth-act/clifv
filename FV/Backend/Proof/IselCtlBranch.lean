import FV.Backend.Proof.IselCtlUnmatch

/-!
# Family Ctl: the `lower_branch` rules

`BranchRuleOk` for the closure root rules of `lower_branch`: `jump` (rule id 1139), and (see
the per-rule status in `docs/contracts/backend-proof.md`, "Family Ctl") the `brif` and
`br_table` rules.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Extern helpers -/

section
variable {ctx : Ctx}

theorem ext_single_target_iff (st : LState) (ls : List Label) (fs : List V) :
    externExtract ctx T.single_target (.labels ls) st = .ok fs ↔ ∃ l, ls = [l] ∧ fs = [.label l] := by
  match ls with
  | [] =>
    have : externExtract ctx T.single_target (.labels []) st = .fail := rfl
    rw [this]; simp
  | [l] =>
    have : externExtract ctx T.single_target (.labels [l]) st = .ok [.label l] := rfl
    rw [this]; simp [eq_comm]
  | a :: b :: ls =>
    have : externExtract ctx T.single_target (.labels (a :: b :: ls)) st = .fail := rfl
    rw [this]; simp

theorem ctor_branch_target_iff (st : LState) (l : Label) (v : V) (st' : LState) :
    externCtor ctx T.branch_target [.label l] st = .ok (v, st') ↔ v = .label l ∧ st' = st := by
  have : externCtor ctx T.branch_target [.label l] st = .ok (.label l, st) := rfl
  rw [this]; simp [eq_comm]

end

/-! ## `jump` -/

theorem ofV_jump (l : Label) : MInst.ofV (.data 58 117 [.label l]) = some (.jump l) := rfl

theorem operands_jump (l : Label) : (MInst.jump l).operands = .ok #[] := rfl

theorem ispec_jump (l : Label) (w : Arm.ArmState) : ispec (.jump l) [] w = some ([], w, .goto 0) :=
  rfl

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
theorem aarch64_jump_ok {n : Nat} (hn : 30 ≤ n) {t : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 46 661 [t] s v s') :
    s'.1 = s.1 ∧ v = .data 46 0 [.data 58 117 [t]] := by
  isel_split hp hc h 661
  isel_inv [*, rule_inst_5371] at hm he

end

/-- The meaning of `jump l`: goes to successor 0 (the jump's target). -/
theorem jump_termOk {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} (hR : Refines F isem)
    (hMR : MRStable F MR) {ctx : Ctx} {d : Clif.BlockCall} {l : Label} {st : LState} :
    LowerTermOk isem MR ctx (.jump d) [l] st (st.emit (.jump l)) [.jump l] := by
  refine ⟨by simp [LState.emit], by simp [vdefs, operands_jump], ?_⟩
  intro fr cm ρ w _ _ _ hmr
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · simp at hi; subst hi; rfl
  · simp [branchIdx] at hj
    subst hj
    obtain ⟨w'', hrun, hsw⟩ := seqRun_one_stop hR (operands_jump l) (ρ := ρ) (w := w)
      (ctl := .goto 0) (by simp) (ispec_jump l w) rfl
    exact ⟨by simp [UsesOk, vuseNums, operands_jump], 0, _, _, _, _, _, _, hrun, rfl,
      hMR _ _ _ _ (SameWorld.nf hsw) hmr⟩

/-- **`jump`** (`rule_lower_3270`, rule id 1139). -/
theorem jump_ruleOk {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    (hR : Refines F isem) (hMR : MRStable F MR) : BranchRuleOk isem MR p rule_lower_3270 := by
  intro f ctx hctx ti t data targets hd hi cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kJ := fun n (hn : 30 ≤ n) t s v s' h => aarch64_jump_ok hp (ctx := ctx) hc (n := n) (t := t)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have hf := ruleFmt_term hp (r := rule_lower_3270) rfl hp.t2462 term_2462_kind hd hi hmatch
  cases t with
  | jump d =>
    rw [termData_jump] at hd; cases hd
    cases hp
    isel_inv [*, rule_lower_3270, ext_single_target_iff, ctor_branch_target_iff] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    repeat (isel_inv_simp [ext_single_target_iff, ctor_branch_target_iff] at * <;> isel_destruct <;>
      subst_vars)
    have h661 := ‹ApplyInternal _ _ _ _ 46 661 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kJ _ (by omega) _ _ _ _ h661
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
    rw [ofV_jump] at hmi
    cases hmi
    simp only at hs1 hs2
    subst hs2
    rw [hs1]
    exact ⟨_, by simp [LState.emit], jump_termOk hR hMR⟩
  | _ => simp [termFmt] at hf

end Backend.Proof
