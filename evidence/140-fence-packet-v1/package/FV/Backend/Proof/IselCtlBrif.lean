import FV.Backend.Proof.IselCtlBranch
import FV.Backend.Proof.IselCmpRoot

/-!
# Family Ctl: `brif` (`lower_branch` rules 1132 `lower_brif`, 1137 `tbnz`, 1138 `tbz`)

The base rule branches on the `CondResult` of `is_nonzero_cmp` (family C's `CondCode`
contract) through `br_cond_result` (4 rules: `cbz`/`cbnz` on a register, `b.cond` after the
flag-setting instruction, and the generic `lower_cond_result_bool` fallback, which never fires
on a condition of E).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Extern helpers -/

section
variable {ctx : Ctx}

theorem ext_two_targets_iff (st : LState) (ls : List Label) (fs : List V) :
    externExtract ctx T.two_targets (.labels ls) st = .ok fs ↔
      ∃ a b, ls = [a, b] ∧ fs = [.label a, .label b] := by
  match ls with
  | [] =>
    have : externExtract ctx T.two_targets (.labels []) st = .fail := rfl
    rw [this]; simp
  | [a] =>
    have : externExtract ctx T.two_targets (.labels [a]) st = .fail := rfl
    rw [this]; simp
  | [a, b] =>
    have : externExtract ctx T.two_targets (.labels [a, b]) st = .ok [.label a, .label b] := rfl
    rw [this]
    simp only [ExtResult.ok.injEq]
    constructor
    · rintro rfl; exact ⟨a, b, rfl, rfl⟩
    · rintro ⟨a', b', h, rfl⟩
      simp only [List.cons.injEq, and_true] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | a :: b :: c :: ls =>
    have : externExtract ctx T.two_targets (.labels (a :: b :: c :: ls)) st = .fail := rfl
    rw [this]; simp

theorem ctor_cond_br_zero_iff (st : LState) (r s : V) (v : V) (st' : LState) :
    externCtor ctx T.cond_br_zero [r, s] st = .ok (v, st') ↔ v = .data 83 0 [r, s] ∧ st' = st := by
  have : externCtor ctx T.cond_br_zero [r, s] st = .ok (.data 83 0 [r, s], st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_cond_br_not_zero_iff (st : LState) (r s : V) (v : V) (st' : LState) :
    externCtor ctx T.cond_br_not_zero [r, s] st = .ok (v, st') ↔
      v = .data 83 1 [r, s] ∧ st' = st := by
  have : externCtor ctx T.cond_br_not_zero [r, s] st = .ok (.data 83 1 [r, s], st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_cond_br_cond_iff (st : LState) (c : V) (v : V) (st' : LState) :
    externCtor ctx T.cond_br_cond [c] st = .ok (v, st') ↔ v = .data 83 2 [c] ∧ st' = st := by
  have : externCtor ctx T.cond_br_cond [c] st = .ok (.data 83 2 [c], st) := rfl
  rw [this]; simp [eq_comm]

end

/-- `brif_inv [lemmas] at h₁ … hₙ`: `ctl_inv` plus this file's extern lemmas at every round. -/
syntax "brif_inv" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? " at " (ppSpace colGt ident)+ : tactic
macro_rules
  | `(tactic| brif_inv [$ts,*] at $hs*) => `(tactic| (
      ctl_inv [$ts,*, ext_two_targets_iff, ctor_branch_target_iff, ctor_cond_br_zero_iff, ctor_cond_br_not_zero_iff, ctor_cond_br_cond_iff] at $hs* <;>
      repeat (isel_inv_simp [ext_two_targets_iff, ctor_branch_target_iff, ctor_cond_br_zero_iff,
        ctor_cond_br_not_zero_iff, ctor_cond_br_cond_iff] at * <;> isel_destruct <;> subst_vars)))

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
theorem emit_side_effect_inst2_ok {n : Nat} (hn : 30 ≤ n) {i j : V} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 13 242 [.data 46 1 [i, j]] s v s') :
    ∃ m1 m2, s'.1 = (s.1.emit m1).emit m2 ∧ MInst.ofV i = some m1 ∧ MInst.ofV j = some m2 := by
  isel_split hp hc h 242
  · isel_inv [*, rule_prelude_lower_522] at hm
  · isel_inv [*, rule_prelude_lower_524] at hm he
    exact ⟨_, _, rfl, ‹_›, ‹_›⟩
  · isel_inv [*, rule_prelude_lower_527] at hm

include hp hc in
theorem a64_br_zero_ok {n : Nat} (hn : 30 ≤ n) {r sz a b : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 46 664 [r, sz, a, b] s v s') :
    s'.1 = s.1 ∧ v = .data 46 0 [.data 58 118 [a, b, .data 83 0 [r, sz]]] := by
  isel_split hp hc h 664
  brif_inv [*, rule_inst_5412] at hm he

include hp hc in
theorem a64_br_not_zero_ok {n : Nat} (hn : 30 ≤ n) {r sz a b : V} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 46 665 [r, sz, a, b] s v s') :
    s'.1 = s.1 ∧ v = .data 46 0 [.data 58 118 [a, b, .data 83 1 [r, sz]]] := by
  isel_split hp hc h 665
  brif_inv [*, rule_inst_5418] at hm he

include hp hc in
theorem a64_br_cond_ok {n : Nat} (hn : 30 ≤ n) {c a b : V} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 49 663 [c, a, b] s v s') :
    s'.1 = s.1 ∧ v = .data 49 0 [.data 58 118 [a, b, .data 83 2 [c]]] := by
  isel_split hp hc h 663
  brif_inv [*, rule_inst_5406] at hm he

set_option maxHeartbeats 2000000 in
include hp hc in
theorem with_flags_side_effect_ok {n : Nat} (hn : 40 ≤ n) {mi ci : V}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 46 256 [.data 47 1 [mi], .data 49 0 [ci]] s v s') :
    s'.1 = s.1 ∧ v = .data 46 1 [mi, ci] := by
  isel_split hp hc h 256
  all_goals brif_inv [*, rule_prelude_lower_1000, rule_prelude_lower_1006,
    rule_prelude_lower_1016, rule_prelude_lower_1023, rule_prelude_lower_1030,
    rule_prelude_lower_1035, rule_prelude_lower_1040, rule_prelude_lower_1045,
    rule_prelude_lower_1050] at hm he


/-- The branch `br_cond_result` builds for a condition of E. -/
def brCondV (c : V) (a b : Label) : V :=
  match c with
  | .data 123 0 [r, sz] => .data 46 0 [.data 58 118 [.label a, .label b, .data 83 0 [r, sz]]]
  | .data 123 1 [r, sz] => .data 46 0 [.data 58 118 [.label a, .label b, .data 83 1 [r, sz]]]
  | .data 123 2 [.data 47 1 [mi], cc] => .data 46 1 [mi, .data 58 118 [.label a, .label b, .data 83 2 [cc]]]
  | _ => .op .unit

set_option maxHeartbeats 4000000 in
include hp hc in
theorem br_cond_result_ok {n : Nat} (hn : 100 ≤ n) {c : V} {P : Nat → Prop} (hsh : CondShape c P)
    {a b : Label} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 46 722 [c, .label a, .label b] s v s') :
    s'.1 = s.1 ∧ v = brCondV c a b := by
  have kZ := fun n (hn : 30 ≤ n) r sz a b s v s' h => a64_br_zero_ok hp (ctx := ctx) hc (n := n)
    (r := r) (sz := sz) (a := a) (b := b) (s := s) (v := v) (s' := s') hn h
  have kN := fun n (hn : 30 ≤ n) r sz a b s v s' h => a64_br_not_zero_ok hp (ctx := ctx) hc (n := n)
    (r := r) (sz := sz) (a := a) (b := b) (s := s) (v := v) (s' := s') hn h
  have kC := fun n (hn : 30 ≤ n) c a b s v s' h => a64_br_cond_ok hp (ctx := ctx) hc (n := n)
    (c := c) (a := a) (b := b) (s := s) (v := v) (s' := s') hn h
  have kW := fun n (hn : 40 ≤ n) mi ci s v s' h => with_flags_side_effect_ok hp (ctx := ctx) hc
    (n := n) (mi := mi) (ci := ci) (s := s) (v := v) (s' := s') hn h
  rcases hsh with ⟨k, i, sz, rfl, -, -⟩ | ⟨k, i, sz, rfl, -, -⟩ | ⟨mi, m, cond, rfl, -⟩
  · isel_split hp hc h 722
    · brif_inv [*, rule_lower_3236] at hm he
      have h664 := ‹ApplyInternal _ _ _ _ 46 664 _ _ _ _›
      obtain ⟨hs, rfl⟩ := kZ _ (by omega) _ _ _ _ _ _ _ h664
      exact ⟨hs, rfl⟩
    · brif_inv [*, rule_lower_3238] at hm
    · brif_inv [*, rule_lower_3240] at hm
    · obtain ⟨k', s2, h2⟩ := hpre _ (List.mem_cons_self ..)
      revert h2
      isel_eval [*, rule_lower_3236, sem_eq]
      simp
  · isel_split hp hc h 722
    · brif_inv [*, rule_lower_3236] at hm
    · brif_inv [*, rule_lower_3238] at hm he
      have h665 := ‹ApplyInternal _ _ _ _ 46 665 _ _ _ _›
      obtain ⟨hs, rfl⟩ := kN _ (by omega) _ _ _ _ _ _ _ h665
      exact ⟨hs, rfl⟩
    · brif_inv [*, rule_lower_3240] at hm
    · obtain ⟨k', s2, h2⟩ := hpre _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      revert h2
      isel_eval [*, rule_lower_3238, sem_eq]
      simp
  · isel_split hp hc h 722
    · brif_inv [*, rule_lower_3236] at hm
    · brif_inv [*, rule_lower_3238] at hm
    · brif_inv [*, rule_lower_3240] at hm he
      have h663 := ‹ApplyInternal _ _ _ _ 49 663 _ _ _ _›
      obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ _ _ h663
      have h256 := ‹ApplyInternal _ _ _ _ 46 256 _ _ _ _›
      obtain ⟨hs2, rfl⟩ := kW _ (by omega) _ _ _ _ _ h256
      exact ⟨hs2.trans hs1, rfl⟩
    · obtain ⟨k', s2, h2⟩ := hpre _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      revert h2
      isel_eval [*, rule_lower_3240, sem_eq]
      simp

end

/-! ## Semantics of the emitted branch -/

theorem vdefs_condBr (a b : Label) (k : CondBrKind) (ops : Array Operand)
    (hops : (MInst.condBr a b k).operands = .ok ops) (hu : ∀ o ∈ ops.toList, o.kind = .use) :
    vdefs (.condBr a b k) = [] := by
  simp only [vdefs, hops]
  simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro o ho
  simp [Operand.isDef, hu o ho]

/-- **Generic `brif` lowering**: a prefix `ms0` that falls through (from `st` to `st2`), then a
conditional branch whose condition, after the prefix, is the truth of the tested value. -/
theorem brif_termOk_gen {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} (hR : Refines F isem)
    (hMR : MRStable F MR) {ctx : Ctx} {st st2 : LState} {ms0 : List MInst} (hf : Frag st st2 ms0)
    {k : CondBrKind} {a b : Label} {ops : Array Operand}
    (hops : (MInst.condBr a b k).operands = .ok ops) (hu : ∀ o ∈ ops.toList, o.kind = .use)
    {x : Nat} {t e : Clif.BlockCall}
    (hsem : ∀ (fr : Clif.Frame) (ρ : Nat → CV) (bb : Bool), ValsHeld fr ρ → DFGCons ctx fr →
      (∃ v, fr.regs x = some v ∧ bb = Clif.Sem.truthy v.bits) →
      UsesLo st.nextVreg fr (ms0 ++ [.condBr a b k]) ∧ ∀ w, ∃ ρ1 w1,
        seqRun isem ms0 ρ w = some (.fall ρ1 w1) ∧ SameWorldNF F w1 w ∧
          condBrHolds k (vuses ops ρ1) w1 = bb) :
    LowerTermOk isem MR ctx (.brif x t e) [a, b] st (st2.emit (.condBr a b k))
      (ms0 ++ [.condBr a b k]) := by
  have hd := vdefs_condBr a b k ops hops hu
  have hf2 := hf.append (Frag.emit_nodef st2 hd)
  refine ⟨hf2.mono, hf2.defs, ?_⟩
  intro fr cm ρ w _ hvh hdfg hmr
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · rw [List.getLast?_append] at hi
    simp at hi
    subst hi
    rfl
  · simp only [branchIdx] at hj
    cases hx : fr.get x with
    | ok v =>
      rw [hx] at hj
      simp only [Clif.Res.bind] at hj
      cases hj
      have hreg : fr.regs x = some v := by
        simp only [Clif.Frame.get, Clif.Res.ofOption] at hx
        split at hx <;> simp_all
      obtain ⟨hus, hrun⟩ := hsem fr ρ _ hvh hdfg ⟨v, hreg, rfl⟩
      obtain ⟨ρ1, w1, h1, hw1, hb⟩ := hrun w
      have hs : ispec (.condBr a b k) (vuses ops ρ1) w1 =
          some ([], w1, .goto (if Clif.Sem.truthy v.bits then 0 else 1)) := by
        simp only [ispec, hb]
      obtain ⟨w2, h2, hw2⟩ := seqRun_one_stop hR hops (ρ := ρ1) (by simp) hs (by
        have : ops.toList.filter Operand.isDef = [] := by
          rw [List.filter_eq_nil_iff]; intro o ho; simp [Operand.isDef, hu o ho]
        simp [this])
      refine ⟨hus, _, _, _, _, _, _, _, seqRun_append_fall_stop isem h1 h2, by simp, ?_⟩
      exact hMR _ _ _ _ ((SameWorld.nf hw2).trans hw1) hmr
    | trap c => rw [hx] at hj; simp [Clif.Res.bind] at hj
    | stuck m => rw [hx] at hj; simp [Clif.Res.bind] at hj


theorem ofV_condBr_zero {i : Nat} {sz : OperandSize} (hi : OperandSize.ofIdx? i = some sz)
    (a b : Label) (r : Reg) :
    MInst.ofV (.data 58 118 [.label a, .label b, .data 83 0 [.reg r, .data 93 i []]]) =
      some (.condBr a b (.zero r sz)) := by
  rcases i with _ | _ | i <;> simp [OperandSize.ofIdx?] at hi <;> subst hi <;> rfl

theorem ofV_condBr_notZero {i : Nat} {sz : OperandSize} (hi : OperandSize.ofIdx? i = some sz)
    (a b : Label) (r : Reg) :
    MInst.ofV (.data 58 118 [.label a, .label b, .data 83 1 [.reg r, .data 93 i []]]) =
      some (.condBr a b (.notZero r sz)) := by
  rcases i with _ | _ | i <;> simp [OperandSize.ofIdx?] at hi <;> subst hi <;> rfl

theorem ofV_condBr_cond (a b : Label) (c : Cond) :
    MInst.ofV (.data 58 118 [.label a, .label b, .data 83 2 [.data 96 c.idx []]]) =
      some (.condBr a b (.cond c)) := by
  cases c <;> rfl

theorem operands_condBr_zero (a b : Label) (k : Nat) (sz : OperandSize) :
    (MInst.condBr a b (.zero (.vreg k .int) sz)).operands = .ok #[⟨k, .int, .use, .early, .reg⟩] :=
  rfl

theorem operands_condBr_notZero (a b : Label) (k : Nat) (sz : OperandSize) :
    (MInst.condBr a b (.notZero (.vreg k .int) sz)).operands =
      .ok #[⟨k, .int, .use, .early, .reg⟩] := rfl

theorem operands_condBr_cond (a b : Label) (c : Cond) :
    (MInst.condBr a b (.cond c)).operands = .ok #[] := rfl

theorem condBrHolds_zero (r : Reg) (sz : OperandSize) (x : CV) (w : Arm.ArmState) :
    condBrHolds (.zero r sz) [x] w = (opnd sz x == 0) := by
  cases sz <;> rfl

theorem condBrHolds_notZero (r : Reg) (sz : OperandSize) (x : CV) (w : Arm.ArmState) :
    condBrHolds (.notZero r sz) [x] w = (opnd sz x != 0) := by
  cases sz <;> rfl

theorem condShape_zero_P {k i : Nat} {P : Nat → Prop}
    (h : CondShape (.data 123 0 [.reg (.vreg k .int), .data 93 i []]) P) : P k := by
  rcases h with ⟨k', i', sz', h1, -, h3⟩ | ⟨_, _, _, h1, -⟩ | ⟨_, _, _, h1, -⟩
  · simp only [V.data.injEq, List.cons.injEq, V.reg.injEq, Reg.vreg.injEq, and_true, true_and] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact h3
  all_goals simp at h1

theorem condShape_notZero_P {k i : Nat} {P : Nat → Prop}
    (h : CondShape (.data 123 1 [.reg (.vreg k .int), .data 93 i []]) P) : P k := by
  rcases h with ⟨_, _, _, h1, -⟩ | ⟨k', i', sz', h1, -, h3⟩ | ⟨_, _, _, h1, -⟩
  · simp at h1
  · simp only [V.data.injEq, List.cons.injEq, V.reg.injEq, Reg.vreg.injEq, and_true, true_and] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact h3
  · simp at h1

theorem condShape_cond_P {mi : V} {m : MInst} {c : Cond} {P : Nat → Prop}
    (hm : MInst.ofV mi = some m) (h : CondShape (.data 123 2 [.data 47 1 [mi], .data 96 c.idx []]) P) :
    ∀ u ∈ vuseNums m, P u := by
  rcases h with ⟨_, _, _, h1, -⟩ | ⟨_, _, _, h1, -⟩ | ⟨mi', m', c', h1, h2, -, -, -, h6⟩
  · simp at h1
  · simp at h1
  · simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at h1
    obtain ⟨rfl, -⟩ := h1
    rw [hm] at h2; cases h2
    exact h6

theorem condSem_zero {ρ : Nat → CV} {k i : Nat} {sz : OperandSize} {b : Bool}
    (hi : OperandSize.ofIdx? i = some sz)
    (h : CondSem ρ (.data 123 0 [.reg (.vreg k .int), .data 93 i []]) b) : (opnd sz (ρ k) == 0) = b := by
  rcases h with ⟨k', i', sz', h1, h2, h3⟩ | ⟨_, _, _, h1, -⟩ | ⟨_, _, _, _, h1, -⟩
  · simp only [V.data.injEq, List.cons.injEq, V.reg.injEq, Reg.vreg.injEq, and_true, true_and] at h1
    obtain ⟨rfl, rfl⟩ := h1
    rw [hi] at h2; cases h2; exact h3
  all_goals simp at h1

theorem condSem_notZero {ρ : Nat → CV} {k i : Nat} {sz : OperandSize} {b : Bool}
    (hi : OperandSize.ofIdx? i = some sz)
    (h : CondSem ρ (.data 123 1 [.reg (.vreg k .int), .data 93 i []]) b) : (opnd sz (ρ k) != 0) = b := by
  rcases h with ⟨_, _, _, h1, -⟩ | ⟨k', i', sz', h1, h2, h3⟩ | ⟨_, _, _, _, h1, -⟩
  · simp at h1
  · simp only [V.data.injEq, List.cons.injEq, V.reg.injEq, Reg.vreg.injEq, and_true, true_and] at h1
    obtain ⟨rfl, rfl⟩ := h1
    rw [hi] at h2; cases h2; exact h3
  · simp at h1

theorem condSem_cond {ρ : Nat → CV} {mi : V} {m : MInst} {c : Cond} {b : Bool}
    (hm : MInst.ofV mi = some m)
    (h : CondSem ρ (.data 123 2 [.data 47 1 [mi], .data 96 c.idx []]) b) :
    ∃ ps, SetsFlags m ρ ps ∧ condOn c.bits ps = b := by
  rcases h with ⟨_, _, _, h1, -⟩ | ⟨_, _, _, h1, -⟩ | ⟨mi', m', c', ps, h1, h2, h3, h4⟩
  · simp at h1
  · simp at h1
  · simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at h1
    obtain ⟨rfl, hc⟩ := h1
    rw [hm] at h2; cases h2
    have : c = c' := by
      have := congrArg Cond.ofIdx? hc
      rwa [cond_ofIdx_idx, cond_ofIdx_idx, Option.some.injEq] at this
    subst this
    exact ⟨ps, h3, h4⟩


set_option maxHeartbeats 4000000 in
/-- **`lower_brif`** (`rule_lower_3231`, rule id 1132). -/
theorem brif_ruleOk {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    (hR : Refines F isem) (hMR : MRStable F MR) : BranchRuleOk isem MR p rule_lower_3231 := by
  intro f ctx hctx ti t data targets hd hi _ _ cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kE2 := fun n (hn : 30 ≤ n) i j s v s' h => emit_side_effect_inst2_ok hp (ctx := ctx) hc
    (n := n) (i := i) (j := j) (s := s) (v := v) (s' := s') hn h
  have kB := fun n (hn : 100 ≤ n) c P (hsh : CondShape c P) a b s v s' h =>
    br_cond_result_ok hp (ctx := ctx) hc (n := n) (c := c) (P := P) (a := a) (b := b) (s := s)
      (v := v) (s' := s') hn hsh h
  have kNZ := fun n (hn : 300 ≤ n) x s c s' hvb h => is_nonzero_cmp_ok hp hc (F := F) hR hctx
    (n := n) hn (x := x) (s := s) (c := c) (s' := s') hvb h
  have hf := ruleFmt_term hp (r := rule_lower_3231) rfl hp.t2452 term_2452_kind hd hi hmatch
  cases t with
  | brif x tb eb =>
    rw [termData_brif] at hd; cases hd
    cases hp
    brif_inv [*, rule_lower_3231] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hdat := ‹V.data 152 5 _ = _›
    simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
    obtain ⟨rfl, rfl⟩ := hdat
    have h650 := ‹ApplyInternal _ _ _ _ 123 650 _ _ _ _›
    obtain ⟨ms0, hfr, hsh, hsem⟩ := kNZ _ (by omega) _ _ _ _ hvb h650
    have h722 := ‹ApplyInternal _ _ _ _ 46 722 _ _ _ _›
    obtain ⟨hs2, rfl⟩ := kB _ (by omega) _ _ hsh _ _ _ _ _ h722
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    rcases hsh with ⟨k, i, sz, rfl, hsz, -⟩ | ⟨k, i, sz, rfl, hsz, -⟩ |
      ⟨mi, mm, cond, rfl, hmi, -, -, hdm, -⟩
    · obtain ⟨mi', hmi', hs3, -⟩ := kE _ (by omega) _ _ _ _ h242
      rw [ofV_condBr_zero hsz] at hmi'
      cases hmi'
      simp only at hs2 hs3
      rw [hs3, hs2]
      refine ⟨ms0 ++ [_], ?emit, brif_termOk_gen hR hMR hfr (operands_condBr_zero _ _ k sz) (by simp)
        fun fr ρ bb hvh hdfg hT => ?_⟩
      case emit => simp [LState.emit, hfr.emitted]
      obtain ⟨hus, hsh', hrun⟩ := hsem fr ρ bb hvh hdfg hT
      refine ⟨UsesLo.append hus ?_, fun w => ?_⟩
      · intro mm hmm u hu
        simp only [List.mem_singleton] at hmm
        subst hmm
        have hu' : u = k := by
          simp only [vuseNums, operands_condBr_zero] at hu
          simpa [Operand.isUse] using hu
        subst hu'
        exact condShape_zero_P hsh'
      · obtain ⟨ρ1, w1, h1, hw1, hcs⟩ := hrun w
        exact ⟨ρ1, w1, h1, hw1, by
          rw [show vuses #[(⟨k, .int, .use, .early, .reg⟩ : Operand)] ρ1 = [ρ1 k] from rfl,
            condBrHolds_zero]
          exact condSem_zero hsz hcs⟩
    · obtain ⟨mi', hmi', hs3, -⟩ := kE _ (by omega) _ _ _ _ h242
      rw [ofV_condBr_notZero hsz] at hmi'
      cases hmi'
      simp only at hs2 hs3
      rw [hs3, hs2]
      refine ⟨ms0 ++ [_], ?emit, brif_termOk_gen hR hMR hfr (operands_condBr_notZero _ _ k sz) (by simp)
        fun fr ρ bb hvh hdfg hT => ?_⟩
      case emit => simp [LState.emit, hfr.emitted]
      obtain ⟨hus, hsh', hrun⟩ := hsem fr ρ bb hvh hdfg hT
      refine ⟨UsesLo.append hus ?_, fun w => ?_⟩
      · intro mm hmm u hu
        simp only [List.mem_singleton] at hmm
        subst hmm
        have hu' : u = k := by
          simp only [vuseNums, operands_condBr_notZero] at hu
          simpa [Operand.isUse] using hu
        subst hu'
        exact condShape_notZero_P hsh'
      · obtain ⟨ρ1, w1, h1, hw1, hcs⟩ := hrun w
        exact ⟨ρ1, w1, h1, hw1, by
          rw [show vuses #[(⟨k, .int, .use, .early, .reg⟩ : Operand)] ρ1 = [ρ1 k] from rfl,
            condBrHolds_notZero]
          exact condSem_notZero hsz hcs⟩
    · obtain ⟨m1, m2, hs3, hm1, hm2⟩ := kE2 _ (by omega) _ _ _ _ _ h242
      rw [hmi] at hm1
      cases hm1
      rw [ofV_condBr_cond] at hm2
      cases hm2
      simp only at hs2 hs3
      rw [hs3, hs2]
      have hf1 := hfr.append (Frag.emit_nodef _ hdm)
      refine ⟨(ms0 ++ [mm]) ++ [_], ?emit, brif_termOk_gen hR hMR hf1 (operands_condBr_cond _ _ cond) (by simp)
        fun fr ρ bb hvh hdfg hT => ?_⟩
      case emit => simp [LState.emit, hfr.emitted]
      obtain ⟨hus, hsh', hrun⟩ := hsem fr ρ bb hvh hdfg hT
      refine ⟨UsesLo.append (UsesLo.append hus ?_) ?_, fun w => ?_⟩
      · intro m' hm' u hu
        simp only [List.mem_singleton] at hm'
        subst hm'
        exact condShape_cond_P hmi hsh' u hu
      · intro m' hm' u hu
        simp only [List.mem_singleton] at hm'
        subst hm'
        simp [vuseNums, operands_condBr_cond] at hu
      · obtain ⟨ρ1, w1, h1, hw1, hcs⟩ := hrun w
        obtain ⟨ps, hps, hb⟩ := condSem_cond hmi hcs
        obtain ⟨ρ2, w2, h2, hw2, -, hcond⟩ := Runs.flags hR hps w1
        exact ⟨ρ2, w2, seqRun_append_fall' isem h1 h2, hw2.trans hw1, by
          simp only [condBrHolds]
          rw [hcond, hb]⟩
  | _ => simp [termFmt] at hf


end Backend.Proof
