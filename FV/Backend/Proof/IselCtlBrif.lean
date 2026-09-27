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

end Backend.Proof
