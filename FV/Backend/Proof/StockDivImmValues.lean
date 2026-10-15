import FV.Backend.Proof.StockDivLcf
import FV.Backend.Proof.StockDivImmFrame
import FV.Backend.Proof.IselTermsImm
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
section Contract
variable {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
theorem stock_div_imm_case_lcf32 (hR : Refines F isem) {w e : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32) (i : Int)
    (st : LState) :
    ImmOut F isem w e (u64 i) st (loadConstantFull w (e == 0) .size32 (u64 i) st).2
      (.reg (loadConstantFull w (e == 0) .size32 (u64 i) st).1) := by
  obtain ⟨ms, d, hd, hsh, hrun⟩ := stock_div_lcf_run (F := F) hR w (e == 0) .size32 (u64 i) st
  refine ⟨ms, d, by rw [hd], hsh, fun ρ => ?_⟩
  obtain ⟨ρ', hp', hv⟩ := hrun ρ
  refine ⟨ρ', _, hp', hv, lcfValue32_mod hw _ (u64_lt' i), fun _ => ?_⟩
  simp only [immVal, szOf, show w ≤ 32 by omega, ↓reduceIte]

theorem stock_div_imm_case_lcf64 (hR : Refines F isem) {e : Nat} (i : Int) (st : LState) :
    ImmOut F isem 64 e (u64 i) st (loadConstantFull 64 (e == 0) .size64 (u64 i) st).2
      (.reg (loadConstantFull 64 (e == 0) .size64 (u64 i) st).1) := by
  obtain ⟨ms, d, hd, hsh, hrun⟩ := stock_div_lcf_run (F := F) hR 64 (e == 0) .size64 (u64 i) st
  refine ⟨ms, d, by rw [hd], hsh, fun ρ => ?_⟩
  obtain ⟨ρ', hp', hv⟩ := hrun ρ
  exact ⟨ρ', _, hp', hv, by rw [lcfValue64 _ (u64_lt' i)], fun _ => rfl⟩

include hp hc in
/-- **Contract of `imm`** (all five rules), at `i8..i64`, both extensions. -/
theorem stock_div_imm_legacy_ok (hR : Refines F isem) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {e : Nat}
    (he : e = 0 ∨ e = 1) {i : Int} {st : LState} {tr : Array RuleId} {n : Nat} {v : V}
    {s' : LState × Array RuleId}
    (h : (applyTerm p (Backend.sem ctx) cfg (n + 40) 27 553 (immArgs w e i)).run (st, tr) =
      .ok (some v, s')) :
    ImmOut F isem w e (u64 i) st s'.1 v := by
  obtain ⟨r, hr, m, env, s1, st2, tr2, hm, hmatch, heval, rfl⟩ :=
    applyTerm_internal_some (n := n + 39) hc hp.t553 term_553_kind rfl h
  rw [hp.r553] at hr hm
  simp only [R.imm, List.length_cons, List.length_nil] at hm
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  simp only [R.imm, List.mem_cons, List.mem_nil_iff, or_false] at hr
  have hwb : w ≤ 64 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · -- movz
    rcases he with rfl | rfl
    · rw [match_3742_none hp ctx st tr m' hw (.inl rfl)] at hmatch; cases hmatch
    cases hmw : MoveWideConst.ofNat? (mwcArg w i) with
    | none => rw [match_3742_none hp ctx st tr m' hw (.inr ⟨rfl, hmw⟩)] at hmatch; cases hmatch
    | some mw =>
      rw [match_3742 hp ctx st tr m' hw hmw] at hmatch
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
      obtain ⟨rfl, rfl⟩ := hmatch
      obtain ⟨tr', hr⟩ := rhs_3742 hp ctx hc st tr (n + 9) hwb (i := i) (mw := mw)
      rw [hr] at heval
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
      obtain ⟨rfl, rfl, rfl⟩ := heval
      exact imm_case_movz hR hw hmw st
  · -- movn
    rcases he with rfl | rfl
    · rw [match_3745_none hp ctx st tr m' hw (.inl rfl)] at hmatch; cases hmatch
    by_cases hn : w = 32 ∨ w = 64
    · cases hmw : MoveWideConst.ofNat? (mwciArg w i) with
      | none =>
        rw [match_3745_none hp ctx st tr m' hw (.inr (.inr ⟨rfl, hmw⟩))] at hmatch; cases hmatch
      | some mw =>
        rw [match_3745 hp ctx st tr m' hn hmw] at hmatch
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
        obtain ⟨rfl, rfl⟩ := hmatch
        obtain ⟨tr', hr⟩ := rhs_3745 hp ctx hc st tr (n + 9) hn (i := i) (mw := mw)
        rw [hr] at heval
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
        obtain ⟨rfl, rfl, rfl⟩ := heval
        exact imm_case_movn hR hn hmw st
    · rw [match_3745_none hp ctx st tr m' hw (.inr (.inl (by omega)))] at hmatch; cases hmatch
  · -- orr
    rcases he with rfl | rfl
    · rw [match_3751_none hp ctx st tr m' hw (.inl rfl) (.inl rfl)] at hmatch; cases hmatch
    by_cases hn : w = 32 ∨ w = 64
    · cases hil : ImmLogic.ofNat? (u64 i) (szOf w) with
      | none =>
        rw [match_3751_none hp ctx st tr m' hw (.inr rfl) (.inr (.inr ⟨rfl, hil⟩))] at hmatch
        cases hmatch
      | some il =>
        rw [match_3751 hp ctx st tr m' hn hil] at hmatch
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
        obtain ⟨rfl, rfl⟩ := hmatch
        obtain ⟨tr', hr⟩ := rhs_3751 hp ctx hc st tr (n + 9) hn (i := i) (il := il) (.int w)
        rw [hr] at heval
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
        obtain ⟨rfl, rfl, rfl⟩ := heval
        have hilv := immLogic_value hil
        subst hilv
        exact imm_case_orr hR hn hil st
    · rw [match_3751_none hp ctx st tr m' hw (.inr rfl) (.inr (.inl (by omega)))] at hmatch
      cases hmatch
  · -- load_constant_full at ≤ 32 bits
    by_cases h64 : w = 64
    · subst h64
      rw [match_3786_none hp ctx st tr m'] at hmatch; cases hmatch
    have hw' : w = 8 ∨ w = 16 ∨ w = 32 := by omega
    rw [match_3786 hp ctx st tr m' hw'] at hmatch
    simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
    obtain ⟨rfl, rfl⟩ := hmatch
    obtain ⟨tr', hr⟩ := rhs_3786 hp ctx hc st tr (n + 9) (w := w) (e := e) (i := i)
    rw [hr] at heval
    simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
    obtain ⟨rfl, rfl, rfl⟩ := heval
    exact stock_div_imm_case_lcf32 hR hw' i st
  · -- load_constant_full at 64 bits
    by_cases h64 : w = 64
    · subst h64
      rw [match_3790 hp ctx st tr m'] at hmatch
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
      obtain ⟨rfl, rfl⟩ := hmatch
      obtain ⟨tr', hr⟩ := rhs_3790 hp ctx hc st tr (n + 9) (e := e) (i := i)
      rw [hr] at heval
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
      obtain ⟨rfl, rfl, rfl⟩ := heval
      exact stock_div_imm_case_lcf64 hR i st
    · rw [match_3790_none hp ctx st tr m' (w := w) (by omega)] at hmatch; cases hmatch

end Contract
/-- Actual Stock immediate materialization establishes original machine values
and fragment/result allocation for every immediate rule, with standard-only
MOVK/constant-loop arithmetic. Old theorem variants and trust sets are retained. -/
theorem stock_div_imm_values {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {w e : Nat}
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (extension : e = 0 ∨ e = 1)
    {i : Int} {st next : State} {tr trace : Array RuleId} {n : Nat} {out : V}
    (run : (applyTerm p (Stock.sem ctx) cfg (n+40) 27 553 (immArgs w e i)).run (st,tr) =
      .ok (some out,next,trace)) :
    next = {st with base := next.base} ∧ ImmOut F isem w e (u64 i) st.base next.base out := by
  have projected := stock_imm_projects hp ctx cfg hc (n+40) (immArgs w e i) st tr
  rw [run] at projected
  simp only [projectResult] at projected
  have values := stock_div_imm_legacy_ok hp ctx hc refines width extension projected.symm
  have frame := (stock_div_imm_observed hp ctx hc (n := n+39) run).1
  exact ⟨frame,values⟩
end Backend.Stock.Proof.ScalarDiv
