import FV.E2E.LinkOwnCallsStmt

/-!
# `CallStmtRunHyp`: a `call`/`call_indirect` statement's `lower` run

The no-call model of `LinkOwnCallsRun` with the run relation `CallRel` (no `tryCall`, only calls
of the statement) and the state invariant "fresh vregs from `N`": the rules of `lower` but
1031–1033 run in `callTab` (no call); 1031–1033 are checked by hand (`run_2508_rel`,
`run_2518_rel`, `run_2529_rel`). **`callStmtRunHyp : CallStmtRunHyp`.**
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 100000

/-- **The call-statement model**: the no-call model with the run relation `CallRel` of the
statement `inst` and the counter invariant `N ≤ nextVreg`. -/
def callModelS (ctx : Ctx) (hd : DataC ctx) (f : Clif.Function) (inst : Clif.Inst) (N : Nat) :
    UModel program (sem ctx) where
  P := fun _ v => vCIn v = false
  Is := fun s => N ≤ s.nextVreg
  Rs := fun s s' => s.nextVreg ≤ s'.nextVreg ∧ CallRel f inst N s s'
  T := (· ∈ callTab)
  C := callSite
  O := fun _ => False
  rs_refl := fun s => ⟨Nat.le_refl _, callRel_refl _ _ _ s⟩
  rs_trans := fun _ _ _ h1 h2 => ⟨Nat.le_trans h1.1 h2.1, callRel_trans h1.2 h2.2⟩
  mono := fun _ _ _ _ _ _ h => h
  int := fun _ _ _ _ => rfl
  bool := fun _ _ _ => rfl
  prim := fun s ty n c _ h => (callModel ctx hd).prim s ty n c trivial h
  mkd := fun s ty t term k vs hT hC ht hk _ hvs =>
    (callModel ctx hd).mkd s ty t term k vs hT hC ht hk trivial hvs
  un := fun s ty t term v k fs hT ht hk _ hv hu =>
    (callModel ctx hd).un s ty t term v k fs hT ht hk trivial hv hu
  ext := fun s t term flags c fn inf v fs hT ht hk _ hv h =>
    (callModel ctx hd).ext s t term flags c fn inf v fs hT ht hk trivial hv h
  ctor := fun s t term flags fn ex vs v s' hT ht hk hIs hvs h => by
    have hv := (Flow.externCtor_ok ctx term vs s v s' h).vreg
    exact ⟨externCtor_c ctx term vs s v s' h (vCInL_eq_false.mpr hvs), Nat.le_trans hIs hv, hv,
      callRel_of_noCall (ctor_noCall ctx hvs h)⟩
  oracle := fun _ h => h.elim
  closed := fun t ht _ rl hrl => callTab_closed t ht rl hrl

theorem lower_len : (program.rulesOf T.lower.id).length ≤ 1000 := by
  show (program.rulesOf 686).length ≤ 1000
  rw [data_program.r686]
  decide

/-- **A statement's `lower` run** emits no `tryCall` and only calls of that statement. -/
theorem stmt_callRel {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hd : DataC ctx)
    (ha : AbiSigsOk f) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hmem : ∃ B ∈ f.blocks, ∃ st ∈ B.body, st.inst = inst) {s : LState} {out : Option V}
    {s' : LState} {tr : List RuleId} (hN : ctx.valDef.size ≤ s.nextVreg)
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) :
    CallRel f inst ctx.valDef.size s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  let M := callModelS ctx hd f inst ctx.valDef.size
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      ((∀ u ∈ ruleTerms rl, M.T u) ∧ ∀ q ∈ ruleTys rl, M.C q.1 q.2) ∨
        (rl ∈ program.rulesOf TId.lower ∧ callExcl.contains rl.id = true) ∨
        ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠
          .ok (some env, s1) := by
    intro rl hrl
    cases hx : callExcl.contains rl.id with
    | true => exact .inr (.inl ⟨hrl, rfl⟩)
    | false =>
      have h := List.all_eq_true.mp callRootS_ok rl hrl
      rw [hx, Bool.false_or] at h
      exact .inl (callRuleOk_of h)
  have hhand : ∀ rl ∈ program.rulesOf T.lower.id,
      (rl ∈ program.rulesOf TId.lower ∧ callExcl.contains rl.id = true) →
      ∀ k m s tr env s1 tr1 r s2 tr2, 1000000 = k + 1 → m + 2 ≤ k →
        k ≤ m + 2 + (program.rulesOf T.lower.id).length → (∀ v ∈ [V.inst ii], M.P s v) → M.Is s →
        (matchRule program (sem ctx) {} m rl [.inst ii]).run (s, tr) = .ok (some env, (s1, tr1)) →
        (evalExpr program (sem ctx) {} k rl.rhs env).run (s1, tr1) = .ok (r, (s2, tr2)) →
        M.Is s2 ∧ M.Rs s s2 ∧ ∀ v, r = some v → True := by
    intro rl _ ⟨hrl, hx⟩ k m s tr env s1 tr1 r s2 tr2 hk hmk hkm _ hIs hm he
    have hlen := lower_len
    have hm1 : 1000 ≤ m := by omega
    have hk1 : 1000 ≤ k := by omega
    simp only [callExcl, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
      beq_iff_eq] at hx
    rcases hx with e | e | e
    · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2508 (by rw [e]; rfl)
      obtain ⟨out, rfl⟩ := Option.isSome_iff_exists.mp
        (Cov.totality.1 ctx {} k _ env (s1, tr1) r (s2, tr2) Cov.total_2508 he)
      obtain ⟨E, nm, L, D, he', hrc, h2⟩ := run_2508_rel data_program hctx ha hi hc rfl hm1 hk1 hIs hm he
      exact ⟨Nat.le_trans hIs h2, ⟨h2, callRel_emit E [] _ he' (fun _ h => by cases h) hrc⟩,
        fun _ _ => trivial⟩
    · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2518 (by rw [e]; rfl)
      obtain ⟨out, rfl⟩ := Option.isSome_iff_exists.mp
        (Cov.totality.1 ctx {} k _ env (s1, tr1) r (s2, tr2) Cov.total_2518 he)
      obtain ⟨E, nm, L, k, he', hrc, h2, -⟩ := run_2518_rel data_program hctx ha hi hc rfl hm1 hk1 hIs
        hm he
      exact ⟨Nat.le_trans hIs h2, ⟨h2, callRel_emit E _ _ he' (by simp [isCallB]) hrc⟩,
        fun _ _ => trivial⟩
    · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2529 (by rw [e]; rfl)
      obtain ⟨out, rfl⟩ := Option.isSome_iff_exists.mp
        (Cov.totality.1 ctx {} k _ env (s1, tr1) r (s2, tr2) Cov.total_2529 he)
      have hsigs : ∀ sig callee args s, inst = .callIndirect sig callee args →
          f.sigDecls.lookup sig = some s → sigAbiOk s = true := fun sig callee args s he hs =>
        (ha.2 s (Cov.mem_indSigs (he ▸ hmem) hs)).2
      obtain ⟨E, x, L, D, he', hrc, h2⟩ := run_2529_rel (N := ctx.valDef.size) data_program
        indData_program hctx hi hc hsigs rfl hm1 hk1 hm he
      exact ⟨Nat.le_trans hIs h2, ⟨h2, callRel_emit E [] _ he' (fun _ h => by cases h) hrc⟩,
        fun _ _ => trivial⟩
  exact (uRoot M rfl (fun _ _ => True)
    (fun rl => rl ∈ program.rulesOf TId.lower ∧ callExcl.contains rl.id = true) data_program.t686
    term_686_kind rfl hrules hhand
    (fun v hv => by simp only [List.mem_singleton] at hv; subst hv; rfl) hN happ).2.1.2

/-- **`CallStmtRunHyp`.** -/
theorem callStmtRunHyp : CallStmtRunHyp := by
  intro f ctx ranges st0 _ hs ha hb ii info inst s out s' tr hi hc _ hmem hN h
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  obtain ⟨ms, h1, h2, h3⟩ := stmt_callRel hctx (dataC_of_build hb) ha hi hc hmem hN h
  exact ⟨ms, h1, h2, h3⟩

end E2E.LinkCheck
