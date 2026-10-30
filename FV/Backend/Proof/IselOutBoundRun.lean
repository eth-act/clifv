import FV.Backend.Proof.RegallocOperands
import FV.E2E.RegLevelPush
import FV.Backend.Proof.KillTermIds
import FV.Backend.Proof.KillGen
import FV.E2E.LinkOwnCallsStmtHyp
import FV.E2E.LinkOwnCallsTryHyp
import FV.Backend.Proof.IselOutBoundExt
import FV.Backend.Proof.IselOutBoundCall
import FV.Backend.Proof.IselOutBoundTry
import FV.Backend.Proof.LowerComplete
import FV.Backend.Proof.IselOutBoundDefs

/-!
# An upper bound of the outgoing area from the call signatures (S10g, #404)

**`lowerFunction_outgoing_le`**: on `LowerScope` input with `outBoundLe Bd`
(`IselOutBoundDefs`), the outgoing area of `lowerFunction`'s VCode is at most `Bd`.

The proof: only `gen_call_info`/`gen_call_ind_info` change the outgoing area
(`externCtor_out`); they are not in `callTab` (one kernel decision over the certified term set),
the closure of the terms of every rule of `lower` but the `call` rules 1031–1033 and of the
closure-root rules of `lower_branch` (`callTab_closed`, `LinkOwnCallsRun`). So every run in
`callTab` keeps the outgoing area at most `max outgoing Bd` (the uniform invariant `outModel`),
the `call` rules raise it to the callee's stack arguments exactly (`call_bl_outEq`,
`call_got_outEq`, `call_ind_outEq`), and so do the `try_call` rules 1034–1036, the only rules
matching a `try_call` (`try_bl_outEq`, `try_got_outEq`, `try_ind_outEq`). `lowBlocks_bnd`
carries the bound through the recorded lowering.
-/

namespace Backend.Proof.OutBound

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
  E2E.LinkCheck

set_option maxRecDepth 100000

/-! ## The input condition, per call -/

theorem outBoundLe_call {Bd : Nat} {f : Clif.Function} (h : outBoundLe Bd f = true)
    {B : Clif.Block} (hB : B ∈ f.blocks) {st : Clif.Stmt} (hst : st ∈ B.body) :
    ∀ fn args e, st.inst = .call fn args → f.extern? fn = some e → stackBytes e.sig ≤ Bd := by
  intro fn args e hi he
  have h0 := List.all_eq_true.mp h B hB
  rw [Bool.and_eq_true] at h0
  have h1 := List.all_eq_true.mp h0.1 st hst
  rw [hi] at h1
  simp only [he, decide_eq_true_eq] at h1
  exact h1

theorem outBoundLe_ind {Bd : Nat} {f : Clif.Function} (h : outBoundLe Bd f = true)
    {B : Clif.Block} (hB : B ∈ f.blocks) {st : Clif.Stmt} (hst : st ∈ B.body) :
    ∀ sg callee args s, st.inst = .callIndirect sg callee args → f.sigDecls.lookup sg = some s →
      stackBytes s ≤ Bd := by
  intro sg callee args s hi hs
  have h0 := List.all_eq_true.mp h B hB
  rw [Bool.and_eq_true] at h0
  have h1 := List.all_eq_true.mp h0.1 st hst
  rw [hi] at h1
  simp only [hs, decide_eq_true_eq] at h1
  exact h1

theorem outBoundLe_try {Bd : Nat} {f : Clif.Function} (h : outBoundLe Bd f = true)
    {B : Clif.Block} (hB : B ∈ f.blocks) {et : Clif.ExnTable} (ht : IsTryWith B.term et)
    {s : Clif.Signature} (hs : f.sigDecls.lookup et.sig = some s) : stackBytes s ≤ Bd := by
  have h0 := List.all_eq_true.mp h B hB
  rw [Bool.and_eq_true] at h0
  have h1 := h0.2
  rcases ht with ⟨fn, args, he⟩ | ⟨callee, args, he⟩ <;>
  · rw [he] at h1
    simp only [hs, decide_eq_true_eq] at h1
    exact h1

/-! ## The model -/

theorem callTab_info : callTab.contains TId.gen_call_info = false := by decide +kernel

theorem callTab_indInfo : callTab.contains TId.gen_call_ind_info = false := by decide +kernel

/-- **`gen_call_info` and `gen_call_ind_info` are not in `callTab`.** -/
theorem callTab_ne {t : TermId} (ht : t ∈ callTab) :
    t ≠ TId.gen_call_info ∧ t ≠ TId.gen_call_ind_info := by
  have h1 : TId.gen_call_info ∉ callTab := by simpa using callTab_info
  have h2 : TId.gen_call_ind_info ∉ callTab := by simpa using callTab_indInfo
  exact ⟨fun e => h1 (e ▸ ht), fun e => h2 (e ▸ ht)⟩

/-- **The outgoing-bound model** on `callTab`: every run keeps the outgoing area at most
`max outgoing Bd` (it keeps it, `externCtor_out`). -/
def outModel (ctx : Ctx) (Bd : Nat) : UModel program (sem ctx) where
  P := fun _ _ => True
  Is := fun _ => True
  Rs := fun s s' => s'.outgoing ≤ max s.outgoing Bd
  T := (· ∈ callTab)
  C := fun _ _ => True
  O := fun _ => False
  rs_refl := fun s => Nat.le_max_left _ _
  rs_trans := fun _ _ _ h1 h2 => by omega
  mono := by intros; trivial
  int := by intros; trivial
  bool := by intros; trivial
  prim := by intros; trivial
  mkd := by intros; trivial
  un := by intros; trivial
  ext := by intros; trivial
  ctor := fun s t term _ _ _ _ _ s' hT ht _ _ _ h => by
    have hid := Kill.termOf_id_eq ht
    obtain ⟨h1, h2⟩ := callTab_ne hT
    have := externCtor_out_eq (ctx := ctx) (t := term) (by rw [hid]; exact h1)
      (by rw [hid]; exact h2) h
    exact ⟨trivial, trivial, by omega⟩
  oracle := fun _ h => h.elim
  closed := fun t ht _ rl hrl => ⟨(callTab_closed t ht rl hrl).1, fun _ _ => trivial⟩

/-! ## The driver's runs -/

/-- **A statement's `lower` run** keeps the outgoing area at most `max outgoing Bd`, if its
`call`/`call_indirect` passes at most `Bd` bytes on the stack. -/
theorem stmt_out {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {Bd : Nat} {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst)
    (hcall : ∀ fn args e, inst = .call fn args → f.extern? fn = some e → stackBytes e.sig ≤ Bd)
    (hind : ∀ sg callee args s, inst = .callIndirect sg callee args →
      f.sigDecls.lookup sg = some s → stackBytes s ≤ Bd)
    {s : LState} {out : Option V} {s' : LState} {tr : List RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) :
    s'.outgoing ≤ max s.outgoing Bd := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  let M := outModel ctx Bd
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
      exact .inl ⟨(callRuleOk_of h).1, fun _ _ => trivial⟩
  have hhand : ∀ rl ∈ program.rulesOf T.lower.id,
      (rl ∈ program.rulesOf TId.lower ∧ callExcl.contains rl.id = true) →
      ∀ k m s tr env s1 tr1 r s2 tr2, 1000000 = k + 1 → m + 2 ≤ k →
        k ≤ m + 2 + (program.rulesOf T.lower.id).length → (∀ v ∈ [V.inst ii], M.P s v) →
        M.Is s →
        (matchRule program (sem ctx) {} m rl [.inst ii]).run (s, tr) = .ok (some env, (s1, tr1)) →
        (evalExpr program (sem ctx) {} k rl.rhs env).run (s1, tr1) = .ok (r, (s2, tr2)) →
        M.Is s2 ∧ M.Rs s s2 ∧ ∀ v, r = some v → True := by
    intro rl _ ⟨hrl, hx⟩ k m s tr env s1 tr1 r s2 tr2 hk hmk hkm _ _ hm he
    have hlen := E2E.LinkCheck.lower_len
    have hm1 : 1000 ≤ m := by omega
    have hk1 : 1000 ≤ k := by omega
    refine ⟨trivial, ?_, fun _ _ => trivial⟩
    show s2.outgoing ≤ max s.outgoing Bd
    simp only [callExcl, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
      beq_iff_eq] at hx
    rcases hx with e | e | e
    · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2508 (by rw [e]; rfl)
      obtain ⟨out, rfl⟩ := Option.isSome_iff_exists.mp
        (Cov.totality.1 ctx {} k _ env (s1, tr1) r (s2, tr2) Cov.total_2508 he)
      obtain ⟨fn, args, e', hinst, he', heq⟩ := call_bl_outEq data_program f ctx hctx ii info inst
        hi hc {} rfl m k s tr env (s1, tr1) out s2 tr2 hm1 hk1 hm he
      have := hcall fn args e' hinst he'
      omega
    · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2518 (by rw [e]; rfl)
      obtain ⟨out, rfl⟩ := Option.isSome_iff_exists.mp
        (Cov.totality.1 ctx {} k _ env (s1, tr1) r (s2, tr2) Cov.total_2518 he)
      obtain ⟨fn, args, e', hinst, he', heq⟩ := call_got_outEq data_program f ctx hctx ii info inst
        hi hc {} rfl m k s tr env (s1, tr1) out s2 tr2 hm1 hk1 hm he
      have := hcall fn args e' hinst he'
      omega
    · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2529 (by rw [e]; rfl)
      obtain ⟨out, rfl⟩ := Option.isSome_iff_exists.mp
        (Cov.totality.1 ctx {} k _ env (s1, tr1) r (s2, tr2) Cov.total_2529 he)
      obtain ⟨sg, callee, args, sig, hinst, hs, heq⟩ := call_ind_outEq data_program indData_program
        f ctx hctx ii info inst hi hc {} rfl m k s tr env (s1, tr1) out s2 tr2 hm1 hk1 hm he
      have := hind sg callee args sig hinst hs
      omega
  exact (uRoot M rfl (fun _ _ => True)
    (fun rl => rl ∈ program.rulesOf TId.lower ∧ callExcl.contains rl.id = true) data_program.t686
    term_686_kind rfl hrules hhand (fun _ _ => trivial) trivial happ).2.1

/-- **A non-`try_call` terminator's run** keeps the outgoing area at most `max outgoing Bd`. -/
theorem term_out {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {Bd : Nat}
    {ti : Nat} (hti : ti < ctx.insts.size) (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {t : Clif.Terminator} (hty : t.isTry = false) {data : V}
    (hdat : termData (abiTerm f t) = .ok data) {targets : List Label} {s : LState}
    {out : Option V} {s' : LState} {tr : List RuleId}
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) :
    s'.outgoing ≤ max s.outgoing Bd := by
  have hctx' := ctxInv_termCtx hctx hph data
  have hslot := termCtx_self hti data
  unfold termCallF at h
  have hbranch : retOrTrap (abiTerm f t) = false →
      runTerm (termCtx ctx ti data) "lower_branch" [.inst ti, .labels targets] s =
        .ok (out, s', tr) →
      s'.outgoing ≤ max s.outgoing Bd := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower_branch] at ht
    cases ht
    have hrules : ∀ rl ∈ program.rulesOf T.lower_branch.id,
        ((∀ u ∈ ruleTerms rl, (outModel (termCtx ctx ti data) Bd).T u) ∧
          ∀ q ∈ ruleTys rl, (outModel (termCtx ctx ti data) Bd).C q.1 q.2) ∨ False ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl
            [.inst ti, .labels targets]).run s0 ≠ .ok (some env, s1) := by
      intro rl hrl
      cases hcr : closureRoot rl with
      | false => exact .inr (.inr fun m s0 env s1 =>
          branchExcludedUnmatchable rl hrl hcr f _ hctx' ti _ data targets hrt hdat hslot {} m s0
            env s1)
      | true =>
        have h := List.all_eq_true.mp callRootB_ok rl hrl
        rw [hcr, Bool.not_true, Bool.false_or] at h
        exact .inl ⟨(callRuleOk_of h).1, fun _ _ => trivial⟩
    exact (uRoot (outModel (termCtx ctx ti data) Bd) rfl (fun _ _ => False) (fun _ => False)
      data_program.t687 term_687_kind rfl hrules (fun _ _ h => h.elim)
      (fun _ _ => trivial) trivial happ).2.1
  have hlower : retOrTrap (abiTerm f t) = true →
      runTerm (termCtx ctx ti data) "lower" [.inst ti] s = .ok (out, s', tr) →
      s'.outgoing ≤ max s.outgoing Bd := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower] at ht
    cases ht
    have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
        ((∀ u ∈ ruleTerms rl, (outModel (termCtx ctx ti data) Bd).T u) ∧
          ∀ q ∈ ruleTys rl, (outModel (termCtx ctx ti data) Bd).C q.1 q.2) ∨ False ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl
            [.inst ti]).run s0 ≠ .ok (some env, s1) := by
      intro rl hrl
      cases hroot : termRootRule rl with
      | false => exact .inr (.inr (lower_term_nomatch hrt hdat hslot hrl hroot))
      | true =>
        have h := List.all_eq_true.mp callRootS_ok rl hrl
        simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
        have hx : callExcl.contains rl.id = false := by
          rcases hroot with e | e <;> simp [callExcl, e]
        rw [hx, Bool.false_or] at h
        exact .inl ⟨(callRuleOk_of h).1, fun _ _ => trivial⟩
    exact (uRoot (outModel (termCtx ctx ti data) Bd) rfl (fun _ _ => False) (fun _ => False)
      data_program.t686 term_686_kind rfl hrules (fun _ _ h => h.elim)
      (fun _ _ => trivial) trivial happ).2.1
  cases t with
  | ret vs => exact hlower rfl h
  | trap c => exact hlower rfl h
  | jump bc => exact hbranch rfl h
  | brif c a b => exact hbranch rfl h
  | brTable x d tb => exact hbranch rfl h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hdat
  | tryCall fn args et => simp [Clif.Terminator.isTry] at hty
  | tryCallIndirect callee args et => simp [Clif.Terminator.isTry] at hty

/-- **A `try_call`'s run** sets the outgoing area to at most `max outgoing Bd`, if the exception
table's signature passes at most `Bd` bytes on the stack. -/
theorem try_out {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {Bd : Nat} {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator}
    {et : Clif.ExnTable} (het : IsTryWith t et) {data : V} {sig : Clif.Signature}
    {items : List (Option Nat)} (hd : tryCallData f t = .ok data)
    (he : exnTableOpnd f et = .ok (sig, items)) (hb : stackBytes sig ≤ Bd)
    {trs : List Reg × List Reg} {targets : List Label} {s : LState} {out : V} {s' : LState}
    {tr : List RuleId} (h : tryCallF ctx ti data trs targets s = .ok (some out, s', tr)) :
    s'.outgoing ≤ max s.outgoing Bd := by
  have hctx' : CtxInv f (tryCtx ctx ti data trs) := { ctxInv_termCtx hctx hph data with }
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
    rw [show TId.lower_branch = 687 from rfl, data_program.r687]
    decide +kernel
  have hlen := E2E.LinkCheck.lower_branch_len
  unfold tryCallF at h
  obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  rcases internal_cases (cfg := {}) rfl data_program.t687 term_687_kind rfl happ with
    ⟨hr, -⟩ | ⟨rl, hrl, m, env, s1, tr1, tr2, hmn, hnm, hmatch, heval⟩
  · cases hr
  · have hm1 : 1000 ≤ m := by omega
    rcases het with ⟨fn, args, rfl⟩ | ⟨callee, args, rfl⟩
    · obtain ⟨sig0, items0, ext, he0, hext, hsig⟩ := tryCallData_spec hd
      rw [he] at he0
      simp only [Except.ok.injEq, Prod.mk.injEq] at he0
      obtain ⟨rfl, rfl⟩ := he0
      have hcx : TryCtxOk f (tryCtx ctx ti data trs) := ⟨hctx'.func, hctx'.valueReg⟩
      cases hroot : tryRootRule rl with
      | false =>
        exact absurd hmatch (tryUnmatchable rl hrl hroot f _ hctx' ti fn args et data targets hd hi
          {} m _ env _)
      | true =>
        simp only [tryRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
        rcases hroot with e | e
        · rw [eq_of_mem_of_rid hnd hrl mem_lower_branch_2542 (by rw [e]; rfl)] at hmatch heval
          have := try_bl_outEq data_program tryData_program f _ hcx ti fn args et data targets hd hi
            {} rfl m _ s _ env _ out s' _ hm1 (by omega) hmatch heval ext hext
          rw [hsig] at this
          omega
        · rw [eq_of_mem_of_rid hnd hrl mem_lower_branch_2551 (by rw [e]; rfl)] at hmatch heval
          have := try_got_outEq data_program tryData_program f _ hcx ti fn args et data targets hd
            hi {} rfl m _ s _ env _ out s' _ hm1 (by omega) hmatch heval ext hext
          rw [hsig] at this
          omega
    · cases hroot : tryIndRootRule rl with
      | false =>
        exact absurd hmatch (tryIndUnmatchable rl hrl hroot f _ hctx' ti callee args et data
          targets hd hi {} m _ env _)
      | true =>
        simp only [tryIndRootRule, beq_iff_eq] at hroot
        rw [eq_of_mem_of_rid hnd hrl mem_lower_branch_2561 (by rw [hroot]; rfl)] at hmatch heval
        have := try_ind_outEq data_program tryData_program indData_program tryIndData_program f _
          hctx' ti callee args et data sig items targets hd he hi {} rfl m _ s _ env _ out s' _ hm1
          (by omega) hmatch heval
        omega

/-! ## Through the recorded lowering -/

theorem lowStmts_bnd {call : StmtCall} {Bd : Nat} :
    ∀ {ss : List Clif.Stmt} {ii : Nat} {st : LState} {sls : List SLow} {stE : LState},
      lowStmts call ii ss st = some (sls, stE) → st.outgoing ≤ Bd →
      (∀ sl ∈ sls, sl.st.outgoing ≤ Bd → sl.st'.outgoing ≤ Bd) → stE.outgoing ≤ Bd
  | [], _, _, _, _, h, h0, _ => by
    simp only [lowStmts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact h0
  | _ :: ss, ii, st, sls, stE, h, h0, hs => by
    simp only [lowStmts] at h
    split at h
    · rename_i out st' tr' hc
      split at h
      · rename_i rss _
        cases hrec : lowStmts call (ii + 1) ss { st' with emitted := #[] } with
        | none => rw [hrec] at h; cases h
        | some q =>
          rw [hrec] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have h1 := hs _ List.mem_cons_self h0
          exact lowStmts_bnd hrec h1 fun sl hsl => hs sl (List.mem_cons_of_mem _ hsl)
      · cases h
    · cases h

theorem lowBlocks_bnd {f : Clif.Function} {call : StmtCall} {tcall : TermCallF} {ycall : TryCallF}
    {Bd : Nat} :
    ∀ {Bs : List Clif.Block} {start : Nat} {st : LState} {nl : Nat} {bl : List BLow},
      lowBlocks f call tcall ycall start Bs st nl = some bl → st.outgoing ≤ Bd →
      (∀ L ∈ bl, (∀ sl ∈ L.sl, sl.st.outgoing ≤ Bd → sl.st'.outgoing ≤ Bd) ∧
        (L.tst.outgoing ≤ Bd → L.tst'.outgoing ≤ Bd)) →
      (bl.getLast?.map (·.tst'.outgoing)).getD st.outgoing ≤ Bd
  | [], _, _, _, _, h, h0, _ => by
    simp only [lowBlocks, Option.some.injEq] at h
    subst h
    exact h0
  | B :: Bs, start, st, nl, bl, h, h0, hL => by
    simp only [lowBlocks] at h
    cases hstm : lowStmts call start B.body st with
    | none => rw [hstm] at h; cases h
    | some q =>
      obtain ⟨sls, stE⟩ := q
      rw [hstm] at h
      simp only at h
      cases hterm : lowTerm f tcall ycall (start + B.body.length) B.term { stE with emitted := #[] } nl with
      | none => rw [hterm] at h; cases h
      | some q =>
        obtain ⟨data, targets, tl, tst', nl'⟩ := q
        rw [hterm] at h
        simp only at h
        cases hrec : lowBlocks f call tcall ycall (start + B.body.length + 1) Bs
            { tst' with emitted := #[] } nl' with
        | none => rw [hrec] at h; cases h
        | some bl' =>
          rw [hrec] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨hs, ht⟩ := hL _ List.mem_cons_self
          have hE := lowStmts_bnd hstm h0 hs
          have hT : tst'.outgoing ≤ Bd := ht hE
          have := lowBlocks_bnd hrec hT fun L hL' => hL L (List.mem_cons_of_mem _ hL')
          rw [getLast?_cons_getD]
          exact this

/-- `buildCtx` starts with no outgoing area. -/
theorem buildCtx_outgoing {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hb : buildCtx f = .ok (ctx, ranges, st0)) : st0.outgoing = 0 := by
  obtain ⟨-, -, rfl, -⟩ := buildCtx_model hb
  rfl

/-- **The outgoing area of `lowerFunction`'s VCode is at most `Bd`** on `LowerScope` input
whose calls and `try_call`s pass at most `Bd` bytes on the stack (`outBoundLe`). -/
theorem lowerFunction_outgoing_le {f : Clif.Function} {vc : VCode} {Bd : Nat}
    (hs : LowerScope f) (hob : outBoundLe Bd f = true) (h : lowerFunction f = .ok vc) :
    vc.outgoing ≤ Bd := by
  obtain ⟨ctx, ranges, st0, bl, hb, hl, -, hout, -⟩ := lowerFunction_run hs.subsetE h
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  have hcf := ctxFacts_of hb
  obtain ⟨hlen, hstart⟩ := lowBlocks_start hl
  obtain ⟨-, hspec⟩ := lowBlocks_spec hl
  rw [hout]
  unfold outOf
  refine lowBlocks_bnd hl (by rw [buildCtx_outgoing hb]; exact Nat.zero_le _) ?_
  intro L hL
  obtain ⟨bi, hbi⟩ := List.mem_iff_getElem?.mp hL
  obtain ⟨B, hB⟩ : ∃ B, f.blocks[bi]? = some B :=
    ⟨_, List.getElem?_eq_getElem (by rw [← hlen]; exact lt_of_getElem? hbi)⟩
  have hBm : B ∈ f.blocks := List.mem_of_getElem? hB
  obtain ⟨hsll, hc, -, nl0, nl', hterm⟩ := hspec bi B L hB hbi
  have hti : L.start + B.body.length < ctx.insts.size := by
    have := hcf.term bi B hB
    rw [← hstart bi L hbi] at this
    exact (Array.getElem?_eq_some_iff.mp this).1
  have hph : ctx.insts[L.start + B.body.length]? = some ⟨.op .unit, [], [], none⟩ := by
    have := hcf.term bi B hB
    rw [← hstart bi L hbi] at this
    exact this
  refine ⟨fun sl hsl hle => ?_, fun hle => ?_⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hsl
    obtain ⟨stm, hstm⟩ : ∃ stm, B.body[j]? = some stm :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hsll]; exact lt_of_getElem? hj)⟩
    have hstmm : stm ∈ B.body := List.mem_of_getElem? hstm
    obtain ⟨info, hi, hic, -⟩ := hcf.stmt bi B j stm hB hstm
    rw [← hstart bi L hbi] at hi
    obtain ⟨tr, hrun⟩ := hc j sl hj
    have := stmt_out hctx hi hic (outBoundLe_call hob hBm hstmm) (outBoundLe_ind hob hBm hstmm)
      hrun
    omega
  · obtain ⟨hn, hy⟩ := lowTerm_spec hterm
    cases hty : B.term.isTry with
    | false =>
      obtain ⟨-, hd, out, tr, hrun⟩ := hn hty
      have := term_out (Bd := Bd) hctx hti hph hty hd hrun
      omega
    | true =>
      obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := by
        cases hB' : B.term <;> rw [hB'] at hty <;> simp [Clif.Terminator.isTry] at hty
        · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
        · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
      obtain ⟨T, -, hd, he, -, hr, -, out, tr, hrun⟩ := hy et het
      have hsb := outBoundLe_try hob hBm het (Driver.exnTableOpnd_sig he)
      have := try_out (Bd := Bd) hctx hph het hd he hsb hrun
      have hr' := tryRegsOf_outgoing hr
      simp only at this
      omega

end Backend.Proof.OutBound
