import FV.Backend.Proof.IselEmitTModel
import FV.Backend.Proof.IselEmitTLast
import FV.Backend.Proof.IselEmitTHand
import FV.Backend.Proof.IselEmitTTab
import FV.Backend.Proof.IselCovTDriver
import FV.Backend.Proof.IselCovTFamCover

/-!
# Emission conditions of the typed ISLE lowering (S11): the driver's calls, `IselEmitT`

The typed emission model `emModelT` (the typed interpreter with `aextET`/`actorET`/`apreET`,
state invariant `EmSince s0`) over a float-capable context (`CtxInvT`) whose statements belong to
the instruction families (`FamCover`), its soundness on the table `emitTabT`, and the driver's
three ISLE calls: a statement's `lower` on its family (`stmt_emitT`: `EmSince`; the rules
`emitHandIdsT` by hand, `hand_emitT`, under `ExtendsWiden` and `BitcastsSameWidth`), a
terminator's `lower` (`return`/`trap`, input `c0`) or `lower_branch` on its family
(`termCall_emitT`: `EmLast`; the branch rules end in their branch, `root_last`), a `try_call`'s
`lower_branch` (`tryCall_emitT`).

**`iselEmitT`: `IselEmitT f` on the typed scope (`dominatedB`, `LowerScopeT`, class-checked float
`store`s/`select`s) with `extendsWidenB f` and `bitcastWidthB f`.**
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (Clean emSince_emLast)
open Backend.Proof.Driver

set_option maxRecDepth 20000

section Root

variable {f : Clif.Function} {ctx : Ctx} {p : Program} {aext : TermId → AT → List AT}
  {actor : TermId → List AT → AT}
  {apre : TermId → List AT → Bool} {aOracle : TermId → List AT → Option AT}
  {md : CovModel aext actor apre aOracle p f ctx} {cfg : Config} {tab : Tab}

/-- **A root term whose rules pass `aRule`, never match, or are checked by hand** keeps the
invariant (typed domain; `Cov.root_hand`). -/
theorem root_handE (hc : cfg.checkOverlap = false) (sa : ∀ n, SoundAt md cfg tab n)
    {vs : List V} {Hand : Rule → Prop}
    (hhand : ∀ rl, Hand rl → ∀ (m n : Nat) (s : LState) (tr : Array RuleId) (env : Isle.Interp.Env V)
      (s1 : LState × Array RuleId) (r : Option V) (s2 : LState) (tr2 : Array RuleId),
      1000 ≤ m → 1000 ≤ n → md.Is s →
      (matchRule p (sem ctx) cfg m rl vs).run (s, tr) = .ok (some env, s1) →
      (evalExpr p (sem ctx) cfg n rl.rhs env).run s1 = .ok (r, (s2, tr2)) → md.Is s2)
    {ty : TypeId} {t : TermId} {term : Term} {flags : TermFlags} {ex : Option Extractor}
    {ins : List AT} {out : AT} {s : LState} {tr : Array RuleId} {r : Option V} {s' : LState}
    {tr' : Array RuleId} (ht : termOf p t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    (hrules : ∀ rl ∈ p.rulesOf t, aRule p tab aext actor apre aOracle ins out rl = true ∨
      (∀ m s0 env s1, (matchRule p (sem ctx) cfg m rl vs).run s0 ≠ .ok (some env, s1)) ∨ Hand rl)
    (hins : Holds2 f ctx ins vs) (hIs : md.Is s) {n : Nat} (hn : 1002 + (p.rulesOf t).length ≤ n)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty t vs).run (s, tr) = .ok (r, (s', tr'))) : md.Is s' := by
  cases hm : flags.isMulti with
  | true =>
    rw [applyTerm.eq_2] at h
    obtain ⟨term', s1, h1, h2⟩ := bind_ok h
    obtain ⟨_, ht', he⟩ := liftM_ok h1
    rw [ht] at ht'; cases ht'; cases he
    rw [hk] at h2
    simp only [hm, ↓reduceIte] at h2
    exact (throw_ok h2).elim
  | false =>
  rw [applyTerm_internal_run ht hk hm] at h
  obtain ⟨⟨sel, ⟨s1, tr1⟩⟩, h1, h2⟩ := except_bind_eq_ok h
  cases sel with
  | none =>
    have := selectRule_none h1
    cases this
    simp only at h2
    split at h2
    · cases pure_ok h2; exact hIs
    · exact (throw_ok h2).elim
  | some re =>
    obtain ⟨rl, env⟩ := re
    obtain ⟨hrl, m, hmn, hmatch⟩ := selectRule_some_lt hc h1
    simp only at h2
    obtain ⟨ev, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
    have hfin : md.Is s2 → md.Is s' := by
      intro hIs2
      cases ev with
      | some v =>
        obtain ⟨u, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
        have hf := fire_ok h5
        cases pure_ok h6
        simp only at hf
        subst hf
        exact hIs2
      | none => cases pure_ok h4; exact hIs2
    rcases hrules rl hrl with hok | hno | hhd
    · obtain ⟨envs, hae, hall⟩ := aRule_inv hok
      obtain ⟨hIs1, aenv, haenv, he1⟩ := (sa m).mrule _ _ _ _ _ _ _ _ _ hae hins hIs hmatch
      obtain ⟨a, ha, -⟩ := hall aenv haenv
      exact hfin ((sa n).expr _ _ _ _ _ _ _ _ _ ha he1 hIs1 h3).1
    · exact absurd hmatch (hno m _ _ _)
    · obtain ⟨-, m', hm', hmatch'⟩ := selectRule_some hc h1
      exact hfin (hhand rl hhd m' n s tr env _ ev s2 tr2 (by omega) (by omega) hIs hmatch' h3)

end Root

variable {f : Clif.Function} {ctx : Ctx}

theorem em_soundT (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) (s0 : LState)
    {cfg : Config} (hc : cfg.checkOverlap = false) :
    ∀ n, SoundAt (emModelT hctx hcl hfam s0) cfg emitTabT n :=
  soundAt (md := emModelT hctx hcl hfam s0) (cfg := cfg) (tab := emitTabT) hc emitTabT_ok

/-! ## The driver's calls -/

set_option maxRecDepth 100000 in
/-- **A statement's lowering emits only instructions with the emission conditions and no branch
targets** (typed). -/
theorem stmt_emitT (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx)
    (hw : ExtendsWiden ctx) (hB : BitcastsSameWidth ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) : EmSince s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  obtain ⟨i, F, hF, hok⟩ := hfam ii info inst hi hc
  have hins := holds_famT (f := f) hi hF hok
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      aRule program emitTabT aextET actorET apreET aOracle [.inst [i]] AT.top rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1)) ∨
      (rl ∈ program.rulesOf TId.lower ∧ emitHandIdsT.contains rl.id = true) := by
    intro rl hrl
    have hs := List.all_eq_true.mp emitStmtT_ok rl hrl
    unfold emitStmtOkT at hs
    simp only [Bool.or_eq_true] at hs
    rcases hs with hh | hs
    · exact .inr (.inr ⟨hrl, hh⟩)
    · exact .inl (List.all_eq_true.mp hs i (List.mem_range.mpr (famTab_lt hF)))
  exact root_handE (md := emModelT hctx hcl hfam s) rfl (em_soundT hctx hcl hfam s rfl)
    (Hand := fun rl => rl ∈ program.rulesOf TId.lower ∧ emitHandIdsT.contains rl.id = true)
    (fun rl ⟨hrl, hid⟩ m n s1 tr1 env s2 r s3 tr3 hm hn hIs h1 h2 =>
      hand_emitT hctx hw hB hi hc hrl hid {} rfl m n s s1 tr1 env s2 r s3 tr3 hm hn hIs h1 h2)
    data_program.t686 term_686_kind hrules hins (Cov.emSince_self s) (n := 999999)
    lower_len happ

set_option maxRecDepth 100000 in
/-- `lower_branch` on a terminator of a family: everything emitted has the emission conditions,
branch targets only last. -/
theorem branch_emitT (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) {ti : Nat}
    {tinfo : IInfo} {i : Nat} {F : Fam} (hti : ctx.insts[ti]? = some tinfo)
    (hF : famTab[i]? = some F) (hok : FamOk ctx F tinfo) {targets : List Label} {s : LState}
    {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    EmLast s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  have hins : Holds2 f ctx [.inst [i], AT.c0] [.inst ti, .labels targets] :=
    ⟨⟨ti, tinfo, rfl, hti, i, List.mem_singleton_self _, F, hF, hok⟩,
      ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩, trivial⟩
  exact root_last (emModelT hctx hcl hfam s) (fun _ => Iff.rfl) rfl emitTabT_ok
    (fun nb a v m ha hv hm => emChk_sound ha hv hm) data_program.t687 term_687_kind
    (fun rl hrl => by
      have hb := List.all_eq_true.mp emitBranchT_ok rl hrl
      unfold emitBranchOkT at hb
      have hf := List.all_eq_true.mp hb i (List.mem_range.mpr (famTab_lt hF))
      simp only [Bool.or_eq_true] at hf
      rcases hf with ha | ha
      · exact .inl ha
      · exact .inr (.inl ha))
    hins (Cov.emSince_self s) happ

set_option maxRecDepth 100000 in
/-- **A terminator's lowering** (typed): the emission conditions, branch targets only last
(`lower` on `return`/`trap`, `lower_branch` on a branch of a family). -/
theorem termCall_emitT (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator}
    (hty : t.isTry = false) {data : V} (hd : termData (abiTerm f t) = .ok data)
    (htf : ∃ (i : Nat) (F : Fam), famTab[i]? = some F ∧ FamOk ctx F ⟨data, [], [], none⟩)
    {targets : List Label} {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) : EmLast s s' := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have hctx' := ctxInvT_termCtx hctx hph data
  have hcl' := Cov.clean_termCtx hcl hd ti
  have hfam' := famCover_termCtx hfam hph data
  have hslot := termCtx_self hti data
  unfold termCallF at h
  have hlower : retOrTrap (abiTerm f t) = true →
      runTerm (termCtx ctx ti data) "lower" [.inst ti] s = .ok (out, s', tr) → EmLast s s' := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower] at ht
    cases ht
    have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
        aRule program emitTabT aextET actorET apreET aOracle [AT.c0] AT.top rl = true ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl [.inst ti]).run s0 ≠
            .ok (some env, s1) := by
      intro rl hrl
      cases hroot : termRootRule rl with
      | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
      | true =>
        have hf := List.all_eq_true.mp emitTermT_ok rl hrl
        simp only [termRootRule] at hroot
        simp only [hroot, Bool.not_true, Bool.false_or] at hf
        exact .inl hf
    exact emSince_emLast ((em_soundT hctx' hcl' hfam' s rfl 1000000).root T.lower.ret T.lower.id
      T.lower _ _ [AT.c0] AT.top [.inst ti] s #[] out s' tr' data_program.t686 term_686_kind hrules
      ⟨⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩, trivial⟩ (Cov.emSince_self s) happ).1
  obtain ⟨i, F, hF, hok⟩ := htf
  have hok' : FamOk (termCtx ctx ti data) F ⟨data, [], [], none⟩ :=
    famOk_valTy (ctx := ctx) (ctx' := termCtx ctx ti data) rfl hok
  cases t with
  | ret vs => exact hlower rfl h
  | trap c => exact hlower rfl h
  | jump bc => exact branch_emitT hctx' hcl' hfam' hslot hF hok' h
  | brif c a b => exact branch_emitT hctx' hcl' hfam' hslot hF hok' h
  | brTable x d tb => exact branch_emitT hctx' hcl' hfam' hslot hF hok' h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [Clif.Terminator.isTry] at hty
  | tryCallIndirect callee args et => simp [Clif.Terminator.isTry] at hty

/-- **A `try_call`'s lowering** (typed): the emission conditions, branch targets only last. -/
theorem tryCall_emitT (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator} {data : V}
    (hd : tryCallData f t = .ok data)
    (htf : ∃ (i : Nat) (F : Fam), famTab[i]? = some F ∧ FamOk ctx F ⟨data, [], [], none⟩)
    {trs : List Reg × List Reg} {targets : List Label} {s : LState} {out : Option V} {s' : LState}
    {tr : List Isle.RuleId} (h : tryCallF ctx ti data trs targets s = .ok (out, s', tr)) :
    EmLast s s' := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have h' := ctxInvT_termCtx hctx hph data
  have hctx' : CtxInvT f (tryCtx ctx ti data trs) := { h' with }
  obtain ⟨i, F, hF, hok⟩ := htf
  exact branch_emitT hctx' (Cov.clean_tryCtx hcl hd ti trs)
    (famCover_eq (ctx := termCtx ctx ti data) (ctx' := tryCtx ctx ti data trs) rfl rfl
      (famCover_termCtx hfam hph data)) (termCtx_self hti data) hF
    (famOk_valTy (ctx := ctx) (ctx' := tryCtx ctx ti data trs) rfl hok) h

end Backend.Proof.CovT

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- **The ISLE runs of the driver meet the emission conditions on the typed scope**: for input in
`Dominated` and `LowerScopeT` with class-checked float `store`s and `select`s whose extends widen
and whose bitcasts keep the width. -/
theorem iselEmitT {f : Clif.Function} (hdom : dominatedB f = true) (hs : LowerScopeT f)
    (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (hw : extendsWidenB f = true) (hbw : bitcastWidthB f = true) : IselEmitT f := by
  intro ctx ranges st0 hb
  have hctx : CtxInvT f ctx := ctxInvT_of hs hb
  have hcl : Cov.Clean ctx := Cov.clean_of_build hb
  have hfam := CovT.famCover_of hs hdom hst hsel hb
  have hW := extendsWiden_of hw hb
  have hB := bitcastsSameWidth_of hbw hb
  exact ⟨fun ii info inst s out s' tr hi hc h => CovT.stmt_emitT hctx hcl hfam hW hB hi hc h,
    fun B hB' ti data targets s out s' tr _ hph hty hd h =>
      CovT.termCall_emitT hctx hcl hfam hph hty hd (CovT.termFam_of hs hdom hb hB' (.inl hd)) h,
    fun B hB' ti data trs targets s out s' tr _ hph hd h =>
      CovT.tryCall_emitT hctx hcl hfam hph hd (CovT.termFam_of hs hdom hb hB' (.inr hd)) h⟩

end Backend.Proof.Driver
