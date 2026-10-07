import FV.Backend.Proof.IselEmitModel
import FV.Backend.Proof.IselEmitChk
import FV.Backend.Proof.IselEmitLast
import FV.Backend.Proof.IselEmitHand
import FV.Backend.Proof.IselEmitTab
import FV.Backend.Proof.IselShpDriver

/-!
# Emission conditions of the ISLE lowering (V6c): the driver's calls, `IselEmit`

The emission model `emModel` (V3's abstract interpreter with `aextE`/`actorE`/`apreE`, state
invariant `EmSince s0`), its soundness on the table `emitTab`, and the driver's three ISLE calls:
a statement's `lower` (`stmt_emit`: `EmSince`; the rules `emitHandIds` by hand, `hand_emit`, under
`ExtendsWiden`), a terminator's `lower`/`lower_branch` (`termCall_emit`: `EmLast`; the branch
rules end in their branch, `root_last`), a `try_call`'s `lower_branch` (`tryCall_emit`).
**`iselEmit`: `IselEmit f` for in-scope `f` with `extendsWidenB f`.**
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

theorem emSince_refl (s : LState) : EmSince s s := ⟨[], by simp, by simp⟩

theorem em_sound (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) (s0 : LState) {cfg : Config}
    (hc : cfg.checkOverlap = false) : ∀ n, SoundAt (emModel hctx hcl s0) cfg emitTab n :=
  soundAt (hctx := hctx) (md := emModel hctx hcl s0) (cfg := cfg) (tab := emitTab) hc emitTab_ok

/-- `ExtendsWiden` of the built context from the input condition. -/
theorem extendsWiden_of {ranges : Array (Nat × Nat)} {st0 : LState} (hw : extendsWidenB f = true)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) : ExtendsWiden ctx := by
  intro ii info op ty x hi hc
  unfold extendsWidenB at hw
  rw [hb] at hw
  simp only at hw
  have h := (Array.all_eq_true_iff_forall_mem.mp hw) info (Array.mem_of_getElem? hi)
  rw [hc] at h
  simp only at h
  cases ht : ctx.valueType? x with
  | none => rw [ht] at h; cases h
  | some t => rw [ht] at h; exact ⟨t, rfl, of_decide_eq_true h⟩

/-! ## The driver's calls -/

set_option maxRecDepth 100000 in
/-- **A statement's lowering emits only instructions with the emission conditions and no branch
targets.** -/
theorem stmt_emit (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) (hw : ExtendsWiden ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) : EmSince s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      aRule program emitTab aextE actorE apreE aOracle [.xv .inst] AW.top rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1)) ∨
      (rl ∈ program.rulesOf TId.lower ∧ emitHandIds.contains rl.id = true) := by
    intro rl hrl
    have hf := List.all_eq_true.mp emitStmt_ok rl hrl
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hf
    rcases hf with (hcr | hh) | ha
    · exact .inr (.inl (lower_nonroot_nomatch hctx hi hc hrl hcr))
    · exact .inr (.inr ⟨hrl, hh⟩)
    · exact .inl ha
  exact root_hand (md := emModel hctx hcl s) rfl (em_sound hctx hcl s rfl)
    (Hand := fun rl => rl ∈ program.rulesOf TId.lower ∧ emitHandIds.contains rl.id = true)
    (fun rl ⟨hrl, hid⟩ m n s1 tr1 env s2 r s3 tr3 hm hn hIs h1 h2 =>
      hand_emit hctx hw hi hc hrl hid {} rfl m n s s1 tr1 env s2 r s3 tr3 hm hn hIs h1 h2)
    data_program.t686 term_686_kind hrules (holds_inst hctx hi hc) (emSince_refl s) (n := 999999)
    lower_len happ

set_option maxRecDepth 100000 in
/-- `lower_branch`: everything emitted has the emission conditions, branch targets only last. -/
theorem branch_emit (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) {ti : Nat} {targets : List Label}
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    EmLast s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  have hins : Holds2 f ctx [AW.c0, AW.c0] [.inst ti, .labels targets] :=
    ⟨γ_c0_inst ti, γ_c0_labels targets, trivial⟩
  exact root_last hctx (emModel hctx hcl s) (fun _ => Iff.rfl) rfl emitTab_ok
    (fun nb a v m ha hv hm => emChk_sound ha hv hm) data_program.t687 term_687_kind
    (fun rl hrl => by
      have hf := List.all_eq_true.mp emitBranch_ok rl hrl
      simp only [Bool.or_eq_true] at hf
      rcases hf with ha | ha
      · exact .inl ha
      · exact .inr (.inl ha))
    hins (emSince_refl s) happ

set_option maxRecDepth 100000 in
/-- **A terminator's lowering**: the emission conditions, branch targets only last. -/
theorem termCall_emit (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator} (hty : t.isTry = false)
    {data : V} (hd : termData (abiTerm f t) = .ok data) {targets : List Label} {s : LState}
    {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) : EmLast s s' := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have hctx' := ctxInv_termCtx hctx hph data
  have hcl' := clean_termCtx hcl hd ti
  have hslot := termCtx_self hti data
  unfold termCallF at h
  have hbranch : runTerm (termCtx ctx ti data) "lower_branch" [.inst ti, .labels targets] s =
      .ok (out, s', tr) → EmLast s s' := fun h => branch_emit hctx' hcl' h
  have hlower : retOrTrap (abiTerm f t) = true →
      runTerm (termCtx ctx ti data) "lower" [.inst ti] s = .ok (out, s', tr) → EmLast s s' := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower] at ht
    cases ht
    have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
        aRule program emitTab aextE actorE apreE aOracle [AW.c0] AW.top rl = true ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl [.inst ti]).run s0 ≠
            .ok (some env, s1) := by
      intro rl hrl
      cases hroot : termRootRule rl with
      | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
      | true =>
        have hf := List.all_eq_true.mp emitTerm_ok rl hrl
        simp only [termRootRule] at hroot
        simp only [hroot, Bool.not_true, Bool.false_or] at hf
        exact .inl hf
    exact emSince_emLast ((em_sound hctx' hcl' s rfl 1000000).root T.lower.ret T.lower.id T.lower _ _
      [AW.c0] AW.top [.inst ti] s #[] out s' tr' data_program.t686 term_686_kind hrules
      ⟨γ_c0_inst ti, trivial⟩ (emSince_refl s) happ).1
  cases t with
  | ret vs => exact hlower rfl h
  | trap c => exact hlower rfl h
  | jump bc => exact hbranch h
  | brif c a b => exact hbranch h
  | brTable x d tb => exact hbranch h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [Clif.Terminator.isTry] at hty
  | tryCallIndirect callee args et => simp [Clif.Terminator.isTry] at hty

/-- **A `try_call`'s lowering**: the emission conditions, branch targets only last. -/
theorem tryCall_emit (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator} {data : V}
    (hd : tryCallData f t = .ok data) {trs : List Reg × List Reg} {targets : List Label}
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : tryCallF ctx ti data trs targets s = .ok (out, s', tr)) : EmLast s s' := by
  have h' := ctxInv_termCtx hctx hph data
  have hctx' : CtxInv f (tryCtx ctx ti data trs) := { h' with }
  exact branch_emit hctx' (clean_tryCtx hcl hd ti trs) h

/-! ## `IselEmit` -/

/-- **The ISLE runs of the driver meet the emission conditions** for every in-scope function
whose extends widen. -/
theorem iselEmit (hs : LowerScope f) (hw : extendsWidenB f = true) : IselEmit f := by
  intro ctx ranges st0 hb
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  have hcl : Cov.Clean ctx := clean_of_build hb
  have hW := extendsWiden_of hw hb
  exact ⟨fun ii info inst s out s' tr hi hc h => stmt_emit hctx hcl hW hi hc h,
    fun ti t data targets s out s' tr _ hph hty hd h => termCall_emit hctx hcl hph hty hd h,
    fun ti t data trs targets s out s' tr _ hph hd h => tryCall_emit hctx hcl hph hd h⟩

end Backend.Proof.Driver
