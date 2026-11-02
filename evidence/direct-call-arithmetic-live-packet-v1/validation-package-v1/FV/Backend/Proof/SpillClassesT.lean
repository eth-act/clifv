import FV.Backend.Proof.SpillClasses
import FV.Backend.Proof.IselExclTF
import FV.Backend.Proof.SpillEdgesT
import FV.Backend.Proof.IselFlowT

/-!
# `ClassesHyp` over the typed scope (S11e5 Stage C, slice 6)

`classesHypT`: on `Dominated`, `LowerScopeT` input, the prepared code's vreg classes are
consistent (`ClassesOk`), given `ResClassOk f`: the lowering returns each statement result in
a vreg of its result type's class. That premise is what the alias resolution needs (the driver
aliases result `r` to the vreg `o` the rules return, `.vreg r c ↦ .vreg o c`, so `o`'s recorded
class must be `r`'s); over subset E it is a theorem (`resClassOk_of_lowerScope`, from
`stmt_cov`: the results are int vregs), so `classesHyp` is a corollary (`classesHyp_of_T`).

The rest is `classesHyp`'s proof over the typed lowering run: the class facts of the driver's
ISLE calls hold over float-capable contexts (`stmt_clsT`: the typed exclusion
`lower_nonroot_nomatchT` and `pinned_namesT` in place of the integer ones; the terminator and
`try_call` calls need no context invariant, `termCall_clsT`, `tryCall_cls`); the values' vregs
have the classes `buildCtx` records (`buildCtx`'s initial classes are type-derived); the typed
entry code (`Args`, `stackArgLoad`), result copies, block parameters and edge arguments use
those vregs; the alias resolution keeps classes when every alias joins vregs of one class
(`resolve_clsT`).

`classesOkB`: `ClassesOk`, decided on a VCode (`classesOk_of_classesOkB`), so a run-time check
can establish it directly.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

/-! ## The driver's ISLE calls over float-capable contexts -/

set_option maxRecDepth 100000 in
/-- **A statement's lowering** keeps `ClsIs` over a float-capable context whose non-root `lower`
rules never match (`LowerNoMatch`); its result (of an instruction with results) has registers of
their classes. -/
theorem stmt_clsG {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) (hnm : LowerNoMatch ctx)
    (hcl : Cov.Clean ctx)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst) {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) (hIs : ClsIs ctx s s) :
    ClsIs ctx s s' ∧ ∀ v, out = some v → info.results ≠ [] → GoodV s'.classes v := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have sa := soundAtC (md := clsModel hcl s) (cfg := {}) (tab := clsTab) rfl clsTab_ok 1000000
  have hrulesTop : ∀ rl ∈ program.rulesOf T.lower.id,
      aRuleC program clsTab false [⟨1, true⟩] FA.top rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    have hf := List.all_eq_true.mp clsRoot_ok rl hrl
    simp only [clsRootOk, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at hf
    rcases hf with hcr | ⟨ha, -⟩
    · exact .inr (hnm ii info inst hi hc rl hrl hcr {})
    · exact .inl ha
  refine ⟨(sa.root T.lower.ret T.lower.id T.lower _ _ [⟨1, true⟩] FA.top [.inst ii] s #[] out s'
    tr' data_program.t686 term_686_kind hrulesTop (holds_inst_cls s ii) hIs happ).1, ?_⟩
  intro v hout hres
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      aRuleC program clsTab false [⟨1, true⟩] ⟨1, false⟩ rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    have hf := List.all_eq_true.mp clsRoot_ok rl hrl
    have hop := List.all_eq_true.mp lower_ops rl hrl
    simp only [clsRootOk, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, beq_iff_eq] at hf
    rcases hf with hcr | ⟨-, h587 | ha⟩
    · exact .inr (hnm ii info inst hi hc rl hrl hcr {})
    · refine .inr fun m s0 env s1 hm => hres ?_
      simp only [h587, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hop
      have hn := pinned_namesT hctx hi hc hop.1 kind_nullAry kind_nop (by decide) hm
      rw [variantNames_Nop] at hn
      have hnop := Driver.instNames_nop (Option.some.inj hn).symm
      subst hnop
      obtain ⟨tys, hty, -, hlen⟩ := hctx.resTys ii info .nop hi hc
      simp [Clif.Inst.resultTypes] at hty
      subst hty
      exact List.eq_nil_of_length_eq_zero hlen
    · exact .inl ha
  exact (sa.root T.lower.ret T.lower.id T.lower _ _ [⟨1, true⟩] ⟨1, false⟩ [.inst ii] s #[] out s'
    tr' data_program.t686 term_686_kind hrules (holds_inst_cls s ii) hIs happ).2 v hout (by decide)

/-- **A statement's lowering** keeps `ClsIs` over a float-capable context; its result (of an
instruction with results) has registers of their classes. -/
theorem stmt_clsT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) (hsc : InstScopeT ctx)
    (hx : f.externs.all (Compile.sigE ·.2.sig) = true) (hcl : Cov.Clean ctx)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst) {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) (hIs : ClsIs ctx s s) :
    ClsIs ctx s s' ∧ ∀ v, out = some v → info.results ≠ [] → GoodV s'.classes v :=
  stmt_clsG hctx (lowerNoMatch_ofT hctx hsc hx) hcl hi hc h hIs

set_option maxRecDepth 100000 in
/-- **A terminator's lowering** keeps `ClsIs` (`termCall_cls` without a context invariant). -/
theorem termCall_clsT {f : Clif.Function} {ctx : Ctx} (hcl : Cov.Clean ctx)
    {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {t : Clif.Terminator} {data : V} (hd : termData (abiTerm f t) = .ok data) {targets : List Label}
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr))
    (hIs : ClsIs (termCtx ctx ti data) s s) : ClsIs (termCtx ctx ti data) s s' := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have hcl' := Cov.clean_termCtx hcl hd ti
  unfold termCallF at h
  have hlower : retOrTrap (abiTerm f t) = true →
      runTerm (termCtx ctx ti data) "lower" [.inst ti] s = .ok (out, s', tr) →
      ClsIs (termCtx ctx ti data) s s' := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower] at ht
    cases ht
    have hslot := termCtx_self hti data
    have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
        aRuleC program clsTab false [⟨1, true⟩] FA.top rl = true ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl [.inst ti]).run s0 ≠
            .ok (some env, s1) := by
      intro rl hrl
      cases hroot : termRootRule rl with
      | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
      | true =>
        have hf := List.all_eq_true.mp clsTerm_ok rl hrl
        simp only [hroot, Bool.not_true, Bool.false_or] at hf
        exact .inl hf
    have sa := soundAtC (md := clsModel hcl' s) (cfg := {}) (tab := clsTab) rfl clsTab_ok 1000000
    exact (sa.root T.lower.ret T.lower.id T.lower _ _ [⟨1, true⟩] FA.top [.inst ti] s #[] out s' tr'
      data_program.t686 term_686_kind hrules (holds_inst_cls s ti) hIs happ).1
  cases t with
  | ret vs => exact hlower rfl h
  | trap c => exact hlower rfl h
  | jump bc => exact branch_cls hcl' h hIs
  | brif c a b => exact branch_cls hcl' h hIs
  | brTable x d tb => exact branch_cls hcl' h hIs
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCallIndirect callee args et => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd

/-- The alias resolution keeps classes when every alias joins two vregs of one class. -/
theorem resolve_clsT {cls : Array RegClass} {a : Array (Option Nat)}
    (ha : ∀ n o : Nat, (a[n]?).join = some o → ∃ c, cls[n]? = some c ∧ cls[o]? = some c) :
    ∀ k r, RegCls cls r → RegCls cls (lowerFunction.resolve a k r) := by
  have hc : ∀ k n c, cls[n]? = some c → cls[chaseF (fun n => (a[n]?).join) k n]? = some c := by
    intro k
    induction k with
    | zero => intro n c h; exact h
    | succ k ih =>
      intro n c h
      simp only [chaseF]
      split
      · rename_i o ho
        obtain ⟨c', h1, h2⟩ := ha n o ho
        rw [h1] at h; cases h
        exact ih o _ h2
      · exact h
  intro k r hr
  cases r with
  | vreg n c =>
    rw [resolve_vreg]
    exact regCls_vreg.mpr (hc k n c (regCls_vreg.mp hr))
  | _ => cases k <;> exact hr

/-! ## The premise on results -/

/-- **The lowering returns each statement result in a vreg of the result's class**: in the
recorded lowering of `f` (`buildCtx f`'s context `ctx`, `lowBlocks`' record `bl`), when a
statement's `lower` returns `[.vreg o c]` for its result `r` (which `lowerFunction` then aliases
to `o`), `c` is `r`'s class `valClassOf ctx r` (that of its type). Decided by `resClassOkB`. -/
def ResClassOk (f : Clif.Function) : Prop :=
  ∀ ctx ranges st0 bl, buildCtx f = .ok (ctx, ranges, st0) →
  lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length = some bl →
  ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
    f.blocks[bi]? = some B → bl[bi]? = some L → B.body[j]? = some stm → L.sl[j]? = some sl →
  ∀ (k r o : Nat) (c : RegClass), stm.results[k]? = some r → sl.rss[k]? = some [.vreg o c] →
    valClassOf ctx r = c

/-- `ResClassOk`, decided on `f` (the recorded lowering is computed). -/
def resClassOkB (f : Clif.Function) : Bool :=
  match buildCtx f with
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length with
    | some bl => (f.blocks.zip bl).all fun (B, L) => (B.body.zip L.sl).all fun (stm, sl) =>
        (stm.results.zip sl.rss).all fun (r, rs) => match rs with
          | [.vreg _ c] => valClassOf ctx r == c
          | _ => true
    | none => true
  | .error _ => true

/-- **Soundness of `resClassOkB`.** -/
theorem resClassOk_of_resClassOkB {f : Clif.Function} (h : resClassOkB f = true) : ResClassOk f := by
  intro ctx ranges st0 bl hb hl bi B L j stm sl hB hL hj hsl k r o c hrk hok
  simp only [resClassOkB, hb, hl, List.all_eq_true] at h
  have h1 := h (B, L) (zip_mem_of_idx hB hL)
  have h2 := h1 (stm, sl) (zip_mem_of_idx hj hsl)
  have h3 := h2 (r, [.vreg o c]) (zip_mem_of_idx hrk hok)
  simpa using h3

/-- **Subset E meets `ResClassOk`**: its statements' results are int vregs (`stmt_cov`), and its
values are integers. -/
theorem resClassOk_of_lowerScope {f : Clif.Function} (hs : LowerScope f) : ResClassOk f := by
  intro ctx ranges st0 bl hb hl bi B L j stm sl hB hL hj hsl k r o c hrk hok
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hl
  obtain ⟨-, hc, -, -⟩ := (lowBlocks_spec hl).2 bi B L hB hL
  obtain ⟨info, hi, hic, hres⟩ := hcf.stmt bi B j stm hB hj
  obtain ⟨tr, hrun⟩ := hc j sl hsl
  rw [hstart bi L hL] at hrun
  have hne : info.results ≠ [] := by
    rw [hres]; exact List.ne_nil_of_mem (List.mem_of_getElem? hrk)
  obtain ⟨n, hn⟩ := (stmt_cov Cov.logicImmComplete hctx (Cov.clean_of_build hb) hi hic hrun).2 sl.rss rfl
    hne [.vreg o c] (List.mem_of_getElem? hok) (.vreg o c) (List.mem_singleton_self _)
  cases hn
  exact valClassOf_int hctx.valTyE r

/-! ## The edge blocks -/

/-- The shape of a typed edge block. -/
theorem edgeBlocksT_shape {f : Clif.Function} {ctx : Ctx} {B : Clif.Block} {L : BLow} {e : VBlock}
    (h : e ∈ edgeBlocksT f ctx B L) : (∃ tl, e.insts = #[.jump tl]) ∧ e.params = #[] ∧
    ∀ r ∈ e.branchArgs.toList, (∃ bc ∈ dests B.term, ∃ a ∈ bc.args, vregOf ctx a = r) ∨
      (∃ et T, IsTryWith B.term et ∧ L.tl = some T ∧ ∃ td ∈ et.dests, ∃ a ∈ td.args,
        tryEdgeArgT ctx T.regs.1 T.regs.2 a = r) := by
  unfold edgeBlocksT at h
  split at h
  · rename_i fn args et T hBt hT
    simp only [List.mem_filterMap, Option.map_eq_some_iff] at h
    obtain ⟨⟨td, l⟩, hp, tl, -, rfl⟩ := h
    refine ⟨⟨tl, rfl⟩, rfl, fun r hr => .inr ⟨et, T, .inl ⟨_, _, hBt⟩, hT, td, (List.of_mem_zip hp).1, ?_⟩⟩
    simpa using hr
  · rename_i fn args et T hBt hT
    simp only [List.mem_filterMap, Option.map_eq_some_iff] at h
    obtain ⟨⟨td, l⟩, hp, tl, -, rfl⟩ := h
    refine ⟨⟨tl, rfl⟩, rfl, fun r hr => .inr ⟨et, T, .inr ⟨_, _, hBt⟩, hT, td, (List.of_mem_zip hp).1, ?_⟩⟩
    simpa using hr
  · simp at h
  · simp only [List.mem_filterMap] at h
    obtain ⟨⟨bc, l⟩, hp, h⟩ := h
    split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨tl, -, rfl⟩ := h
      refine ⟨⟨tl, rfl⟩, rfl, fun r hr => .inl ⟨bc, (List.of_mem_zip hp).1, ?_⟩⟩
      simpa using hr

/-! ## The lowering -/

/-- **`lowerFunction`'s VCode meets `ClassesOkM`** (float scope, `ResClassOk`). -/
theorem classesOkM_lowerTF {f : Clif.Function} {vc : VCode} (hs : LowerScopeTF f)
    (hrc : ResClassOk f) (h : lowerFunction f = .ok vc) : ClassesOkM vc := by
  obtain ⟨ctx, ranges, st0, bl, hb, hl, hvb, -, hlf⟩ := lowerFunction_runT hs.externsE h
  obtain ⟨ctx', ranges', st0', pb, d, blk, hb', -, hI, hvc⟩ := loop_runT hs.externsE h
  rw [hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl, rfl⟩ := hb'
  have hlow := hI.low
  rw [List.take_of_length_le (Nat.le_refl _)] at hlow
  have hblk : bl = blk := by
    have := lowBlocks_eq f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) f.blocks 0 st0 f.blocks.length
    rw [hl, hlow] at this
    exact Option.some.inj this
  subst hblk
  have hcls : vc.classes = d.st.classes := by rw [hvc]; rfl
  have hctx : CtxInvT f ctx := ctxInvT_ofF hs hb
  have hnm : LowerNoMatch ctx := fun _ _ _ hi hc _ hr hroot =>
    lower_nonroot_nomatchTF_calls hctx ((ctxSpec_of hb).instScopeTF hs.subsetTF)
      (callsE_of_externs hs.externsE ctx) hi hc hr hroot
  have hcl : Cov.Clean ctx := Cov.clean_of_build hb
  have hsp := ctxSpec_of hb
  have hcf := hsp.facts
  obtain ⟨-, hstart⟩ := lowBlocks_start hl
  obtain ⟨-, hspec⟩ := lowBlocks_spec hl
  have hemp := lowBlocks_emptied hl
  obtain ⟨hfin, hLs⟩ := lowB_chain (stepsCls_driver ctx) f.blocks 0 st0 f.blocks.length bl d.st _ hlow
  have hsz0 : Sz st0 := by rw [hsp.st0]; simp [Sz]
  have hval0 : ∀ x r, ctx.valueReg? x = some r → RegCls st0.classes r := by
    intro x r hx
    have hr := hctx.valueReg x r hx
    subst hr
    have hxl : x < ctx.valReg.size := by
      unfold Ctx.valueReg? at hx
      cases h' : ctx.valReg[x]? with
      | none => rw [h'] at hx; cases hx
      | some _ => exact (Array.getElem?_eq_some_iff.mp h').1
    rw [hcf.size.2.1] at hxl
    rw [hsp.st0, regCls_vreg]
    simp [Array.getElem?_range, hxl, valClassOf, Ctx.valueType?]
  have hIs : ∀ s, ClsStep st0 s → ClsIs ctx s s := fun s hs0 =>
    ⟨sz_step hs0 hsz0, fun x r hx => regCls_step hs0 (hval0 x r hx),
     (fun r hr => by rw [hcf.tryRegs] at hr; cases hr), (fun r hr => by rw [hcf.tryRegs] at hr; cases hr),
     ⟨[], by simp, by simp⟩⟩
  have hvalF : ∀ x, x ∈ valueDefs f → RegCls d.st.classes (vregOf ctx x) := fun x hx => by
    obtain ⟨-, t, ht, hr⟩ := hcf.vals x hx
    have := regCls_step hfin (hval0 x _ hr)
    rwa [vregOf, valClassOf_of_type ht]
  -- statements
  have hstm : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
      f.blocks[bi]? = some B → bl[bi]? = some L →
      B.body[j]? = some stm → L.sl[j]? = some sl →
      (∀ m ∈ sl.st'.emitted.toList, RegsFrom (RegCls d.st.classes) m) ∧
      (stm.results ≠ [] → GoodV d.st.classes (.regsVec sl.rss)) ∧
      ∀ (k r o : Nat) (c : RegClass), stm.results[k]? = some r → sl.rss[k]? = some [.vreg o c] →
        valClassOf ctx r = c := by
    intro bi B L j stm sl hB hL hj hsl
    obtain ⟨-, hc, -, -⟩ := hspec bi B L hB hL
    obtain ⟨info, hi, hic, hres⟩ := hcf.stmt bi B j stm hB hj
    obtain ⟨tr, hrun⟩ := hc j sl hsl
    rw [hstart bi L hL] at hrun
    have hLm := hLs L (List.mem_of_getElem? hL)
    have hslm := hLm.2.2.1 sl (List.mem_of_getElem? hsl)
    obtain ⟨hI', hout⟩ := stmt_clsG hctx hnm hcl hi hic hrun (hIs sl.st hslm.1)
    obtain ⟨ms, hms, hall⟩ := hI'.emitted
    rw [hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)] at hms
    refine ⟨fun m hm => ?_, fun hne => fun r hr => regCls_step hslm.2
      (hout _ rfl (by rw [hres]; exact hne) r hr), fun k r o c hrk hok => ?_⟩
    · rw [hms] at hm
      exact (hall m (by simpa using hm)).mono fun r hr => regCls_step hslm.2 hr
    · exact hrc ctx ranges st0 bl hb hl bi B L j stm sl hB hL hj hsl k r o c hrk hok
  -- terminators
  have hterm : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
      (∀ m ∈ L.tst'.emitted.toList, RegsFrom (RegCls d.st.classes) m) ∧
      (∀ T, L.tl = some T → ∀ r ∈ T.regs.1 ++ T.regs.2, IntCls d.st.classes r) := by
    intro bi B L hB hL
    obtain ⟨-, -, htst, nl0, nl', hlt⟩ := hspec bi B L hB hL
    obtain ⟨hn, hy⟩ := lowTerm_spec hlt
    have hLm := hLs L (List.mem_of_getElem? hL)
    have hph : ctx.insts[L.start + B.body.length]? = some ⟨.op .unit, [], [], none⟩ := by
      rw [hstart bi L hL]; exact hcf.term bi B hB
    cases ht : B.term.isTry with
    | false =>
      obtain ⟨htl, hd, out, tr, hc⟩ := hn ht
      have hI2 := termCall_clsT hcl hph hd hc (clsIs_termCtx (hIs L.tst hLm.1) _ _)
      obtain ⟨ms, hms, hall⟩ := hI2.emitted
      rw [htst] at hms
      refine ⟨fun m hm => ?_, fun T hT => by rw [htl] at hT; cases hT⟩
      rw [hms] at hm
      exact (hall m (by simpa using hm)).mono fun r hr => regCls_step hLm.2.1 hr
    | true =>
      obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := by
        cases hB' : B.term <;> rw [hB'] at ht <;> simp [Clif.Terminator.isTry] at ht
        · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
        · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
      obtain ⟨T, hT, hd, -, -, hr, -, out, tr, hc⟩ := hy et het
      obtain ⟨-, hr1⟩ := tryRegsOf_cls hr
      have hst1 : ClsStep st0 T.st1 := hLm.2.2.2 T hT
      have hs1' : ClsStep T.st1 L.tst' := clsStep_trans (clsStep_clear _) (runTerm_cls hc)
      have hgoodT : ∀ r ∈ T.regs.1 ++ T.regs.2, IntCls T.st1.classes r := hr1 (sz_step hLm.1 hsz0)
      have hIs' : ClsIs (tryCtx ctx (L.start + B.body.length) L.data T.regs)
          { T.st1 with emitted := #[] } { T.st1 with emitted := #[] } :=
        ⟨sz_step hst1 hsz0, fun x r hx => regCls_step hst1 (hval0 x r hx),
         fun r hr' => (hgoodT r (List.mem_append_left _ hr')).1,
         fun r hr' => (hgoodT r (List.mem_append_right _ hr')).1, ⟨[], by simp, by simp⟩⟩
      have hI2 := tryCall_cls hcl hd hc hIs'
      obtain ⟨ms, hms, hall⟩ := hI2.emitted
      refine ⟨fun m hm => ?_, fun T' hT' r hr' => ?_⟩
      · rw [hms] at hm
        exact (hall m (by simpa using hm)).mono fun r hr => regCls_step hLm.2.1 hr
      · rw [hT] at hT'; cases hT'
        exact intCls_step (clsStep_trans hs1' hLm.2.1) (hgoodT r hr')
  -- the alias resolution keeps classes
  have halias : ∀ n o : Nat, ((aliasArr (aliasOf f bl))[n]?).join = some o →
      ∃ c, d.st.classes[n]? = some c ∧ d.st.classes[o]? = some c := by
    intro n o hno
    have hmem := (faithful_arr (aliasOf f bl)).some n o hno
    rw [aliasOf_eq] at hmem
    simp only [List.mem_flatMap, stmtAl, List.mem_filterMap] at hmem
    obtain ⟨⟨B, L⟩, hBL, ⟨stm, sl⟩, hss, ⟨r, rs⟩, hrrs, hm⟩ := hmem
    split at hm
    · rename_i out c' heq
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      obtain ⟨bi, hB, hL⟩ := zip_idx hBL
      obtain ⟨j, hj, hsl⟩ := zip_idx hss
      obtain ⟨k, hrk, hsk⟩ := zip_idx hrrs
      have hB' : B ∈ f.blocks := List.mem_of_getElem? hB
      have hrm : r ∈ stm.results := List.mem_of_getElem? hrk
      have hrss : rs ∈ sl.rss := List.mem_of_getElem? hsk
      subst heq
      have hne : stm.results ≠ [] := List.ne_nil_of_mem hrm
      obtain ⟨-, hg, hcl'⟩ := hstm bi B L j stm sl hB hL hj hsl
      have hceq := hcl' k r out c' hrk hsk
      refine ⟨c', ?_, regCls_vreg.mp (hg hne _ (by
        simp only [V.regsIn, List.mem_flatten]; exact ⟨_, hrss, List.mem_singleton_self _⟩))⟩
      have := regCls_vreg.mp (hvalF r (mem_valueDefs_result hB' (List.mem_of_getElem? hj) hrm))
      rwa [hceq] at this
    · cases hm
  have hR := resolve_clsT halias ((aliasArr (aliasOf f bl)).size + 1)
  -- the raw code
  have hraw : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
      ∀ m ∈ (rawBlockT f ctx bl bi B).insts.toList, RegsFrom (RegCls d.st.classes) m := by
    intro bi B L hB hL m hm
    simp only [rawBlockT, List.toList_toArray, List.mem_append, List.mem_flatten] at hm
    rcases hm with (hpre | ⟨sg, hsg, hm0⟩) | htseg
    · unfold preT at hpre
      split at hpre
      · rename_i B0 hB0
        have hB0m : B0 ∈ f.blocks := List.mem_of_getElem? hB0
        simp only [List.mem_cons] at hpre
        rcases hpre with rfl | hpre
        · refine args_regsFrom fun q hq => ?_
          simp only [entryRegsT, List.mem_filterMap] at hq
          obtain ⟨q0, hq0, hq⟩ := hq
          unfold entryRegOfT at hq
          split at hq
          · cases hq
            exact hvalF _ (mem_valueDefs_param hB0m (List.of_mem_zip (List.of_mem_zip hq0).1).1)
          · cases hq
        · simp only [entryLoadsT, List.mem_filterMap] at hpre
          obtain ⟨q, hq0, hq⟩ := hpre
          unfold entryLoadOfT at hq
          split at hq
          · cases hq
            intro g hg
            have hv := hg _ (hvalF _ (mem_valueDefs_param hB0m (List.of_mem_zip (List.of_mem_zip hq0).1).1))
            cases hc : (vregOf ctx q.1.1.1).homeCls <;>
              simp [stackArgLoad, hc, MInst.mapRegs, AMode.mapRegs, hv]
          · cases hq
      · simp at hpre
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hsg
      unfold segT at hm0
      rw [hB, hL] at hm0
      simp only at hm0
      split at hm0
      · rename_i stm sl hstm' hsl
        simp only [List.mem_map, mapRegs_id] at hm0
        obtain ⟨m1, hm1, rfl⟩ := hm0
        rcases List.mem_append.mp hm1 with hm1 | hm1
        · exact (hstm bi B L j stm sl hB hL hstm' hsl).1 m1 hm1
        · simp only [extraOfT, List.mem_filterMap] at hm1
          obtain ⟨⟨r, rs⟩, hrrs, hq⟩ := hm1
          split at hq
          · cases hq
          · rename_i out hnv hout
            cases hq
            have hrv := hvalF r (mem_valueDefs_result (List.mem_of_getElem? hB) (List.mem_of_getElem? hstm')
              (List.of_mem_zip hrrs).1)
            have hreal : ∀ n c, out ≠ .vreg n c := fun n c he => hnv n c he
            intro g hg
            simp [MInst.mapRegs, hg _ hrv, hg _ (regCls_real hreal)]
          · cases hq
      · simp at hm0
    · unfold tseg at htseg
      rw [hL] at htseg
      simp only [List.mem_map, mapRegs_id] at htseg
      obtain ⟨m1, hm1, rfl⟩ := htseg
      have ht := (hterm bi B L hB hL).1
      rcases fixTry_mem hm1 with hm1 | ⟨c, ti, rfl, hc⟩
      · exact ht _ hm1
      · exact regsFrom_tryCall (ht _ hc)
  -- the final code
  unfold ClassesOkM
  rw [hvb, hcls]
  have hblocks : ∀ vb ∈ (vcBlocksOfT f ctx bl).toList, ∃ (vb0 : VBlock) (bi : Nat) (B : Clif.Block) (L : BLow),
      f.blocks[bi]? = some B ∧
      bl[bi]? = some L ∧ vb = fixBlock (lowerFunction.resolve (aliasArr (aliasOf f bl))
        ((aliasArr (aliasOf f bl)).size + 1)) vb0 ∧
      (vb0 = rawBlockT f ctx bl bi B ∨ vb0 ∈ edgeBlocksT f ctx B L) := by
    intro vb hvb'
    simp only [vcBlocksOfT, List.toList_toArray, List.mem_map, List.mem_append, List.mem_flatMap] at hvb'
    obtain ⟨vb0, h1, rfl⟩ := hvb'
    rcases h1 with ⟨p, hp, rfl⟩ | ⟨p, hp, he⟩
    · have := List.mem_zipIdx_iff_getElem?.mp hp
      rw [List.getElem?_zip_eq_some] at this
      exact ⟨_, p.2, p.1.1, p.1.2, this.1, this.2, rfl, .inl rfl⟩
    · obtain ⟨bi, hB, hL⟩ := zip_idx (show (p.1, p.2) ∈ f.blocks.zip bl from hp)
      exact ⟨vb0, bi, p.1, p.2, hB, hL, rfl, .inr he⟩
  refine ⟨fun vb hvb' m hm => ?_, fun vb hvb' r hr => ?_⟩
  · obtain ⟨vb0, bi, B, L, hB, hL, rfl, hraw' | hedge⟩ := hblocks vb hvb'
    · simp only [fixBlock, Array.toList_map, List.mem_map] at hm
      obtain ⟨m0, hm0, rfl⟩ := hm
      subst hraw'
      exact instCls_mapRegs (hraw bi B L hB hL m0 hm0) hR
    · obtain ⟨⟨tl, htl⟩, -, -⟩ := edgeBlocksT_shape hedge
      simp only [fixBlock, htl, Array.toList_map, List.mem_map] at hm
      obtain ⟨m0, hm0, rfl⟩ := hm
      simp at hm0
      subst hm0
      exact instCls_mapRegs (fun g _ => rfl) hR
  · obtain ⟨vb0, bi, B, L, hB, hL, rfl, hraw' | hedge⟩ := hblocks vb hvb'
    · subst hraw'
      have hB' : B ∈ f.blocks := List.mem_of_getElem? hB
      simp only [fixBlock, rawBlockT, List.mem_append, Array.toList_map, List.mem_map] at hr
      rcases hr with hr | ⟨r0, hr0, rfl⟩
      · split at hr
        · simp at hr
        · simp only [List.mem_map] at hr
          obtain ⟨p, hp, rfl⟩ := hr
          exact ⟨_, _, rfl, regCls_vreg.mp (hvalF _ (mem_valueDefs_param hB' hp))⟩
      · split at hr0
        · rename_i bc hBt
          simp only [List.mem_map] at hr0
          obtain ⟨a, ha, rfl⟩ := hr0
          obtain ⟨tb, -, -, hargs⟩ := hlf.args B hB' bc (by simp [hBt, dests])
          have hg := hR _ (regCls_step hfin (hval0 a _ (hargs a ha)))
          rw [vregOf, resolve_vreg] at hg ⊢
          exact ⟨_, _, rfl, regCls_vreg.mp hg⟩
        · simp at hr0
    · obtain ⟨-, hp, hba⟩ := edgeBlocksT_shape hedge
      have hB' : B ∈ f.blocks := List.mem_of_getElem? hB
      simp only [fixBlock, hp, Array.toList_map, List.mem_append, List.mem_map] at hr
      rcases hr with hr | ⟨r0, hr0, rfl⟩
      · simp at hr
      · have hg0 : RegCls d.st.classes r0 ∧ ∃ n c, r0 = .vreg n c := by
          rcases hba r0 hr0 with ⟨bc, hbc, a, ha, rfl⟩ | ⟨et, T, het, hT, td, htd, a, ha, rfl⟩
          · obtain ⟨tb, -, -, hargs⟩ := hlf.args B hB' bc hbc
            exact ⟨regCls_step hfin (hval0 a _ (hargs a ha)), a, _, rfl⟩
          · obtain ⟨T', hT', hk⟩ := hlf.tryArgs bi B L et hB hL het
            rw [hT] at hT'; cases hT'
            obtain ⟨k, hk'⟩ := List.mem_iff_getElem?.mp htd
            have hka := (hk k td hk').2 a ha
            have hTg := (hterm bi B L hB hL).2 T hT
            cases a with
            | val v => exact ⟨regCls_step hfin (hval0 v _ hka), v, _, rfl⟩
            | ret i =>
              simp only [tryEdgeArgT]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hka.2, Option.getD_some]
              obtain ⟨h1, n, hn⟩ := hTg _ (List.mem_append_left _ (List.getElem_mem _))
              exact ⟨h1, n, _, hn⟩
            | exn i =>
              simp only [tryEdgeArgT]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hka.2, Option.getD_some]
              obtain ⟨h1, n, hn⟩ := hTg _ (List.mem_append_right _ (List.getElem_mem _))
              exact ⟨h1, n, _, hn⟩
        obtain ⟨n, c, rfl⟩ := hg0.2
        have hg := hR _ hg0.1
        rw [resolve_vreg] at hg ⊢
        exact ⟨_, _, rfl, regCls_vreg.mp hg⟩

/-- **`lowerFunction`'s VCode meets `ClassesOkM`** (typed scope, `ResClassOk`). -/
theorem classesOkM_lowerT {f : Clif.Function} {vc : VCode} (hs : LowerScopeT f)
    (hrc : ResClassOk f) (h : lowerFunction f = .ok vc) : ClassesOkM vc :=
  classesOkM_lowerTF hs.toTF hrc h

/-- **`ClassesHyp` over the typed scope**: on `Dominated`, `LowerScopeT` input whose lowering
returns results in vregs of their types' classes (`ResClassOk`), the prepared code's vreg classes
are consistent. -/
theorem classesHypT (f : Clif.Function) (vc vcp : VCode) (hd : Dominated f) (hs : LowerScopeT f)
    (hrc : ResClassOk f) (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp) :
    ClassesOk vcp :=
  classesOk_of (classesOkM_prepare hp (prepDomain_ofT hd hs hl) (classesOkM_lowerT hs hrc hl))

/-- **Integer specialization**: `ClassesHyp` from `classesHypT` and `resClassOk_of_lowerScope`. -/
theorem classesHyp_of_T : ClassesHyp := fun f vc vcp hd hs hl hp =>
  classesHypT f vc vcp hd hs.toT (resClassOk_of_lowerScope hs) hl hp

/-! ## `ClassesOk`, decided -/

/-- **`ClassesOk`, decided** on a VCode: every operand's vreg, every block parameter and branch
argument has the class `classes` records. -/
def classesOkB (vc : VCode) : Bool :=
  vc.blocks.all fun vb =>
    vb.insts.all (fun i => match i.operands with
      | .ok ops => ops.all fun o => vc.classes[o.vreg]? == some o.cls
      | .error _ => true) &&
    (vb.params.toList ++ vb.branchArgs.toList).all fun r => match r with
      | .vreg n c => vc.classes[n]? == some c
      | _ => false

/-- **Soundness of `classesOkB`.** -/
theorem classesOk_of_classesOkB {vc : VCode} (h : classesOkB vc = true) : ClassesOk vc := by
  simp only [classesOkB, Array.all_eq_true, Bool.and_eq_true] at h
  refine ⟨fun b vb k i ops hvb hi hops o ho => ?_, fun b vb hvb r hr => ?_⟩
  · obtain ⟨hb, rfl⟩ := Array.getElem?_eq_some_iff.mp hvb
    obtain ⟨hk, rfl⟩ := Array.getElem?_eq_some_iff.mp hi
    have h1 := (h b hb).1 k hk
    rw [hops] at h1
    simp only [Array.all_eq_true] at h1
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp ho)
    simpa using h1 j hj
  · obtain ⟨hb, rfl⟩ := Array.getElem?_eq_some_iff.mp hvb
    have h2 := List.all_eq_true.mp (h b hb).2 r hr
    cases r with
    | vreg n c => exact ⟨n, c, rfl, by simpa using h2⟩
    | _ => simp at h2

end Backend.Proof.Spill
