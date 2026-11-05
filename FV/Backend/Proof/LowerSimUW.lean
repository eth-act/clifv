import FV.Backend.Proof.LowerSimU

/-!
# The driver simulation with unwinding, generic in the world type (S10f, #233)

`LowerSimU.lean`'s driver (`sim_runX`) fixes the world type to `Arm.ArmState` (`Sem`, `XRaise`,
`RaiseHyp`): its raising steps run M4's rule theorems (stated for `Sem`) on a probe
(`stmt_raise`, `try_raise`). The non-interference proof runs the driver on pairs of worlds
(`E2E.pairSem`), so this file states the driver with unwinding for any world type `W`:

* `RaiseFn W`: the callees' exceptional results on worlds `W` (`XRaise.raise` at
  `W = Arm.ArmState`); `VUnwFromW`: `E2E.VUnwFrom` for it.
* `RaiseCalls`, `RaiseTries`: what the raising steps use of the lowered code of a raising
  statement / `try_call` — exactly the conclusions of `stmt_raise`/`try_raise`, as contracts on
  `sem` (as `InstCalls`/`TryCalls` are M4's for the normal edge); `RaiseHypW` bundles them with
  the outgoing area's `TryStack`.
* `raiseHypW_of`: at `W = Arm.ArmState`, `RaiseHyp` gives `RaiseHypW` (by `stmt_raise`,
  `try_raise`).
* `stmt_step_raiseW`, `enter_matchUW`, `term_step_try_exnW`, `RunOkUW`, `sim_runXW`: the
  proofs of `LowerSimU.lean`, with `RaiseHypW` for `RaiseHyp`.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- The callees' exceptional results on worlds `W`: `rz d uses w = some (obj, w')`: the callee
of the call (`d`: `bl`'s symbol, `none` for `blr`) raised `obj`, the world after the unwinder
restored the call being `w'`. -/
abbrev RaiseFn (W : Type) := Option String → List CV → W → Option (BitVec 64 × W)

/-- `E2E.VUnwFrom` on worlds `W`: from `vs`, the VCode run reaches a `call` whose callee raises
`obj` (`rz`) and whose step ends the activation with world `w'`. -/
def VUnwFromW {W : Type} (vc : VCode) (sem : ISem CV W) (rz : RaiseFn W) (vs : VState CV W)
    (obj : BitVec 64) (w' : W) : Prop :=
  ∃ b k ρ w vb info ops outs, Star (VStep vc sem) (.run vs) (.run ⟨b, k, ρ, w⟩) ∧
    vc.blocks[b]? = some vb ∧ vb.insts[k]? = some (.call info) ∧
    (MInst.call info).operands = .ok ops ∧
    rz (callDest info) (vuses ops ρ) w = some (obj, w') ∧
    sem (.call info) (vuses ops ρ) w = some (outs, w', .halt) ∧
    outs.length = (ops.toList.filter Operand.isDef).length

theorem VUnwFromW.prefix {W : Type} {vc : VCode} {sem : ISem CV W} {rz : RaiseFn W}
    {vs vs' : VState CV W} {obj : BitVec 64} {w' : W}
    (h : Star (VStep vc sem) (.run vs) (.run vs')) (h' : VUnwFromW vc sem rz vs' obj w') :
    VUnwFromW vc sem rz vs obj w' := by
  obtain ⟨b, k, ρ, w, vb, info, ops, outs, hs, h1⟩ := h'
  exact ⟨b, k, ρ, w, vb, info, ops, outs, h.trans hs, h1⟩

/-- `VUnwFromW` at `W = Arm.ArmState` is `E2E.VUnwFrom`. -/
theorem vUnwFromW_iff {vc : VCode} {sem : Sem} {XR : XRaise} {vs : VState CV Arm.ArmState}
    {obj : BitVec 64} {w' : Arm.ArmState} :
    VUnwFromW vc sem XR.raise vs obj w' ↔ E2E.VUnwFrom vc sem XR vs obj w' := Iff.rfl

/-! ## The contracts of the raising code -/

/-- **The lowered code of a raising statement** (`stmt_raise`'s conclusion as a contract on
`sem`): the code of a `call`/`call_indirect` statement whose extern unwinds (exception `e`,
memory `m`), if it contains a call, runs to a `call` whose callee raises (`rz`) an object related
to `e`, the world after the unwinder related to `m`, where the activation ends. -/
def RaiseCalls {W : Type} (f : Clif.Function) (sem : ISem CV W) (rz : RaiseFn W)
    (MR : MemRelTW W) (env : Clif.XEnv) (p : Clif.Program) : Prop :=
  ∀ (ctx : Ctx) (ii : Nat) (info : IInfo) (inst : Clif.Inst) (st : LState) (rss : List (List Reg))
    (st' : LState) (tr : List Isle.RuleId), CtxInv f ctx → Compile.functionE f = true →
    (∃ B ∈ f.blocks, ∃ stm ∈ B.body, stm.inst = inst) →
    ctx.insts[ii]? = some info → info.clif = some inst → IndSigOk f (indSigs f) inst →
    st.emitted = #[] → ValsBelow ctx st →
    runTerm ctx "lower" [.inst ii] st = .ok (some (.regsVec rss), st', tr) →
    (∃ ci, MInst.call ci ∈ st'.emitted.toList) →
    ∀ {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : W},
    fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → MR fr.slots cm w →
    ∀ {e : Clif.Exn} {m : Clif.Mem}, instRaise env p fr cm inst = some (e, m) →
    UsesOk st fr st'.emitted.toList ∧ ∃ k ci ops ρ₁ w₁ obj w',
      seqRun sem st'.emitted.toList ρ w =
        some (.stop k (.call ci) ops ρ₁ w₁ ((defCons (.call ci)).map fun _ => ofX 0) w' .halt) ∧
      rz (callDest ci) (vuses ops ρ₁) w₁ = some (obj, w') ∧ E2E.ExnRel e obj ∧
      MR fr.slots m w' ∧
      ((defCons (.call ci)).map fun _ => ofX 0).length =
        (ops.toList.filter Operand.isDef).length

/-- **The lowered code of a raising `try_call`** (`try_raise`'s conclusion as a contract on
`sem`; `out`: the outgoing area the direct calls' stack arguments fit): the code of a
`try_call`/`try_call_indirect` whose extern unwinds, when the code before the call contains no
call and the call's shape is supported (`tryUOk`), runs to its `tryCall`, whose callee raises an
object related to `e` (the world related to `m`) and which continues at the first handler. -/
def RaiseTries {W : Type} (f : Clif.Function) (sem : ISem CV W) (rz : RaiseFn W)
    (MR : MemRelTW W) (env : Clif.XEnv) (p : Clif.Program) (out : Nat) : Prop :=
  ∀ {ctx : Ctx}, CtxInv f ctx → ∀ {ti : Nat} {et : Clif.ExnTable} {data : V}
    {sig : Clif.Signature} {items : List (Option Nat)} {targets : List Label} {info : TryInfo}
    {trs : List Reg × List Reg} {lo st1 : LState} {outv : V} {st' : LState}
    {tr : List Isle.RuleId} {ci : Clif.Inst},
    ((∃ fn args, ci = .call fn args ∧ tryCallData f (.tryCall fn args et) = .ok data ∧
        ∀ e, f.extern? fn = some e → SigStackOk e.sig out) ∨
      (∃ callee args, ci = .callIndirect et.sig callee args ∧
        tryCallData f (.tryCallIndirect callee args et) = .ok data ∧ sig ∈ indSigs f ∧
        sig.params.length ≤ 8)) →
    exnTableOpnd f et = .ok (sig, items) →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ →
    tryInfoOf sig items targets = some info → tryRegsOf sig lo = some (trs, st1) →
    ValsBelow ctx lo →
    runTerm (tryCtx ctx ti data trs) "lower_branch" [.inst ti, .labels targets]
      { st1 with emitted := #[] } = .ok (some outv, st', tr) →
    ∀ {pre : List MInst} {c : CallInfo}, st'.emitted.toList = pre ++ [.call c] →
    (∀ m ∈ pre, ∀ ci, m ≠ .call ci) → tryUOk c info = true →
    ∀ {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : W},
    fr.func = ctx.func → ValsHeld fr ρ → DFGCons (tryCtx ctx ti data trs) fr →
    MR fr.slots cm w → ∀ {e : Clif.Exn} {m : Clif.Mem}, instRaise env p fr cm ci = some (e, m) →
    UsesOk { st1 with emitted := #[] } fr st'.emitted.toList ∧ ∃ ops ρ₁ w₁ obj w',
      seqRun sem (pre ++ [.tryCall c info]) ρ w =
        some (.stop pre.length (.tryCall c info) ops ρ₁ w₁ (payloadOuts (.call c) obj) w'
          (.goto 0)) ∧
      rz (callDest c) (vuses ops ρ₁) w₁ = some (obj, w') ∧ E2E.ExnRel e obj ∧
      MR fr.slots m w'

/-- **What the raising steps assume** (`RaiseHyp`, generic in the world type): the contracts of
the raising code, and the outgoing area holding every `try_call`'s stack arguments. -/
structure RaiseHypW {W : Type} (f : Clif.Function) (sem : ISem CV W) (rz : RaiseFn W)
    (MR : MemRelTW W) (env : Clif.XEnv) (p : Clif.Program) (out : Nat) : Prop where
  calls : RaiseCalls f sem rz MR env p
  tries : RaiseTries f sem rz MR env p out
  tstk : TryStack f out

/-- **`RaiseHyp` gives `RaiseHypW`** at `W = Arm.ArmState` (`stmt_raise`, `try_raise`). -/
theorem raiseHypW_of {f : Clif.Function} {sem : Sem} {MR : MemRelT} {env : Clif.XEnv}
    {F : BitVec 64 → Prop} {X : ExtSem} {XR : XRaise} {sb : Nat} {syms : String → Option Nat}
    {out : Nat} (HR : RaiseHyp f sem MR env F X XR sb syms out) (p : Clif.Program) :
    RaiseHypW f sem XR.raise MR env p out where
  calls := by
    intro ctx ii info inst st rss st' tr hctx hE hin hi hc hsig hemp hvb hrun hcall fr cm ρ w hf hvh
      hdc hmr e m hr
    exact stmt_raise HR.rs HR.ref HR.mem HR.mrs HR.outOk HR.mro HR.stk HR.xr HR.xri HR.sym
      HR.mrsyms hctx hE hin hi hc hsig hemp hvb hrun hcall hf hvh hdc hmr hr
  tries := by
    intro ctx hctx ti et data sig items targets info trs lo st1 outv st' tr ci hT he hph hinfo
      hregs hvb hrun pre c hms hpre hok fr cm ρ w hf hvh hdc hmr e m hr
    exact try_raise HR.rs HR.ref HR.mem HR.mrs HR.outOk HR.xr HR.xri HR.sym HR.mrsyms hctx hT he hph
        hinfo hregs hvb hrun hms hpre hok hf hvh hdc hmr hr
  tstk := HR.tstk

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {W : Type}
  {sem : ISem CV W} {MR : MemRelTW W} {env : Clif.XEnv} {p : Clif.Program}
  {slots : List (Clif.SlotId × Nat)}
  {rz : RaiseFn W} {out : Nat}

/-! ## A raising statement -/

/-- `VUnwFromW`, executing only from configurations satisfying `P` (the raising `call`'s
included). -/
def VUnwFromWP (P : VConf CV W → Prop) (vc : VCode) (sem : ISem CV W) (rz : RaiseFn W)
    (vs : VState CV W) (obj : BitVec 64) (w' : W) : Prop :=
  ∃ b k ρ w vb info ops outs, StarP (VStep vc sem) P (.run vs) (.run ⟨b, k, ρ, w⟩) ∧
    P (.run ⟨b, k, ρ, w⟩) ∧
    vc.blocks[b]? = some vb ∧ vb.insts[k]? = some (.call info) ∧
    (MInst.call info).operands = .ok ops ∧
    rz (callDest info) (vuses ops ρ) w = some (obj, w') ∧
    sem (.call info) (vuses ops ρ) w = some (outs, w', .halt) ∧
    outs.length = (ops.toList.filter Operand.isDef).length

theorem VUnwFromWP.toVUnwFromW {P : VConf CV W → Prop} {vs : VState CV W} {obj : BitVec 64}
    {w' : W} (h : VUnwFromWP P vc sem rz vs obj w') : VUnwFromW vc sem rz vs obj w' := by
  obtain ⟨b, k, ρ, w, vb, info, ops, outs, hs, -, h1⟩ := h
  exact ⟨b, k, ρ, w, vb, info, ops, outs, hs.star, h1⟩

/-- **A `call`/`call_indirect` statement whose extern unwinds**, with the zone of the run (the
statement's segment). -/
theorem stmt_step_raiseWP (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHypW f sem rz MR env p out)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    {e : Clif.Exn} {mm : Clif.Mem} (hr : instRaise env p s.frame s.mem stm.inst = some (e, mm)) :
    ∃ B j, f.blocks[b]? = some B ∧ B.body[j]? = some stm ∧ k = pos f R bl b j ∧
      ∃ obj w', VUnwFromWP (AtSeg b k (seg f R bl b j).length) vc sem rz ⟨b, k, ρ, w⟩ obj w' ∧
        E2E.ExnRel e obj ∧ MR slots mm w' := by
  obtain ⟨hcall, hfunc, hslots, hmem, B, j, hB, hterm, hj, hbd, hk, hheld, hcons⟩ := hm
  simp only at hk hheld hcons hB hmem
  subst hk
  obtain ⟨hjlt, hstm, hrest⟩ := drop_cons_split (hbd ▸ hbody)
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, hsllen, hstmts, -, -, -, -, hcode, htne, -⟩ := H.shape.blk b B L hB hL
  obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
    ⟨L.sl[j]'(by omega), List.getElem?_eq_getElem _⟩
  obtain ⟨⟨info, hinfo, hclif, hres⟩, hemp, hst0, ⟨tr, hrun⟩, -⟩ := hstmts j stm sl hstm hsl
  have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
  have hstmmem : stm ∈ B.body := List.mem_of_getElem? hstm
  have hok := H.insts ctx (L.start + j) info stm.inst sl.st sl.rss sl.st' tr
    H.shape.ctxInv ⟨B, hBmem, stm, hstmmem, rfl⟩ H.subE hinfo hclif (H.indSig B hBmem stm hstmmem) hemp
    (fun x r h => Nat.lt_of_lt_of_le (H.shape.valsBelow x r h) hst0) hrun
  obtain ⟨hargs, -, -, -, hnoclob⟩ := H.cert.stmt b B L j stm sl hB hL hstm hsl
  let fr' := restrict s.frame (A b j)
  let ρ₀ : Nat → CV := fun n => ρ (gn n)
  have hvh : ValsHeld fr' ρ₀ := by
    intro x v hx
    have hxA : x ∈ A b j := restrict_regs_isSome (by rw [hx]; rfl)
    obtain ⟨v', hv', hh⟩ := hheld x hxA
    rw [restrict_regs_of_mem hxA, hv'] at hx
    cases hx
    exact hh
  have hr' : instRaise env p fr' s.mem stm.inst = some (e, mm) := by
    rw [instRaise_congr (fr := s.frame) (fr' := fr') rfl _ _
      (fun x hx => restrict_regs_of_mem (hargs x hx))]
    exact hr
  have hkind : (∃ fn args, stm.inst = .call fn args) ∨
      ∃ sig callee args, stm.inst = .callIndirect sig callee args := by
    cases hi : stm.inst with
    | call fn args => exact .inl ⟨fn, args, rfl⟩
    | callIndirect sig callee args => exact .inr ⟨sig, callee, args, rfl⟩
    | _ => rw [hi] at hr; simp [instRaise] at hr
  obtain ⟨hU, k', ci, ops, ρ₁, w₁, obj, w', hsr, hra, hex, hmr', -⟩ :=
    HR.calls ctx (L.start + j) info stm.inst sl.st sl.rss sl.st' tr
      H.shape.ctxInv H.subE ⟨B, hBmem, stm, hstmmem, rfl⟩ hinfo hclif
      (H.indSig B hBmem stm hstmmem) hemp
      (fun x r h => Nat.lt_of_lt_of_le (H.shape.valsBelow x r h) hst0) hrun
      (HU.calls b B L j stm sl hB hL hstm hsl hkind) (fr := fr')
      (by simp [fr', restrict, hfunc, H.shape.ctxInv.func]) hvh hcons
      (by simpa [fr', restrict, hslots] using hmem) hr'
  let D : Nat → Prop := fun n => sl.st.nextVreg ≤ n ∧ n < sl.st'.nextVreg
  have hD : ∀ d, D d → gn d = d := fun d hd => H.shape.temps d (by simp only [D] at hd; omega)
  have hdefs : ∀ m ∈ sl.st'.emitted.toList, ∀ d ∈ vdefs m, D d := hok.defs
  have hAg : Agree gn D ρ₀ ρ := fun _ _ => rfl
  have huses : ∀ m ∈ sl.st'.emitted.toList, ∀ u ∈ vuseNums m, D u ∨ ¬ D (gn u) := by
    intro m hm u hu
    rcases hU m hm u hu with h | h
    · by_cases h' : u < sl.st'.nextVreg
      · exact .inl ⟨h, h'⟩
      · right
        rw [H.shape.temps u (by omega)]
        intro hd; exact h' hd.2
    · right; exact hnoclob u (restrict_regs_isSome h)
  have hren := seqRun_rename (sem := sem) (ρ₀ := ρ₀) (ρ := ρ) (w := w) H.shape.ren
    (H.dsem.rename R gn H.shape.ren) hD hdefs
  obtain ⟨ρ₁', hsr', hA1, -⟩ := (hren huses hAg).2 hsr
  have hsegat := (seg_at hcode htne hjlt).1
  have hlen' := congrArg List.length (seg_eq (R := R) hB hL hstm hsl)
  rw [seg_eq hB hL hstm hsl, List.map_append] at hsegat
  obtain ⟨hstar, hk'lt, hi, hops, hsem, hlen, -⟩ := seqRun_stop_starP hvb hsegat.append_left hsr'
  have hzone : ∀ c, AtSeg (V := CV) (W := W) b (pos f R bl b j)
      (sl.st'.emitted.toList.map (·.mapRegs R)).length c →
      AtSeg b (pos f R bl b j) (seg f R bl b j).length c := by
    rintro c ⟨t, ht, ρ', w', rfl⟩
    refine ⟨t, ?_, ρ', w', rfl⟩
    simp only [List.length_map, List.length_append] at hlen' ht
    omega
  obtain ⟨hmk, hops0⟩ := seqRun_stop_mem hsr
  have hcm : MInst.call ci ∈ sl.st'.emitted.toList := List.mem_of_getElem? hmk
  have hu : ∀ o ∈ ops.toList, o.isUse = true → D o.vreg ∨ ¬ D (gn o.vreg) := by
    intro o ho hou
    have hm' : o.vreg ∈ vuseNums (.call ci) := by
      simp only [vuseNums, hops0]
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨ho, hou⟩)
    exact huses _ hcm o.vreg hm'
  have hvu := vuses_rename hA1 hu
  obtain ⟨ci', hci', hdest⟩ : ∃ ci', (MInst.call ci).mapRegs R = .call ci' ∧
      callDest ci' = callDest ci := by
    obtain ⟨d, us, ds⟩ := ci
    cases d <;> exact ⟨_, rfl, rfl⟩
  rw [hci'] at hi hops hsem
  refine ⟨B, j, hB, hstm, rfl, obj, w', ⟨b, _, ρ₁', w₁, vb, ci', ops.map (rnOp gn), _,
    hstar.mono hzone, hzone _ ⟨_, hk'lt, ρ₁', w₁, rfl⟩, hvb, hi, hops,
    by rw [hdest, hvu]; exact hra, hsem, hlen⟩, hex, ?_⟩
  simpa [fr', restrict, hslots] using hmr'

/-- **A `call`/`call_indirect` statement whose extern unwinds** (`stmt_step_raiseWP` without the
zone). -/
theorem stmt_step_raiseW (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHypW f sem rz MR env p out)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    {e : Clif.Exn} {mm : Clif.Mem} (hr : instRaise env p s.frame s.mem stm.inst = some (e, mm)) :
    ∃ obj w', VUnwFromW vc sem rz ⟨b, k, ρ, w⟩ obj w' ∧ E2E.ExnRel e obj ∧ MR slots mm w' := by
  obtain ⟨B, j, -, -, -, obj, w', hu, h1, h2⟩ := stmt_step_raiseWP H HU HR hm hbody hr
  exact ⟨obj, w', VUnwFromWP.toVUnwFromW hu, h1, h2⟩

/-! ## Entering a handler -/

/-- **Entering a successor block** (`enter_match`), with the edge's `Cert` conditions given
(a handler edge: `UnwShape.tries`; `Cert.term` covers only the normal-return edge). -/
theorem enter_matchUW (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    {s : Clif.State} {b : Nat} {B : Clif.Block}
    (hcall : s.callers = []) (hfunc : s.frame.func = f) (hslots : s.frame.slots = slots)
    {ρ : Nat → CV} (hheld : Held gn (A b B.body.length) ρ s.frame)
    (hcons : DFGCons ctx (restrict s.frame (A b B.body.length)))
    {bc : Clif.BlockCall} {tl : Nat} (htl : blockIdx? f bc.block = some tl) (hne0 : tl ≠ 0)
    (hedge : ∀ TB, f.blocks[tl]? = some TB → EdgeCert ctx gn A b B tl TB)
    {fr2 : Clif.Frame} (hent : Clif.enterBlock s.frame bc = .ok fr2) {ρ₂ : Nat → CV}
    (hρ₂ : ∀ x ∈ A b B.body.length, ρ₂ (gn x) = ρ (gn x)) {xs : List Nat}
    (hxl : xs.length = bc.args.length)
    (hxv : ∀ (m : Nat) a v x, bc.args[m]? = some a → s.frame.regs a = some v → xs[m]? = some x →
      VHolds v (ρ₂ x))
    {w₂ : W} (hmr : MR slots s.mem w₂) :
    ∃ TB, f.blocks[tl]? = some TB ∧ bc.args.length = TB.params.length ∧
      Match f ctx R gn bl A MR slots { s with frame := fr2 }
        ⟨tl, 0, parCopyEnv ρ₂ (TB.params.map (·.1)) xs, w₂⟩ := by
  obtain ⟨TB, args, regs, hTBf, hargs, hty, hset, rfl⟩ := enterBlock_spec hent
  rw [hfunc] at hTBf
  have hTB := blockIdx_block htl hTBf
  obtain ⟨hl1, hgm⟩ := getMany_spec hargs
  have hl2 := setMany_length hset
  have hlen : bc.args.length = TB.params.length := by simp at hl2; omega
  obtain ⟨hnd, hpA, hA0⟩ := hedge TB hTB
  have hTBmem : TB ∈ f.blocks := List.mem_of_getElem? hTB
  have hpos : pos f R bl tl 0 = 0 := by
    simp [pos, pre]
    cases tl with
    | zero => exact absurd rfl hne0
    | succ n => rfl
  refine ⟨TB, hTB, hlen, hcall, hfunc, hslots, hmr, TB, 0, hTB, rfl, Nat.zero_le _,
    by simp, hpos.symm, ?_, ?_⟩
  · intro x hx
    rcases hA0 x hx with ⟨hxp, -⟩ | ⟨hxp, hxA, hgx⟩
    · obtain ⟨m, v, hxm, hvm, hrv⟩ := setMany_mem hset hnd x hxp
      refine ⟨v, hrv, ?_⟩
      have hm : m < bc.args.length := by
        have := (List.getElem?_eq_some_iff.mp hxm).1; simp at this; omega
      have ha := List.getElem?_eq_getElem hm
      obtain ⟨v', hv', hvm'⟩ := hgm m _ ha
      rw [hvm] at hvm'; cases hvm'
      have hgp : gn x = x := by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hxp
        exact H.shape.params TB hTBmem q hq
      have hxm' : xs[m]? = some xs[m] := List.getElem?_eq_getElem (by omega)
      show VHolds v (parCopyEnv ρ₂ (TB.params.map (·.1)) xs (gn x))
      rw [hgp, parCopyEnv_param hnd (by simp; omega) m hxm hxm']
      exact hxv m _ v _ ha hv' hxm'
    · obtain ⟨v, hv, hh⟩ := hheld x hxA
      refine ⟨v, by show regs x = some v; rw [setMany_other hset hxp]; exact hv, ?_⟩
      show VHolds v (parCopyEnv ρ₂ (TB.params.map (·.1)) xs (gn x))
      rw [parCopyEnv_other hgx, hρ₂ x hxA]
      exact hh
  refine ⟨?_, ?_⟩
  rotate_left
  · intro x t v ht hv
    have hx0 : x ∈ A tl 0 := restrict_regs_isSome (by rw [hv]; rfl)
    have hv' : regs x = some v := by
      have := restrict_regs_of_mem (fr := { s.frame with regs, body := TB.body, term := TB.term }) hx0
      rw [this] at hv; exact hv
    by_cases hxp : x ∈ TB.params.map (·.1)
    · obtain ⟨q, hq, rfl, hqt⟩ := setMany_param_ty hset hnd hty hxp hv'
      rw [H.cert.paramTy TB hTBmem q hq] at ht
      rw [hqt]; exact Option.some.inj ht
    · rcases hA0 x hx0 with ⟨hxp', -⟩ | ⟨-, hxA, -⟩
      · exact absurd hxp' hxp
      · refine hcons.2 x t v ht ?_
        rw [restrict_regs_of_mem hxA, ← setMany_other hset hxp]
        exact hv'
  · intro x d info cl v hd hinfo hcl hp hv
    have hx0 : x ∈ A tl 0 := restrict_regs_isSome (by rw [hv]; rfl)
    have hv' : regs x = some v := by
      have := restrict_regs_of_mem (fr := { s.frame with regs, body := TB.body, term := TB.term }) hx0
      rw [this] at hv; exact hv
    rcases hA0 x hx0 with ⟨-, hdn⟩ | ⟨hxp, hxA, -⟩
    · rw [hdn] at hd; cases hd
    · have hvx : (restrict s.frame (A b B.body.length)).regs x = some v := by
        rw [restrict_regs_of_mem hxA, ← setMany_other hset hxp]; exact hv'
      obtain ⟨vals0, hev, hlk⟩ := hcons.1 x d info cl v hd hinfo hcl hp hvx
      refine ⟨vals0, fun cm => ?_, hlk⟩
      rw [← hev cm]
      refine evalInst_congr ?_ ?_ cm cl ?_
      · rfl
      · rfl
      intro y hy
      have hy0 := H.cert.closed tl 0 x d info cl hx0 hd hinfo hcl hp y hy
      have hyA := H.cert.closed b B.body.length x d info cl hxA hd hinfo hcl hp y hy
      have hyp : y ∉ TB.params.map (·.1) := hpA x hx0 hxp d info cl hd hinfo hcl y hy
      rw [restrict_regs_of_mem hy0, restrict_regs_of_mem hyA]
      exact setMany_other hset hyp

/-! ## A raising `try_call` -/

/-- **A `try_call`/`try_call_indirect` whose extern unwinds** (caught by the first item of its
exception table, a `tag 0`/`tag 1` handler). The CLIF steps — the payload bound, the jump to the
handler — are matched by the terminator's code up to the `tryCall` (`.goto 0`), the landing-pad
edge block and its `jump`. -/
theorem term_step_try_exnWP (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHypW f sem rz MR env p out)
    {xs : Clif.XState} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MR slots xs.s ⟨b, k, ρ, w⟩) (hbody : xs.s.frame.body = [])
    {et : Clif.ExnTable} (hT : IsTryWith xs.s.frame.term et)
    {e : Clif.Exn} {mm : Clif.Mem} (hr : Clif.raiseAt? env p xs.s = some (e, mm)) :
    ∃ xs1, Clif.stepX env p xs = .next xs1 ∧
      (∀ c, Clif.stepX env p xs1 ≠ .trapped c) ∧ (∀ vals cm, Clif.stepX env p xs1 ≠ .done vals cm) ∧
      (∀ e' cm, Clif.stepX env p xs1 ≠ .unwound e' cm) ∧
      ∀ xs2, Clif.stepX env p xs1 = .next xs2 →
        ∃ vs', StarP (VStep vc sem) (TermZone vc b k) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
          Match f ctx R gn bl A MR slots xs2.s vs' := by
  obtain ⟨hcall, hfunc, hslots, hmem, B, j, hB, hterm, hj, hbd, hk, hheld, hcons⟩ := hm
  simp only at hk hheld hcons hB hmem
  subst hk
  have hjn : j = B.body.length := by
    rw [hbd] at hbody
    have := List.drop_eq_nil_iff.mp hbody
    omega
  subst hjn
  have hBT : IsTryWith B.term et := hterm ▸ hT
  have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, -, -, -, hst0t, -, htry, hcode, -, -, hbargs, -⟩ := H.shape.blk b B L hB hL
  obtain ⟨T, hTl, hdata, hexn, hregs, hinfo, outv, tr, hrun⟩ := htry et hBT
  have hvbL : ValsBelow ctx L.tst := fun x r h =>
    Nat.lt_of_lt_of_le (H.shape.valsBelow x r h) hst0t
  obtain ⟨hargsTA, hnoclobT, -⟩ := H.cert.term b B L hB hL
  have hnr : abiTerm f B.term = B.term := by
    rcases hBT with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] <;> rfl
  have htA : ∀ y ∈ termArgs B.term, y ∈ A b B.body.length := fun y hy =>
    hargsTA y (by rw [hnr]; exact hy)
  -- the exceptional edge's facts
  obtain ⟨T', n, d, rest, pre, c, ops, h0, eb, tl, hTl', hitems, hn, hms, hpre, hok, hops,
    hlate, hndd, hhd, heb, hebi, hebp, hebba, hargsOk, htl, htl0, hedge⟩ :=
    HU.tries b B L et hB hL hBT
  rw [hTl] at hTl'
  cases hTl'
  -- the raising call and the normal-return contract (for its static facts)
  obtain ⟨ci, hciA, hraise, hTarg, hlow⟩ : ∃ ci : Clif.Inst,
      (∀ y ∈ instArgs ci, y ∈ termArgs B.term) ∧
      instRaise env p xs.s.frame xs.s.mem ci = some (e, mm) ∧
      ((∃ fn args, ci = .call fn args ∧ tryCallData f (.tryCall fn args et) = .ok L.data ∧
        ∀ e, f.extern? fn = some e → SigStackOk e.sig out) ∨
      (∃ callee args, ci = .callIndirect et.sig callee args ∧
        tryCallData f (.tryCallIndirect callee args et) = .ok L.data ∧ T.sig ∈ indSigs f ∧
        T.sig.params.length ≤ 8)) ∧
      LowerTryOk sem MR env.toEnv p (tryCtx ctx (L.start + B.body.length) L.data T.regs) ci
        T.info { T.st1 with emitted := #[] } L.tst' L.tst'.emitted.toList := by
    rcases hBT with ⟨fn, args, hBT⟩ | ⟨callee, args, hBT⟩
    · have hdata' : tryCallData f (.tryCall fn args et) = .ok L.data := hBT ▸ hdata
      refine ⟨.call fn args, fun y hy => by
          simp only [instArgs] at hy; simp [termArgs, hBT, hy],
        raiseAt_tryCall hbody (hterm.trans hBT) hr,
        .inl ⟨fn, args, rfl, hdata', fun e he => HR.tstk B hBmem fn args et hBT e he⟩,
        H.tries.choose_spec.1 ctx (L.start + B.body.length) fn args et L.data
          T.sig T.items L.targets T.info T.regs L.tst T.st1 outv L.tst' tr H.shape.ctxInv
          (H.tries.choose_spec.2 B hBmem fn args et hBT) hdata' hexn
          (H.shape.tslot b B L hB hL) hinfo hregs hvbL hrun⟩
    · have hdata' : tryCallData f (.tryCallIndirect callee args et) = .ok L.data := hBT ▸ hdata
      have hsd := exnTableOpnd_sig hexn
      obtain ⟨hsin, h8⟩ := H.tryIndSig B hBmem callee args et T.sig hBT hsd
      refine ⟨.callIndirect et.sig callee args, fun y hy => by
          simp only [instArgs] at hy
          simp only [hBT, termArgs, List.cons_append]
          exact List.mem_cons.mpr ((List.mem_cons.mp hy).imp id fun h => List.mem_append_left _ h),
        raiseAt_tryCallInd hbody (hterm.trans hBT) hr,
        .inr ⟨callee, args, rfl, hdata', hsin, h8⟩,
        H.tryInd f ctx (L.start + B.body.length) callee args et L.data T.sig T.items L.targets
          T.info T.regs L.tst T.st1 outv L.tst' tr H.shape.ctxInv hdata' hexn hsin h8
          (H.shape.tslot b B L hB hL) hinfo hregs hvbL hrun⟩
  have hargsA : ∀ y ∈ instArgs ci, y ∈ A b B.body.length := fun y hy => htA y (hciA y hy)
  obtain ⟨pre', ci', hms', hpre', hcd⟩ := hlow.shape
  have hpc' : pre' = pre ∧ ci' = c := by
    rw [hms] at hms'
    obtain ⟨h1, h2⟩ := List.append_inj' hms' rfl
    simp only [List.cons.injEq, MInst.call.injEq, and_true] at h2
    exact ⟨h1.symm, h2.symm⟩
  obtain ⟨rfl, rfl⟩ := hpc'
  have hmono : T.st1.nextVreg ≤ L.tst'.nextVreg := hlow.mono
  obtain ⟨-, hregsEq, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc hexn) hregs
  have hmax1 : (sigRets T.sig).length ≤ max (sigRets T.sig).length 2 := Nat.le_max_left _ _
  have hmax2 : 2 ≤ max (sigRets T.sig).length 2 := Nat.le_max_right _ _
  have hfix : tryFix T.info L.tst'.emitted.toList = pre' ++ [.tryCall ci' T.info] := by
    rw [hms, tryFix_append]
  let fr' := restrict xs.s.frame (A b B.body.length)
  let ρ₀ : Nat → CV := fun n => ρ (gn n)
  have hvh : ValsHeld fr' ρ₀ := by
    intro x v hx
    have hxA : x ∈ A b B.body.length := restrict_regs_isSome (by rw [hx]; rfl)
    obtain ⟨v', hv', hh⟩ := hheld x hxA
    rw [restrict_regs_of_mem hxA, hv'] at hx
    cases hx
    exact hh
  have hraise' : instRaise env p fr' xs.s.mem ci = some (e, mm) := by
    rw [instRaise_congr (fr := xs.s.frame) (fr' := fr') rfl _ _
      (fun x hx => restrict_regs_of_mem (hargsA x hx))]
    exact hraise
  obtain ⟨hU, ops0, ρ₁, w₁, obj, w₂, hsr, -, hex, hmr2⟩ :=
    HR.tries H.shape.ctxInv
      hTarg hexn (H.shape.tslot b B L hB hL) hinfo hregs hvbL hrun hms hpre hok (fr := fr')
      (by simp [fr', restrict, hfunc, H.shape.ctxInv.func]) hvh (dfgCons_termCtx hcons _ _)
      (by simpa [fr', restrict, hslots] using hmem) hraise'
  have hops0 : ops0 = ops := by
    have h2 := (seqRun_stop_mem hsr).2
    rw [operands_tryCall_call, hops] at h2
    exact (Except.ok.inj h2).symm
  subst ops0
  -- the renamed run
  let D : Nat → Prop := fun n => L.tst.nextVreg ≤ n ∧ n < L.tst'.nextVreg
  have hD : ∀ d, D d → gn d = d := fun d hd => H.shape.temps d (by
    have : L.tst.nextVreg ≤ d := hd.1; omega)
  have hdefs : ∀ m ∈ pre' ++ [.tryCall ci' T.info], ∀ d ∈ vdefs m, D d := by
    intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨h1, h2⟩ := hpre' m hm d hd
      have h1' : T.st1.nextVreg ≤ d := h1
      exact ⟨by omega, h2⟩
    · rw [List.mem_singleton] at hm
      subst hm
      rw [vdefs_tryCall] at hd
      have hmem' : Reg.vreg d .int ∈ T.regs.1 ++ T.regs.2 := hcd d hd
      rw [hregsEq] at hmem'
      simp only [List.mem_append, List.mem_map, List.mem_range, Reg.vreg.injEq, and_true,
        List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      show L.tst.nextVreg ≤ d ∧ d < L.tst'.nextVreg
      rcases hmem' with ⟨a, ha, rfl⟩ | rfl | rfl <;> constructor <;> omega
  have huses : UsesOk { T.st1 with emitted := #[] } fr' L.tst'.emitted.toList →
      ∀ m ∈ pre' ++ [.tryCall ci' T.info], ∀ u ∈ vuseNums m, D u ∨ ¬ D (gn u) := by
    intro hU m hm u hu
    have hU' : ∀ m ∈ L.tst'.emitted.toList, ∀ u ∈ vuseNums m, D u ∨ ¬ D (gn u) := by
      intro m hm u hu
      rcases hU m hm u hu with h | h
      · have h' : T.st1.nextVreg ≤ u := h
        by_cases h'' : u < L.tst'.nextVreg
        · exact .inl ⟨by omega, h''⟩
        · right
          rw [H.shape.temps u (by omega)]
          intro hd; exact h'' hd.2
      · right; exact hnoclobT u (restrict_regs_isSome h)
    rcases List.mem_append.mp hm with hm | hm
    · exact hU' m (by rw [hms]; exact List.mem_append_left _ hm) u hu
    · rw [List.mem_singleton] at hm
      subst hm
      rw [vuseNums_tryCall] at hu
      exact hU' _ (by rw [hms]; simp) u hu
  have hAg : Agree gn D ρ₀ ρ := fun _ _ => rfl
  have hren := seqRun_rename (sem := sem) (ρ₀ := ρ₀) (ρ := ρ) (w := w) H.shape.ren
    (H.dsem.rename R gn H.shape.ren) hD hdefs
  obtain ⟨ρ₁', hsr', -, hA2⟩ := (hren (huses hU) hAg).2 hsr
  obtain ⟨hsegat, hsize⟩ := tseg_at hcode
  have htseg : tseg R bl b = (pre' ++ [MInst.tryCall ci' T.info]).map (·.mapRegs R) := by
    rw [tseg_eq hL, hTl]
    show (tryFix T.info _).map _ = _
    rw [hfix]
  rw [htseg] at hsegat hsize
  obtain ⟨hstar, -, hi, hops', hsem, hlen, -⟩ := seqRun_stop_starP hvb hsegat hsr'
  replace hstar := hstar.mono (Q := TermZone vc b (pos f R bl b B.body.length)) (by
    rintro c ⟨i, -, ρ', w', rfl⟩; exact .inl ⟨_, _, _, rfl, Nat.le_add_right _ _⟩)
  have hK : pos f R bl b B.body.length + pre'.length + 1 = vb.insts.size := by
    rw [hsize]; simp only [List.length_map, List.length_append, List.length_singleton]; omega
  have hback : vb.insts.back? = some ((MInst.tryCall ci' T.info).mapRegs R) := by
    rw [Array.back?_eq_getElem?, ← hK, Nat.add_sub_cancel]; exact hi
  obtain ⟨ss, ps, hcfg⟩ := H.cfg
  have hsucc0 : succOf vc b 0 = some h0.label := by
    rw [succOf_eq H.shape.labels hcfg hvb hback, targets_mapRegs]
    simp only [MInst.targets]
    cases hh : T.info.handlers with
    | nil => rw [hh] at hhd; cases hhd
    | cons h' hs =>
      rw [hh] at hhd
      simp only [List.head?_cons, Option.some.injEq] at hhd
      subst hhd
      simp
  -- tracked values keep their registers across the terminator's code
  let ρ₂ := vdefUpd (ops.map (rnOp gn)) (payloadOuts (.call ci') obj) ρ₁'
  have hρ₂ : ∀ x ∈ A b B.body.length, ρ₂ (gn x) = ρ (gn x) := by
    intro x hx
    have hnd : ¬ D x := by
      have h4 : x < st0.nextVreg := H.cert.small _ _ x hx
      intro hd
      have h3 : L.tst.nextVreg ≤ x := hd.1
      exact absurd (Nat.lt_of_lt_of_le h4 hst0t) (Nat.not_lt.mpr h3)
    show vdefUpd (ops.map (rnOp gn)) _ ρ₁' (gn x) = ρ (gn x)
    rw [← hA2 x (.inr (hnoclobT x hx))]
    exact (seqRun_stop_frame (fun m hm hxm => hnd (hdefs m hm x hxm)) hsr).2
  have hbargs' : vb.branchArgs = #[] := by
    rw [hbargs]; rcases hBT with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h]
  have henv1 := edgeEnv_eq (V := CV) hvb heb (xs := []) (ps := []) (by rw [hbargs']; rfl)
    (by rw [hebp]; rfl) rfl ρ₂
  have hstep1 := VStep.step hvb hi hops' hsem hlen (VNext.goto hK hsucc0 henv1)
  -- the CLIF steps: the handler catches, then the jump
  have hcatch : e.catches n = true := by
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
    · exact hex.2.1
    · exact hex.2.2
  have hcd' : et.catch? e = some d := by
    simp [Clif.ExnTable.catch?, hitems, hcatch]
  have hnoret : ∀ a ∈ d.args, ∀ i, a ≠ .ret i := by
    intro a ha i he
    subst he
    have := hargsOk _ ha
    simp [exnArgOk] at this
  let base := f.freshValue
  let bc : Clif.BlockCall := { block := d.block, args := d.args.map (exnArgVal base) }
  have hth : Clif.tryHandler d base = .ok bc := tryHandler_ok hnoret
  let regs' : Clif.Regs := (xs.s.frame.regs.set (base + 0) ⟨.i64, obj⟩).set (base + 1) ⟨.i64, 0⟩
  have hset : xs.s.frame.regs.setMany ((List.range e.payload.length).map (base + ·)) e.payload =
      some regs' := by
    rw [hex.1]; rfl
  let s1 : Clif.State :=
    { xs.s with frame := { xs.s.frame with regs := regs', body := [], term := .jump bc }, mem := mm }
  have hcin : Clif.catchIn xs.s.frame et e = some (.ok s1.frame) := by
    have hth' : Clif.tryHandler d xs.s.frame.func.freshValue = .ok bc := by rw [hfunc]; exact hth
    have hset' : xs.s.frame.regs.setMany
        ((List.range e.payload.length).map (xs.s.frame.func.freshValue + ·)) e.payload =
        some regs' := by rw [hfunc]; exact hset
    simp only [Clif.catchIn, hcd', Option.map_some]
    rw [hth', Clif.Res.ok_bind, hset']
    rfl
  have hpend : Clif.pendingOf xs.s = some et := by
    unfold Clif.pendingOf
    rw [hbody]
    rcases hT with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h]
  have hx1 : Clif.stepX env p xs = .next ⟨s1, xs.tries⟩ := by
    simp only [Clif.stepX, hr, Clif.raiseIn, hpend, Option.bind_some, hcin]
    rfl
  have hra1 : Clif.raiseAt? env p s1 = none := by simp [Clif.raiseAt?, s1]
  have hjne : dests (.jump bc) ≠ [] := by simp [dests]
  have hsx : Clif.stepX env p ⟨s1, xs.tries⟩ =
      Clif.liftStep ⟨s1, xs.tries⟩ (Clif.stepTerm env.toEnv p s1 (.jump bc)) := by
    simp only [Clif.stepX, hra1]
    rw [Clif.step_term _ _ _ rfl]
  refine ⟨⟨s1, xs.tries⟩, hx1, fun c h => ?_, fun vals cm h => ?_, fun e' cm h => ?_,
    fun xs2 h => ?_⟩
  · rw [hsx] at h
    cases hst : Clif.stepTerm env.toEnv p s1 (.jump bc) with
    | trapped c' => exact (stepTerm_branch_ne hjne).2 c' hst
    | _ => rw [hst] at h; simp [Clif.liftStep] at h
  · rw [hsx] at h
    cases hst : Clif.stepTerm env.toEnv p s1 (.jump bc) with
    | done v' m' => exact (stepTerm_branch_ne hjne).1 v' m' hst
    | _ => rw [hst] at h; simp [Clif.liftStep] at h
  · rw [hsx] at h
    cases hst : Clif.stepTerm env.toEnv p s1 (.jump bc) <;> rw [hst] at h <;>
      simp [Clif.liftStep] at h
  rw [hsx] at h
  cases hst : Clif.stepTerm env.toEnv p s1 (.jump bc) with
  | next s'' =>
    rw [hst] at h
    simp only [Clif.liftStep, Clif.XStepResult.next.injEq] at h
    subst h
    obtain ⟨j', bc', fr2, -, hbc', hent, rfl⟩ := stepTerm_branch hjne hst
    have hbcbc : bc = bc' := by
      cases j' with
      | zero => simp [dests] at hbc'; exact hbc'
      | succ n => simp [dests] at hbc'
    subst hbcbc
    have hnotres : ∀ x ∈ A b B.body.length, x ∉ (List.range e.payload.length).map (base + ·) := by
      intro x hx hm
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hm
      have h1 : f.freshValue + a < st0.nextVreg := H.cert.small _ _ _ hx
      exact absurd (Nat.lt_of_lt_of_le h1 H.shape.fresh) (Nat.not_lt.mpr (Nat.le_add_right _ _))
    have hheld' : Held gn (A b B.body.length) ρ s1.frame := by
      intro x hx
      obtain ⟨v, hv, hh⟩ := hheld x hx
      refine ⟨v, ?_, hh⟩
      show regs' x = some v
      rw [setMany_other hset (hnotres x hx), hv]
    have hcons' : DFGCons ctx (restrict s1.frame (A b B.body.length)) := by
      refine dfgCons_congr (fr := restrict xs.s.frame (A b B.body.length)) rfl rfl
        (funext fun x => ?_) hcons
      by_cases hx : x ∈ A b B.body.length
      · simp only [restrict, s1, hx, ite_true]
        exact setMany_other hset (hnotres x hx)
      · simp only [restrict, s1, hx, ite_false]
    let xsl := d.args.map (exnArgNum gn ops)
    have hxl : xsl.length = bc.args.length := by simp [xsl, bc]
    have hnodup2 : ((List.range e.payload.length).map (base + ·)).Nodup :=
      List.Pairwise.map _ (fun a b h e => h (Nat.add_left_cancel e)) List.nodup_range
    have hxv : ∀ (m : Nat) a v x, bc.args[m]? = some a → s1.frame.regs a = some v →
        xsl[m]? = some x → VHolds v (ρ₂ x) := by
      intro m a v x ha hv hx
      simp only [bc, xsl, List.getElem?_map] at ha hx
      cases hta : d.args[m]? with
      | none => rw [hta] at ha; cases ha
      | some ta =>
        rw [hta] at ha hx
        simp only [Option.map_some, Option.some.injEq] at ha hx
        subst ha hx
        have htam := List.mem_of_getElem? hta
        have hv' : regs' _ = some v := hv
        cases ta with
        | val v0 =>
          have hv0A : v0 ∈ A b B.body.length := htA v0 (etVals_termArgs hBT v0 (by
            simp only [Clif.ExnTable.vals, hitems, List.flatMap_cons, List.mem_append,
              Clif.TryDest.vals, List.mem_filterMap]
            exact .inr (.inl ⟨.val v0, htam, rfl⟩)))
          show VHolds v (ρ₂ (gn v0))
          rw [hρ₂ v0 hv0A]
          simp only [exnArgVal] at hv'
          rw [setMany_other hset (hnotres v0 hv0A)] at hv'
          obtain ⟨v', hv'', hh⟩ := hheld v0 hv0A
          rw [hv'] at hv''; cases hv''
          exact hh
        | exn i =>
          have hok' := hargsOk _ htam
          simp only [exnArgOk, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists]
            at hok'
          obtain ⟨hi2, n0, hn0⟩ := hok'
          have hpl : e.payload.length = 2 := by rw [hex.1]; rfl
          obtain ⟨vi, hvi⟩ : ∃ vi, e.payload[i]? = some vi :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          have hrv := setMany_nodup hset hnodup2 i (base + i) vi
            (by simp [hpl, hi2]) hvi
          simp only [exnArgVal] at hv'
          rw [hrv] at hv'
          obtain rfl : vi = v := Option.some.inj hv'
          rw [hex.1] at hvi
          obtain ⟨j0, o0, hj0, rfl, -⟩ := payVreg_spec hn0
          have hDn : D o0.vreg := hdefs (.tryCall ci' T.info) (by simp) o0.vreg (by
            rw [vdefs_tryCall]
            simp only [vdefs, hops]
            exact List.mem_map_of_mem (List.mem_of_getElem? hj0))
          show VHolds vi (vdefUpd (ops.map (rnOp gn)) (payloadOuts (.call ci') obj) ρ₁'
            (gn ((payVreg ops i).getD 0)))
          rw [hn0, Option.getD_some, ← hA2 _ (.inl hDn), payload_def hops hlate hndd hi2 hn0]
          exact vholds_payWord hvi
        | ret i => exact absurd rfl (hnoret _ htam i)
    obtain ⟨TB, hTB, hlenA, hM⟩ := enter_matchUW H (b := b) (B := B) (s := s1) hcall hfunc hslots
      hheld' hcons'
      (bc := bc) htl htl0 hedge hent hρ₂ hxl hxv (by simpa [fr', restrict, hslots] using hmr2)
    obtain ⟨Lt, hLt⟩ := H.blow hTB
    obtain ⟨vbt, hvbt, -, -, -, -, -, -, -, -, hpt, -, -⟩ := H.shape.blk tl TB Lt hTB hLt
    simp only [htl0, ite_false] at hpt
    have hebba' : eb.branchArgs = (xsl.map fun n => Reg.vreg n .int).toArray := by
      rw [hebba]
      refine congrArg List.toArray ?_
      simp only [xsl, List.map_map]
      apply List.map_congr_left
      intro a ha
      cases a with
      | val v => simp [exnArgReg, exnArgNum, H.shape.ren.vreg]
      | exn i =>
        have hok' := hargsOk _ ha
        simp only [exnArgOk, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists]
          at hok'
        obtain ⟨-, n0, hn0⟩ := hok'
        simp [exnArgReg, exnArgNum, hn0, H.shape.ren.vreg]
      | ret i => exact absurd rfl (hnoret _ ha i)
    have henv2 := edgeEnv_eq (V := CV) heb hvbt (xs := xsl) (ps := TB.params.map (·.1)) hebba'
      (by rw [hpt]; simp [List.map_map, Function.comp_def]) (by simp only [List.length_map]; omega)
      (parCopyEnv ρ₂ [] [])
    have hpc : parCopyEnv ρ₂ [] [] = ρ₂ := rfl
    rw [hpc] at henv2
    have hebback : eb.insts.back? = some (.jump tl) := by rw [hebi]; rfl
    have hstep2 : VStep vc sem (.run ⟨h0.label, 0, parCopyEnv ρ₂ [] [], w₂⟩)
        (.run ⟨tl, 0, parCopyEnv ρ₂ (TB.params.map (·.1)) xsl, w₂⟩) := by
      rw [hpc]
      refine VStep.step heb (by rw [hebi]; rfl) (i := .jump tl) (ops := #[]) rfl
        (H.dsem.jump tl w₂) rfl (VNext.goto (by rw [hebi]; rfl) ?_ henv2)
      rw [succOf_eq H.shape.labels hcfg heb hebback]; rfl
    exact ⟨_, hstar.trans (.step (.inl ⟨_, _, _, rfl, Nat.le_add_right _ _⟩) hstep1
      (StarP.single (.inr ⟨_, _, _, eb, tl, rfl, heb, hebi⟩) hstep2)), hM⟩
  | _ => rw [hst] at h; simp [Clif.liftStep] at h

/-- **A raising `try_call`/`try_call_indirect`** (`term_step_try_exnWP` without the zone). -/
theorem term_step_try_exnW (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHypW f sem rz MR env p out)
    {xs : Clif.XState} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MR slots xs.s ⟨b, k, ρ, w⟩) (hbody : xs.s.frame.body = [])
    {et : Clif.ExnTable} (hT : IsTryWith xs.s.frame.term et)
    {e : Clif.Exn} {mm : Clif.Mem} (hr : Clif.raiseAt? env p xs.s = some (e, mm)) :
    ∃ xs1, Clif.stepX env p xs = .next xs1 ∧
      (∀ c, Clif.stepX env p xs1 ≠ .trapped c) ∧ (∀ vals cm, Clif.stepX env p xs1 ≠ .done vals cm) ∧
      (∀ e' cm, Clif.stepX env p xs1 ≠ .unwound e' cm) ∧
      ∀ xs2, Clif.stepX env p xs1 = .next xs2 →
        ∃ vs', Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
          Match f ctx R gn bl A MR slots xs2.s vs' := by
  obtain ⟨xs1, h1, h2, h3, h4, h5⟩ := term_step_try_exnWP H HU HR hm hbody hT hr
  exact ⟨xs1, h1, h2, h3, h4, fun xs2 h => let ⟨vs', hs, hm'⟩ := h5 xs2 h; ⟨vs', hs.star, hm'⟩⟩

/-! ## Whole runs -/

/-- What a VCode run from `vs` does when the CLIF run with unwinding from the matching state
ends: `RunOk`, and for an exception the VCode run reaches a raising `call` that ends the
activation (`VUnwFromW`), with the object related to the exception and the world related to
the memory before the frame was left. -/
def RunOkUW (vc : VCode) (sem : ISem CV W) (rz : RaiseFn W) (MR : MemRelTW W)
    (slots : List (Clif.SlotId × Nat)) (vs : VState CV W) : Clif.XOutcome → Prop
  | .returned vals cm => ∃ us outs w cm0, VRetFrom vc sem vs us outs w ∧
      us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
      PrefixHold vals outs ∧ MR slots cm0 w ∧ cm = (cm0.free (slots.map (·.2))).leave
  | .trapped c => VTrapFrom vc sem vs c
  | .unwound e cm => ∃ obj w cm0, VUnwFromW vc sem rz vs obj w ∧ E2E.ExnRel e obj ∧
      MR slots cm0 w ∧ cm = (cm0.free (slots.map (·.2))).leave
  | .stuck _ | .outOfFuel => True

theorem RunOkUW.prefix {vs vs' : VState CV W} {o : Clif.XOutcome}
    (h : Star (VStep vc sem) (.run vs) (.run vs')) (h' : RunOkUW vc sem rz MR slots vs' o) :
    RunOkUW vc sem rz MR slots vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨us, outs, w, cm0, hr, h1⟩ := h'
    exact ⟨us, outs, w, cm0, VRetFrom.prefix h hr, h1⟩
  | trapped c => exact VTrapFrom.prefix h h'
  | unwound e cm =>
    obtain ⟨obj, w, cm0, hu, h1⟩ := h'
    exact ⟨obj, w, cm0, VUnwFromW.prefix h hu, h1⟩
  | _ => trivial

/-- **Whole runs with unwinding**: from matching states, every outcome of `Clif.runLoopX` is
realised by the VCode run (under `TrapsExplicitX`). -/
theorem sim_runXW (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHypW f sem rz MR env p out)
    {cs : Clif.State} (hcf : cs.frame.func = f) (htr : E2E.TrapsExplicitX env p cs) :
    ∀ fuel (xs : Clif.XState) (vs : VState CV W), E2E.ReachX env p cs.toX xs →
      Match f ctx R gn bl A MR slots xs.s vs →
      RunOkUW vc sem rz MR slots vs (Clif.runLoopX env p fuel xs) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro xs vs hr hm
  cases fuel with
  | zero => trivial
  | succ n =>
    obtain ⟨b, k, ρ, w⟩ := vs
    have hfunc : xs.s.frame.func = f := hm.2.1
    have hcallers : xs.s.callers = [] := hm.1
    have hslots : xs.s.frame.slots = slots := hm.2.2.1
    -- the CLIF step continues: the old simulation (its trap/indirect premises from `htr`)
    have hnext : ∀ s', Clif.step env.toEnv p xs.s = .next s' →
        (∃ vs', Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
          Match f ctx R gn bl A MR slots s' vs') →
        RunOkUW vc sem rz MR slots ⟨b, k, ρ, w⟩ (Clif.runLoopX env p (n + 1) xs) := by
      intro s' hs ⟨vs', hstar, hm'⟩
      obtain ⟨t, hx⟩ := stepX_next_of hs
      rw [runLoopX_next hx]
      exact RunOkUW.prefix hstar (ih n (by omega) _ vs' (hr.snoc hx) hm')
    cases hbody : xs.s.frame.body with
    | cons st rest =>
      obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hm
      have hst : st ∈ B.body := by
        rw [hbd] at hbody
        exact List.mem_of_mem_drop (hbody ▸ List.mem_cons_self)
      have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
      have hext : ∀ fn args, st.inst = .call fn args → ∀ e, xs.s.frame.func.extern? fn = some e →
          p.func? e.name = none := by
        intro fn args hi e he
        exact H.ext B hBmem st hst fn args hi e (hfunc ▸ he)
      have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
          xs.s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, xs.s.mem.symbols g.name ≠ some cv.toNat :=
        fun sig callee args hi => htr.indirect xs st rest sig callee args hr hbody hi
          ⟨B, hcf ▸ hBmem, hst⟩
      obtain ⟨S1, S2⟩ := stmt_step H hm hbody hind
      cases hs : Clif.step env.toEnv p xs.s with
      | next s' => exact hnext s' hs (S1 s' hs)
      | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
      | trapped c =>
        rw [runLoopX_trapped (stepX_trapped_of hs)]
        exact S2 c hs (htr.stmt xs c st rest hr hs hbody)
      | stuck msg =>
        cases hra : instRaise env p xs.s.frame xs.s.mem st.inst with
        | none =>
          rw [runLoopX_stuck (stepX_stuck_of hs (by rw [raiseAt_stmt hbody, hra]))]
          trivial
        | some em =>
          obtain ⟨e, mm⟩ := em
          obtain ⟨obj, w', hu, hex, hmr⟩ := stmt_step_raiseW H HU HR hm hbody hra
          have hx : Clif.stepX env p xs =
              .unwound e ((mm.free (xs.s.frame.slots.map (·.2))).leave) := by
            have hpend : Clif.pendingOf xs.s = none := by
              unfold Clif.pendingOf; rw [hbody]
            simp only [Clif.stepX, raiseAt_stmt hbody, hra, Clif.raiseIn, hpend, Option.bind_none,
              hcallers, Clif.unwindFrom]
          rw [runLoopX_unwound hx]
          exact ⟨obj, w', mm, hu, hex, hmr, by rw [hslots]⟩
    | nil =>
      obtain ⟨B, j, hB, hterm, -⟩ := hm.2.2.2.2
      have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
      cases hty : xs.s.frame.term.isTry with
      | false =>
        obtain ⟨T1, T2, T3⟩ := term_step H hm hbody hty
        cases hs : Clif.step env.toEnv p xs.s with
        | next s' => exact hnext s' hs (T1 s' hs)
        | done vals cm =>
          rw [runLoopX_done (stepX_done_of hs)]
          obtain ⟨us, outs, w', hret, h1, h2, h3, h4, h5⟩ := T2 vals cm hs
          exact ⟨us, outs, w', xs.s.mem, hret, h1, h2, h3, h4, h5⟩
        | trapped c =>
          rw [runLoopX_trapped (stepX_trapped_of hs)]
          exact T3 c hs
        | stuck msg =>
          have hra : Clif.raiseAt? env p xs.s = none := raiseAt_term_none hbody hty
            (fun fn args ht => H.noTail B hBmem fn args (hterm.symm.trans ht))
          rw [runLoopX_stuck (stepX_stuck_of hs hra)]
          trivial
      | true =>
        obtain ⟨et, hT⟩ : ∃ et, IsTryWith xs.s.frame.term et := by
          cases ht : xs.s.frame.term with
          | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
          | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
          | _ => rw [ht] at hty; cases hty
        have hind : ∀ callee args, xs.s.frame.term = .tryCallIndirect callee args et → ∀ cv,
            xs.s.frame.get callee = .ok cv → ∀ g ∈ p.funcs,
              xs.s.mem.symbols g.name ≠ some cv.toNat :=
          fun callee args ht => htr.tryIndirect xs callee args et hr hbody ht
            ⟨B, hcf ▸ hBmem, hterm.symm.trans ht⟩
        obtain ⟨Tnd, Tnx⟩ := term_step_try H hm hbody hT hind
        cases hs : Clif.step env.toEnv p xs.s with
        | next s' =>
          obtain ⟨N1, N2, N3⟩ := Tnx s' hs
          obtain ⟨t, hx⟩ := stepX_next_of hs
          rw [runLoopX_next hx]
          cases n with
          | zero => trivial
          | succ m =>
            have hr' := hr.snoc hx
            cases hs' : Clif.step env.toEnv p s' with
            | next s'' =>
              obtain ⟨vs', hstar, hm'⟩ := N3 s'' hs'
              obtain ⟨t', hx'⟩ := stepX_next_of (xs := ⟨s', t⟩) hs'
              rw [runLoopX_next hx']
              exact RunOkUW.prefix hstar (ih m (by omega) _ vs' (hr'.snoc hx') hm')
            | done vals cm => exact absurd hs' (N2 vals cm)
            | trapped c => exact absurd hs' (N1 c)
            | stuck msg =>
              cases hra' : Clif.raiseAt? env p s' with
              | none =>
                rw [runLoopX_stuck (stepX_stuck_of (xs := ⟨s', t⟩) hs' hra')]
                trivial
              | some em =>
                -- `s'` is at the pending `jump` of the `try_call`: it never raises
                exfalso
                revert hra'
                rcases hT with ⟨fn, args, hT⟩ | ⟨callee, args, hT⟩
                · obtain ⟨-, hnx⟩ := stepTry_spec (env := env.toEnv) (p := p) (args := args)
                    (et := et) (fun e he => H.tryExt B hBmem fn args et (hterm.symm.trans hT) e
                      (hfunc ▸ he))
                  have hs2 : Clif.stepTerm env.toEnv p xs.s (.tryCall fn args et) = .next s' := by
                    rw [← hT, ← Clif.step_term _ _ _ hbody]; exact hs
                  obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := hnx s' hs2
                  simp [Clif.raiseAt?, tryNext]
                · obtain ⟨-, hnx⟩ := stepTryInd_spec (env := env.toEnv) (p := p) (args := args)
                    (et := et) (hind callee args hT)
                  have hs2 : Clif.stepTerm env.toEnv p xs.s (.tryCallIndirect callee args et) =
                      .next s' := by
                    rw [← hT, ← Clif.step_term _ _ _ hbody]; exact hs
                  obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := hnx s' hs2
                  simp [Clif.raiseAt?, tryNext]
        | done vals cm => exact absurd hs (Tnd vals cm)
        | trapped c =>
          rcases hT with ⟨fn, args, hT⟩ | ⟨callee, args, hT⟩
          · exact absurd (hterm.symm.trans hT)
              (htr.tryCall xs c fn args et hr hs hbody hT B (hcf ▸ hBmem))
          · exact absurd (hterm.symm.trans hT)
              (htr.tryCallInd xs c callee args et hr hs hbody hT B (hcf ▸ hBmem))
        | stuck msg =>
          cases hra : Clif.raiseAt? env p xs.s with
          | none =>
            rw [runLoopX_stuck (stepX_stuck_of hs hra)]
            trivial
          | some em =>
            obtain ⟨e, mm⟩ := em
            obtain ⟨xs1, hx1, hX1, hX2, hX3, hnx1⟩ := term_step_try_exnW H HU HR hm hbody hT hra
            rw [runLoopX_next hx1]
            cases n with
            | zero => trivial
            | succ m =>
              have hr' := hr.snoc hx1
              cases hs1 : Clif.stepX env p xs1 with
              | next xs2 =>
                obtain ⟨vs', hstar, hm'⟩ := hnx1 xs2 hs1
                rw [runLoopX_next hs1]
                exact RunOkUW.prefix hstar (ih m (by omega) _ vs' (hr'.snoc hs1) hm')
              | done vals cm => exact absurd hs1 (hX2 vals cm)
              | unwound e' cm => exact absurd hs1 (hX3 e' cm)
              | trapped c => exact absurd hs1 (hX1 c)
              | stuck msg =>
                rw [runLoopX_stuck hs1]
                trivial


end

end Backend.Proof.Driver
