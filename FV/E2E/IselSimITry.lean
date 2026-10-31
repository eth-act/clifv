import FV.E2E.IselSimI

/-!
# The `try_call` step of the counted CLIF → VCode simulation (SEM1, `docs/plans/uninit.md` §5.9)

`term_step_tryP` (`FV/Backend/Proof/LowerSim.lean`) gives the VCode run of a `try_call` /
`try_call_indirect` terminator only as a star in the terminator's zone, which can re-enter the
block (a self-loop through an edge block): from that alone the number of VCode calls on it is
not determined. `term_step_tryI` is `term_step_tryP`'s proof (copied: the statement there
stays) for `csem F fctx (XI.at n)`, ending instead in the counted run: the terminator's code is
its argument moves `pre` and one call (`LowerTryOk.shape`), and `pre` has no VCode call
(`TryCallsOne`, a property of the ISLE lowering taken as a premise), so the call is call number
`n` of `csemI F fctx XI` and the run arrives at the normal-return successor with counter `n + 1`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The argument moves of a `try_call`/`try_call_indirect` lowering contain no VCode call**
(the lowering is `pre ++ [call]`, `LowerTryOk.shape`; a property of the ISLE lowering, taken as a
premise, `docs/plans/uninit.md` §5.9). -/
def TryCallsOne (f : Clif.Function) : Prop :=
  (∀ ctx ti fn args et data sig items targets info trs lo st1 out st' tr, CtxInv f ctx →
    (∃ B ∈ f.blocks, B.term = .tryCall fn args et) →
    tryCallData f (.tryCall fn args et) = .ok data →
    exnTableOpnd f et = .ok (sig, items) → ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ →
    tryInfoOf sig items targets = some info → tryRegsOf sig lo = some (trs, st1) →
    ValsBelow ctx lo →
    runTerm (tryCtx ctx ti data trs) "lower_branch" [.inst ti, .labels targets]
      { st1 with emitted := #[] } = .ok (some out, st', tr) →
    ∀ pre ci, st'.emitted.toList = pre ++ [.call ci] → callsI pre = 0) ∧
  (∀ ctx ti callee args et data sig items targets info trs lo st1 out st' tr, CtxInv f ctx →
    (∃ B ∈ f.blocks, B.term = .tryCallIndirect callee args et) →
    tryCallData f (.tryCallIndirect callee args et) = .ok data →
    exnTableOpnd f et = .ok (sig, items) → ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ →
    tryInfoOf sig items targets = some info → tryRegsOf sig lo = some (trs, st1) →
    ValsBelow ctx lo →
    runTerm (tryCtx ctx ti data trs) "lower_branch" [.inst ti, .labels targets]
      { st1 with emitted := #[] } = .ok (some out, st', tr) →
    ∀ pre ci, st'.emitted.toList = pre ++ [.call ci] → callsI pre = 0)

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {F : BitVec 64 → Prop} {fctx : FnCtx} {XI : ExtSemI} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {W : Type} {sem semB : Nat → ISem CV W}
  {MRW : MemRelTW W}

/-- **`try_call`/`try_call_indirect` step, counted, for a family** (`term_step_tryP`'s proof for
`sem n`, the run lifted to `ISem.counted sem`: one VCode call, the counter `n` to `n + 1`). -/
theorem term_step_tryG (hni : NoncallIndep sem) {n : Nat}
    (H : DriverHyp f vc ctx st0 R gn bl A (sem n) MRW env p) (htc : TryCallsOne f)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MRW slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    {et : Clif.ExnTable} (hT : IsTryWith s.frame.term et)
    (hind : ∀ callee args, s.frame.term = .tryCallIndirect callee args et → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ vals cm, Clif.step env p s ≠ .done vals cm) ∧
    ∀ s', Clif.step env p s = .next s' →
      (s'.frame.body = [] ∧ ∃ bc, s'.frame.term = .jump bc) ∧
      (∀ c, Clif.step env p s' ≠ .trapped c) ∧ (∀ vals cm, Clif.step env p s' ≠ .done vals cm) ∧
      ∀ s'', Clif.step env p s' = .next s'' →
        ∃ b' k' ρ' w', Star (VStep vc (ISem.counted sem)) (.run ⟨b, k, ρ, (w, n)⟩)
          (.run ⟨b', k', ρ', (w', n + 1)⟩) ∧
          Match f ctx R gn bl A MRW slots s'' ⟨b', k', ρ', w'⟩ := by
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
  have hstep : Clif.step env p s = Clif.stepTerm env p s B.term := by
    rw [Clif.step_term env p s hbody, hterm]
  -- the lowering of the terminator
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, -, -, -, hst0t, -, htry, hcode, -, -, hbargs, hsucc⟩ :=
    H.shape.blk b B L hB hL
  obtain ⟨T, hTl, hdata, hexn, hregs, hinfo, out, tr, hrun⟩ := htry et hBT
  have hvbL : ValsBelow ctx L.tst := fun x r h =>
    Nat.lt_of_lt_of_le (H.shape.valsBelow x r h) hst0t
  obtain ⟨hargsTA, hnoclobT, -⟩ := H.cert.term b B L hB hL
  have hnr : abiTerm f B.term = B.term := by
    rcases hBT with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] <;> rfl
  have htA : ∀ y ∈ termArgs B.term, y ∈ A b B.body.length := fun y hy =>
    hargsTA y (by rw [hnr]; exact hy)
  -- the moves before the call contain no VCode call
  have hpre0 : ∀ pre ci, L.tst'.emitted.toList = pre ++ [.call ci] → callsI pre = 0 := by
    rcases id hBT with ⟨fn, args, hBT'⟩ | ⟨callee, args, hBT'⟩
    · exact htc.1 ctx (L.start + B.body.length) fn args et L.data T.sig T.items L.targets
        T.info T.regs L.tst T.st1 out L.tst' tr H.shape.ctxInv ⟨B, hBmem, hBT'⟩ (hBT' ▸ hdata) hexn
        (H.shape.tslot b B L hB hL) hinfo hregs hvbL hrun
    · exact htc.2 ctx (L.start + B.body.length) callee args et L.data T.sig T.items L.targets
        T.info T.regs L.tst T.st1 out L.tst' tr H.shape.ctxInv ⟨B, hBmem, hBT'⟩ (hBT' ▸ hdata) hexn
        (H.shape.tslot b B L hB hL) hinfo hregs hvbL hrun
  -- the call `ci` of the terminator: its CLIF step and its lowering
  obtain ⟨ci, hciA, hnd, hnx, hok⟩ : ∃ ci : Clif.Inst,
      (∀ y ∈ instArgs ci, y ∈ termArgs B.term) ∧
      (∀ vals cm, Clif.stepTerm env p s B.term ≠ .done vals cm) ∧
      (∀ s', Clif.stepTerm env p s B.term = .next s' → ∃ bc rvals cm' regs',
        Clif.tryNormal et s.frame.func.freshValue = .ok bc ∧
        instOutcome env p s.frame s.mem ci = .ok (rvals, cm') ∧
        s.frame.regs.setMany ((List.range T.sig.returns.length).map
          (s.frame.func.freshValue + ·)) rvals = some regs' ∧
        s' = tryNext s regs' bc cm') ∧
      LowerTryOk (sem n) MRW env p
        (tryCtx ctx (L.start + B.body.length) L.data T.regs) ci T.info
        { T.st1 with emitted := #[] } L.tst' L.tst'.emitted.toList := by
    rcases hBT with ⟨fn, args, hBT⟩ | ⟨callee, args, hBT⟩
    · have hext : ∀ e, s.frame.func.extern? fn = some e → p.func? e.name = none :=
        fun e he => H.tryExt B hBmem fn args et hBT e (hfunc ▸ he)
      have hdata' : tryCallData f (.tryCall fn args et) = .ok L.data := hBT ▸ hdata
      obtain ⟨sig0, items0, ext0, hexn0, hx0, hsig0⟩ := tryCallData_spec hdata'
      rw [hexn] at hexn0
      simp only [Except.ok.injEq, Prod.mk.injEq] at hexn0
      obtain ⟨rfl, rfl⟩ := hexn0
      obtain ⟨hnd, hnx⟩ := stepTry_spec (env := env) (p := p) (args := args) (et := et) hext
      rw [hBT]
      refine ⟨.call fn args, fun y hy => by
          simp only [instArgs] at hy; simp [termArgs, hy], hnd,
        fun s' hs => ?_, H.tries.choose_spec.1 ctx (L.start + B.body.length) fn args et L.data
          T.sig T.items L.targets T.info T.regs L.tst T.st1 out L.tst' tr H.shape.ctxInv
          (H.tries.choose_spec.2 B hBmem fn args et hBT) hdata' hexn
          (H.shape.tslot b B L hB hL) hinfo hregs hvbL hrun⟩
      obtain ⟨ext, bc, rvals, cm', regs', hx, htn, hO, hset, rfl⟩ := hnx s' hs
      rw [hfunc, hx0] at hx
      cases hx
      exact ⟨bc, rvals, cm', regs', htn, hO, by rw [← hsig0]; exact hset, rfl⟩
    · have hdata' : tryCallData f (.tryCallIndirect callee args et) = .ok L.data := hBT ▸ hdata
      have hsd := exnTableOpnd_sig hexn
      have hsin := H.tryIndSig B hBmem callee args et T.sig hBT hsd
      obtain ⟨hnd, hnx⟩ := stepTryInd_spec (env := env) (p := p) (args := args) (et := et)
        (hind callee args (hterm.trans hBT))
      rw [hBT]
      refine ⟨.callIndirect et.sig callee args,
        fun y hy => by
          simp only [instArgs] at hy
          simp only [termArgs, List.cons_append]
          exact List.mem_cons.mpr ((List.mem_cons.mp hy).imp id fun h => List.mem_append_left _ h),
        hnd, fun s' hs => ?_,
        H.tryInd f ctx (L.start + B.body.length) callee args et L.data T.sig T.items L.targets
          T.info T.regs L.tst T.st1 out L.tst' tr H.shape.ctxInv hdata' hexn hsin
          (H.shape.tslot b B L hB hL) hinfo hregs hvbL hrun⟩
      obtain ⟨declared, bc, rvals, cm', regs', hd, htn, hO, hset, rfl⟩ := hnx s' hs
      rw [hfunc, hsd] at hd
      cases hd
      exact ⟨bc, rvals, cm', regs', htn, hO, hset, rfl⟩
  refine ⟨fun vals cm h => hnd vals cm (hstep.symm.trans h), fun s' hs => ?_⟩
  rw [hstep] at hs
  obtain ⟨bc, rvals, cm', regs', htn, hO, hset, rfl⟩ := hnx s' hs
  have hbc := tryNormal_ok htn
  rw [hfunc] at hbc hset
  have hstep' : Clif.step env p (tryNext s regs' bc cm') =
      Clif.stepTerm env p (tryNext s regs' bc cm') (.jump bc) := Clif.step_term env p _ rfl
  have hjne : dests (.jump bc) ≠ [] := by simp [dests]
  refine ⟨⟨rfl, bc, rfl⟩, fun c h => (stepTerm_branch_ne hjne).2 c (hstep'.symm.trans h),
    fun vals cm h => (stepTerm_branch_ne hjne).1 vals cm (hstep'.symm.trans h), fun s'' hs' => ?_⟩
  rw [hstep'] at hs'
  obtain ⟨j', bc', fr2, -, hbc', hent, rfl⟩ := stepTerm_branch hjne hs'
  have hbcbc : bc = bc' := by
    cases j' with
    | zero => simp [dests] at hbc'; exact hbc'
    | succ n => simp [dests] at hbc'
  subst hbcbc
  have hsucc2 : L.targets.length = et.dests.length ∧
      ∃ tl tlab T eb, blockIdx? f et.normal.block = some tl ∧ L.targets.getLast? = some tlab ∧
        L.tl = some T ∧ vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧ eb.params = #[] ∧
        eb.branchArgs = (et.normal.args.map (normArgReg R T.regs.1)).toArray ∧
        ∀ a ∈ et.normal.args, match a with
          | .val _ => True
          | .ret i => i < T.sig.returns.length
          | .exn _ => False := by
    rcases hBT with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] at hsucc <;> exact hsucc
  obtain ⟨-, tl, tlab, T', eb, htl, hlast, hTl', heb, hebi, hebp, hebba, hargsOk⟩ := hsucc2
  rw [hTl] at hTl'
  cases hTl'
  have hbargs' : vb.branchArgs = #[] := by
    rw [hbargs]; rcases hBT with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h]
  obtain ⟨-, hregsEq, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc hexn) hregs
  obtain ⟨pre, ci', hms, hpre, hcd⟩ := hok.shape
  have hmono : T.st1.nextVreg ≤ L.tst'.nextVreg := hok.mono
  have hmax1 : (sigRets T.sig).length ≤ max (sigRets T.sig).length 2 := Nat.le_max_left _ _
  have hmax2 : 2 ≤ max (sigRets T.sig).length 2 := Nat.le_max_right _ _
  have hfix : tryFix T.info L.tst'.emitted.toList = pre ++ [.tryCall ci' T.info] := by
    rw [hms, tryFix_append]
  have hargsA : ∀ y ∈ instArgs ci, y ∈ A b B.body.length := fun y hy => htA y (hciA y hy)
  -- the call's results are not tracked values
  have hnotres : ∀ x ∈ A b B.body.length,
      x ∉ (List.range T.sig.returns.length).map (f.freshValue + ·) := by
    intro x hx hm
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hm
    have h1 : f.freshValue + a < st0.nextVreg := H.cert.small _ _ _ hx
    exact absurd (Nat.lt_of_lt_of_le h1 H.shape.fresh) (Nat.not_lt.mpr (Nat.le_add_right _ _))
  let fr' := restrict s.frame (A b B.body.length)
  let ρ₀ : Nat → CV := fun n => ρ (gn n)
  have hvh : ValsHeld fr' ρ₀ := by
    intro x v hx
    have hxA : x ∈ A b B.body.length := restrict_regs_isSome (by rw [hx]; rfl)
    obtain ⟨v', hv', hh⟩ := hheld x hxA
    rw [restrict_regs_of_mem hxA, hv'] at hx
    cases hx
    exact hh
  have hrun' := hok.run fr' s.mem ρ₀ w
    (by simp [fr', restrict, hfunc, tryCtx, termCtx, H.shape.ctxInv.func]) hvh
    (dfgCons_termCtx hcons _ _) (by simpa [fr', restrict, hslots] using hmem)
  have hio : instOutcome env p fr' s.mem ci = instOutcome env p s.frame s.mem ci :=
    instOutcome_congr (fr := s.frame) (fr' := fr') rfl rfl env p s.mem _
      fun x hx => restrict_regs_of_mem (hargsA x hx)
  rw [hio, hO] at hrun'
  obtain ⟨hU, k', i, ops, ρ₁, w₁, outs, w₂, hsr, hk1, hrets, hmr⟩ := hrun'
  rw [hfix] at hsr
  let D : Nat → Prop := fun n => L.tst.nextVreg ≤ n ∧ n < L.tst'.nextVreg
  have hD : ∀ d, D d → gn d = d := fun d hd => H.shape.temps d (by
    have : L.tst.nextVreg ≤ d := hd.1; omega)
  have hdefs : ∀ m ∈ pre ++ [.tryCall ci' T.info], ∀ d ∈ vdefs m, D d := by
    intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨h1, h2⟩ := hpre m hm d hd
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
      ∀ m ∈ pre ++ [.tryCall ci' T.info], ∀ u ∈ vuseNums m, D u ∨ ¬ D (gn u) := by
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
  have hren := seqRun_rename (sem := sem n) (ρ₀ := ρ₀) (ρ := ρ) (w := w)
    H.shape.ren (H.dsem.rename R gn H.shape.ren) hD hdefs
  obtain ⟨ρ₁', hsr', -, hA2⟩ := (hren (huses hU) hAg).2 hsr
  obtain ⟨hsegat, hsize⟩ := tseg_at hcode
  have htseg : tseg R bl b = (pre ++ [MInst.tryCall ci' T.info]).map (·.mapRegs R) := by
    rw [tseg_eq hL, hTl]
    show (tryFix T.info _).map _ = _
    rw [hfix]
  rw [htseg] at hsegat hsize
  obtain ⟨hmk, -⟩ := seqRun_stop_mem hsr
  have hk' : k' = pre.length := by
    rw [hms] at hk1; simp only [List.length_append, List.length_singleton] at hk1; omega
  subst hk'
  have hiT : i = .tryCall ci' T.info := by
    rw [List.getElem?_append_right (Nat.le_refl _)] at hmk
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hmk
    exact hmk.symm
  subst hiT
  -- the counted run of the terminator's code: no call before the `try_call`'s
  have hp0 : callsI pre = 0 := hpre0 pre ci' hms
  have hle : callsI ((pre ++ [MInst.tryCall ci' T.info]).map (·.mapRegs R)) ≤ 1 := by
    rw [callsI_map_mapRegs, callsI_append, hp0]
    simp [callsI, MInst.isCallI]
  have htk : callsI (((pre ++ [MInst.tryCall ci' T.info]).map (·.mapRegs R)).take pre.length) = 0 := by
    rw [List.map_append, List.take_left' (by simp), callsI_map_mapRegs, hp0]
  have hsrI := seqRun_counted_le1 hni hle ρ w n
  rw [hsr'] at hsrI
  simp only [Option.map_some, SeqEnd.liftW, htk, Nat.add_zero, MInst.isCallI] at hsrI
  obtain ⟨hstar, -, hi, hops, hsem, hlen, -⟩ := seqRun_stop_starP hvb hsegat hsrI
  have hK : pos f R bl b B.body.length + pre.length + 1 = vb.insts.size := by
    rw [hsize]; simp only [List.length_map, List.length_append, List.length_singleton]; omega
  have hback : vb.insts.back? = some ((MInst.tryCall ci' T.info).mapRegs R) := by
    rw [Array.back?_eq_getElem?, ← hK, Nat.add_sub_cancel]; exact hi
  obtain ⟨ss, ps, hcfg⟩ := H.cfg
  obtain ⟨hcont, -⟩ := tryInfoOf_spec hinfo
  have hsucc1 : succOf vc b T.info.handlers.length = some tlab := by
    rw [succOf_eq H.shape.labels hcfg hvb hback, targets_mapRegs]
    simp only [MInst.targets, hcont]
    rw [List.getElem?_append_right (by simp), List.length_map, Nat.sub_self]
    simp only [List.getElem?_cons_zero, Option.some.injEq]
    rw [List.getLastD_eq_getLast?, hlast]; rfl
  -- tracked values keep their registers across the terminator's code
  let ρ₂ := vdefUpd (ops.map (rnOp gn)) outs ρ₁'
  have hρ₂ : ∀ x ∈ A b B.body.length, ρ₂ (gn x) = ρ (gn x) := by
    intro x hx
    have hnd : ¬ D x := by
      have h4 : x < st0.nextVreg := H.cert.small _ _ x hx
      intro hd
      have h3 : L.tst.nextVreg ≤ x := hd.1
      exact absurd (Nat.lt_of_lt_of_le h4 hst0t) (Nat.not_lt.mpr h3)
    show vdefUpd (ops.map (rnOp gn)) outs ρ₁' (gn x) = ρ (gn x)
    rw [← hA2 x (.inr (hnoclobT x hx))]
    exact (seqRun_stop_frame (fun m hm hxm => hnd (hdefs m hm x hxm)) hsr).2
  have henv1 := edgeEnv_eq (V := CV) hvb heb (xs := []) (ps := []) (by rw [hbargs']; rfl)
    (by rw [hebp]; rfl) rfl ρ₂
  have hstep1 := VStep.step hvb hi hops hsem hlen (VNext.goto hK hsucc1 henv1)
  -- the successor
  let xs := et.normal.args.map (tryArgNum gn L.tst.nextVreg)
  have hbcb : bc.block ∈ edgeIds B.term := by
    rw [hbc]; rcases hBT with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] <;> simp [edgeIds]
  have htl' : blockIdx? f bc.block = some tl := by rw [hbc]; exact htl
  have hheld' : Held gn (A b B.body.length) ρ (tryNext s regs' bc cm').frame := by
    intro x hx
    obtain ⟨v, hv, hh⟩ := hheld x hx
    refine ⟨v, ?_, hh⟩
    show regs' x = some v
    rw [setMany_other hset (hnotres x hx), hv]
  have hcons' : DFGCons ctx (restrict (tryNext s regs' bc cm').frame (A b B.body.length)) := by
    refine dfgCons_congr (fr := restrict s.frame (A b B.body.length)) rfl rfl
      (funext fun x => ?_) hcons
    by_cases hx : x ∈ A b B.body.length
    · simp only [restrict, tryNext, hx, ite_true]
      exact setMany_other hset (hnotres x hx)
    · simp only [restrict, tryNext, hx, ite_false]
  have hxl : xs.length = bc.args.length := by rw [hbc]; simp [xs]
  have hlr := setMany_length hset
  simp only [List.length_map, List.length_range] at hlr
  have hxv : ∀ (m : Nat) a v x, bc.args[m]? = some a → (tryNext s regs' bc cm').frame.regs a = some v →
      xs[m]? = some x → VHolds v (ρ₂ x) := by
    intro m a v x ha hv hx
    rw [hbc] at ha
    simp only [List.getElem?_map, xs] at ha hx
    cases hta : et.normal.args[m]? with
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
          simp only [Clif.ExnTable.vals, Clif.TryDest.vals, List.mem_append, List.mem_filterMap]
          exact .inl ⟨.val v0, htam, rfl⟩))
        show VHolds v (ρ₂ (gn v0))
        rw [hρ₂ v0 hv0A]
        simp only [tryArgVal] at hv'
        rw [setMany_other hset (hnotres v0 hv0A)] at hv'
        obtain ⟨v', hv'', hh⟩ := hheld v0 hv0A
        rw [hv'] at hv''; cases hv''
        exact hh
      | ret ii =>
        have hii : ii < T.sig.returns.length := hargsOk _ htam
        have hiN : ii < (sigRets T.sig).length :=
          Nat.lt_of_lt_of_le hii (returns_le_sigRets _)
        have hvi : regs' (f.freshValue + ii) = some rvals[ii] :=
          setMany_nodup hset (List.Pairwise.map _ (fun a b h e => h (Nat.add_left_cancel e)) List.nodup_range) ii _ _
            (by simp [List.getElem?_map, hii]) (List.getElem?_eq_getElem (by omega))
        simp only [tryArgVal] at hv'
        rw [hvi] at hv'
        cases hv'
        have hr : (tryCtx ctx (L.start + B.body.length) L.data T.regs).tryRegs.1[ii]? =
            some (.vreg (L.tst.nextVreg + ii) .int) := by
          show T.regs.1[ii]? = _
          rw [hregsEq]; simp [hiN]
        obtain ⟨n, hn, hvh⟩ := hrets ii _ _ hr (List.getElem?_eq_getElem (by omega))
        cases hn
        have hDi : D (L.tst.nextVreg + ii) := ⟨by omega, by omega⟩
        show VHolds rvals[ii] (ρ₂ (L.tst.nextVreg + ii))
        rw [show ρ₂ (L.tst.nextVreg + ii) = ρ₂ (gn (L.tst.nextVreg + ii)) by rw [hD _ hDi]]
        show VHolds rvals[ii] (vdefUpd (ops.map (rnOp gn)) outs ρ₁' (gn (L.tst.nextVreg + ii)))
        rw [← hA2 _ (.inl hDi)]
        exact hvh
      | exn _ => exact absurd (hargsOk _ htam) id
  have hmr' : MRW slots cm' w₂ := by simpa [fr', restrict, hslots] using hmr
  obtain ⟨TB, hTB, hlenA, hne0, hM⟩ := enter_match H hB (s := tryNext s regs' bc cm') hcall hfunc
    hslots hheld' hcons' hbcb htl' hent hρ₂ hxl hxv hmr'
  obtain ⟨Lt, hLt⟩ := H.blow hTB
  obtain ⟨vbt, hvbt, -, -, -, -, -, -, -, -, hpt, -, -⟩ := H.shape.blk tl TB Lt hTB hLt
  simp only [hne0, ite_false] at hpt
  have hebba' : eb.branchArgs = (xs.map fun n => Reg.vreg n .int).toArray := by
    rw [hebba]
    refine congrArg List.toArray ?_
    simp only [xs, List.map_map]
    apply List.map_congr_left
    intro a ha
    cases a with
    | val v => simp [normArgReg, tryArgNum, H.shape.ren.vreg]
    | ret ii =>
      have hii : ii < T.sig.returns.length := hargsOk _ ha
      have hiN : ii < (sigRets T.sig).length := Nat.lt_of_lt_of_le hii (returns_le_sigRets _)
      have hg : gn (L.tst.nextVreg + ii) = L.tst.nextVreg + ii := H.shape.temps _ (by omega)
      simp [normArgReg, tryArgNum, hregsEq, hiN, H.shape.ren.vreg, hg]
    | exn _ => exact absurd (hargsOk _ ha) id
  have henv2 := edgeEnv_eq (V := CV) heb hvbt (xs := xs) (ps := TB.params.map (·.1)) hebba'
    (by rw [hpt]; simp [List.map_map, Function.comp_def]) (by simp only [List.length_map]; omega)
    (parCopyEnv ρ₂ [] [])
  have hpc : parCopyEnv ρ₂ [] [] = ρ₂ := rfl
  rw [hpc] at henv2
  have hebback : eb.insts.back? = some (.jump tl) := by rw [hebi]; rfl
  have hjump : ISem.counted sem (.jump tl) [] (w₂, n + 1) = some ([], (w₂, n + 1), .goto 0) := by
    rw [counted_noncall hni (by rfl) [] w₂ (n + 1) n, H.dsem.jump tl w₂]
    rfl
  have hstep2 : VStep vc (ISem.counted sem) (.run ⟨tlab, 0, parCopyEnv ρ₂ [] [], (w₂, n + 1)⟩)
      (.run ⟨tl, 0, parCopyEnv ρ₂ (TB.params.map (·.1)) xs, (w₂, n + 1)⟩) := by
    rw [hpc]
    refine VStep.step heb (by rw [hebi]; rfl) (i := .jump tl) (ops := #[]) rfl
      hjump rfl (VNext.goto (by rw [hebi]; rfl) ?_ henv2)
    rw [succOf_eq H.shape.labels hcfg heb hebback]; rfl
  exact ⟨_, _, _, _, hstar.star.trans (.step hstep1 (.single hstep2)), hM⟩

/-- **Whole runs, counted, for a family**: from matching states at CLIF call count `n`, every
CLIF outcome is realised by the counted VCode run from counter `n` (call number `n` with
`sem n`): the steps without extern call by the probe `semB n` (`Hb`), the calling ones with the
environment restricted to their invocation (`Hs`). -/
theorem sim_runG (hni : NoncallIndep sem) (hPr : ProbeOf semB sem) {cs : Clif.State}
    (hP : RunPrem env p f cs)
    (Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    (Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A (sem n) MRW
      (env.only (Clif.Invoked env p s)) p)
    (hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1)
    (htc : TryCallsOne f) :
    ∀ fuel s n b k ρ w, ReachN env p cs s n →
      Match f ctx R gn bl A MRW slots s ⟨b, k, ρ, w⟩ →
        RunOkAbi vc (ISem.counted sem) (fun sl cm w => MRW sl cm w.1) slots (fun _ => True)
          ⟨b, k, ρ, (w, n)⟩
          (Clif.runLoop env p fuel s) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro s n b k ρ w hr hm
  cases fuel with
  | zero => trivial
  | succ m =>
    rw [Clif.runLoop_succ]
    have hfunc : s.frame.func = f := hm.2.1
    cases hbody : s.frame.body with
    | nil =>
      cases hty : s.frame.term.isTry with
      | false =>
        obtain ⟨T1, T2, T3⟩ := term_stepG hPr (Hb n) hm hbody hty
        have hc0 : callNum s = 0 := by simp [callNum, hbody, hty]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := T1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc0, Nat.add_zero] at h
          exact RunOkAbi.prefix hstar h
        | done vals cm =>
          obtain ⟨us, outs, w', sv, hret, h1, h2, hsv, h3, h4, h5⟩ := T2 vals cm hs
          exact ⟨us, outs, (w', n), s.mem, sv, hret, h1, h2, trivial, h3, h4, h5⟩
        | trapped c => exact T3 c hs
        | stuck => trivial
      | true =>
        obtain ⟨B, j, hB, hterm, -⟩ := hm.2.2.2.2
        have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
        obtain ⟨et, hT⟩ : ∃ et, IsTryWith s.frame.term et := by
          cases ht : s.frame.term with
          | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
          | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
          | _ => rw [ht] at hty; cases hty
        have hind : ∀ callee args, s.frame.term = .tryCallIndirect callee args et → ∀ cv,
            s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
          fun callee args ht => hP.tryIndirect s callee args et hr.reach hbody ht
            ⟨B, hBmem, hterm.symm.trans ht⟩
        obtain ⟨Tnd, Tnx⟩ := term_step_tryG hni (Hs s n hr) htc hm hbody hT hind
        have hst : Clif.step (env.only (Clif.Invoked env p s)) p s = Clif.step env p s :=
          Clif.step_only fun _ _ _ h => h
        have hc1 : callNum s = 1 := by simp [callNum, hbody, hty]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨⟨hb', bc, ht'⟩, N1, N2, N3⟩ := Tnx s' (hst.trans hs)
          have hst' : Clif.step (env.only (Clif.Invoked env p s)) p s' = Clif.step env p s' := by
            apply Clif.step_only
            intro _ _ _ ⟨_, hI⟩
            simp [hb', ht'] at hI
          have hc0 : callNum s' = 0 := by simp [callNum, hb', ht', Clif.Terminator.isTry]
          cases m with
          | zero => trivial
          | succ m' =>
            show RunOkAbi vc (ISem.counted sem) (fun sl cm w => MRW sl cm w.1) slots (fun _ => True) _
              (Clif.runLoop env p (m' + 1) s')
            rw [Clif.runLoop_succ]
            cases hs' : Clif.step env p s' with
            | next s'' =>
              obtain ⟨b', k', ρ', w', hstar, hm'⟩ := N3 s'' (hst'.trans hs')
              have h := ih m' (by omega) s'' (n + callNum s + callNum s') b' k' ρ' w'
                ((hr.snoc hs).snoc hs') hm'
              rw [hc1, hc0, Nat.add_zero] at h
              exact RunOkAbi.prefix hstar h
            | done vals cm => exact absurd (hst'.trans hs') (N2 vals cm)
            | trapped c => exact absurd (hst'.trans hs') (N1 c)
            | stuck => trivial
        | done vals cm => exact absurd (hst.trans hs) (Tnd vals cm)
        | trapped c =>
          rcases hT with ⟨fn, args, hT⟩ | ⟨callee, args, hT⟩
          · exact absurd (hterm.symm.trans hT)
              (hP.tryCall s c fn args et hr.reach hs hbody hT B hBmem)
          · exact absurd (hterm.symm.trans hT)
              (hP.tryCallInd s c callee args et hr.reach hs hbody hT B hBmem)
        | stuck => trivial
    | cons st rest =>
      obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hm
      have hst : st ∈ B.body := by
        rw [hbd] at hbody
        exact List.mem_of_mem_drop (hbody ▸ List.mem_cons_self)
      have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
      have hext : ∀ fn args, st.inst = .call fn args → ∀ e, s.frame.func.extern? fn = some e →
          p.func? e.name = none := by
        intro fn args hi e he
        exact (Hb n).ext B hBmem st hst fn args hi e (hfunc ▸ he)
      have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
          s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
        fun sig callee args hi => hP.indirect s st rest sig callee args hr.reach hbody hi
          ⟨B, hBmem, hst⟩
      cases hcl : st.inst.isCallLike with
      | false =>
        obtain ⟨S1, S2⟩ := stmt_stepG_noCall hPr (Hb n) hm hbody hcl hind
        have hc0 : callNum s = 0 := by simp [callNum, hbody, hcl]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := S1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc0, Nat.add_zero] at h
          exact RunOkAbi.prefix hstar h
        | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
        | trapped c => exact S2 c hs (hP.stmt s c st rest hr.reach hs hbody)
        | stuck => trivial
      | true =>
        obtain ⟨S1, S2⟩ := stmt_stepG_call hni (Hs s n hr) hseg hm hbody hcl hind
        have hc1 : callNum s = 1 := by simp [callNum, hbody, hcl]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := S1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc1] at h
          exact RunOkAbi.prefix hstar h
        | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
        | trapped c => exact S2 c hs (hP.stmt s c st rest hr.reach hs hbody)
        | stuck => trivial


/-- **`try_call`/`try_call_indirect` step, counted** (`term_step_tryG` for `csem F fctx (XI.at n)`). -/
theorem term_step_tryI {n : Nat}
    (H : DriverHyp f vc ctx st0 R gn bl A (csem F fctx (XI.at n)) MR env p) (htc : TryCallsOne f)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : Arm.ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    {et : Clif.ExnTable} (hT : IsTryWith s.frame.term et)
    (hind : ∀ callee args, s.frame.term = .tryCallIndirect callee args et → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ vals cm, Clif.step env p s ≠ .done vals cm) ∧
    ∀ s', Clif.step env p s = .next s' →
      (s'.frame.body = [] ∧ ∃ bc, s'.frame.term = .jump bc) ∧
      (∀ c, Clif.step env p s' ≠ .trapped c) ∧ (∀ vals cm, Clif.step env p s' ≠ .done vals cm) ∧
      ∀ s'', Clif.step env p s' = .next s'' →
        ∃ b' k' ρ' w', Star (VStep vc (csemI F fctx XI)) (.run ⟨b, k, ρ, (w, n)⟩)
          (.run ⟨b', k', ρ', (w', n + 1)⟩) ∧
          Match f ctx R gn bl A MR slots s'' ⟨b', k', ρ', w'⟩ :=
  term_step_tryG (sem := fun n => csem F fctx (XI.at n)) (noncallIndep_csem F fctx XI) H htc hm
    hbody hT hind

/-- **Whole runs, counted** (`sim_runG` for `csem F fctx (XI.at n)`, the probe with failing
calls). -/
theorem sim_runI {cs : Clif.State} (hP : RunPrem env p f cs)
    (Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A (csem F fctx (XI.at n).noCall) MR
      (env.only fun _ _ _ => False) p)
    (Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A (csem F fctx (XI.at n)) MR
      (env.only (Clif.Invoked env p s)) p)
    (hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1)
    (htc : TryCallsOne f) :
    ∀ fuel s n b k ρ w, ReachN env p cs s n →
      Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩ →
        RunOkAbi vc (csemI F fctx XI) (MRI MR) slots (fun _ => True) ⟨b, k, ρ, (w, n)⟩
          (Clif.runLoop env p fuel s) :=
  sim_runG (sem := fun n => csem F fctx (XI.at n))
    (semB := fun n => csem F fctx (XI.at n).noCall) (noncallIndep_csem F fctx XI)
    (probeOf_csem F fctx XI) hP Hb Hs hseg htc
end

/-- **CLIF → counted VCode for the backend's `csem`** (`iselSim_relW` for the counted run
`csemI F ctx XI` from counter `0`), with the callee contract of call number `n` needed only at
the states of the CLIF run reached after `n` extern calls, for the environment restricted to
that state's invocation; under the ISLE call-count properties `InstCallsOne`, `TryCallsOne`. -/
theorem iselSim_relWI {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VRetFrom vc (csemI F ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ us outs w ∧
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w.1) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTrapFrom vc (csemI F ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c') := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A (csem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)
      (RelW Γ f c) (env.only fun _ _ _ => False) p := fun n =>
    driverHyp_relW hsub hc hshape hcert hbr (xCallsOk_none _ _ _ _) (xCallsIndOk_none _ _ _ _)
      hsym hslot
  have Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (csem F ⟨fa.k, af.slotBase⟩ (XI.at n)) (RelW Γ f c) (env.only (Clif.Invoked env p s)) p :=
    fun s n hr => driverHyp_relW hsub hc hshape hcert hbr (hX s n hr).1 (hX s n hr).2 hsym hslot
  have hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1 :=
    fun _ _ _ _ hB hstm hcl => segCalls_of (Hb 0) hone hB hstm hcl
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := by
    have hf := hce.func
    exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
        (hf ▸ hB),
      fun s c callee args et hr hs hb hT B hB =>
        htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
      fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
        htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
      fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
        htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩
  obtain ⟨k0, ρ₁, w₁, hstar, hm⟩ := entry_step (Hb 0)
    (driverSem_csem F ⟨fa.k, af.slotBase⟩ (XI.at 0).noCall)
    (memRefines_csem _ _ (XI.at 0).noCall hslot hsym) (mrStable_relW Γ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs
  have hrun := RunOkAbi.runOk (RunOkAbi.prefix
    (vstar_mapW (csem_noCall_proj F ⟨fa.k, af.slotBase⟩ XI 0) hstar)
    (sim_runI hP Hb Hs hseg htc fuel cs 0 0 k0 ρ₁ w₁ .refl hm))
  refine ⟨fun vals cm h => ?_, fun c' h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1.1 _)⟩
  · rw [h] at hrun
    exact hrun

end E2E
