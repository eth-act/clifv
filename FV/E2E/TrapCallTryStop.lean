import FV.Backend.Proof.LowerSimU
import FV.E2E.TrapCallTry

/-!
# Callee traps of `try_call`s: the CLIF → VCode prefix (S9b, #375)

`sim_runX` follows a callee's exception through a `try_call`'s handler; for the trap of a
`try_call`'s callee the proof needs the VCode run only up to that call. Here the CLIF → VCode
simulation of a run of `env` that traps with `c`, under the activation semantics of the proof
device `trapEnv env c` (`FV/E2E/TrapCallClif.lean`), **stopped at the trapping step**:

* `VTryRaiseFrom`: the VCode run reaches a `tryCall` whose callee raises (`XR`);
* `term_step_try_stop`: a `try_call`/`try_call_indirect` whose extern unwinds is matched by the
  code up to its `tryCall` (`term_step_try_exn`'s first part: `try_raise`, renamed);
* `sim_trapStop` (fuel induction on `env`'s run, `step_trapRel`): the VCode run from a matching
  state reaches an explicit trap with `c` (`VTrapFrom`), a raising `call` that ends the
  activation (`VUnwFrom`), or a raising `tryCall` (`VTryRaiseFrom`).
-/

namespace E2E

open Backend Backend.Proof

/-- **From `vs`, the VCode run reaches a `tryCall` whose callee raises** (`XR`; operands
`ops`, the raised object `obj`, the world `w'` after the unwinder). -/
def VTryRaiseFrom (vc : VCode) (sem : Sem) (XR : XRaise) (vs : VState CV Arm.ArmState) : Prop :=
  ∃ b k ρ w vb info ti ops obj w', Star (VStep vc sem) (.run vs) (.run ⟨b, k, ρ, w⟩) ∧
    vc.blocks[b]? = some vb ∧ vb.insts[k]? = some (.tryCall info ti) ∧
    (MInst.tryCall info ti).operands = .ok ops ∧
    XR.raise (callDest info) (vuses ops ρ) w = some (obj, w')

theorem VTryRaiseFrom.prefix {vc : VCode} {sem : Sem} {XR : XRaise}
    {vs vs' : VState CV Arm.ArmState} (h : Star (VStep vc sem) (.run vs) (.run vs'))
    (h' : VTryRaiseFrom vc sem XR vs') : VTryRaiseFrom vc sem XR vs := by
  obtain ⟨b, k, ρ, w, vb, info, ti, ops, obj, w', hs, h1⟩ := h'
  exact ⟨b, k, ρ, w, vb, info, ti, ops, obj, w', h.trans hs, h1⟩

end E2E

namespace Backend.Proof.Driver

open Backend Backend.Proof E2E

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {sem : Sem}
  {MR : MemRelT} {env : Clif.XEnv} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
  {F : BitVec 64 → Prop} {X : ExtSem} {XR : XRaise} {sb : Nat} {syms : String → Option Nat}
  {out : Nat}

/-- **A `try_call`/`try_call_indirect` whose extern unwinds, up to its call**: the VCode run
reaches the terminator's `tryCall`, whose callee raises (`term_step_try_exn` without the
handler). -/
theorem term_step_try_stop (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHyp f sem MR env F X XR sb syms out)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : Arm.ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    {et : Clif.ExnTable} (hT : IsTryWith s.frame.term et)
    {e : Clif.Exn} {mm : Clif.Mem} (hr : Clif.raiseAt? env p s = some (e, mm)) :
    VTryRaiseFrom vc sem XR ⟨b, k, ρ, w⟩ := by
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
  obtain ⟨vb, hvb, -, -, -, hst0t, -, htry, hcode, -, -, -, -⟩ := H.shape.blk b B L hB hL
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
      instRaise env p s.frame s.mem ci = some (e, mm) ∧
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
  have hmax1 : T.sig.returns.length ≤ max T.sig.returns.length 2 := Nat.le_max_left _ _
  have hmax2 : 2 ≤ max T.sig.returns.length 2 := Nat.le_max_right _ _
  have hfix : tryFix T.info L.tst'.emitted.toList = pre' ++ [.tryCall ci' T.info] := by
    rw [hms, tryFix_append]
  let fr' := restrict s.frame (A b B.body.length)
  let ρ₀ : Nat → CV := fun n => ρ (gn n)
  have hvh : ValsHeld fr' ρ₀ := by
    intro x v hx
    have hxA : x ∈ A b B.body.length := restrict_regs_isSome (by rw [hx]; rfl)
    obtain ⟨v', hv', hh⟩ := hheld x hxA
    rw [restrict_regs_of_mem hxA, hv'] at hx
    cases hx
    exact hh
  have hraise' : instRaise env p fr' s.mem ci = some (e, mm) := by
    rw [instRaise_congr (fr := s.frame) (fr' := fr') rfl _ _
      (fun x hx => restrict_regs_of_mem (hargsA x hx))]
    exact hraise
  obtain ⟨hU, ops0, ρ₁, w₁, obj, w₂, hsr, hra, -, -⟩ :=
    try_raise HR.rs HR.ref HR.mem HR.mrs HR.outOk HR.xr HR.xri HR.sym HR.mrsyms H.shape.ctxInv
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
  have huses : ∀ m ∈ pre' ++ [.tryCall ci' T.info], ∀ u ∈ vuseNums m, D u ∨ ¬ D (gn u) := by
    intro m hm u hu
    rcases List.mem_append.mp hm with hm | hm
    · exact hU' m (by rw [hms]; exact List.mem_append_left _ hm) u hu
    · rw [List.mem_singleton] at hm
      subst hm
      rw [vuseNums_tryCall] at hu
      exact hU' _ (by rw [hms]; simp) u hu
  have hAg : Agree gn D ρ₀ ρ := fun _ _ => rfl
  have hren := seqRun_rename (sem := sem) (ρ₀ := ρ₀) (ρ := ρ) (w := w) H.shape.ren
    (H.dsem.rename R gn H.shape.ren) hD hdefs
  obtain ⟨ρ₁', hsr', hA1, -⟩ := (hren huses hAg).2 hsr
  obtain ⟨hsegat, -⟩ := tseg_at hcode
  have htseg : tseg R bl b = (pre' ++ [MInst.tryCall ci' T.info]).map (·.mapRegs R) := by
    rw [tseg_eq hL, hTl]
    show (tryFix T.info _).map _ = _
    rw [hfix]
  rw [htseg] at hsegat
  obtain ⟨hstar, -, hi, hops', -, -, -⟩ := seqRun_stop_star hvb hsegat hsr'
  -- the uses of the call are kept by the renaming
  have hu : ∀ o ∈ ops.toList, o.isUse = true → D o.vreg ∨ ¬ D (gn o.vreg) := by
    intro o ho hou
    have hm' : o.vreg ∈ vuseNums (.tryCall ci' T.info) := by
      rw [vuseNums_tryCall]
      simp only [vuseNums, hops]
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨ho, hou⟩)
    exact huses _ (by simp) o.vreg hm'
  have hvu := vuses_rename hA1 hu
  obtain ⟨ci'', ti'', hci'', hdest⟩ : ∃ ci'' ti'', (MInst.tryCall ci' T.info).mapRegs R =
      .tryCall ci'' ti'' ∧ callDest ci'' = callDest ci' := by
    obtain ⟨dd, us, ds⟩ := ci'
    cases dd <;> exact ⟨_, _, rfl, rfl⟩
  rw [hci''] at hi hops'
  exact ⟨b, _, ρ₁', w₁, vb, ci'', ti'', ops.map (rnOp gn), obj, w₂, hstar, hvb, hi, hops',
    by rw [hdest, hvu]; exact hra⟩

/-- The step from a `try_call`'s pending `jump` never traps. -/
theorem step_tryNext_ne_trapped {env' : Clif.Env} {s : Clif.State} {regs : Clif.Regs}
    {bc : Clif.BlockCall} {cm : Clif.Mem} (c' : Clif.TrapCode) :
    Clif.step env' p (tryNext s regs bc cm) ≠ .trapped c' := by
  rw [Clif.step_term _ _ _ rfl]
  exact (stepTerm_branch_ne (t := .jump bc) (by simp [dests])).2 c'

/-- **The CLIF → VCode simulation of a trapping run, stopped at the trapping step**: for a run
of `env` (a program without functions) that traps with `c` under `TrapsExplicitCT` (callee
traps allowed, `try_call` callees included), and the activation semantics `sem` of the proof
device `trapEnv env c` (`DriverHyp`, `UnwShape`, `RaiseHyp`), the VCode run from a matching
state reaches an explicit trap with `c`, a raising `call` that ends the activation, or a raising
`tryCall`. -/
theorem sim_trapStop {env0 : Clif.Env} {c : Clif.TrapCode} (hp : p.funcs = [])
    (H : DriverHyp f vc ctx st0 R gn bl A sem MR (trapEnv env0 c).toEnv p)
    (HU : UnwShape f vc ctx R gn bl A)
    (HR : RaiseHyp f sem MR (trapEnv env0 c) F X XR sb syms out)
    {cs : Clif.State} (hcf : cs.frame.func = f) (htr : TrapsExplicitCT env0 p cs) :
    ∀ (fuel : Nat) (s : Clif.State) (vs : VState CV Arm.ArmState), Reach env0 p cs s →
      Match f ctx R gn bl A MR slots s vs → Clif.runLoop env0 p fuel s = .trapped c →
      VTrapFrom vc sem vs c ∨ (∃ obj w', VUnwFrom vc sem XR vs obj w') ∨
        VTryRaiseFrom vc sem XR vs := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro s vs hr hm hrun
  cases fuel with
  | zero => simp [Clif.runLoop] at hrun
  | succ n =>
  obtain ⟨b, k, ρ, w⟩ := vs
  rw [Clif.runLoop_succ] at hrun
  have hrel := step_trapRel env0 c hp s
  have hnx : ∀ s', Clif.step env0 p s = .next s' →
      Clif.step (trapEnv env0 c).toEnv p s = .next s' := by
    intro s' hs
    rcases hrel with e | ⟨e, -⟩
    · rw [e, hs]
    · rw [hs] at e; cases e
  -- a continuing step
  have hcont : ∀ s', Clif.step env0 p s = .next s' → Clif.runLoop env0 p n s' = .trapped c →
      (∃ vs', Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
        Match f ctx R gn bl A MR slots s' vs') →
      VTrapFrom vc sem ⟨b, k, ρ, w⟩ c ∨ (∃ obj w', VUnwFrom vc sem XR ⟨b, k, ρ, w⟩ obj w') ∨
        VTryRaiseFrom vc sem XR ⟨b, k, ρ, w⟩ := by
    intro s' hs hrun' ⟨vs', hstar, hm'⟩
    rcases ih n (by omega) s' vs' (hr.snoc hs) hm' hrun' with h | ⟨o, w', h⟩ | h
    · exact .inl (VTrapFrom.prefix hstar h)
    · exact .inr (.inl ⟨o, w', VUnwFrom.prefix hstar h⟩)
    · exact .inr (.inr (VTryRaiseFrom.prefix hstar h))
  cases hbody : s.frame.body with
  | cons st rest =>
    obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hm
    have hst : st ∈ B.body := by
      rw [hbd] at hbody
      exact List.mem_of_mem_drop (hbody ▸ List.mem_cons_self)
    have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
    have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
        s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
      fun sig callee args hi => htr.indirect s st rest sig callee args hr hbody hi
        ⟨B, hcf ▸ hBmem, hst⟩
    obtain ⟨S1, S2⟩ := stmt_step H hm hbody hind
    cases hs : Clif.step env0 p s with
    | next s' =>
      rw [hs] at hrun
      exact hcont s' hs hrun (S1 s' (hnx s' hs))
    | trapped c' =>
      rw [hs] at hrun
      cases hrun
      rcases hrel with e | ⟨-, m, e⟩
      · rw [hs] at e
        rcases htr.stmt s c st rest hr hs hbody with hx | hx
        · exact .inl (S2 c e hx)
        · exact absurd e (step_call_trap_stuck env0 c hp hbody hx hs)
      · have hra := raiseAt_of_trapRel env0 c hp (fun h => by rw [hbody] at h; cases h) hs e
        rw [raiseAt_stmt hbody] at hra
        obtain ⟨obj, w', hu, -, -⟩ := stmt_step_raise H HU HR hm hbody hra
        exact .inr (.inl ⟨obj, w', hu⟩)
    | done vals cm => rw [hs] at hrun; cases hrun
    | stuck msg => rw [hs] at hrun; cases hrun
  | nil =>
    obtain ⟨B, j, hB, hterm, -⟩ := hm.2.2.2.2
    have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
    cases hty : s.frame.term.isTry with
    | false =>
      obtain ⟨T1, -, T3⟩ := term_step H hm hbody hty
      cases hs : Clif.step env0 p s with
      | next s' =>
        rw [hs] at hrun
        exact hcont s' hs hrun (T1 s' (hnx s' hs))
      | trapped c' =>
        rw [hs] at hrun
        cases hrun
        rcases hrel with e | ⟨-, m, e⟩
        · rw [hs] at e
          exact .inl (T3 c e)
        · have hra := raiseAt_of_trapRel env0 c hp (fun _ => hty) hs e
          rw [raiseAt_term_none hbody hty
            (fun fn args ht => H.noTail B hBmem fn args (hterm.symm.trans ht))] at hra
          cases hra
      | done vals cm => rw [hs] at hrun; cases hrun
      | stuck msg => rw [hs] at hrun; cases hrun
    | true =>
      obtain ⟨et, hT⟩ : ∃ et, IsTryWith s.frame.term et := by
        cases ht : s.frame.term with
        | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
        | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
        | _ => rw [ht] at hty; cases hty
      have hind : ∀ callee args, s.frame.term = .tryCallIndirect callee args et → ∀ cv,
          s.frame.get callee = .ok cv → ∀ g ∈ p.funcs,
            s.mem.symbols g.name ≠ some cv.toNat :=
        fun callee args ht => htr.tryIndirect s callee args et hr hbody ht
          ⟨B, hcf ▸ hBmem, hterm.symm.trans ht⟩
      obtain ⟨-, Tnx⟩ := term_step_try H hm hbody hT hind
      cases hs : Clif.step env0 p s with
      | next s' =>
        rw [hs] at hrun
        obtain ⟨-, -, N3⟩ := Tnx s' (hnx s' hs)
        -- `s'` is the pending `jump`
        have hs' : ∃ regs bc cm, s' = tryNext s regs bc cm := by
          rw [Clif.step_term _ _ _ hbody] at hs
          rcases hT with ⟨fn, args, ht⟩ | ⟨callee, args, ht⟩
          · rw [ht] at hs
            obtain ⟨-, hnx'⟩ := stepTry_spec (env := env0) (p := p) (args := args) (et := et)
              (fun e he => H.tryExt B hBmem fn args et (hterm.symm.trans ht) e
                (hm.2.1 ▸ he))
            obtain ⟨-, bc, -, cm, regs, -, -, -, -, rfl⟩ := hnx' s' hs
            exact ⟨regs, bc, cm, rfl⟩
          · rw [ht] at hs
            obtain ⟨-, hnx'⟩ := stepTryInd_spec (env := env0) (p := p) (args := args) (et := et)
              (hind callee args ht)
            obtain ⟨-, bc, -, cm, regs, -, -, -, -, rfl⟩ := hnx' s' hs
            exact ⟨regs, bc, cm, rfl⟩
        obtain ⟨regs, bc, cm, rfl⟩ := hs'
        cases n with
        | zero => simp [Clif.runLoop] at hrun
        | succ m =>
          dsimp only at hrun
          rw [Clif.runLoop_succ] at hrun
          have hrel' := step_trapRel env0 c hp (tryNext s regs bc cm)
          cases hs2 : Clif.step env0 p (tryNext s regs bc cm) with
          | next s'' =>
            rw [hs2] at hrun
            have hs2' : Clif.step (trapEnv env0 c).toEnv p (tryNext s regs bc cm) = .next s'' := by
              rcases hrel' with e | ⟨e, -⟩
              · rw [e, hs2]
              · rw [hs2] at e; cases e
            obtain ⟨vs', hstar, hm'⟩ := N3 s'' hs2'
            rcases ih m (by omega) s'' vs' ((hr.snoc hs).snoc hs2) hm' hrun with h | ⟨o, w', h⟩ | h
            · exact .inl (VTrapFrom.prefix hstar h)
            · exact .inr (.inl ⟨o, w', VUnwFrom.prefix hstar h⟩)
            · exact .inr (.inr (VTryRaiseFrom.prefix hstar h))
          | trapped c' => exact absurd hs2 (step_tryNext_ne_trapped c')
          | done vals cm' => rw [hs2] at hrun; cases hrun
          | stuck msg => rw [hs2] at hrun; cases hrun
      | trapped c' =>
        rw [hs] at hrun
        cases hrun
        rcases hrel with e | ⟨-, m, e⟩
        · rw [hs] at e
          exact absurd e (step_try_trap_stuck env0 c hp hbody hT hs)
        · exact .inr (.inr (term_step_try_stop H HU HR hm hbody hT
            (raiseAt_of_trapRel_try env0 c hp hbody hT hs)))
      | done vals cm => rw [hs] at hrun; cases hrun
      | stuck msg => rw [hs] at hrun; cases hrun

/-- **`sim_trapStop` from the entry** (`driver_correctU`'s counterpart): the VCode run from
the entry reaches an explicit trap with `c`, a raising `call` that ends the activation, or a
raising `tryCall`. -/
theorem driver_trapStop {env0 : Clif.Env} {c : Clif.TrapCode} (hp : p.funcs = [])
    (H : DriverHyp f vc ctx st0 R gn bl A sem MR (trapEnv env0 c).toEnv p)
    (HU : UnwShape f vc ctx R gn bl A)
    (HR : RaiseHyp f sem MR (trapEnv env0 c) F X XR sb syms out) (hds : DriverSem sem)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicitCT env0 p cs) {fuel : Nat}
    (hrun : Clif.runLoop env0 p fuel cs = .trapped c) :
    VTraps vc sem ρ₀ w₀ c ∨ (∃ obj w', VUnwinds vc sem XR ρ₀ w₀ obj w') ∨
      VTryRaiseFrom vc sem XR ⟨0, 0, ρ₀, w₀⟩ := by
  obtain ⟨k, ρ₁, w₁, hstar, hm⟩ := entry_step H hds HR.mem HR.mrs hB0 hcall hfunc hslots hbody
    hterm hregs hty hsig hmr hargs (ρ₀ := ρ₀)
  rcases sim_trapStop hp H HU HR hfunc htr fuel cs _ (.refl _) hm hrun with h | ⟨o, w', h⟩ | h
  · exact .inl (VTrapFrom.prefix hstar h)
  · exact .inr (.inl ⟨o, w', VUnwFrom.prefix hstar h⟩)
  · exact .inr (.inr (VTryRaiseFrom.prefix hstar h))

end

end Backend.Proof.Driver
