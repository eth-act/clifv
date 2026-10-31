import FV.Backend.Proof.LowerSim
import FV.Backend.Proof.LowerSimURaise
import FV.Backend.Proof.LowerSimUCheck

/-!
# The driver simulation with unwinding: CLIF `runLoopX` ↦ VCode (S10e, #232)

`docs/plans/unwinding.md`, "The exceptional edge in the per-function theorem". The driver
simulation (`LowerSim.lean`) for the CLIF runs with unwinding (`Clif.runLoopX`), for any
activation semantics `sem` with the facts the proof uses (`RaiseHyp`: `Refines`, `MemRefines`,
the steps of raising calls `RaiseSem`, the memory relation's facts, the callees' exceptional
results `XRaiseOk`/`XRaiseIndOk`) — `csemU` and the dead-cleanup chain's `valueSemU` both have
them. A step whose call does not raise is a step of `Clif.step env.toEnv` (`stepX_of_not_stuck`),
simulated by `stmt_step`/`term_step`/`term_step_try` under the old hypotheses `DriverHyp` (for
`env.toEnv`); the new steps:

* `stmt_step_raise`: a `call`/`call_indirect` statement whose extern unwinds — the CLIF frame
  is left (`.unwound`), the VCode run reaches a `call` whose callee raises and which ends the
  activation (`VUnwFrom`), with the exception object and the world related to the extern's
  memory (`stmt_raise`, renamed);
* `term_step_try_exn`: a `try_call`/`try_call_indirect` whose extern unwinds, caught by the
  first item of its exception table (a `tag 0`/`tag 1` handler, which catches a Rust exception,
  `ExnRel`) — the payload bound, then the jump to the handler (two CLIF steps) are simulated by
  the code up to the `tryCall` (`try_raise`, renamed), its `.goto 0` into the landing-pad edge
  block and that block's `jump` (`UnwShape.tries`);
* `sim_runX` (strong induction on the fuel), `driver_correctU` (from the entry).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## CLIF facts -/

theorem instRaise_congr {env : Clif.XEnv} {p : Clif.Program} {fr fr' : Clif.Frame}
    (hf : fr'.func = fr.func) (cm : Clif.Mem) (i : Clif.Inst)
    (h : ∀ x ∈ instArgs i, fr'.regs x = fr.regs x) :
    instRaise env p fr' cm i = instRaise env p fr cm i := by
  cases i with
  | call fn args =>
    have hg : fr'.getMany args = fr.getMany args :=
      getMany_congr (fun x hx => h x (by simpa [instArgs] using hx))
    simp only [instRaise, Clif.callRaise, hf, hg]
  | callIndirect sig callee args =>
    have hg : fr'.getMany args = fr.getMany args :=
      getMany_congr (fun x hx => h x (by simp [instArgs, hx]))
    have hc : fr'.get callee = fr.get callee := get_congr (h callee (by simp [instArgs]))
    simp only [instRaise, Clif.callIndRaise, hf, hg, hc]
  | _ => rfl

theorem raiseAt_stmt {env : Clif.XEnv} {p : Clif.Program} {s : Clif.State} {st : Clif.Stmt}
    {rest : List Clif.Stmt} (h : s.frame.body = st :: rest) :
    Clif.raiseAt? env p s = instRaise env p s.frame s.mem st.inst := by
  simp only [Clif.raiseAt?, h]
  cases st.inst <;> rfl

theorem raiseAt_tryCall {env : Clif.XEnv} {p : Clif.Program} {s : Clif.State}
    {fn : Clif.FnRef} {args : List Clif.ValueId} {et : Clif.ExnTable} (hb : s.frame.body = [])
    (ht : s.frame.term = .tryCall fn args et) {e : Clif.Exn} {m : Clif.Mem}
    (h : Clif.raiseAt? env p s = some (e, m)) :
    instRaise env p s.frame s.mem (.call fn args) = some (e, m) := by
  simp only [Clif.raiseAt?, hb, ht] at h
  unfold Clif.tryCallRaise at h
  split at h
  · exact h
  · cases h

theorem raiseAt_tryCallInd {env : Clif.XEnv} {p : Clif.Program} {s : Clif.State}
    {callee : Clif.ValueId} {args : List Clif.ValueId} {et : Clif.ExnTable}
    (hb : s.frame.body = []) (ht : s.frame.term = .tryCallIndirect callee args et) {e : Clif.Exn}
    {m : Clif.Mem} (h : Clif.raiseAt? env p s = some (e, m)) :
    instRaise env p s.frame s.mem (.callIndirect et.sig callee args) = some (e, m) := by
  simp only [Clif.raiseAt?, hb, ht] at h
  unfold Clif.tryCallIndRaise at h
  split at h
  · exact h
  · cases h

theorem raiseAt_term_none {env : Clif.XEnv} {p : Clif.Program} {s : Clif.State}
    (hb : s.frame.body = []) (ht : s.frame.term.isTry = false)
    (hnr : ∀ fn args, s.frame.term ≠ .returnCall fn args) : Clif.raiseAt? env p s = none := by
  simp only [Clif.raiseAt?, hb]
  cases h : s.frame.term with
  | returnCall fn args => exact absurd h (hnr fn args)
  | tryCall _ _ _ => rw [h] at ht; cases ht
  | tryCallIndirect _ _ _ => rw [h] at ht; cases ht
  | _ => rfl

theorem stepX_next_of {env : Clif.XEnv} {p : Clif.Program} {xs : Clif.XState} {s' : Clif.State}
    (h : Clif.step env.toEnv p xs.s = .next s') : ∃ t, Clif.stepX env p xs = .next ⟨s', t⟩ := by
  rw [Clif.stepX_of_not_stuck (fun msg e => by rw [h] at e; cases e), h]
  exact ⟨_, rfl⟩

theorem stepX_done_of {env : Clif.XEnv} {p : Clif.Program} {xs : Clif.XState}
    {vals : List Clif.Val} {cm : Clif.Mem} (h : Clif.step env.toEnv p xs.s = .done vals cm) :
    Clif.stepX env p xs = .done vals cm := by
  rw [Clif.stepX_of_not_stuck (fun msg e => by rw [h] at e; cases e), h]
  rfl

theorem stepX_trapped_of {env : Clif.XEnv} {p : Clif.Program} {xs : Clif.XState}
    {c : Clif.TrapCode} (h : Clif.step env.toEnv p xs.s = .trapped c) :
    Clif.stepX env p xs = .trapped c := by
  rw [Clif.stepX_of_not_stuck (fun msg e => by rw [h] at e; cases e), h]
  rfl

theorem stepX_stuck_of {env : Clif.XEnv} {p : Clif.Program} {xs : Clif.XState} {msg : String}
    (h : Clif.step env.toEnv p xs.s = .stuck msg) (hr : Clif.raiseAt? env p xs.s = none) :
    Clif.stepX env p xs = .stuck msg := by
  simp only [Clif.stepX, hr, h, Clif.liftStep]

theorem stepX_next_inv {env : Clif.XEnv} {p : Clif.Program} {xs xs' : Clif.XState}
    (hr : Clif.raiseAt? env p xs.s = none) (h : Clif.stepX env p xs = .next xs') :
    Clif.step env.toEnv p xs.s = .next xs'.s := by
  simp only [Clif.stepX, hr] at h
  cases hs : Clif.step env.toEnv p xs.s with
  | next s' =>
    rw [hs] at h
    simp only [Clif.liftStep, Clif.XStepResult.next.injEq] at h
    rw [← h]
  | _ => rw [hs] at h; simp [Clif.liftStep] at h

theorem runLoopX_next {env : Clif.XEnv} {p : Clif.Program} {n : Nat} {xs xs' : Clif.XState}
    (h : Clif.stepX env p xs = .next xs') : Clif.runLoopX env p (n + 1) xs = Clif.runLoopX env p n xs' := by
  simp only [Clif.runLoopX, h]

theorem runLoopX_done {env : Clif.XEnv} {p : Clif.Program} {n : Nat} {xs : Clif.XState}
    {vals : List Clif.Val} {cm : Clif.Mem} (h : Clif.stepX env p xs = .done vals cm) :
    Clif.runLoopX env p (n + 1) xs = .returned vals cm := by
  simp only [Clif.runLoopX, h]

theorem runLoopX_unwound {env : Clif.XEnv} {p : Clif.Program} {n : Nat} {xs : Clif.XState}
    {e : Clif.Exn} {cm : Clif.Mem} (h : Clif.stepX env p xs = .unwound e cm) :
    Clif.runLoopX env p (n + 1) xs = .unwound e cm := by
  simp only [Clif.runLoopX, h]

theorem runLoopX_trapped {env : Clif.XEnv} {p : Clif.Program} {n : Nat} {xs : Clif.XState}
    {c : Clif.TrapCode} (h : Clif.stepX env p xs = .trapped c) :
    Clif.runLoopX env p (n + 1) xs = .trapped c := by
  simp only [Clif.runLoopX, h]

theorem runLoopX_stuck {env : Clif.XEnv} {p : Clif.Program} {n : Nat} {xs : Clif.XState}
    {msg : String} (h : Clif.stepX env p xs = .stuck msg) :
    Clif.runLoopX env p (n + 1) xs = .stuck msg := by
  simp only [Clif.runLoopX, h]

/-- The CLIF value a handler argument passes (`tryHandler`; `base`: the first payload value). -/
def exnArgVal (base : Nat) : Clif.TryArg → Clif.ValueId
  | .val v => v
  | .exn i => base + i
  | .ret _ => 0

theorem mapM_res_ok {α β : Type} {F : α → Clif.Res β} {g : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, F a = .ok (g a)) → l.mapM F = .ok (l.map g) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    simp only [List.mapM_cons, h a (by simp), Clif.Res.ok_bind,
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb)), Clif.Res.pure_eq, List.map_cons]

theorem tryHandler_ok {d : Clif.TryDest} {base : Nat} (h : ∀ a ∈ d.args, ∀ i, a ≠ .ret i) :
    Clif.tryHandler d base = .ok { block := d.block, args := d.args.map (exnArgVal base) } := by
  unfold Clif.tryHandler
  rw [mapM_res_ok (g := exnArgVal base)]
  · rfl
  · intro a ha
    cases a with
    | val v => rfl
    | exn i => rfl
    | ret i => exact absurd rfl (h _ ha i)

/-! ## The payload in the VCode -/

theorem vdefUpd_late {V : Type} {ops : Array Operand} {outs : List V} {ρ : Nat → V}
    (hl : ∀ o ∈ ops.toList.filter Operand.isDef, o.isLate = true)
    (hnd : ((ops.toList.filter Operand.isDef).map (·.vreg)).Nodup)
    (hlen : outs.length = (ops.toList.filter Operand.isDef).length)
    {j : Nat} {o : Operand} {x : V} (ho : (ops.toList.filter Operand.isDef)[j]? = some o)
    (hx : outs[j]? = some x) : vdefUpd ops outs ρ o.vreg = x := by
  have hearly : ((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isEarly) = [] := by
    rw [List.filter_eq_nil_iff]
    intro q hq
    have := hl q.1 (List.of_mem_zip hq).1
    simp only [Operand.isLate, beq_iff_eq] at this
    simp [Operand.isEarly, this]
  have hlate : ((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isLate) =
      (ops.toList.filter Operand.isDef).zip outs := by
    rw [List.filter_eq_self]
    intro q hq
    exact hl q.1 (List.of_mem_zip hq).1
  simp only [vdefUpd, hearly, hlate]
  refine writeV_nodup_ctl _ _ j o x ?_ (by simp [List.getElem?_zip_eq_some, ho, hx])
  have : ((ops.toList.filter Operand.isDef).zip outs).map (fun q => q.1.vreg) =
      (ops.toList.filter Operand.isDef).map (·.vreg) := by
    rw [show (fun q : Operand × V => q.1.vreg) = Operand.vreg ∘ Prod.fst from rfl,
      ← List.map_map, List.map_fst_zip (by omega)]
  rw [this]; exact hnd

theorem payVreg_spec {ops : Array Operand} {i n : Nat} (h : payVreg ops i = some n) :
    ∃ (j : Nat) (o : Operand), (ops.toList.filter Operand.isDef)[j]? = some o ∧ o.vreg = n ∧
      o.con = .fixed (.x i) := by
  simp only [payVreg, Option.map_eq_some_iff] at h
  obtain ⟨o, ho, rfl⟩ := h
  have hp := List.find?_some ho
  have hm := List.mem_of_find?_eq_some ho
  obtain ⟨j, hj, hjo⟩ := List.getElem_of_mem hm
  refine ⟨j, o, ?_, rfl, ?_⟩
  · rw [List.getElem?_eq_getElem hj, hjo]
  simpa using hp

/-- The value of payload register `i` (`payloadOuts`): the object in x0, 0 in x1. -/
def payWord (obj : BitVec 64) : Nat → BitVec 64
  | 0 => obj
  | _ => 0

theorem payload_def {c : CallInfo} {ops : Array Operand} (hops : (MInst.call c).operands = .ok ops)
    (hl : ∀ o ∈ ops.toList.filter Operand.isDef, o.isLate = true)
    (hnd : ((ops.toList.filter Operand.isDef).map (·.vreg)).Nodup) {ρ : Nat → CV}
    {obj : BitVec 64} {i n : Nat} (hi : i < 2) (h : payVreg ops i = some n) :
    vdefUpd ops (payloadOuts (.call c) obj) ρ n = ofX (payWord obj i) := by
  obtain ⟨j, o, hj, rfl, hc⟩ := payVreg_spec h
  have hdc : defCons (.call c) = (ops.toList.filter Operand.isDef).map (·.con) := by
    simp [defCons, hops]
  have hlen : (payloadOuts (.call c) obj).length = (ops.toList.filter Operand.isDef).length := by
    rw [payloadOuts, hdc, List.length_map, List.length_map]
  refine vdefUpd_late (outs := payloadOuts (.call c) obj) hl hnd hlen hj ?_
  rw [payloadOuts, hdc, List.map_map, List.getElem?_map, hj, Option.map_some]
  simp only [Function.comp_apply, hc]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simp [payWord]
  · simp [payWord]

theorem vholds_payWord {obj : BitVec 64} {i : Nat} {v : Clif.Val}
    (h : [(⟨.i64, obj⟩ : Clif.Val), ⟨.i64, 0⟩][i]? = some v) : VHolds v (ofX (payWord obj i)) := by
  rcases i with _ | _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    show (obj.setWidth 128).setWidth 64 = obj
    rw [BitVec.setWidth_setWidth_of_le _ (by omega)]
    exact BitVec.setWidth_eq obj
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [VHolds, ofX, payWord]
  · simp at h

/-! ## The hypotheses of the raising steps -/

/-- **What the raising steps assume** of the activation semantics `sem` (its steps at raising
calls, `RaiseSem`; `ispec` and the memory forms, as M4's rule theorems need them), of the
memory relation `MR` (as M4's call rules need it), of the outgoing area `out`, and of the
callees' exceptional results (`XRaiseOk`, `XRaiseIndOk`). -/
structure RaiseHyp (f : Clif.Function) (sem : Sem) (MR : MemRelT) (env : Clif.XEnv)
    (F : BitVec 64 → Prop) (X : ExtSem) (XR : XRaise) (sb : Nat) (syms : String → Option Nat)
    (out : Nat) : Prop where
  rs : RaiseSem F X XR sem
  ref : Refines F sem
  mem : MemRefines F sb syms sem
  mrs : MRStable F MR
  outOk : OutArgsOk F out MR
  mro : MemRelOk F sb syms f MR
  stk : CallsStack f out
  tstk : TryStack f out
  xr : XRaiseOk env (f.externs.map (·.2)) MR X XR
  xri : XRaiseIndOk env (indSigs f) MR X XR
  sym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b
  mrsyms : ∀ sl cm w, MR sl cm w → cm.symbols = syms

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {sem : Sem}
  {MR : MemRelT} {env : Clif.XEnv} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
  {F : BitVec 64 → Prop} {X : ExtSem} {XR : XRaise} {sb : Nat} {syms : String → Option Nat}
  {out : Nat}

/-! ## A raising statement -/

/-- **A `call`/`call_indirect` statement whose extern unwinds**: the VCode run reaches a `call`
whose callee raises an object related to the exception and which ends the activation, the world
after the unwinder related to the extern's memory. -/
theorem stmt_step_raise (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHyp f sem MR env F X XR sb syms out)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : Arm.ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    {e : Clif.Exn} {mm : Clif.Mem} (hr : instRaise env p s.frame s.mem stm.inst = some (e, mm)) :
    ∃ obj w', E2E.VUnwFrom vc sem XR ⟨b, k, ρ, w⟩ obj w' ∧ E2E.ExnRel e obj ∧ MR slots mm w' := by
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
    stmt_raise HR.rs HR.ref HR.mem HR.mrs HR.outOk HR.mro HR.stk HR.xr HR.xri HR.sym HR.mrsyms
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
  rw [seg_eq hB hL hstm hsl, List.map_append] at hsegat
  obtain ⟨hstar, -, hi, hops, hsem, hlen, -⟩ := seqRun_stop_star hvb hsegat.append_left hsr'
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
  refine ⟨obj, w', ⟨b, _, ρ₁', w₁, vb, ci', ops.map (rnOp gn), _, hstar, hvb, hi, hops,
    by rw [hdest, hvu]; exact hra, hsem, hlen⟩, hex, ?_⟩
  simpa [fr', restrict, hslots] using hmr'

/-! ## Entering a handler -/

/-- **Entering a successor block** (`enter_match`), with the edge's `Cert` conditions given
(a handler edge: `UnwShape.tries`; `Cert.term` covers only the normal-return edge). -/
theorem enter_matchU (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
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
    {w₂ : Arm.ArmState} (hmr : MR slots s.mem w₂) :
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

/-- The vreg number an exception edge passes for a handler argument (`exnArgReg` resolved). -/
def exnArgNum (gn : Nat → Nat) (ops : Array Operand) : Clif.TryArg → Nat
  | .val v => gn v
  | .exn i => gn ((payVreg ops i).getD 0)
  | .ret _ => 0

/-- **A `try_call`/`try_call_indirect` whose extern unwinds** (caught by the first item of its
exception table, a `tag 0`/`tag 1` handler). The CLIF steps — the payload bound, the jump to the
handler — are matched by the terminator's code up to the `tryCall` (`.goto 0`), the landing-pad
edge block and its `jump`. -/
theorem term_step_try_exn (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHyp f sem MR env F X XR sb syms out)
    {xs : Clif.XState} {b k : Nat} {ρ : Nat → CV} {w : Arm.ArmState}
    (hm : Match f ctx R gn bl A MR slots xs.s ⟨b, k, ρ, w⟩) (hbody : xs.s.frame.body = [])
    {et : Clif.ExnTable} (hT : IsTryWith xs.s.frame.term et)
    {e : Clif.Exn} {mm : Clif.Mem} (hr : Clif.raiseAt? env p xs.s = some (e, mm)) :
    ∃ xs1, Clif.stepX env p xs = .next xs1 ∧
      (∀ c, Clif.stepX env p xs1 ≠ .trapped c) ∧ (∀ vals cm, Clif.stepX env p xs1 ≠ .done vals cm) ∧
      (∀ e' cm, Clif.stepX env p xs1 ≠ .unwound e' cm) ∧
      ∀ xs2, Clif.stepX env p xs1 = .next xs2 →
        ∃ vs', Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
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
  obtain ⟨hstar, -, hi, hops', hsem, hlen, -⟩ := seqRun_stop_star hvb hsegat hsr'
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
    obtain ⟨TB, hTB, hlenA, hM⟩ := enter_matchU H (b := b) (B := B) (s := s1) hcall hfunc hslots
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
    exact ⟨_, hstar.trans (.step hstep1 (Star.single hstep2)), hM⟩
  | _ => rw [hst] at h; simp [Clif.liftStep] at h

/-! ## Whole runs -/

/-- What a VCode run from `vs` does when the CLIF run with unwinding from the matching state
ends: `RunOk`, and for an exception the VCode run reaches a raising `call` that ends the
activation (`VUnwFrom`), with the object related to the exception and the world related to
the memory before the frame was left. -/
def RunOkU (vc : VCode) (sem : Sem) (XR : XRaise) (MR : MemRelT)
    (slots : List (Clif.SlotId × Nat)) (vs : VState CV Arm.ArmState) : Clif.XOutcome → Prop
  | .returned vals cm => ∃ us outs w cm0, VRetFrom vc sem vs us outs w ∧
      RetPins vals us ∧ us.length = outs.length ∧
      PrefixHold vals outs ∧ MR slots cm0 w ∧ cm = (cm0.free (slots.map (·.2))).leave
  | .trapped c => VTrapFrom vc sem vs c
  | .unwound e cm => ∃ obj w cm0, E2E.VUnwFrom vc sem XR vs obj w ∧ E2E.ExnRel e obj ∧
      MR slots cm0 w ∧ cm = (cm0.free (slots.map (·.2))).leave
  | .stuck _ | .outOfFuel => True

theorem RunOkU.prefix {vs vs' : VState CV Arm.ArmState} {o : Clif.XOutcome}
    (h : Star (VStep vc sem) (.run vs) (.run vs')) (h' : RunOkU vc sem XR MR slots vs' o) :
    RunOkU vc sem XR MR slots vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨us, outs, w, cm0, hr, h1⟩ := h'
    exact ⟨us, outs, w, cm0, VRetFrom.prefix h hr, h1⟩
  | trapped c => exact VTrapFrom.prefix h h'
  | unwound e cm =>
    obtain ⟨obj, w, cm0, hu, h1⟩ := h'
    exact ⟨obj, w, cm0, E2E.VUnwFrom.prefix h hu, h1⟩
  | _ => trivial

/-- **Whole runs with unwinding**: from matching states, every outcome of `Clif.runLoopX` is
realised by the VCode run (under `TrapsExplicitX`). -/
theorem sim_runX (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHyp f sem MR env F X XR sb syms out)
    {cs : Clif.State} (hcf : cs.frame.func = f) (htr : E2E.TrapsExplicitX env p cs) :
    ∀ fuel (xs : Clif.XState) (vs : VState CV Arm.ArmState), E2E.ReachX env p cs.toX xs →
      Match f ctx R gn bl A MR slots xs.s vs →
      RunOkU vc sem XR MR slots vs (Clif.runLoopX env p fuel xs) := by
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
        RunOkU vc sem XR MR slots ⟨b, k, ρ, w⟩ (Clif.runLoopX env p (n + 1) xs) := by
      intro s' hs ⟨vs', hstar, hm'⟩
      obtain ⟨t, hx⟩ := stepX_next_of hs
      rw [runLoopX_next hx]
      exact RunOkU.prefix hstar (ih n (by omega) _ vs' (hr.snoc hx) hm')
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
          obtain ⟨obj, w', hu, hex, hmr⟩ := stmt_step_raise H HU HR hm hbody hra
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
              exact RunOkU.prefix hstar (ih m (by omega) _ vs' (hr'.snoc hx') hm')
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
            obtain ⟨xs1, hx1, hX1, hX2, hX3, hnx1⟩ := term_step_try_exn H HU HR hm hbody hT hra
            rw [runLoopX_next hx1]
            cases n with
            | zero => trivial
            | succ m =>
              have hr' := hr.snoc hx1
              cases hs1 : Clif.stepX env p xs1 with
              | next xs2 =>
                obtain ⟨vs', hstar, hm'⟩ := hnx1 xs2 hs1
                rw [runLoopX_next hs1]
                exact RunOkU.prefix hstar (ih m (by omega) _ vs' (hr'.snoc hs1) hm')
              | done vals cm => exact absurd hs1 (hX2 vals cm)
              | unwound e' cm => exact absurd hs1 (hX3 e' cm)
              | trapped c => exact absurd hs1 (hX1 c)
              | stuck msg =>
                rw [runLoopX_stuck hs1]
                trivial

/-- **The driver lemma with unwinding (CLIF → VCode).** A CLIF run with unwinding of `f` from
an entry state is realised by the VCode run from the entry (`RunOkU`): returns and explicit
traps as in `driver_correct`, and an exception that leaves the frame by a VCode run that ends
at a raising `call` with the exception object. Generic in the activation semantics `sem`
(`RaiseHyp`; instances: `csemU`, the dead-cleanup chain's `valueSemU`). -/
theorem driver_correctU (H : DriverHyp f vc ctx st0 R gn bl A sem MR env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (HR : RaiseHyp f sem MR env F X XR sb syms out)
    (hds : DriverSem sem)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : E2E.TrapsExplicitX env p cs) (fuel : Nat) :
    RunOkU vc sem XR MR slots ⟨0, 0, ρ₀, w₀⟩ (Clif.runLoopX env p fuel cs.toX) := by
  obtain ⟨k, ρ₁, w₁, hstar, hm⟩ := entry_step H hds HR.mem HR.mrs hB0 hcall hfunc hslots hbody
    hterm hregs hty hsig hmr hargs (ρ₀ := ρ₀)
  exact RunOkU.prefix hstar (sim_runX H HU HR hfunc htr fuel cs.toX _ (.refl _) hm)

end

end Backend.Proof.Driver
