import FV.Concurrency.CallSegLive

/-!
# Return addresses and return values at a call (#473, `SegOkG` call case)

* `CallsInside F`: every call instruction (`bl`, `blr`) of `F`'s laid-out code is followed by
  another instruction word (a static check of the layout);
* **`ra_in`**: at a paused `call` of an activation of `F` (`atCall_of_pause` with `Q`), the
  return address `pc + 4` is in `F`'s code range;
* **`ra_out`**: it is no word of another function of a well-formed link (`Link.Ok.sep`);
* `ret_tys`: a done CLIF `return` without callers returns values of the function's return types.
-/

namespace Concurrency.CallSegPc

open Arm ArmThread Backend Backend.Proof Backend.Proof.Driver E2E ArmAllocThread LinkedMachine
  LinkedMachine.Link IselCall IselCallRet PrepThread VCodeThread IselCheck

/-- **Every call instruction of `F` is followed by an instruction word** (module doc). -/
def CallsInside (F : LFn) : Prop :=
  ∀ j i t, F.fa.lines.toList[j]? = some (.ins i t) → ((∃ n, i = .bl n) ∨ (∃ r, i = .blr r)) →
    lineOffset F.fa.lines.toList j + 4 < 4 * F.fb.words.size

/-- The pc of a paused `call` is at a call instruction. (`hRA` since #553: `callAt_of_q` and
`q_op` read the call's line from the emission plan, `R.Wf`; every caller has it.) -/
theorem callPc_of_pause {RA : RL} (hRA : RA.Wf) (hX0 : NoCall RA.X) {f : Clif.Function} {vc : VCode}
    {ctx : Ctx} {st0 : LState} {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow}
    {A : Nat → Nat → List Clif.ValueId} {MR : MemRelT} {env : Clif.Env} {p : Clif.Program}
    {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) MR env p)
    (hchk : threadCheckBlC f bl = true) {Lp : Nat → Prop} {ss ss' : Array (Array Nat)}
    (H3 : PrepFacts vc RA.vc Lp ss ss') {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV} {s' : Clif.State}
    {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState} {x : ArmState}
    (hq : Q RA x (.run cM')) (hP : Pause RA (.run cM'))
    (hat : AtCallS s') (hm2 : Match f ctx R gn bl A MR slots s' vV')
    (hm3 : PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) Lp ss' (.run vV') (.run vP'))
    (hm4 : MatchRun cc ins ckeep r₀ cM' vP') : CallPc RA.fa RA.base (Arm.r .PC x) := by
  obtain ⟨b, k, allocs, its, m, w, vb, info, rfl, -, hvb, hi, -⟩ :=
    CallResumeAll.atCall_of_pause hX0 H hchk H3 hc hP hat hm2 hm3 hm4
  obtain ⟨-, -, -, regs, i', -, -, -, -, -, -, -, -, -, -, -, -, hal, -, -, hasg, -⟩ :=
    q_op hRA hq hvb hi (ArmAllocThread.lt_size_of_not_term hRA hvb hi rfl)
  exact (callAt_of_q hRA hq hvb hi call_hcall regs i' hal hasg).callPc

/-- **The return address of a call is in the caller's code** (module doc). -/
theorem ra_in {L : Link} {F : LFn} {s0 : ArmState} {K : Nat} {G : BitVec 64 → Prop}
    (hR : (L.act F s0 K G).Wf) (hci : CallsInside F) {pc : BitVec 64}
    (h : CallPc (L.act F s0 K G).fa (L.act F s0 K G).base pc) : F.InRange (pc + 4#64) := by
  obtain ⟨j, i, t, hj, hi, rfl⟩ := h
  have hlt := hci j i t hj hi
  have hfit := hR.fit
  simp only [act_fb] at hfit
  unfold LFn.InRange
  have e : F.base + BitVec.ofNat 64 (lineOffset F.fa.lines.toList j) + 4#64 - F.base =
      BitVec.ofNat 64 (lineOffset F.fa.lines.toList j + 4) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := F.base.isLt
    omega
  show (F.base + BitVec.ofNat 64 (lineOffset F.fa.lines.toList j) + 4#64 - F.base).toNat < _
  rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact hlt

/-- **The return address is no word of another linked function** (module doc). -/
theorem ra_out {L : Link} (hL : L.Ok) {nA nB : String} {FA FB : LFn} (hA : (nA, FA) ∈ L.fns)
    (hB : (nB, FB) ∈ L.fns) (hne : nA ≠ nB) {a : BitVec 64} (ha : FA.InRange a) :
    ∀ k < FB.fb.words.size, a ≠ FB.base + BitVec.ofNat 64 (4 * k) := by
  have hsep : Sep (nA, FA) (nB, FB) ∨ Sep (nB, FB) (nA, FA) := by
    obtain ⟨i, hi, hei⟩ := List.getElem_of_mem hA
    obtain ⟨j, hj, hej⟩ := List.getElem_of_mem hB
    have hij : i ≠ j := fun e => by subst e; rw [hei] at hej; cases hej; exact hne rfl
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · left; rw [← hei, ← hej]; exact List.pairwise_iff_getElem.mp hL.sep i j hi hj h
    · right; rw [← hei, ← hej]; exact List.pairwise_iff_getElem.mp hL.sep j i hj hi h
  intro k hk e
  unfold LFn.InRange at ha
  subst e
  have hfA := (hL.laid _ hA).fit
  have hfB := (hL.laid _ hB).fit
  have h4k : (FB.base + BitVec.ofNat 64 (4 * k)).toNat = FB.base.toNat + 4 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * k) (by simp at hfB; omega)]
    exact Nat.mod_eq_of_lt (by simp at hfB; omega)
  have hd : (FB.base + BitVec.ofNat 64 (4 * k) - FA.base).toNat < 4 * FA.fb.words.size := ha
  rw [BitVec.toNat_sub, h4k] at hd
  simp only at hfA hfB
  rcases hsep with ⟨-, h⟩ | ⟨-, h⟩ <;> simp only at h <;> rcases h with h | h <;>
    · have := FA.base.isLt
      omega

/-- **The values of a done `return`** have the function's return types. -/
theorem ret_tys {env : Clif.Env} {p : Clif.Program} {s : Clif.State} (hcall : s.callers = [])
    (hat : AtRetS s) {vals : List Clif.Val} {cm : Clif.Mem}
    (hs : Clif.step env p s = .done vals cm) :
    vals.map (·.ty) = Clif.AbiParam.tys s.frame.func.sig.returns := by
  obtain ⟨hbody, xs, hT⟩ := hat
  rw [Clif.step_term env p s hbody, hT] at hs
  obtain ⟨-, -, hdn⟩ := stepTerm_ret (env := env) (p := p) (s := s) (xs := xs) hcall
  obtain ⟨hg, rfl⟩ := hdn vals cm hs
  have hs' := hs
  simp only [Clif.stepTerm, hg, Clif.StepResult.ofRes, Clif.returnValues, hcall] at hs'
  rcases checkTys_cases s!"return values of %{s.frame.func.name}" vals
    (Clif.AbiParam.tys s.frame.func.sig.returns) with ⟨-, h⟩ | ⟨m, hc⟩
  · exact h
  · rw [hc] at hs'; cases hs'

end Concurrency.CallSegPc
