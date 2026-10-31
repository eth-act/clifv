import FV.E2E.IselCallsOneAll
import FV.E2E.IselSimIWitness

/-!
# Non-vacuity of the call-count certificate (SEM1, `docs/plans/uninit.md` §5.9)

* `f_hasCall`: the witness program's entry `f` (`LinkWitness`) has `call`/`call_indirect`
  statements;
* `f_compiled`: its compiled image;
* `f_segCalls`: in `f`'s compiled code every `call`/`call_indirect` statement's segment has
  exactly one VCode call (`segCalls_of` with `instCallsOne_all`, the lowering shape of `f`'s
  `lowerCheck`);
* `a2_iselSimIC`: `iselSim_relWIC` applies to `a2` without the call-count premises.
-/

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- `f` has `call`/`call_indirect` statements. -/
theorem f_hasCall : fF.blocks.any (fun B => B.body.any fun st => st.inst.isCallLike) = true := by
  native_decide

theorem f_compiled : Compiled fF (A fF).k (A fF).vc (A fF).vcp (A fF).rf
    (A fF).af (A fF).fa (A fF).fb := by
  have hF : fF ∈ P.funcs := by simp [P]
  have hfa := facts hF
  obtain ⟨hl, hp, ha, he, hla, hk, hb⟩ := pipe_spec hfa.pipe
  exact ⟨hl, hfa.lowerOk, hp, hfa.prepOk, hfa.check, ha, he, hla⟩

/-- **Every `call`/`call_indirect` statement of `f` lowers to a segment with exactly one VCode
call** (in the lowering shape `lowerCheck` certifies for `f`'s compiled code). -/
theorem f_segCalls : ∃ (ctx : Ctx) (st0 : LState) (R : Reg → Reg) (gn : Nat → Nat)
    (bl : List BLow), LowerShape fF (A fF).vc ctx st0 R gn bl ∧
    ∀ b B j stm, fF.blocks[b]? = some B → B.body[j]? = some stm → stm.inst.isCallLike = true →
      callsI (seg fF R bl b j) = 1 := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hF : fF ∈ P.funcs := by simp [P]
  obtain ⟨ctx, st0, R, gn, bl, A', hshape, hcert, hbr⟩ := loweringObligations_of_check f_compiled.lowerOk
  have Hb := driverHyp_relW (hL.subset fF hF) f_compiled hshape hcert hbr
    (xCallsOk_none Clif.Rust.env _ _ ((ExtSemI.const Xb).at 0).noCall)
    (xCallsIndOk_none Clif.Rust.env _ _ ((ExtSemI.const Xb).at 0).noCall)
    (syms := fun _ => none) (F := fun _ => True) (c := 0) (p := (L fun _ => True).P.bare)
    (fun _ _ h => by cases h) rfl
  exact ⟨ctx, st0, R, gn, bl, hshape, fun b B j stm hB hstm hcl =>
    segCalls_of Hb (instCallsOne_all fF) hB hstm hcl⟩

/-- **`iselSim_relWIC` applies** to `a2` (no call-count premise). -/
theorem a2_iselSimIC {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} (ρ₀ : Nat → CV) (hce : ClifEntry fA2 args cs)
    (hrel : RelW ⟨F, fun _ => none, (A fA2).af.slotBase,
      (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2 c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fA2.sig args w₀)
    (htr : TrapsExplicit Clif.Rust.env (L F).P.bare cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .returned vals cm →
      ∃ us outs w, VRetFrom (A fA2).vc (csemI F ⟨(A fA2).fa.k, (A fA2).af.slotBase⟩
          (ExtSemI.const Xb)) ⟨0, 0, ρ₀, (w₀, 0)⟩ us outs w ∧
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F (fun _ => none) cm w.1) ∧
    (∀ c', Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .trapped c' →
      VTrapFrom (A fA2).vc (csemI F ⟨(A fA2).fa.k, (A fA2).af.slotBase⟩ (ExtSemI.const Xb))
        ⟨0, 0, ρ₀, (w₀, 0)⟩ c') := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  exact iselSim_relWIC (hL.subset fA2 hA2) a2_compiled (fun _ n _ => a2_xcalls _ _ _ n)
    (fun n b h => by cases h) rfl ρ₀ hce hrel hargs htr fuel

end E2E.LinkWitness
