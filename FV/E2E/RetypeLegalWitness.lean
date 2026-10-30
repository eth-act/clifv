import FV.E2E.NonVacuityLink
import FV.E2E.RetypeLegal
import FV.Opt.Proof.RetypeWitness

/-!
# Non-vacuity of the retyped-data-movement theorem (S12e, #36)

`a2_retype_legal_wide`: `E2E.backend_correct_retype_legal_wide` applies to the witness program's
legalised callee `a2` (`FV/E2E/LegalWideWitness.lean`) under the witness `TyMap`
`Opt.Retype.Witness.f64AsI64`, with every function-level premise discharged: its source is in the
retyping's domain and unchanged by it (no `f64` access). The retyping itself is witnessed on a
function it changes by `Opt.Retype.Witness.copyF_sim`.
-/

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver Opt.Retype Opt.Retype.Witness

theorem okB_srcFn9 : Opt.Retype.okB f64AsI64 (srcFn 9) = true := by native_decide

theorem retype_srcFn9 : Opt.Retype.retype f64AsI64 (srcFn 9) = srcFn 9 := by native_decide

/-- **`backend_correct_retype_legal_wide` applies** to the program's legalised callee `a2` (the
entry premises remain, as for `a2_legal_wide`). -/
theorem a2_retype_legal_wide {F : BitVec 64 → Prop} {p : Clif.Program} {K : Nat}
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val}
    {cs cs' : Clif.State}
    (hent : AbiEntry (A fA2).fb base ra s) (hres : StackAvail K (A fA2).af s)
    (hbe : BodyEntry (A fA2).af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups (srcFn 9).sig.params).getD []) args args')
    (hargs : ArgsIn fA2.sig args' s) (hcs : ClifEntry (srcFn 9) args cs)
    (hcs' : ClifEntry fA2 args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase
      (RAFrame.compute (A fA2).vcp (A fA2).rf).size (A fA2).af s, fun _ => none,
      (A fA2).af.slotBase, (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2
      cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicit Clif.Rust.env p (retypeEntry f64AsI64 (srcFn 9) cs))
    (htr : TrapsExplicit Clif.Rust.env (L F).P.bare cs') (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups (srcFn 9).sig.returns).getD []) (A fA2).fb base ra
      (ArmStepX Xb Hb (A fA2).fa) s (Clif.runLoop Clif.Rust.env p fuel cs) := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  have hfa := facts hA2
  have hcompiled : Compiled fA2 (A fA2).k (A fA2).vc (A fA2).vcp (A fA2).rf
      (A fA2).af (A fA2).fa (A fA2).fb := by
    obtain ⟨hl, hp, ha, he, hla, hk, hb⟩ := pipe_spec hfa.pipe
    exact ⟨hl, hfa.lowerOk, hp, hfa.prepOk, hfa.check, ha, he, hla⟩
  have ha := a2B_true
  simp only [a2B, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, Bool.not_eq_true'] at ha
  obtain ⟨⟨⟨⟨⟨⟨he9, heA⟩, hi9⟩, hiA⟩, hnt⟩, hnc⟩, hchk⟩ := ha
  refine backend_correct_retype_legal_wide (σ := f64AsI64) (X := Xb) (H := Hb)
    (syms := fun _ => none) (slotOff := (A fA2).af.slotBase) (K := K) okB_srcFn9
    (by rw [retype_srcFn9]; exact Opt.Legal.checkW_of_check hchk)
    (hL.subset fA2 hA2) hcompiled
    (fun fn e h => by simp [Clif.Function.extern?, he9] at h)
    (fun fn e h => by simp [Clif.Function.extern?, heA] at h)
    (fun ⟨sig, hs⟩ => by
      rw [retype_srcFn9] at hs
      rcases hs with ⟨B, hB, st, hst, callee, args, hi⟩ | ⟨B, hB, callee, args, et, ht, -⟩
      · exact absurd hi ((indFreeB_sound hi9 B hB).1 st hst sig callee args)
      · exact absurd ht ((indFreeB_sound hi9 B hB).2 callee args et))
    (hL.covered fA2 hA2) (fun _ => ⟨fun ctx info hsite => ?_, fun d u _ _ => by
      simp [Hb, Arm.r_of_w_same], fun d uses w outs w' hx _ => by simp [Xb] at hx⟩)
    (fun ⟨B, hB, ht⟩ => absurd ht (by simpa using hnt B hB))
    (fun ht => absurd ht (by simp [hfa.tls]))
    (fun _ ext hin => by simp [heA] at hin)
    (fun _ => by rw [indSigs_nil_of_indFree (indFreeB_sound hiA)]; exact xCallsIndOk_nil _ _ _)
    (fun n b h => by cases h) rfl hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel
  obtain ⟨b, vb, k, hb, hk | ⟨ti, hk⟩⟩ := hsite
  · have := allInsts_sound hnc hb hk; simp at this
  · have := allInsts_sound hnc hb hk; simp at this

end E2E.LinkWitness
