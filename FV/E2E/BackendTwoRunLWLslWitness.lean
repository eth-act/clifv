import FV.E2E.BackendTwoRunLW
import FV.E2E.LinkSlotSysWitness

/-!
# The machine lock on the slot system `Lsl` (SEM1 #537, `BackendTwoRunLW.lean`, item (5))

`LinkSlotSysWitness.Lsl`'s function `r` reads its explicit stack slot before writing it (the
uninitialised-read case of SEM1). The machine lock of two activations of `r`, run by the linked
machine's own hooks (`Lsl.hooks M`, every depth), applies:

* `fR_mem`, `fR_compiled` (the legacy pipeline of `LinkCheck.okR_sound`), `fR_noExterns`,
  `fR_indFree`, `fR_x30Free`, `fR_noHookLines` (the code holds no `bl`/`blr`/TLS line, so the
  call and TLS premises are vacuous), `xNI_nil`, `lslTls`;
* **`r_twoRunLERW_Lsl`**: `backend_twoRunLERW` for `r` at `Lsl.hooks M`.
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck

theorem fR_mem : fR ∈ Lsl.P.funcs := by rw [funcs_eq]; simp

theorem fR_compiled : Compiled fR (Lsl.A fR).k (Lsl.A fR).vc (Lsl.A fR).vcp (Lsl.A fR).rf
    (Lsl.A fR).af (Lsl.A fR).fa (Lsl.A fR).fb := by
  have hg : fR ∈ (progOf I.results).funcs := fR_mem
  have fa := factsR (results_ok I) okB_true hg
  obtain ⟨hl, hpr, ha, he, hla, -⟩ := fa.pipe
  exact ⟨hl, fa.lowerOk, hpr, fa.prepOk, fa.check, ha, he, hla⟩

theorem fR_noExterns : fR.externs.isEmpty = true := by native_decide

theorem fR_indFree : indFreeB fR = true := by native_decide

theorem fR_x30Free :
    (Lsl.A fR).fa.x30Free (getOk (labelOffsets (Lsl.A fR).fa.lines)) = true := by native_decide

/-- No line of the code is a call or the TLS hook line. -/
def noHookLinesB (fa : FnAsm) : Bool :=
  fa.lines.toList.all fun ln => match ln with
    | .ins (.bl _) _ => false
    | .ins (.blr _) _ => false
    | .ins (.ldrTlsDescLo12 _ _ _) _ => false
    | _ => true

theorem fR_noHookLines : noHookLinesB (Lsl.A fR).fa = true := by native_decide

theorem noHook_line {fa : FnAsm} (h : noHookLinesB fa = true) {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : fa.lines.toList[j]? = some (.ins x t)) :
    (∀ n, x ≠ .bl n) ∧ (∀ r, x ≠ .blr r) ∧ ∀ a b c, x ≠ .ldrTlsDescLo12 a b c := by
  have hall := List.all_eq_true.mp h _ (List.mem_of_getElem? hj)
  refine ⟨fun n e => ?_, fun r e => ?_, fun a b c e => ?_⟩ <;> subst e <;> simp at hall

/-- Non-interference of the externs of a function without externs and indirect calls. -/
theorem xNI_nil {F : BitVec 64 → Prop} {syms : String → Option Nat} {sp0 : BitVec 64}
    {Lg : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {X : ExtSem} :
    XNI F syms [] [] sp0 Lg X := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  rcases h with ⟨⟨_, he, _⟩, _⟩ | ⟨hs, _⟩
  · cases he
  · cases hs

/-- The TLSDESC flags of the closed base (the world's `pstate`). -/
theorem lslTls (F : BitVec 64 → Prop) : XTls F Lsl.Xb := by
  intro Z n w w' _ hsw
  have e : ∀ fl, Arm.r (.FLAG fl) w = Arm.r (.FLAG fl) w' := fun fl => hsw.1 _ (by simp [Masked])
  have h1 := e .N
  have h2 := e .Z
  have h3 := e .C
  have h4 := e .V
  simp only [Arm.r, Arm.read_base_flag] at h1 h2 h3 h4
  show Arm.read_pstate w = Arm.read_pstate w'
  apply Arm.PState.ext <;> simp only [Arm.read_pstate] <;> assumption

/-- **`backend_twoRunLERW` applies** to `Lsl`'s `r` (reads its uninitialised slot), run by the
linked machine's hooks at any depth: the lock along the body, `RetAgreeX` and the memory outside
`F` at the return; the hook premises are vacuous (no call or TLS line). -/
theorem r_twoRunLERW_Lsl (M : Nat) {F : BitVec 64 → Prop} {c : BitVec 64} {K : Nat}
    {args : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState} {env : Clif.Env}
    (hce : ClifEntry fR args cs)
    (hrel : RelW ⟨F, fun _ => none, (Lsl.A fR).af.slotBase,
      (RAFrame.compute (Lsl.A fR).vcp (Lsl.A fR).rf).intBase⟩ fR c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fR.sig args w₀)
    (htr : TrapsExplicit env Lsl.P.bare cs) (fuel : Nat)
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {Pp : Nat → BitVec 64 → BitVec 8} {Rr : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPR (Lsl.A fR).vcp (Lsl.A fR).rf (Lsl.A fR).af (Lsl.A fR).fa (Lsl.A fR).fb K F G
      (ExtSemI.const Lsl.Xb) (Lsl.hooks M) base ra Kp cc Pp Rr s w₀) :
    ∀ vals cm, Clif.runLoop env Lsl.P.bare fuel cs = .returned vals cm →
      ∃ N, RetAgreeX (frameDrop (Lsl.A fR).af + K) (spv s)
        (iterN (ArmStepX Lsl.Xb (Lsl.hooks M) (Lsl.A fR).fa)
          ((prologueLines (Lsl.A fR).af.saves (Lsl.A fR).af.frameSize).length + N +
            ((epiLines (Lsl.A fR).af.saves (Lsl.A fR).af.frameSize).length + 1)) s)
        (iterN (ArmStepX Lsl.Xb (Lsl.hooks M) (Lsl.A fR).fa)
          ((prologueLines (Lsl.A fR).af.saves (Lsl.A fR).af.frameSize).length + N +
            ((epiLines (Lsl.A fR).af.saves (Lsl.A fR).af.frameSize).length + 1)) s) := by
  have hc := fR_compiled
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨body, psF, hpsF, -, hk⟩ := emitFunc_ok hc.emit
  have hx30 : (Lsl.A fR).fa.x30Free lm = true := by
    have h := fR_x30Free
    rwa [show getOk (labelOffsets (Lsl.A fR).fa.lines) = lm by rw [hlm]; rfl] at h
  have hext : fR.externs.map (·.2) = [] := by
    have := fR_noExterns
    simp only [List.isEmpty_iff] at this
    simp [this]
  have hind : indSigs fR = [] := indSigs_nil_of_indFree (indFreeB_sound fR_indFree)
  have hnh := fR_noHookLines
  intro vals cm hrun
  obtain ⟨N, -, -, -, h, -, -⟩ := backend_twoRunLERW (D := fun _ => False)
    (Lsl_ok.subset fR fR_mem) hc (instCallsOne_all fR) (tryCallsOne_all fR)
    (fun _ _ _ => ⟨(by rw [hext]; exact fun _ hin => nomatch hin),
      (by rw [hind]; exact xCallsIndOk_nil _ _ _)⟩)
    (fun _ _ _ => by rw [hext, hind]; exact xNI_nil)
    (fun _ => lslTls F) (fun n b h => by cases h) rfl (fun _ => 0) hce hrel hrel hargs
    (SameWorld.refl _ _) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) htr fuel hlm (hk ▸ hpsF) he he
    rfl (Lsl_ok.covered fR fR_mem) hx30
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x d ⟨j, t, hj, _⟩ hd => by
      obtain ⟨hbl, hblr, -⟩ := noHook_line hnh hj
      rcases hd with ⟨n, rfl, -⟩ | ⟨r, rfl, -⟩
      · exact absurd rfl (hbl n)
      · exact absurd rfl (hblr r))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨a, b, c, j, t, hj, _⟩ _ _ => by
      obtain ⟨-, -, htl⟩ := noHook_line hnh hj
      exact absurd rfl (htl a b c))
    ⟨fun _ _ _ _ => rfl, fun _ _ => rfl⟩ rfl vals cm hrun
  exact ⟨N, h⟩

end E2E.LinkSlotSysWitness
