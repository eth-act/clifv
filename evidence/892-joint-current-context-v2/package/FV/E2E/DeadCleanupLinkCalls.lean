import FV.E2E.LinkCheck
import FV.E2E.DeadCleanupGotCheck

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.DeadCleanup

/-- More precise GOT knowledge only narrows the callees checked for a `blr`. -/
theorem blrOk_got_mono {P : Clif.Program} {may : Clif.Function → Bool}
    {old new : Nat → Option String} {info : CallInfo}
    (hm : ∀ t n, old t = some n → new t = some n)
    (h : blrOk P may old info = true) : blrOk P may new info = true := by
  obtain ⟨dest, us, ds⟩ := info
  unfold blrOk at h ⊢
  cases dest with
  | sym n => cases h
  | reg r =>
    cases r <;> try cases h
    rename_i t cl
    cases cl <;> try cases h
    simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
    refine ⟨h.1, fun f hf => ?_⟩
    have hh := h.2 f hf
    cases ho : old t with
    | none =>
      simp only [ho, Bool.or_false, Bool.or_eq_true] at hh ⊢
      rcases hh with (hm | hl) | ha
      · exact .inl (.inl (.inl hm))
      · exact .inl (.inr hl)
      · exact .inr ha
    | some n => simpa [ho, hm t n ho] using hh

theorem preparedCleanup_siteOk {P : Clif.Program} {g : Clif.Function}
    {may : Clif.Function → Bool} (vc vcp : VCode) (info : CallInfo)
    (h : siteOk P g may vcp info = true) :
    siteOk P g may (preparedCleanup vc vcp) info = true := by
  unfold siteOk at h ⊢
  cases hd : info.dest with
  | sym n => simpa [hd] using h
  | reg r =>
    simp only [hd] at h ⊢
    exact blrOk_got_mono (fun _ _ => preparedCleanup_gotOf vc vcp) h

/-- The same call-site checker accepts all surviving calls. -/
theorem preparedCleanup_sites {P : Clif.Program} {g : Clif.Function}
    {may : Clif.Function → Bool} (vc vcp : VCode)
    (h : allInsts vcp (siteB (siteOk P g may vcp)) = true) :
    allInsts (preparedCleanup vc vcp)
      (siteB (siteOk P g may (preparedCleanup vc vcp))) = true := by
  unfold allInsts at h ⊢
  simp only [Array.all_eq_true_iff_forall_mem] at h ⊢
  intro b hb i hi
  have hold : siteB (siteOk P g may vcp) i = true :=
    preparedCleanup_insts vc vcp (fun b hb i hi =>
      h b (Array.mem_toList_iff.mp hb) i (Array.mem_toList_iff.mp hi)) b
      (Array.mem_toList_iff.mpr hb) i (Array.mem_toList_iff.mpr hi)
  cases i with
  | call info => exact preparedCleanup_siteOk vc vcp info hold
  | tryCall info ti => exact preparedCleanup_siteOk vc vcp info hold
  | _ => rfl

end E2E.LinkCheck
