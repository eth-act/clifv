import FV.Backend.Proof.FormsCoverComplete
import FV.Backend.Proof.DeadCleanupPrepare

namespace Backend.Proof.Driver
open Backend Backend.Proof Backend.Proof.Cov Backend.DeadCleanup

private theorem lower_covered {f : Clif.Function} {vc : VCode}
    (hs : LowerScope f) (hl : lowerFunction f = .ok vc)
    (hrun : ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) →
      StmtCov ctx ∧ TermCov f ctx ∧ TryCov f ctx)
    : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList,
      i.isCtl = true ∨ FormOk default i = true := by
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, -⟩ := lowerFunction_run hl
  obtain ⟨hS, hT, hY⟩ := hrun ctx ranges st0 hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  have hall := vcBlocks_all (fun m => Cov.Covered m = true)
    (fun _ _ hg m h => by rw [covered_mapRegs hg]; exact h) (fun _ => rfl) covered_load
    (fun _ => rfl) (f := f) (bl := bl)
    (fun bi B L j stm sl hB hL hj hsl => by
      obtain ⟨-, hc, -, -⟩ := hspec bi B L hB hL
      obtain ⟨info, hi, hic, hres⟩ := hcf.stmt bi B j stm hB hj
      obtain ⟨tr, hrun⟩ := hc j sl hsl
      rw [hstart bi L hL] at hrun
      obtain ⟨⟨ms, hms, hcov⟩, hvr⟩ := hS _ info stm.inst _ _ _ _ hi hic hrun
      have hex : extraOf stm.results sl.rss = [] := by
        cases hr : stm.results with
        | nil => simp [extraOf]
        | cons r rs => exact extraOf_nil_of_vregs (hvr sl.rss rfl (by rw [hres, hr]; simp))
      rw [hex, List.append_nil, hms,
        hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)]
      simpa using hcov)
    (fun bi B L hB hL => by
      obtain ⟨-, -, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
      obtain ⟨hn, hy⟩ := lowTerm_spec hterm
      have hph := hcf.term bi B hB
      rw [← hstart bi L hL] at hph
      have hti := (Array.getElem?_eq_some_iff.mp hph).1
      intro m hm
      rcases mem_fixTry hm with hm | ⟨c, ti, rfl⟩
      · cases ht : B.term.isTry with
        | false =>
          obtain ⟨-, hd, out, tr, hc⟩ := hn ht
          obtain ⟨ms, hms, hcov⟩ := hT _ _ _ _ _ _ _ _ hti hph ht hd hc
          rw [hms, htst] at hm
          exact hcov m (by simpa using hm)
        | true =>
          obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := by
            cases hB' : B.term <;> rw [hB'] at ht <;> simp [Clif.Terminator.isTry] at ht
            · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
            · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
          obtain ⟨T, -, hd, -, -, -, -, out, tr, hc⟩ := hy et het
          obtain ⟨ms, hms, hcov⟩ := hY _ _ _ _ _ _ _ _ _ hti hph hd hc
          rw [hms] at hm
          exact hcov m (by simpa using hm)
      · rfl)
  rw [hvb]
  intro vb hvb' i hi
  have := hall vb hvb' i hi
  simpa [Cov.Covered, Bool.or_eq_true] using this
theorem formsCovered_cleanup_complete {f : Clif.Function} {vc vcp : VCode}
    (hs : LowerScope f) (hl : lowerFunction f = .ok vc) (hp : prepare (prune vc) = .ok vcp) (cx : FnCtx) :
    FormsCovered cx vcp :=
  formsCovered_of_prepare hp (prune_prepDomain (prepDomain_of_lower hs hl hs.nonempty))
    (prune_insts (lower_covered hs hl (fun ctx _ _ hb => by
    have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
    have hcl : Cov.Clean ctx := clean_of_build hb
    exact ⟨fun _ _ _ _ _ _ _ hi hc h => stmt_cov logicImmComplete hctx hcl hi hc h,
      fun _ _ _ _ _ _ _ _ _ hph _ hd h => termCall_cov logicImmComplete hctx hcl hph hd h,
      fun _ _ _ _ _ _ _ _ _ _ hph hd h => tryCall_cov logicImmComplete hctx hcl hph hd h⟩))) cx


end Backend.Proof.Driver
