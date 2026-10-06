import FV.Backend.Proof.IselCovCtor
import FV.Backend.Proof.LowerComplete
import FV.Backend.Proof.CSemRename
import FV.Backend.Proof.RegallocCover

/-!
# Form coverage of the compiled function (V3, assembly)

`formsCovered_of_runs`: on input in `Dominated` and `LowerScope`, every instruction of
`prepare (lowerFunction f)` is a control form or `FormOk` (`FormsCovered`), given that every ISLE
run of the driver emits only covered instructions (`StmtCov`, `TermCov`, `TryCov`, discharged by
the ISLE coverage proofs). The driver's own instructions (`args`, the parameter loads, `jump`s,
the `tryCall` replacing a `try_call`'s `call`) are covered; result `mov`s never occur since a
statement with results gets them in int vregs; the alias renaming keeps coverage
(`covered_mapRegs`); `prepare` only retargets control instructions and adds `jump`s
(`formsCovered_of_prepare`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## Coverage under renaming and retargeting -/

theorem isCtl_mapRegs (R : Reg → Reg) (m : MInst) : (m.mapRegs R).isCtl = m.isCtl := by
  cases m <;> rfl

theorem covered_mapRegs {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn) (m : MInst) :
    Cov.Covered (m.mapRegs R) = Cov.Covered m := by
  unfold Cov.Covered
  rw [isCtl_mapRegs, formOk_mapRegs hg]

/-- The entry block's load of a stack-passed parameter is covered. -/
theorem covered_load (b n : Nat) (off : Int) :
    Cov.Covered (.load (loadOpOfBytes b) (.vreg n .int) (.fpOffset off) trustedFlags) = true := by
  unfold Cov.Covered loadOpOfBytes
  split <;> rfl

theorem setTargets_isCtl {i i' : MInst} {ls : List Label} (h : i.setTargets ls = some i') :
    i'.isCtl = true := by
  unfold MInst.setTargets at h
  split at h
  all_goals (try split at h)
  all_goals (cases h <;> rfl)

/-- `prepare` keeps form coverage: its instructions are the input's, retargeted control
instructions, or edge blocks' `jump`s. -/
theorem formsCovered_of_prepare {vc vcp : VCode} (h : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc)
    (hc : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true ∨ FormOk default i = true)
    (cx : FnCtx) : FormsCovered cx vcp := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ := Prep.prepare_facts h
  have cs0 := Prep.cfg_spec hc0
  have cs2 : Prep.CfgSpec (B ++ E) ss2 := Prep.cfg_spec hc2
  intro b vb k i hvb hi
  rcases Prep.insts3 hd cs0 cs2 hS (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hvb))
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) with
    ⟨vb0, hvb0, hi0⟩ | ⟨vb0, hvb0, i0, hi0, ls, hset⟩ | ⟨l, rfl⟩
  · exact hc vb0 hvb0 i hi0
  · exact .inl (setTargets_isCtl hset)
  · exact .inl rfl

/-! ## The ISLE runs' coverage (discharged by the ISLE coverage proofs) -/

/-- Every statement's `lower` run emits only covered instructions, and returns a statement's
results in int vregs. -/
def StmtCov (ctx : Ctx) : Prop :=
  ∀ ii info inst s out s' tr, ctx.insts[ii]? = some info → info.clif = some inst →
    runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr) →
    Cov.CovSince s s' ∧ ∀ rss, out = some (.regsVec rss) → info.results ≠ [] →
      ∀ rs ∈ rss, ∀ r ∈ rs, ∃ n, r = .vreg n .int

/-- Every non-`try_call` terminator's run (at its placeholder slot) emits only covered
instructions. -/
def TermCov (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ ti t data targets s out s' tr, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → t.isTry = false →
    termData (abiTerm f t) = .ok data →
    termCallF ctx ti data t targets s = .ok (out, s', tr) → Cov.CovSince s s'

/-- Every `try_call` terminator's run (at its placeholder slot) emits only covered
instructions. -/
def TryCov (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ ti t data trs targets s out s' tr, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → tryCallData f t = .ok data →
    tryCallF ctx ti data trs targets s = .ok (out, s', tr) → Cov.CovSince s s'

/-- No result `mov`s when every result register is an int vreg. -/
theorem extraOf_nil_of_vregs {results : List Nat} {rss : List (List Reg)}
    (h : ∀ rs ∈ rss, ∀ r ∈ rs, ∃ n, r = .vreg n .int) : extraOf results rss = [] := by
  unfold extraOf
  rw [List.filterMap_eq_nil_iff]
  intro ⟨r, rs⟩ hq
  have hv := h rs (List.of_mem_zip hq).2
  simp only
  split
  · rfl
  · rename_i out hne
    obtain ⟨n, rfl⟩ := hv out (by simp)
    exact absurd rfl (hne n .int)
  · rfl

/-! ## Assembly -/

/-- **Form coverage of the compiled function.** Given the ISLE runs' coverage, every
instruction of `prepare (lowerFunction f)` is a control form or `FormOk`. -/
theorem formsCovered_of_runs {f : Clif.Function} {vc vcp : VCode}
    (hs : LowerScope f) (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp)
    (hrun : ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) →
      StmtCov ctx ∧ TermCov f ctx ∧ TryCov f ctx)
    (cx : FnCtx) : FormsCovered cx vcp := by
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
  apply formsCovered_of_prepare hp (prepDomain_of_lower hs hl hs.nonempty)
  rw [hvb]
  intro vb hvb' i hi
  have := hall vb hvb' i hi
  simpa [Cov.Covered, Bool.or_eq_true] using this

end Backend.Proof.Driver
