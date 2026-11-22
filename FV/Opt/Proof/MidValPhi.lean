import FV.Opt.Proof.ConstPhiSimU
import FV.Opt.Proof.MidValPhiM
import FV.Opt.MidValFold

/-!
# The validator's constant-phi removal is simulated by its input (#1119, removed block parameters)

`Opt.MidVal.phiPre f` (`FV/Opt/MidValFold.lean`) applies `ConstPhi`'s solution of `f` when
`phiOk` accepts it: `ConstPhi.cpOk` without the well-formedness of the result and without the
backend's condition that a function with a `try_call` keeps its fresh value. The proof of
`ConstPhi.cpOk_simU` uses only the facts `ConstPhi.CpFacts` (`f` well-formed, the solution's keys
and edges), which `phiOk` checks as `cpOk` does (`phiOk_facts`); the fresh values of the two
sides are never compared (the `try_call` results and payloads are bound at each side's own fresh
value, `FV/Opt/Proof/ConstPhiSimU.lean`). Here:

* **`phiOk_simU`**: `phiOk f sol = true → FunSimU f (ConstPhi.apply f sol)`;
* **`phiPre_simU`**: `FunSimU f (phiPre f)` for every `f`.
-/

namespace Opt.MidVal

open Clif Opt ConstPhi

/-- `phiOk` gives the facts `ConstPhi.cpOk_facts` gives (the same proof without the two
conjuncts `phiOk` drops). -/
theorem phiOk_facts {f : Function} {sol : List (ValueId × ValueId)} (h : phiOk f sol = true) :
    ∃ fi, Opt.check f = .ok fi ∧ CpFacts (solMap sol) f (wfData f fi) := by
  unfold phiOk at h
  split at h
  · cases h
  rename_i fi hfi
  simp only [Bool.and_eq_true] at h
  obtain ⟨hkeys, hedges⟩ := h
  refine ⟨fi, hfi, wf_of_check hfi, fun x hx => ?_, fun i b hb e he j db hj hdb => ?_⟩
  · have hmem := solMap_get (get_of_contains hx)
    simp only [keysOk, Bool.and_eq_true, List.all_eq_true] at hkeys
    have h1 := hkeys.2 _ hmem
    simp only [Bool.not_eq_true'] at h1
    obtain ⟨hnc, h2⟩ := h1
    split at h2
    · rename_i bp dv t hp hv
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h2
      obtain ⟨⟨hbp, hdv⟩, ha⟩ := h2
      exact ⟨bp, dv, t, by simpa [wfData, Std.HashMap.get?_eq_getElem?] using hp, hbp, hnc,
        by simpa [wfData, Std.HashMap.get?_eq_getElem?] using hv, hdv, ancB_sound ha⟩
    · cases h2
  · simp only [edgesOk, List.all_eq_true] at hedges
    have h1 := hedges b (List.mem_of_getElem? hb) e he
    have hj' : fi.cfg.index[e.1]? = some j := by
      simpa [wfData, Std.HashMap.get?_eq_getElem?] using hj
    obtain ⟨dst, args⟩ := e
    simp only at h1 hj' ⊢
    simp only [hj', hdb, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h1
    obtain ⟨hlen, hall⟩ := h1
    refine ⟨hlen, fun n p a hp ha hc => ?_⟩
    have hz : (p, a) ∈ db.params.zip args :=
      List.mem_iff_getElem?.2 ⟨n, by simp [List.getElem?_zip_eq_some, hp, ha]⟩
    have h2 := hall _ hz
    simp only [hc, Bool.not_true, Bool.false_or] at h2
    split at h2
    · rename_i x
      exact ⟨x, rfl, by simpa using h2⟩
    · cases h2

/-- **An accepted solution's rewrite is simulated by its input** (`ConstPhi.cpOk_simU`'s proof
from `phiOk_facts`). -/
theorem phiOk_simU {f : Function} {sol : List (ValueId × ValueId)} (h : phiOk f sol = true) :
    FunSimU f (apply f sol) := by
  obtain ⟨fi, -, hF⟩ := phiOk_facts h
  rw [ConstPhi.apply_eq]
  refine FunSimU.ofWU rfl rfl rfl rfl fun syms =>
    ⟨_, ConstPhi.CR.isSimWU hF (syms := syms), fun b hb => ?_⟩
  have hb0 : f.blocks[0]? = some b := by
    simpa [Function.entry?, List.head?_eq_getElem?] using hb
  have hkeep : ∀ p ∈ b.params, (solMap sol).contains p.1 = false := by
    intro p hp
    cases hc : (solMap sol).contains p.1
    · rfl
    · obtain ⟨bp, -, -, hd, hbp, -⟩ := hF.key p.1 hc
      rw [Opt.site_param hF.wf hb0 hp] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      exact absurd hd.1.symm hbp
  have hpar : (cpBlock (solMap sol) (keepMap (solMap sol) f) b).params = b.params := by
    simp only [cpBlock]
    exact List.filter_eq_self.2 (fun p hp => by simp [hkeep p hp])
  refine ⟨cpBlock _ _ b, by rw [cpFun_entry?, hb]; rfl, hpar,
    fun args regs slots hty hr hsl => ⟨0, 0, Inv.entry hF.wf hb hty hr hsl, rfl, rfl, rfl, rfl,
      fun v hv => ?_⟩⟩
  obtain ⟨b1, p, hb1, hp, hpv⟩ := Opt.site_param' hF.wf (Opt.avail_entry hF.wf hv)
  rw [hb0] at hb1; cases hb1
  show regs (ConstPhi.rename (solMap sol) v) = regs v
  rw [← hpv, rename_of_not (hkeep p hp)]

/-- **The validator's constant-phi removal is simulated by its input.** -/
theorem phiPre_simU (f : Function) : FunSimU f (phiPre f) := by
  unfold phiPre
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h
    rcases h.2 with h2 | h2
    · exact phiOk_simU h2
    · exact phiOkM_simU h2
  · exact FunSimU.refl f

end Opt.MidVal
