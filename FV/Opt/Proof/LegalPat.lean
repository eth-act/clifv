import FV.Opt.Legal
import FV.Opt.Proof.SemSim

/-!
# Pure pattern instances (`Opt.Legal.pureOk`)

A canonical pattern is straight-line pure code over canonical value ids. `runPat` runs it on a
register file (`canon ins`: the inputs at `0 ..< n`); `runPat_lstar` shows that an instance
of the pattern (renamed by `σ`, injective on the written ids) runs in a frame from registers
agreeing with the canonical inputs, to registers agreeing with the canonical run on every id it
wrote and unchanged elsewhere. The per-pattern semantics (`FV/Opt/Proof/LegalArith.lean`) is
then about the closed canonical run only.
-/

namespace Opt.Legal

open Clif

/-- A frame whose only relevant field is its register file. -/
def dframe (ρ : Regs) : Frame := ⟨default, ρ, [], [], .trap .stkOvf⟩

/-- The canonical register file of the inputs `vs`: `vs[c]` at `c`. -/
def canon (vs : List Val) : Regs := fun c => vs[c]?

/-- The canonical run of a pattern. -/
def runPat : Regs → List Stmt → Option Regs
  | ρ, [] => some ρ
  | ρ, s :: ss =>
    match evalInst (dframe ρ) Mem.empty s.inst with
    | .ok (vs, _) => (ρ.setMany s.results vs).bind (runPat · ss)
    | _ => none

@[simp] theorem runPat_nil (ρ : Regs) : runPat ρ [] = some ρ := rfl

theorem runPat_cons (ρ : Regs) (s : Stmt) (ss : List Stmt) :
    runPat ρ (s :: ss) = match evalInst (dframe ρ) Mem.empty s.inst with
      | .ok (vs, _) => (ρ.setMany s.results vs).bind (runPat · ss)
      | _ => none := rfl

theorem runPat_append (ρ : Regs) (a b : List Stmt) :
    runPat ρ (a ++ b) = (runPat ρ a).bind (runPat · b) := by
  induction a generalizing ρ with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.cons_append, runPat_cons]
    split
    · cases ρ.setMany s.results _ <;> simp [ih]
    · rfl

/-! ## Pure instructions: evaluation depends on the registers only -/

/-- A pure instruction evaluated on a frame whose registers agree with `ρ0` (through `σ`) on
the operands `ρ0` defines: the canonical result, memory unchanged. -/
theorem evalInst_pure_rename {i : Inst} (h : pureInst i = true) {ρ0 : Regs} {vs : List Val}
    {m0 : Mem} (hev : evalInst (dframe ρ0) Mem.empty i = .ok (vs, m0))
    {σ : ValueId → ValueId} {fr : Frame}
    (hops : ∀ x ∈ instOps i, ∀ v, ρ0 x = some v → fr.regs (σ x) = some v) (m : Mem) :
    evalInst fr m (renameInst σ i) = .ok (vs, m) := by
  cases i <;> simp only [pureInst, Bool.false_eq_true] at h <;>
    simp only [instOps, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq] at hops <;>
    simp only [evalInst, renameInst, Frame.getAs, Frame.get, dframe, Res.bind_eq_ok,
      Res.ofOption_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at hev ⊢
  case iconst => exact ⟨hev.1, trivial⟩
  case unary =>
    obtain ⟨a, ⟨a1, h1, h2⟩, h3, -⟩ := hev
    exact ⟨a, ⟨a1, hops _ h1, h2⟩, h3, trivial⟩
  case binary op _ _ _ =>
    obtain ⟨a, ⟨a1, h1, h2⟩, h3⟩ := hev
    refine ⟨a, ⟨a1, hops.1 _ h1, h2⟩, ?_⟩
    by_cases hs : op.isShift <;>
      simp only [hs, ite_true, ite_false, Bool.false_eq_true, Res.bind_eq_ok, Res.ofOption_eq_ok,
        Res.pure_eq_ok, Prod.mk.injEq] at h3 ⊢
    · obtain ⟨b, hb, r, hr, h4, -⟩ := h3
      exact ⟨b, hops.2 _ hb, r, hr, h4, trivial⟩
    · obtain ⟨b, ⟨b1, hb1, hb2⟩, h4, -⟩ := h3
      exact ⟨b, ⟨b1, hops.2 _ hb1, hb2⟩, h4, trivial⟩
  case icmp =>
    obtain ⟨a, ⟨a1, h1, h2⟩, b, ⟨b1, hb1, hb2⟩, h3, -⟩ := hev
    exact ⟨a, ⟨a1, hops.1 _ h1, h2⟩, b, ⟨b1, hops.2 _ hb1, hb2⟩, h3, trivial⟩
  case select =>
    obtain ⟨c, hc, a, ⟨a1, h1, h2⟩, b, ⟨b1, hb1, hb2⟩, h3, -⟩ := hev
    exact ⟨c, hops.1 _ hc, a, ⟨a1, hops.2.1 _ h1, h2⟩, b, ⟨b1, hops.2.2 _ hb1, hb2⟩, h3, trivial⟩
  case extend op _ _ =>
    obtain ⟨a, ha, u, hu, h3⟩ := hev
    refine ⟨a, hops _ ha, u, hu, ?_⟩
    cases op <;> simp only [Res.pure_eq_ok, Prod.mk.injEq] at h3 ⊢ <;> exact ⟨h3.1, trivial⟩
  case ireduce =>
    obtain ⟨a, ha, u, hu, h3, -⟩ := hev
    exact ⟨a, hops _ ha, u, hu, h3, trivial⟩

/-! ## Running a pattern instance -/

/-- An instance (renamed by `σ`) of a pure single-result pattern runs, as local steps, from
registers agreeing with the canonical run's start (through `σ`), to registers agreeing with
its end; every id outside the renamed written ids keeps its value. `U`: the canonical ids the
run may define (`σ` is injective from the written ids into `U`). -/
theorem runPat_lstar {pat : List Stmt}
    (hp : ∀ st ∈ pat, pureInst st.inst = true ∧ st.results.length = 1)
    {U : ValueId → Prop} (hwU : ∀ st ∈ pat, ∀ c ∈ st.results, U c)
    {σ : ValueId → ValueId}
    (hinj : ∀ st ∈ pat, ∀ c ∈ st.results, ∀ d, U d → c ≠ d → σ c ≠ σ d)
    {ρ0 ρ0' : Regs} (hrun : runPat ρ0 pat = some ρ0')
    (hdom : ∀ c v, ρ0 c = some v → U c)
    {fr : Frame} (hag : ∀ c v, ρ0 c = some v → fr.regs (σ c) = some v)
    (m : Mem) (rest : List Stmt) :
    ∃ regs', LStar { fr with body := pat.map (renameStmt σ) ++ rest } m
        { fr with regs := regs', body := rest } m ∧
      (∀ c v, ρ0' c = some v → regs' (σ c) = some v) ∧ (∀ c v, ρ0' c = some v → U c) ∧
      (∀ v, (∀ st ∈ pat, ∀ c ∈ st.results, σ c ≠ v) → regs' v = fr.regs v) := by
  induction pat generalizing ρ0 fr with
  | nil =>
    cases hrun
    exact ⟨fr.regs, .refl _ _, hag, hdom, fun _ _ => rfl⟩
  | cons s ss ih =>
    obtain ⟨hpure, hlen⟩ := hp s (List.mem_cons_self ..)
    obtain ⟨r, hr⟩ : ∃ r, s.results = [r] := List.length_eq_one_iff.1 hlen
    rw [runPat_cons] at hrun
    split at hrun
    · rename_i vs m0 hev
      obtain ⟨ρ1, h1, h2⟩ := Option.bind_eq_some_iff.1 hrun
      rw [hr] at h1
      obtain ⟨v, rfl⟩ : ∃ v, vs = [v] := by
        cases vs with
        | nil => simp [Regs.setMany] at h1
        | cons v t => cases t with
          | nil => exact ⟨v, rfl⟩
          | cons => simp [Regs.setMany] at h1
      simp only [Regs.setMany_cons, Regs.setMany_nil, Option.some.injEq] at h1
      subst h1
      have hstep : lstep { fr with body := (s :: ss).map (renameStmt σ) ++ rest } m =
          LRes.next (Frame.mk fr.func (Regs.set fr.regs (σ r) v) fr.slots
            (ss.map (renameStmt σ) ++ rest) fr.term) m := by
        have hc : ∀ fn args, (renameStmt σ s).inst ≠ .call fn args := by
          intro fn args hh
          simp only [renameStmt] at hh
          cases hs : s.inst <;> simp [hs, pureInst] at hpure <;> simp [hs, renameInst] at hh
        rw [lstep_inst (st := renameStmt σ s) (rest := ss.map (renameStmt σ) ++ rest) rfl hc]
        have hops : ∀ x ∈ instOps s.inst, ∀ v, ρ0 x = some v → fr.regs (σ x) = some v :=
          fun x _ v hx => hag x v hx
        have := evalInst_pure_rename hpure hev
          (fr := { fr with body := (s :: ss).map (renameStmt σ) ++ rest }) hops m
        simp only [renameStmt] at this ⊢
        rw [this]
        simp [hr, LRes.ofRes]
      have hU : U r := hwU s (List.mem_cons_self ..) r (by rw [hr]; exact List.mem_cons_self ..)
      obtain ⟨regs', hl, ha, hd, hu⟩ := ih (fun st h => hp st (List.mem_cons_of_mem _ h))
        (fun st h => hwU st (List.mem_cons_of_mem _ h))
        (fun st h => hinj st (List.mem_cons_of_mem _ h)) h2
        (ρ0 := ρ0.set r v) (fr := { fr with regs := fr.regs.set (σ r) v })
        (fun c v' hc => by
          by_cases hcr : c = r
          · subst hcr; exact hU
          · rw [Regs.set_other _ _ hcr] at hc; exact hdom c v' hc)
        (fun c v' hc => by
          by_cases hcr : c = r
          · subst hcr
            simp only [Regs.set_same, Option.some.injEq] at hc
            subst hc
            simp
          · rw [Regs.set_other _ _ hcr] at hc
            have hne : σ c ≠ σ r := fun h =>
              hinj s (List.mem_cons_self ..) r (by rw [hr]; exact List.mem_cons_self ..) c
                (hdom c v' hc) (Ne.symm hcr) h.symm
            simp only [Regs.set_other _ _ hne]
            exact hag c v' hc)
      refine ⟨regs', .step hstep hl, ha, hd, fun w hw => ?_⟩
      rw [hu w (fun st h => hw st (List.mem_cons_of_mem _ h))]
      have hne : w ≠ σ r := fun h => hw s (List.mem_cons_self ..) r
        (by rw [hr]; exact List.mem_cons_self ..) h.symm
      exact Regs.set_other _ _ hne
    · cases hrun

theorem sigma_lt {ins outs : List ValueId} {tm : List (ValueId × ValueId)} {c : ValueId}
    (h : c < ins.length) : sigma ins outs tm c = ins[c] := by
  simp [sigma, h]

theorem sigma_out {ins outs : List ValueId} {tm : List (ValueId × ValueId)} {k : Nat}
    (h : k < outs.length) : sigma ins outs tm (ins.length + k) = outs[k] := by
  have h1 : ¬ (ins.length + k < ins.length) := by omega
  simp [sigma, h1, h]

theorem sigma_out' {ins outs : List ValueId} {tm : List (ValueId × ValueId)} {c : Nat}
    (h1 : ins.length ≤ c) (h2 : c < ins.length + outs.length) :
    sigma ins outs tm c ∈ outs := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, c = ins.length + k := ⟨c - ins.length, by omega⟩
  have hk : k < outs.length := by omega
  rw [sigma_out hk]
  exact List.getElem_mem ..

/-- **A `pureOk` segment runs the pattern.** From registers holding the inputs `inVals` at
`ins`, the segment reaches registers holding the canonical outputs at `outs`, every other
value that is not fresh unchanged. -/
theorem pureOk_run {C : Ctx} {pat : List Stmt} {ins outs : List ValueId} {seg : List Stmt}
    (h : pureOk C pat ins outs seg = true) {inVals : List Val}
    (hlen : inVals.length = ins.length) {ρ0' : Regs}
    (hrun : runPat (canon inVals) pat = some ρ0') {fr : Frame}
    (hin : ∀ i (hi : i < ins.length), fr.regs ins[i] = inVals[i]?) (m : Mem)
    (rest : List Stmt) :
    ∃ regs', LStar { fr with body := seg ++ rest } m { fr with regs := regs', body := rest } m ∧
      (∀ k (hk : k < outs.length) v, ρ0' (ins.length + k) = some v → regs' outs[k] = some v) ∧
      (∀ v, C.fresh v = false → v ∉ outs → regs' v = fr.regs v) := by
  simp only [pureOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨hseg, hpure⟩, hge⟩, hinj⟩, hfresh⟩ := h
  generalize hσ : sigma ins outs (guessTemps (ins.length + outs.length) pat seg) = σ at *
  have hw : ∀ st ∈ pat, ∀ c ∈ st.results, c ∈ written pat := fun st hst c hc => by
    simp only [written, List.mem_flatMap]; exact ⟨st, hst, hc⟩
  obtain ⟨regs', hl, ha, -, hu⟩ := runPat_lstar (U := fun c => c < ins.length ∨ c ∈ written pat)
    (σ := σ) (fun st hst => hpure st hst)
    (fun st hst c hc => .inr (hw st hst c hc))
    (fun st hst c hc d hd hne => by
      have := hinj c (hw st hst c hc) d (by
        simp only [List.mem_append, List.mem_range]; exact hd)
      rcases this with h | h
      · exact absurd h hne
      · exact h)
    hrun
    (fun c v hc => by
      simp only [canon] at hc
      have := (List.getElem?_eq_some_iff.1 hc).1
      exact .inl (hlen ▸ this))
    (fr := fr)
    (fun c v hc => by
      simp only [canon] at hc
      obtain ⟨hc1, hc2⟩ := List.getElem?_eq_some_iff.1 hc
      have hc3 : c < ins.length := hlen ▸ hc1
      rw [← hσ, sigma_lt hc3, hin c hc3, List.getElem?_eq_getElem hc1, hc2])
    m rest
  rw [hseg]
  refine ⟨regs', hl, fun k hk v hv => ?_, fun v hv hvo => hu v fun st hst c hc hcv => ?_⟩
  · have := ha _ _ hv
    rwa [← hσ, sigma_out hk] at this
  · have hcw := hw st hst c hc
    have h1 := hge c hcw
    rcases hfresh c hcw with h2 | h2
    · exact hvo (hcv ▸ hσ ▸ sigma_out' h1 h2)
    · rw [hcv] at h2; rw [h2] at hv; cases hv

end Opt.Legal
