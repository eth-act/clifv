import FV.Concurrency.IselEntry
import FV.Concurrency.AllocThread

/-!
# Composing the per-thread layers (T2h, #311)

The layers are `ThreadRefine.Refines` (layer 2, isel; layer 4b, the Arm machine) or `Thin`
(layer 3, `prepare`; layer 4a, register allocation: equal traces up to steps without events).
Layer 2 and layer 4b refine a *prefix* of their target trace (up to where the source thread
stops), so composing them needs truncation:

* `Thin.trans`, `Thin.take`: `Thin` composes, and a prefix of its source is `Thin` to a prefix of
  its target (the whole target for the whole source);
* `Refines.congr`: kinds weakened, private set replaced by an equivalent one;
* `Refines.take`: a prefix of the source refines a prefix of the target when every target step
  has at most one event (the Arm steps): the target is cut before the first image of a dropped
  source event;
* **`isel_alloc_refines`**: layers 2, 3 and 4a composed: a run of the allocated code from the
  entry (`AllocThread.MTRun` under `csem`, events `cEvs`, any read values) is realized, up to a
  prefix after which the CLIF thread stops (`IselThread.Stop`), by a CLIF thread run (`CRun`),
  `Refines Maps` with no private location and the allocated code's two-event steps as the atomic
  pairs.
-/

namespace Concurrency.ThreadCompose

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine

/-! ## Traces up to steps without events -/

theorem Thin.nil_tgt {α : Type} {trS : List (List α)} (h : Thin trS []) : trS = [] := by
  cases h; rfl

theorem Thin.trans {α : Type} {a b c : List (List α)} (h1 : Thin a b) (h2 : Thin b c) :
    Thin a c := by
  induction h2 generalizing a with
  | nil => rw [Thin.nil_tgt h1]; exact .nil
  | both _ ih =>
    cases h1 with
    | both h => exact .both (ih h)
    | tgt h => exact .tgt (ih h)
  | tgt _ ih => exact .tgt (ih h1)

/-- **A prefix of `Thin`'s source is `Thin` to a prefix of its target.** -/
theorem Thin.take {α : Type} {trS trT : List (List α)} (h : Thin trS trT) :
    ∀ n, ∃ m ≤ trT.length, Thin (trS.take n) (trT.take m) ∧ (trS.length ≤ n → m = trT.length) := by
  induction h with
  | nil => exact fun n => ⟨0, Nat.le_refl _, by simp; exact .nil, fun _ => rfl⟩
  | @both e trS trT _ ih =>
    intro n
    cases n with
    | zero => exact ⟨0, Nat.zero_le _, by simp; exact .nil, fun h => by simp at h⟩
    | succ n =>
      obtain ⟨m, hm, ht, hfull⟩ := ih n
      refine ⟨m + 1, by simp; omega, by simpa using ht.both, fun hl => ?_⟩
      simp at hl ⊢
      exact hfull (by omega)
  | @tgt trS trT _ ih =>
    intro n
    obtain ⟨m, hm, ht, hfull⟩ := ih n
    exact ⟨m + 1, by simp; omega, by simpa using ht.tgt, fun hl => by simp [hfull hl]⟩

/-! ## Refinements -/

/-- The least witness. -/
theorem exists_least {P : Nat → Prop} (h : ∃ n, P n) : ∃ n, P n ∧ ∀ k < n, ¬ P k := by
  classical
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hlt : ∃ k < n, P k
    · obtain ⟨k, hk, hpk⟩ := hlt
      exact ih k hk hpk
    · exact ⟨n, hn, fun k hk hpk => hlt ⟨k, hk, hpk⟩⟩

variable {K K' V : Type}

theorem evAt_take {α : Type} (tr : List (List α)) (m : Nat) (p : Nat × Nat) :
    evAt (tr.take m) p = if p.1 < m then evAt tr p else none := by
  unfold evAt
  split
  · rw [List.getElem?_take_of_lt (by assumption)]
  · rw [List.getElem?_take_eq_none (by omega)]; rfl

theorem evAt_take_some {α : Type} {tr : List (List α)} {m : Nat} {p : Nat × Nat} {x : α}
    (h : evAt (tr.take m) p = some x) : p.1 < m ∧ evAt tr p = some x := by
  rw [evAt_take] at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

theorem isSome_take {α : Type} {tr : List (List α)} {m : Nat} {p : Nat × Nat}
    (h : (evAt (tr.take m) p).isSome) : p.1 < m ∧ (evAt tr p).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨h1, h2⟩ := evAt_take_some hx
  exact ⟨h1, by rw [h2]; rfl⟩

/-- **Weaker kinds, an equivalent private set.** -/
theorem Refines.congr {MK MK' : K → K' → Prop} {P P' : Nat → Prop}
    {pairT : Nat × Nat → Nat × Nat → Prop} {trS : List (List (Ev K V))}
    {trT : List (List (Ev K' V))} {ψ : Nat × Nat → Nat × Nat} (h : Refines MK P pairT trS trT ψ)
    (hK : ∀ a b, MK a b → MK' a b) (hP : ∀ l, P l ↔ P' l) : Refines MK' P' pairT trS trT ψ where
  ev p x hx := by
    obtain ⟨y, hy, hm, hr⟩ := h.ev p x hx
    exact ⟨y, hy, hK _ _ hm, hr⟩
  mono := h.mono
  shared p x hx hF hP' := h.shared p x hx hF ((hP _).mpr hP')
  priv p y hy hW hn := (hP _).mp (h.priv p y hy hW hn)
  len := h.len
  pair := h.pair
  pair_inv := h.pair_inv

/-- **A prefix of the source refines a prefix of the target** (module doc). -/
theorem Refines.take {MK : K → K' → Prop} {P : Nat → Prop}
    {pairT : Nat × Nat → Nat × Nat → Prop} {trS : List (List (Ev K V))}
    {trT : List (List (Ev K' V))} {ψ : Nat × Nat → Nat × Nat} (h : Refines MK P pairT trS trT ψ)
    (h1 : ∀ j (hj : j < trT.length), trT[j].length ≤ 1) (m : Nat) :
    ∃ k ≤ trT.length, Refines MK P pairT (trS.take m) (trT.take k) ψ ∧
      (trS.length ≤ m → k = trT.length) := by
  classical
  -- the first target step holding the image of a dropped source event
  let D : Nat → Prop := fun k => ∃ q, m ≤ q.1 ∧ (evAt trS q).isSome ∧ (ψ q).1 = k
  have hD : ∀ q, m ≤ q.1 → (evAt trS q).isSome → (ψ q).1 < trT.length := by
    intro q _ hq
    exact (evAt_isSome (h.img hq)).1
  by_cases hex : ∃ k, D k
  · obtain ⟨k, hk, hkmin⟩ := exists_least hex
    have hmin : ∀ q, m ≤ q.1 → (evAt trS q).isSome → k ≤ (ψ q).1 :=
      fun q hq hs => Nat.le_of_not_lt fun hlt => hkmin _ hlt ⟨q, hq, hs, rfl⟩
    obtain ⟨q0, hq0, hs0, he0⟩ := hk
    -- every kept source event's image lies before step `k`
    have hbefore : ∀ p, p.1 < m → (evAt trS p).isSome → (ψ p).1 < k := by
      intro p hp hs
      have hl := h.mono p q0 hs hs0 (.inl (by omega))
      rcases hl with hl | ⟨he, hl⟩
      · rw [← he0]; exact hl
      · exfalso
        obtain ⟨hj, hk1⟩ := evAt_isSome (h.img hs)
        obtain ⟨hj', hk2⟩ := evAt_isSome (h.img hs0)
        have := h1 _ hj
        have e : trT[(ψ p).1] = trT[(ψ q0).1] := by congr 1
        rw [e] at this hk1
        omega
    refine ⟨k, by rw [← he0]; exact Nat.le_of_lt (hD q0 hq0 hs0), ?_, fun hl => ?_⟩
    · exact {
        ev := fun p x hx => by
          obtain ⟨hp, hx'⟩ := evAt_take_some hx
          obtain ⟨y, hy, hr⟩ := h.ev p x hx'
          refine ⟨y, ?_, hr⟩
          rw [evAt_take, if_pos (hbefore p hp (by rw [hx']; rfl))]
          exact hy
        mono := fun p q hp hq hl => h.mono p q (isSome_take hp).2 (isSome_take hq).2 hl
        shared := fun p x hx hF => h.shared p x (evAt_take_some hx).2 hF
        priv := fun p y hy hW hn => by
          obtain ⟨hp, hy'⟩ := evAt_take_some hy
          refine h.priv p y hy' hW fun q hq e => ?_
          by_cases hqm : q.1 < m
          · refine hn q ?_ e
            rw [evAt_take, if_pos hqm]; exact hq
          · have := hmin q (by omega) hq
            rw [e] at this; omega
        len := fun j hj => by
          simp only [List.getElem_take]
          exact h.len j (by simp at hj; omega)
        pair := fun j hj h2 => by
          simp only [List.getElem_take] at h2
          exact h.pair j (by simp at hj; omega) h2
        pair_inv := fun p q hp hq hpr =>
          h.pair_inv p q (isSome_take hp).2 (isSome_take hq).2 hpr }
    · exfalso
      have := (evAt_isSome hs0).1
      omega
  · have hnone : ∀ q, m ≤ q.1 → (evAt trS q).isSome → False :=
      fun q hq hs => hex ⟨_, q, hq, hs, rfl⟩
    refine ⟨trT.length, Nat.le_refl _, ?_, fun _ => rfl⟩
    rw [List.take_length]
    exact {
      ev := fun p x hx => h.ev p x (evAt_take_some hx).2
      mono := fun p q hp hq hl => h.mono p q (isSome_take hp).2 (isSome_take hq).2 hl
      shared := fun p x hx hF => h.shared p x (evAt_take_some hx).2 hF
      priv := fun p y hy hW hn => h.priv p y hy hW fun q hq e => by
        by_cases hqm : q.1 < m
        · refine hn q ?_ e
          rw [evAt_take, if_pos hqm]; exact hq
        · exact hnone q (by omega) hq
      len := fun j hj => by
        simp only [List.getElem_take]
        exact h.len j (by simp at hj; omega)
      pair := fun j hj h2 => by
        simp only [List.getElem_take] at h2
        exact h.pair j (by simp at hj; omega) h2
      pair_inv := fun p q hp hq hpr =>
        h.pair_inv p q (isSome_take hp).2 (isSome_take hq).2 hpr }

/-! ## Layers 2, 3 and 4a -/

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat} {syms : String → Option Nat}

/-- **Layers 2, 3 and 4a composed** (module doc). -/
theorem isel_alloc_refines (H : DriverHyp f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBl f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) (hMem : MemRefines F sb syms (csem F fc X)) (hMRs : MRStable F MR)
    (hreg : ∀ off, ArgLoc.stack off ∉ locsOf f.sig)
    {vcp : VCode} (hprep : prepCheck vc vcp = true) {rf : RFunc}
    (halloc : checkAlloc vcp rf = .ok ()) {keep : Reg → CV → CV}
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    (ρ₀ : Nat → CV) {m₀ : Loc → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) {trM : List (List Ev)} {cM : MConf CV ArmState}
    (hr : MTRun vcp rf (csem F fc X) keep (cEvs F fc) (MConf.init rf m₀ w₀) trM cM) :
    ∃ m trS t ψ, m ≤ trM.length ∧ CRun env p (.run cs) trS t ∧
      Refines Maps (fun _ => False) (StepPair (conv (trM.take m))) trS (conv (trM.take m)) ψ ∧
      (m = trM.length ∨ Stop env p t) := by
  obtain ⟨trP, cP, hrP, hthP, -, -⟩ := alloc_thin halloc m₀ ρ₀ w₀ hr
  obtain ⟨trV, cV, hrV, hthV, -, -⟩ := prep_thin_csem (F := F) (ctx := fc) (X := X) hprep hrP
  have hth := Thin.trans hthV hthP
  obtain ⟨n, trS, t, ψ, hn, hrun, href, hend⟩ :=
    IselEntry.isel_refines_entry H hchk hMR hMRw hX hMem hMRs hreg hB0 hcall hfunc hslots hbody
      hterm hregs hty hsig hmr hargs hrV
  obtain ⟨m, hm, htk, hfull⟩ := Thin.take hth n
  have hlenV := vtrun_len (cEvs_len F fc) hrV
  obtain ⟨ψ2, href2⟩ := refines_of_thin (htk.map ProgE2E.convEv) (by
    intro j hj
    have hj' : j < (trV.take n).length := by simpa using hj
    simp only [List.getElem_map, List.length_map, List.getElem_take]
    exact hlenV j (by simp at hj'; omega))
  have href3 := Refines.congr (Refines.trans href href2) (MK' := Maps) (P' := fun _ => False)
    (fun a c ⟨b, h1, h2⟩ => h2 ▸ h1) (fun l => ⟨fun h => by rcases h with h | h <;> exact h,
      fun h => h.elim⟩)
  refine ⟨m, trS, t, fun p => ψ2 (ψ p), hm, hrun, href3, ?_⟩
  · rcases hend with h | h
    · exact .inl (hfull (by rw [h]; simp))
    · exact .inr h

end

end Concurrency.ThreadCompose
