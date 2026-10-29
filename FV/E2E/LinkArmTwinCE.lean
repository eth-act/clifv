import FV.E2E.LinkArmActualEntry
import FV.E2E.LinkArmTwinCTrans
import FV.E2E.LinkArmTwinCLock

/-!
# Call-restricted twins that relate the errors (SEM1 #537, #716)

`TableOfE M g s ini` (`LinkArmTableE.lean`) quantifies over the error-free prefixes of its own
run, and `TabUpToE`'s call clause over the error-free prefixes of the callee runs. `TwinC` does not
relate the two runs' errors, so `TableOfE` cannot be carried along it (#716). The machine lock
gives more: `StEqOutX` leaves only `x30` and memory free, so two locked states have the same `ERR`
field. Decision (new names, the old ones kept):

* `TwinBaseCE` (`TwinBaseC` plus: before the first return the two states are error-free together),
  **`TwinCE`** (`TwinC` with `TwinBaseCE` at every level), `TwinCE.base`, **`TwinCE.twinC`**,
  `twinCE_refl`, **`TwinBaseCE.symm`**, **`TwinCE.symm`**, **`TwinBaseCE.trans`**,
  **`TwinCE.trans`**;
* **`tabUpToE_twinCE`**, **`tableOfE_twinCE`** (the prefix-closed table carries over);
* **`twinBaseCE_of_lock`** (one level from the lock, as `twinBaseC_of_lock`);
* **`CallTwinCE`** (`CallTwinC` concluding `TwinCE`), `CallTwinCE.toC`, **`detTabPRBG_ofCE`**,
  **`detTabPRBGr_ofCE`**, **`detTabPRBE_ofCE`** (#716: `DetTabPRBE` from `CallTwinCE`),
  **`detTabPRBEr_ofCE`** (`DetTabPRBGr L.TableOfE`), **`detTabPRBr_ofCE`**, **`detTabPRB_ofCE'`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **One level of twin runs relating the errors** (module doc). -/
def TwinBaseCE (M : Nat) (g : Clif.Function) (s s₀ : Arm.ArmState) : Prop :=
  L.TwinBaseC M g s s₀ ∧
    ∀ i, (∀ j < i, ¬ L.RetAt g s (runX (L.mach M g) j s)) →
      (Arm.r .ERR (runX (L.mach M g) i s) = .None ↔ Arm.r .ERR (runX (L.mach M g) i s₀) = .None)

/-- **Twin runs relating the errors** (module doc). -/
def TwinCE : Nat → Clif.Function → Arm.ArmState → Arm.ArmState → Prop
  | 0, g, s, s₀ => L.TwinBaseCE 0 g s s₀
  | M + 1, g, s, s₀ => L.TwinBaseCE (M + 1) g s s₀ ∧
      ∀ i, (∀ j < i + 1, ¬ L.RetAt g s (runX (L.mach (M + 1) g) j s)) → ∀ h,
        L.CallsTo g (runX (L.mach (M + 1) g) i s) h →
        TwinCE M h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
          (enterAt (L.A h) (runX (L.mach (M + 1) g) i s₀))

theorem TwinCE.base {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState} (h : L.TwinCE M g s s₀) :
    L.TwinBaseCE M g s s₀ := by
  cases M with
  | zero => exact h
  | succ M => exact h.1

/-- **`TwinCE` gives `TwinC`.** -/
theorem TwinCE.twinC : ∀ {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState},
    L.TwinCE M g s s₀ → L.TwinC M g s s₀
  | 0, _, _, _, h => h.1
  | _ + 1, _, _, _, ⟨h1, h2⟩ => ⟨h1.1, fun i hi h hc => TwinCE.twinC (h2 i hi h hc)⟩

/-- **Every run is its own twin.** -/
theorem twinCE_refl : ∀ (M : Nat) (g : Clif.Function) (s : Arm.ArmState), L.TwinCE M g s s
  | 0, g, s => ⟨(L.twinC_refl 0 g s).base, fun _ _ => Iff.rfl⟩
  | M + 1, g, s => ⟨⟨(L.twinC_refl (M + 1) g s).base, fun _ _ => Iff.rfl⟩,
      fun i _ h _ => twinCE_refl M h _⟩

/-- **Twin runs relating the errors are symmetric, one level.** -/
theorem TwinBaseCE.symm {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState}
    (h : L.TwinBaseCE M g s s₀) : L.TwinBaseCE M g s₀ s :=
  ⟨TwinBaseC.symm L h.1, fun i hi => (h.2 i (L.noRetAt_twinC h.1 hi)).symm⟩

/-- **Twin runs relating the errors are symmetric.** -/
theorem TwinCE.symm : ∀ {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState},
    L.TwinCE M g s s₀ → L.TwinCE M g s₀ s
  | 0, _, _, _, h => TwinBaseCE.symm L h
  | _ + 1, _, _, _, ⟨h1, h2⟩ => ⟨TwinBaseCE.symm L h1, fun i hi h hc => by
      have hi' := L.noRetAt_twinC h1.1 hi
      have hn : ¬ L.RetAt _ _ _ := hi' i (Nat.lt_succ_self i)
      have hct := ((h1.1 i fun j hj => hi' j (by omega)).2 hn).2.2.1 h
      exact TwinCE.symm (h2 i hi' h (hct.2 hc))⟩

/-- **Twin runs relating the errors compose, one level.** -/
theorem TwinBaseCE.trans {M : Nat} {g : Clif.Function} {s s₁ s₂ : Arm.ArmState}
    (h1 : L.TwinBaseCE M g s s₁) (h2 : L.TwinBaseCE M g s₁ s₂) : L.TwinBaseCE M g s s₂ :=
  ⟨TwinBaseC.trans L h1.1 h2.1, fun i hi =>
    (h1.2 i hi).trans (h2.2 i (L.noRetAt_twinC' h1.1 hi))⟩

/-- **Twin runs relating the errors compose.** -/
theorem TwinCE.trans : ∀ {M : Nat} {g : Clif.Function} {s s₁ s₂ : Arm.ArmState},
    L.TwinCE M g s s₁ → L.TwinCE M g s₁ s₂ → L.TwinCE M g s s₂
  | 0, _, _, _, _, h1, h2 => TwinBaseCE.trans L h1 h2
  | _ + 1, _, _, _, _, ⟨b1, n1⟩, ⟨b2, n2⟩ => ⟨TwinBaseCE.trans L b1 b2, fun i hi h hc => by
      have hi1 := L.noRetAt_twinC' b1.1 hi
      have hn : ¬ L.RetAt _ _ _ := hi i (Nat.lt_succ_self i)
      have hct := ((b1.1 i fun j hj => hi j (by omega)).2 hn).2.2.1 h
      exact TwinCE.trans (n1 i hi h hc) (n2 i hi1 h (hct.1 hc))⟩

/-- **The prefix-closed table of a run prefix carries over to its twin** (errors related). -/
theorem tabUpToE_twinCE : ∀ (M : Nat) (g : Clif.Function) (s s₀ : Arm.ArmState)
    (b : Nat → Nat → BitVec 8) (k N e : Nat), L.TwinCE M g s s₀ →
    (∀ j < N, ¬ L.RetAt g s (runX (L.mach M g) j s)) →
    L.TabUpToE M g s b k N e → L.TabUpToE M g s₀ b k N e
  | 0, _, _, _, _, _, _, _, _, _, he => he
  | M + 1, g, s, s₀, b, k, N, e, ⟨htw, hnest⟩, hN, ⟨E, he, hcl⟩ => by
    have hb : ∀ i < N, Arm.r .PC (runX (L.mach (M + 1) g) i s) =
          Arm.r .PC (runX (L.mach (M + 1) g) i s₀) ∧
        spv (runX (L.mach (M + 1) g) i s) = spv (runX (L.mach (M + 1) g) i s₀) ∧
        (∀ h, L.CallsTo g (runX (L.mach (M + 1) g) i s) h ↔
          L.CallsTo g (runX (L.mach (M + 1) g) i s₀) h) ∧
        ∀ h, L.CallsTo g (runX (L.mach (M + 1) g) i s) h →
          ∀ a, L.SlotByte h (spv (runX (L.mach (M + 1) g) i s)) a →
          (runX (L.mach (M + 1) g) i s).mem (BitVec.ofNat 64 a) =
            (runX (L.mach (M + 1) g) i s₀).mem (BitVec.ofNat 64 a) :=
      fun i hi => (htw.1 i fun j hj => hN j (by omega)).2 (hN i hi)
    have hcb : ∀ i ≤ N, callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i =
        callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s₀ i := fun i hi =>
      callsBefore_twin _ _ _ fun j hj => (hb j (by omega)).1
    refine ⟨E, by rw [← hcb N (Nat.le_refl _)]; exact he, fun i hi hcp => ?_⟩
    obtain ⟨hpc, hsp, hct, hsl⟩ := hb i hi
    obtain ⟨h0, h1⟩ := hcl i hi (hpc ▸ hcp)
    rw [← hcb i (Nat.le_of_lt hi)]
    refine ⟨fun hn => h0 fun h hc => hn h ((hct h).1 hc), fun h hc => ?_⟩
    have hc' := (hct h).2 hc
    obtain ⟨hslot, hle, hpre, hret⟩ := h1 h hc'
    have htw' := hnest i (fun j hj => hN j (by omega)) h hc'
    have htb := (TwinCE.base L htw').1
    have hte := (TwinCE.base L htw').2
    refine ⟨fun h1 a ha => ?_, hle, fun N' hN' hE' => ?_, fun N' hr hm => ?_⟩
    · rw [← hsp] at ha
      rw [hslot h1 a ha]
      exact probeMem_congr hsp (hsl h hc' a ha)
    · -- the twin's error-free prefix before its return is one of the run
      have hN'' : ∀ j < N', ¬ L.RetAt h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
          (runX (L.mach M h) j (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))) :=
        L.noRetAt_twinC htb fun j hj hr => hN' j hj ((L.retAt_enterAt_iff).1 hr)
      obtain ⟨e', he'⟩ := hpre N' (fun j hj hr => hN'' j hj ((L.retAt_enterAt_iff).2 hr))
        (fun j hj => (hte j fun l hl => hN'' l (by omega)).2 (hE' j hj))
      exact ⟨e', tabUpToE_twinCE M h _ _ b _ N' e' htw' hN'' he'⟩
    · -- the twin's first return is the run's
      have hpre' : ∀ j < N', ¬ L.RetAt h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
          (runX (L.mach M h) j (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))) :=
        L.noRetAt_twinC htb fun j hj hr => hm j hj ((L.retAt_enterAt_iff).1 hr)
      have hr' : RetOf (L.A h) (runX (L.mach (M + 1) g) i s)
          (runX (L.mach M h) N' (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))) :=
        (L.retAt_enterAt_iff).1 ((htb N' hpre').1.2 ((L.retAt_enterAt_iff).2 hr))
      have ht := hret N' hr' fun j hj hr => hpre' j hj ((L.retAt_enterAt_iff).2 hr)
      exact L.tabUpTo_twinC M h _ _ b _ N' _ (TwinCE.twinC L htw') hpre' ht

/-- **The prefix-closed table of a run carries over to its twin** (errors related). -/
theorem tableOfE_twinCE {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState}
    {ini : Clif.SlotInit} (htw : L.TwinCE M g s s₀) (ht : L.TableOfE M g s ini) :
    L.TableOfE M g s₀ ini := by
  intro N hN hE
  have hb := TwinCE.base L htw
  have hN' := L.noRetAt_twinC hb.1 hN
  obtain ⟨e, he⟩ := ht N hN' fun j hj => (hb.2 j fun l hl => hN' l (by omega)).2 (hE j hj)
  exact ⟨e, L.tabUpToE_twinCE M g s s₀ _ _ N e htw hN' he⟩

/-- **One level of twins relating the errors from the lock up to the shared return index `T`**
(`twinBaseC_of_lock`; locked states have the same `ERR`, both runs are error-free at `T`). -/
theorem twinBaseCE_of_lock (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    (hc : (L.A g).fa.blrLow = true) {K : Nat} {c : BitVec 64} (hroom : K ≤ c.toNat)
    (hK : ∀ h, L.Callee g h → frameDrop (L.A h).af ≤ K) {s s₀ : Arm.ArmState} {T : Nat}
    (hlk : ∀ i < T, ∃ Z, StEqOutX Z (runX (L.mach M g) i s) (runX (L.mach M g) i s₀) ∧
      ∀ a, StackBelow K c a → ¬ Z a)
    (himg : ∀ i < T, ∀ a, L.Img a → (runX (L.mach M g) i s).mem a = L.imgMem a)
    (himg₀ : ∀ i < T, ∀ a, L.Img a → (runX (L.mach M g) i s₀).mem a = L.imgMem a)
    (hsp : ∀ i < T, ∀ h, L.CallsTo g (runX (L.mach M g) i s) h → spv (runX (L.mach M g) i s) = c)
    (hcal : ∀ i < T, ∀ h, L.CallsTo g (runX (L.mach M g) i s) h → L.Callee g h)
    (hnr : ∀ i < T, ¬ L.RetAt g s (runX (L.mach M g) i s) ∧
      ¬ L.RetAt g s₀ (runX (L.mach M g) i s₀))
    (hr : L.RetAt g s (runX (L.mach M g) T s) ∧ L.RetAt g s₀ (runX (L.mach M g) T s₀)) :
    L.TwinBaseCE M g s s₀ := by
  refine ⟨L.twinBaseC_of_lock hL hg hc hroom hK hlk himg himg₀ hsp hcal hnr hr, fun i hi => ?_⟩
  rcases Nat.lt_trichotomy i T with h | rfl | h
  · obtain ⟨Z, hz, -⟩ := hlk i h
    rw [hz.1 .ERR (by simp)]
  · exact ⟨fun _ => hr.2.2.1, fun _ => hr.1.2.1⟩
  · exact absurd hr.1 (hi T h)

/-- **The determinism step at a call, as twin runs relating the errors** (`CallTwinC` concluding
`TwinCE`). -/
def CallTwinCE (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ (n : String) (h : Clif.Function), L.P.func? n = some h → (∃ g ∈ L.P.funcs, L.Callee g h) →
    ∀ (F : BitVec 64 → Prop), (∀ a, L.Img a → F a) →
    ∀ (uses : List CV) (w : Arm.ArmState), Arm.r .ERR w = .None → (spv w).toNat % 16 = 0 →
    frameDrop (L.A h).af + κ (M - 1) h ≤ (spv w).toNat →
    (∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a → F a ∧ ¬ L.Img a) →
    ∀ (vals : List Clif.Val) (cm : Clif.Mem) (cs : Clif.State) (rvals : List Clif.Val)
      (cm' : Clif.Mem) (ini : Clif.SlotInit),
    MemRel F L.syms cm w → ArgsAt h.sig vals uses w → StackArgsAvoid F h.sig vals w →
    (L.NeedSlots → L.PlaceAtB cm (spv w) ini) →
    (L.NeedSlots → ∀ a, L.SlotByte h (spv w) a →
      ini.bytes (ini.next + 1) a = probeMem (L.A h).af w (BitVec.ofNat 64 a)) →
    Clif.initState L.P n vals cm = .ok cs → L.crun M cs = .returned rvals cm' →
    ∀ t, L.CallerOk F h uses w t →
      (∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (L.canon h uses w)) →
      (∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a →
        t.mem a = (L.canon h uses w).mem a) →
      L.TwinCE (M - 1) h (enterAt (L.A h) t) (enterAt (L.A h) (L.canon h uses w))

theorem CallTwinCE.toC {M : Nat} (hd : L.CallTwinCE κ M) : L.CallTwinC κ M :=
  fun n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini hmr hargs hsav hpl
    hslotb hinit hrun t ht hmsk hrgn =>
    TwinCE.twinC L (hd n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini hmr
      hargs hsav hpl hslotb hinit hrun t ht hmsk hrgn)

/-- **`DetTabPRBG` from `CallTwinCE`**, for any table predicate carried along `TwinCE`. -/
theorem detTabPRBG_ofCE (T : Nat → Clif.Function → Arm.ArmState → Clif.SlotInit → Prop)
    (hT : ∀ M h s s₀ ini, L.TwinCE M h s s₀ → T M h s ini → T M h s₀ ini) {M : Nat}
    (hd : L.CallTwinCE κ M) : L.DetTabPRBG T κ M :=
  fun n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini hmr hargs hsav hpl
    hslotb hinit hrun t ht hmsk hrgn htab =>
    hT _ _ _ _ _ (hd n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini hmr
      hargs hsav hpl hslotb hinit hrun t ht hmsk hrgn) htab

/-- **`DetTabPRBGr` from `CallTwinCE`** (`TwinCE.symm`). -/
theorem detTabPRBGr_ofCE (T : Nat → Clif.Function → Arm.ArmState → Clif.SlotInit → Prop)
    (hT : ∀ M h s s₀ ini, L.TwinCE M h s s₀ → T M h s ini → T M h s₀ ini) {M : Nat}
    (hd : L.CallTwinCE κ M) : L.DetTabPRBGr T κ M :=
  fun n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini hmr hargs hsav hpl
    hslotb hinit hrun t ht hmsk hrgn htab =>
    hT _ _ _ _ _ (TwinCE.symm L (hd n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs
      rvals cm' ini hmr hargs hsav hpl hslotb hinit hrun t ht hmsk hrgn)) htab

/-- **#716: `DetTabPRBE` from `CallTwinCE`** (`tableOfE_twinCE`). -/
theorem detTabPRBE_ofCE {M : Nat} (hd : L.CallTwinCE κ M) : L.DetTabPRBE κ M :=
  L.detTabPRBG_ofCE L.TableOfE (fun _ _ _ _ _ htw ht => L.tableOfE_twinCE htw ht) hd

/-- **`DetTabPRBGr L.TableOfE` from `CallTwinCE`** (the canonical callee's prefix-closed table is
the actual one's). -/
theorem detTabPRBEr_ofCE {M : Nat} (hd : L.CallTwinCE κ M) : L.DetTabPRBGr L.TableOfE κ M :=
  L.detTabPRBGr_ofCE L.TableOfE (fun _ _ _ _ _ htw ht => L.tableOfE_twinCE htw ht) hd

/-- **`DetTabPRBr` from `CallTwinCE`** (`tableOf_twinC`). -/
theorem detTabPRBr_ofCE {M : Nat} (hd : L.CallTwinCE κ M) : L.DetTabPRBr κ M :=
  L.detTabPRBGr_ofC L.TableOf (fun _ _ _ _ _ htw ht => L.tableOf_twinC htw ht) (CallTwinCE.toC L hd)

/-- **`DetTabPRB` from `CallTwinCE`.** -/
theorem detTabPRB_ofCE' {M : Nat} (hd : L.CallTwinCE κ M) : L.DetTabPRB κ M :=
  L.detTabPRB_ofC (CallTwinCE.toC L hd)

end LinkSys

end E2E
