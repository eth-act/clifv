import FV.E2E.LinkArmDetPRBOf

/-!
# Twin runs with the slot bytes compared at the calls only (SEM1 #537, `docs/plans/uninit.md`
§5.9, determinism step)

Finding (UninitZ22b): `TwinBase` (and `TwinN`) compare the slot bytes `SlotByte h (spv u) a` of
**every** function `h` at **every** state `u` before the return, not only of the function the
state calls. That is stronger than the determinism of the machine gives, and false in general:
`SlotByte h c` covers bytes down to `frameDrop (L.A h).af` below `c` for any `h` (also functions
`g` never calls, with frames larger than `g`'s dead-stack budget `K`), and below the dead stack the
two entries are unconstrained (`EntryAgree` covers only `frameDrop + K` bytes below the entry
`sp`). The table (`TabUpTo`, `TableOf`) reads the slot bytes only at program calls (`CallsTo g u
h`), of the called `h`; there the callee's frame fits in the caller's dead stack (κ budget,
`LinkSys.slotByte_eq_of_lock`). Decision (conservative: new names, the old ones kept):

* `TwinBaseC`, **`TwinC`**, `TwinNC`: `TwinBase`/`Twin`/`TwinN` with the slot clause under
  `CallsTo g u h`; `Twin.twinC`, `TwinN.twinNC` (the old relations are stronger);
* `twinC_refl`, `twinNC_refl`, `noRetAt_twinC`, **`tabUpTo_twinC`**, **`tableOf_twinC`**,
  **`tabUpTo_twinNC`**;
* **`CallTwinC`**, **`DetRunPRBC`** (`CallTwin`, `DetRunPRB` concluding `TwinC`/`TwinNC`;
  `CallTwin.callTwinC`, `DetRunPRB.toC`), **`detTabPRBG_ofC`**, **`detTabPRB_ofC`**,
  **`detPRBG_ofC`**, **`detPRB_ofC`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **One level of twin runs, slot bytes at the calls** (module doc). -/
def TwinBaseC (M : Nat) (g : Clif.Function) (s s₀ : Arm.ArmState) : Prop :=
  ∀ i, (∀ j < i, ¬ L.RetAt g s (runX (L.mach M g) j s)) →
    (L.RetAt g s (runX (L.mach M g) i s) ↔ L.RetAt g s₀ (runX (L.mach M g) i s₀)) ∧
    (¬ L.RetAt g s (runX (L.mach M g) i s) →
      Arm.r .PC (runX (L.mach M g) i s) = Arm.r .PC (runX (L.mach M g) i s₀) ∧
      spv (runX (L.mach M g) i s) = spv (runX (L.mach M g) i s₀) ∧
      (∀ h, L.CallsTo g (runX (L.mach M g) i s) h ↔ L.CallsTo g (runX (L.mach M g) i s₀) h) ∧
      ∀ h, L.CallsTo g (runX (L.mach M g) i s) h → ∀ a, L.SlotByte h (spv (runX (L.mach M g) i s)) a →
        (runX (L.mach M g) i s).mem (BitVec.ofNat 64 a) =
          (runX (L.mach M g) i s₀).mem (BitVec.ofNat 64 a))

/-- **Twin runs, slot bytes at the calls** (module doc). -/
def TwinC : Nat → Clif.Function → Arm.ArmState → Arm.ArmState → Prop
  | 0, g, s, s₀ => L.TwinBaseC 0 g s s₀
  | M + 1, g, s, s₀ => L.TwinBaseC (M + 1) g s s₀ ∧
      ∀ i, (∀ j < i + 1, ¬ L.RetAt g s (runX (L.mach (M + 1) g) j s)) → ∀ h,
        L.CallsTo g (runX (L.mach (M + 1) g) i s) h →
        TwinC M h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
          (enterAt (L.A h) (runX (L.mach (M + 1) g) i s₀))

theorem TwinC.base {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState} (h : L.TwinC M g s s₀) :
    L.TwinBaseC M g s s₀ := by
  cases M with
  | zero => exact h
  | succ M => exact h.1

theorem TwinBase.twinBaseC {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState}
    (h : L.TwinBase M g s s₀) : L.TwinBaseC M g s s₀ := fun i hi =>
  let ⟨h1, h2⟩ := h i hi
  ⟨h1, fun hn => let ⟨a, b, c, d⟩ := h2 hn; ⟨a, b, c, fun h _ => d h⟩⟩

/-- **`Twin` gives `TwinC`** (it compares more slot bytes). -/
theorem Twin.twinC : ∀ {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState},
    L.Twin M g s s₀ → L.TwinC M g s s₀
  | 0, _, _, _, h => TwinBase.twinBaseC L h
  | _ + 1, _, _, _, ⟨h1, h2⟩ => ⟨TwinBase.twinBaseC L h1,
      fun i hi h hc => Twin.twinC (h2 i hi h hc)⟩

/-- **Every run is its own twin.** -/
theorem twinC_refl (M : Nat) (g : Clif.Function) (s : Arm.ArmState) : L.TwinC M g s s :=
  Twin.twinC L (L.twin_refl M g s)

/-- **No return of the twin before the first return.** -/
theorem noRetAt_twinC {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState}
    (h : L.TwinBaseC M g s s₀) {N : Nat}
    (hN : ∀ j < N, ¬ L.RetAt g s₀ (runX (L.mach M g) j s₀)) :
    ∀ j < N, ¬ L.RetAt g s (runX (L.mach M g) j s) := by
  intro j
  refine Nat.strongRecOn j ?_
  intro j ih hj hr
  exact hN j hj ((h j fun k hk => ih k hk (by omega)).1.1 hr)

/-- **The table of a run prefix carries over to its twin** (slot bytes at the calls). -/
theorem tabUpTo_twinC : ∀ (M : Nat) (g : Clif.Function) (s s₀ : Arm.ArmState)
    (b : Nat → Nat → BitVec 8) (k N e : Nat), L.TwinC M g s s₀ →
    (∀ j < N, ¬ L.RetAt g s (runX (L.mach M g) j s)) →
    L.TabUpTo M g s b k N e → L.TabUpTo M g s₀ b k N e
  | 0, g, s, s₀, b, k, N, e, htw, hN, ⟨he, hcl⟩ => by
    refine ⟨he, fun i hi h hc => ?_⟩
    obtain ⟨-, hb⟩ := htw i fun j hj => hN j (by omega)
    obtain ⟨-, -, hct, -⟩ := hb (hN i hi)
    exact hcl i hi h ((hct h).2 hc)
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
      fun i hi => (htw i fun j hj => hN j (by omega)).2 (hN i hi)
    have hcb : ∀ i ≤ N, callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i =
        callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s₀ i := fun i hi =>
      callsBefore_twin _ _ _ fun j hj => (hb j (by omega)).1
    refine ⟨E, by rw [← hcb N (Nat.le_refl _)]; exact he, fun i hi hcp => ?_⟩
    obtain ⟨hpc, hsp, hct, hsl⟩ := hb i hi
    obtain ⟨h0, h1⟩ := hcl i hi (hpc ▸ hcp)
    rw [← hcb i (Nat.le_of_lt hi)]
    refine ⟨fun hn => h0 fun h hc => hn h ((hct h).1 hc), fun h hc => ?_⟩
    have hc' := (hct h).2 hc
    obtain ⟨hslot, hle, N', hret, hmin, htab⟩ := h1 h hc'
    have htw' := hnest i (fun j hj => hN j (by omega)) h hc'
    have htb := TwinC.base L htw'
    have hpre : ∀ j < N', ¬ L.RetAt h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
        (runX (L.mach M h) j (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))) :=
      fun j hj hr => hmin j hj ((L.retAt_enterAt_iff).1 hr)
    refine ⟨fun h1 a ha => ?_, hle, N', ?_, fun N'' hN'' hr => ?_, ?_⟩
    · rw [← hsp] at ha
      rw [hslot h1 a ha]
      exact probeMem_congr hsp (hsl h hc' a ha)
    · exact (L.retAt_enterAt_iff).1 ((htb N' hpre).1.1 ((L.retAt_enterAt_iff).2 hret))
    · have hpre'' : ∀ j < N'', ¬ L.RetAt h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
          (runX (L.mach M h) j (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))) :=
        fun j hj => hpre j (by omega)
      exact hpre N'' hN'' ((htb N'' hpre'').1.2 ((L.retAt_enterAt_iff).2 hr))
    · exact tabUpTo_twinC M h _ _ b _ N' _ htw' hpre htab

/-- **The table of a run carries over to its twin** (slot bytes at the calls). -/
theorem tableOf_twinC {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState} {ini : Clif.SlotInit}
    (htw : L.TwinC M g s s₀) (ht : L.TableOf M g s ini) : L.TableOf M g s₀ ini := by
  intro N hN
  have hN' := L.noRetAt_twinC (TwinC.base L htw) hN
  obtain ⟨e, he⟩ := ht N hN'
  exact ⟨e, L.tabUpTo_twinC M g s s₀ _ _ N e htw hN' he⟩

/-- **The determinism step at a call, as twin runs with the slot bytes at the calls**
(`CallTwin` concluding `TwinC`). -/
def CallTwinC (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
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
      L.TwinC (M - 1) h (enterAt (L.A h) t) (enterAt (L.A h) (L.canon h uses w))

theorem CallTwin.callTwinC {M : Nat} (hd : L.CallTwin κ M) : L.CallTwinC κ M :=
  fun n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini hmr hargs hsav hpl
    hslotb hinit hrun t ht hmsk hrgn =>
    Twin.twinC L (hd n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini hmr
      hargs hsav hpl hslotb hinit hrun t ht hmsk hrgn)

/-- **`DetTabPRBG` from the determinism step with the slot bytes at the calls**, for any table
predicate carried along `TwinC`. -/
theorem detTabPRBG_ofC (T : Nat → Clif.Function → Arm.ArmState → Clif.SlotInit → Prop)
    (hT : ∀ M h s s₀ ini, L.TwinC M h s s₀ → T M h s ini → T M h s₀ ini) {M : Nat}
    (hd : L.CallTwinC κ M) : L.DetTabPRBG T κ M :=
  fun n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini hmr hargs hsav hpl
    hslotb hinit hrun t ht hmsk hrgn htab =>
    hT _ _ _ _ _ (hd n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini hmr
      hargs hsav hpl hslotb hinit hrun t ht hmsk hrgn) htab

/-- **`DetTabPRB` from `CallTwinC`** (`detTabPRBG_ofC` at `TableOf`, `tableOf_twinC`). -/
theorem detTabPRB_ofC {M : Nat} (hd : L.CallTwinC κ M) : L.DetTabPRB κ M :=
  L.detTabPRBG_ofC L.TableOf (fun _ _ _ _ _ htw ht => L.tableOf_twinC htw ht) hd

/-- **Twin runs (slot bytes at the calls) are symmetric, one level.** -/
theorem TwinBaseC.symm {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState}
    (h : L.TwinBaseC M g s s₀) : L.TwinBaseC M g s₀ s := by
  intro i hi
  have hi' := L.noRetAt_twinC h hi
  obtain ⟨h1, h2⟩ := h i hi'
  refine ⟨h1.symm, fun hn => ?_⟩
  obtain ⟨a, b, c, d⟩ := h2 (fun hr => hn (h1.1 hr))
  exact ⟨a.symm, b.symm, fun h => (c h).symm,
    fun h hc x hx => (d h ((c h).2 hc) x (b ▸ hx)).symm⟩

/-- **Twin runs (slot bytes at the calls) are symmetric.** -/
theorem TwinC.symm : ∀ {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState},
    L.TwinC M g s s₀ → L.TwinC M g s₀ s
  | 0, _, _, _, h => TwinBaseC.symm L h
  | _ + 1, _, _, _, ⟨h1, h2⟩ => ⟨TwinBaseC.symm L h1, fun i hi h hc => by
      have hi' := L.noRetAt_twinC h1 hi
      have hn : ¬ L.RetAt _ _ _ := hi' i (Nat.lt_succ_self i)
      have hct := ((h1 i fun j hj => hi' j (by omega)).2 hn).2.2.1 h
      exact TwinC.symm (h2 i hi' h (hct.2 hc))⟩

/-- **`DetTabPRBGr` from `CallTwinC`** (`TwinC.symm`). -/
theorem detTabPRBGr_ofC (T : Nat → Clif.Function → Arm.ArmState → Clif.SlotInit → Prop)
    (hT : ∀ M h s s₀ ini, L.TwinC M h s s₀ → T M h s ini → T M h s₀ ini) {M : Nat}
    (hd : L.CallTwinC κ M) : L.DetTabPRBGr T κ M :=
  fun n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini hmr hargs hsav hpl
    hslotb hinit hrun t ht hmsk hrgn htab =>
    hT _ _ _ _ _ (TwinC.symm L (hd n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs
      rvals cm' ini hmr hargs hsav hpl hslotb hinit hrun t ht hmsk hrgn)) htab

/-- **Twin runs up to step `n`, slot bytes at the calls.** -/
def TwinNC (M : Nat) (g : Clif.Function) (s s₀ : Arm.ArmState) (n : Nat) : Prop :=
  (∀ i < n, Arm.r .PC (runX (L.mach M g) i s) = Arm.r .PC (runX (L.mach M g) i s₀) ∧
    spv (runX (L.mach M g) i s) = spv (runX (L.mach M g) i s₀) ∧
    (∀ h, L.CallsTo g (runX (L.mach M g) i s) h ↔ L.CallsTo g (runX (L.mach M g) i s₀) h) ∧
    ∀ h, L.CallsTo g (runX (L.mach M g) i s) h → ∀ a, L.SlotByte h (spv (runX (L.mach M g) i s)) a →
      (runX (L.mach M g) i s).mem (BitVec.ofNat 64 a) =
        (runX (L.mach M g) i s₀).mem (BitVec.ofNat 64 a)) ∧
  ∀ M', M = M' + 1 → ∀ i < n, ∀ h, L.CallsTo g (runX (L.mach M g) i s) h →
    L.TwinC M' h (enterAt (L.A h) (runX (L.mach M g) i s))
      (enterAt (L.A h) (runX (L.mach M g) i s₀))

theorem TwinN.twinNC {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState} {n : Nat}
    (h : L.TwinN M g s s₀ n) : L.TwinNC M g s s₀ n :=
  ⟨fun i hi => let ⟨a, b, c, d⟩ := h.1 i hi; ⟨a, b, c, fun h _ => d h⟩,
    fun M' hM i hi h' hc => Twin.twinC L (h.2 M' hM i hi h' hc)⟩

theorem twinNC_refl (M : Nat) (g : Clif.Function) (s : Arm.ArmState) (n : Nat) :
    L.TwinNC M g s s n :=
  TwinN.twinNC L (L.twinN_refl M g s n)

/-- **The table of a run prefix carries over to its twin up to the prefix's end** (slot bytes at
the calls). -/
theorem tabUpTo_twinNC {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState}
    {b : Nat → Nat → BitVec 8} {k N e : Nat} (htw : L.TwinNC M g s s₀ N)
    (ht : L.TabUpTo M g s b k N e) : L.TabUpTo M g s₀ b k N e := by
  obtain ⟨hb, hnest⟩ := htw
  cases M with
  | zero =>
    obtain ⟨he, hcl⟩ := ht
    exact ⟨he, fun i hi h hc => hcl i hi h (((hb i hi).2.2.1 h).2 hc)⟩
  | succ M =>
    obtain ⟨E, he, hcl⟩ := ht
    have hcb : ∀ i ≤ N, callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i =
        callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s₀ i := fun i hi =>
      callsBefore_twin _ _ _ fun j hj => (hb j (by omega)).1
    refine ⟨E, by rw [← hcb N (Nat.le_refl _)]; exact he, fun i hi hcp => ?_⟩
    obtain ⟨hpc, hsp, hct, hsl⟩ := hb i hi
    obtain ⟨h0, h1⟩ := hcl i hi (hpc ▸ hcp)
    rw [← hcb i (Nat.le_of_lt hi)]
    refine ⟨fun hn => h0 fun h hc => hn h ((hct h).1 hc), fun h hc => ?_⟩
    have hc' := (hct h).2 hc
    obtain ⟨hslot, hle, N', hret, hmin, htab⟩ := h1 h hc'
    have htw' := hnest M rfl i hi h hc'
    have htb := TwinC.base L htw'
    have hpre : ∀ j < N', ¬ L.RetAt h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
        (runX (L.mach M h) j (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))) :=
      fun j hj hr => hmin j hj ((L.retAt_enterAt_iff).1 hr)
    refine ⟨fun h1 a ha => ?_, hle, N', ?_, fun N'' hN'' hr => ?_, ?_⟩
    · rw [← hsp] at ha
      rw [hslot h1 a ha]
      exact probeMem_congr hsp (hsl h hc' a ha)
    · exact (L.retAt_enterAt_iff).1 ((htb N' hpre).1.1 ((L.retAt_enterAt_iff).2 hret))
    · have hpre'' : ∀ j < N'', ¬ L.RetAt h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
          (runX (L.mach M h) j (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))) :=
        fun j hj => hpre j (by omega)
      exact hpre N'' hN'' ((htb N'' hpre'').1.2 ((L.retAt_enterAt_iff).2 hr))
    · exact L.tabUpTo_twinC M h _ _ b _ N' _ htw' hpre htab

/-- **The determinism step of `DetPRB` with the slot bytes at the calls** (`DetRunPRB`
concluding `TwinNC`). -/
def DetRunPRBC (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (ini : Clif.SlotInit) (G₀ : BitVec 64 → Prop) (ra₀ : BitVec 64)
    (s₀ : Arm.ArmState) (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState)
    (n₀ : Nat),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G₀ ra₀ s₀ w₀ (prophOf (L.mach M g) (L.A g).fa (L.A g).base s₀)
      (prophStOf (L.mach M g) (L.A g).fa (L.A g).base s₀) →
    ActRet ra₀ F G₀ us outs wf s₀ (runX (L.mach M g) n₀ s₀) →
    PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s₀ n₀ →
    ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
      RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g (spv w₀) cs.frame.slots cs.mem w₀' →
      SameWorld (fun a => F a ∨ D a) w₀ w₀' →
      (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip vals → regVal w₀' r = regVal w₀ r) →
      (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip vals → ∀ k < v.ty.bytes,
        w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
          w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
      ∀ G ra s, L.MachEntry κ M g F G ra s w₀' →
        EntryAgree (frameDrop (L.A g).af + κ M g) s s₀ →
        ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n₀ s) ∧
          PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n₀ ∧
          L.TwinNC M g s₀ s n₀

theorem DetRunPRB.toC {M : Nat} (hd : L.DetRunPRB κ M) : L.DetRunPRBC κ M :=
  fun g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ hWE hME₀ hret₀ hpt₀ D w₀' hrel hsw hreg hstk
    G ra s hME hag =>
    let ⟨hret, hpt, htw⟩ := hd g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ hWE hME₀ hret₀ hpt₀ D
      w₀' hrel hsw hreg hstk G ra s hME hag
    ⟨hret, hpt, TwinN.twinNC L htw⟩

/-- **`DetPRBG` from `DetRunPRBC`**, for any prefix-table predicate carried along `TwinNC`. -/
theorem detPRBG_ofC (T : Nat → Clif.Function → Arm.ArmState → Clif.SlotInit → Prop)
    (U : Nat → Clif.Function → Arm.ArmState → (Nat → Nat → BitVec 8) → Nat → Nat → Nat → Prop)
    (hU : ∀ M g s s₀ b k N e, L.TwinNC M g s s₀ N → U M g s b k N e → U M g s₀ b k N e)
    {M : Nat} (hd : L.DetRunPRBC κ M) : L.DetPRBG T U κ M :=
  fun g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ e hWE hME₀ _ hret₀ hpt₀ htab D w₀' hrel hsw
    hreg hstk G ra s hME hag =>
    let ⟨hret, hpt, htw⟩ := hd g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ hWE hME₀ hret₀ hpt₀ D
      w₀' hrel hsw hreg hstk G ra s hME hag
    ⟨n₀, hret, hpt, hU _ _ _ _ _ _ _ _ htw htab⟩

/-- **`DetPRB` from `DetRunPRBC`** (`detPRBG_ofC` at `TabUpTo`, `tabUpTo_twinNC`). -/
theorem detPRB_ofC {M : Nat} (hd : L.DetRunPRBC κ M) : L.DetPRB κ M :=
  L.detPRBG_ofC L.TableOf L.TabUpTo (fun _ _ _ _ _ _ _ _ htw ht => L.tabUpTo_twinNC htw ht) hd

end LinkSys

end E2E
