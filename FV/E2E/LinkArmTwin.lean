import FV.E2E.LinkArmCallTab
import FV.E2E.LinkArmDetTabPRB

/-!
# Twin runs and the table transfer, generic over the table predicate
(SEM1 #537, `docs/plans/uninit.md` §5.9, item (4): `detTabPRB_of`)

`DetTabPRB` moves the callee table from the actual call state `t` to the canonical one
`canon h uses w`. The table (`TabUpTo`/`TableOf`, and `TableOfE` of #700) reads only the
machine-visible shape of the run: where it returns (`RetAt`), the pcs before that (`CallPc`,
`callsBefore`), the calls of program functions (`CallsTo`), the `sp` and the slot bytes at those
calls, and recursively the callee runs. Two runs agreeing on all of that are **twins**:

* `TwinBase M g s s₀`: up to the first return of the run from `s` both runs return at the same
  indices, and before it they agree on the pc, `sp`, the program calls and the slot bytes at them;
* `Twin M g s s₀`: `TwinBase`, and (depth `M + 1`) at every program call before the return the
  two callee runs are twins one level down.

The machine lock of two activations (`backend_twoRunLERW`) gives these facts (same pcs and
registers but `x30`; the slot bytes are below `sp`, in the dead stack the lock keeps equal; the
two returns at the same index); that is the determinism step (`CallTwin`). Here the table side:

* `callsBefore_twin`, **`tabUpTo_twin`**, `noRetAt_twin`, **`tableOf_twin`**;
* `DetTabPRBG T` (`DetTabPRB` for any table predicate `T`; `DetTabPRB = DetTabPRBG TableOf`,
  `detTabPRB_iff`), `CallTwin κ M` (the determinism step, call-shaped with `DetTabPRB`'s premises),
  **`detTabPRBG_of`** (any `T` transferred along twins, e.g. `TableOfE`), **`detTabPRB_of`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **One level of twin runs** (module doc): before the first return of the run from `s`, both
runs return at the same indices and agree on the pc, `sp`, the program calls and their slot
bytes. -/
def TwinBase (M : Nat) (g : Clif.Function) (s s₀ : Arm.ArmState) : Prop :=
  ∀ i, (∀ j < i, ¬ L.RetAt g s (runX (L.mach M g) j s)) →
    (L.RetAt g s (runX (L.mach M g) i s) ↔ L.RetAt g s₀ (runX (L.mach M g) i s₀)) ∧
    (¬ L.RetAt g s (runX (L.mach M g) i s) →
      Arm.r .PC (runX (L.mach M g) i s) = Arm.r .PC (runX (L.mach M g) i s₀) ∧
      spv (runX (L.mach M g) i s) = spv (runX (L.mach M g) i s₀) ∧
      (∀ h, L.CallsTo g (runX (L.mach M g) i s) h ↔ L.CallsTo g (runX (L.mach M g) i s₀) h) ∧
      ∀ h a, L.SlotByte h (spv (runX (L.mach M g) i s)) a →
        (runX (L.mach M g) i s).mem (BitVec.ofNat 64 a) =
          (runX (L.mach M g) i s₀).mem (BitVec.ofNat 64 a))

/-- **Twin runs** (module doc): `TwinBase`, and at every program call before the return the two
callee runs (one level down) are twins. -/
def Twin : Nat → Clif.Function → Arm.ArmState → Arm.ArmState → Prop
  | 0, g, s, s₀ => L.TwinBase 0 g s s₀
  | M + 1, g, s, s₀ => L.TwinBase (M + 1) g s s₀ ∧
      ∀ i, (∀ j < i + 1, ¬ L.RetAt g s (runX (L.mach (M + 1) g) j s)) → ∀ h,
        L.CallsTo g (runX (L.mach (M + 1) g) i s) h →
        Twin M h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
          (enterAt (L.A h) (runX (L.mach (M + 1) g) i s₀))

theorem Twin.base {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState} (h : L.Twin M g s s₀) :
    L.TwinBase M g s s₀ := by
  cases M with
  | zero => exact h
  | succ M => exact h.1

/-- The call count of two runs with the same pcs. -/
theorem callsBefore_twin (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm) (base : BitVec 64)
    {s s₀ : Arm.ArmState} {N : Nat}
    (h : ∀ i < N, Arm.r .PC (runX Mm i s) = Arm.r .PC (runX Mm i s₀)) :
    callsBefore Mm fa base s N = callsBefore Mm fa base s₀ N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [callsBefore]
    rw [ih fun i hi => h i (by omega), h N (by omega)]

/-- **No return of the twin before the first return.** -/
theorem noRetAt_twin {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState}
    (h : L.TwinBase M g s s₀) {N : Nat}
    (hN : ∀ j < N, ¬ L.RetAt g s₀ (runX (L.mach M g) j s₀)) :
    ∀ j < N, ¬ L.RetAt g s (runX (L.mach M g) j s) := by
  intro j
  refine Nat.strongRecOn j ?_
  intro j ih hj hr
  exact hN j hj ((h j fun k hk => ih k hk (by omega)).1.1 hr)

/-- **The table of a run prefix carries over to its twin.** -/
theorem tabUpTo_twin : ∀ (M : Nat) (g : Clif.Function) (s s₀ : Arm.ArmState)
    (b : Nat → Nat → BitVec 8) (k N e : Nat), L.Twin M g s s₀ →
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
        ∀ h a, L.SlotByte h (spv (runX (L.mach (M + 1) g) i s)) a →
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
    have htb := Twin.base L htw'
    have hpre : ∀ j < N', ¬ L.RetAt h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
        (runX (L.mach M h) j (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))) :=
      fun j hj hr => hmin j hj ((L.retAt_enterAt_iff).1 hr)
    refine ⟨fun h1 a ha => ?_, hle, N', ?_, fun N'' hN'' hr => ?_, ?_⟩
    · rw [← hsp] at ha
      rw [hslot h1 a ha]
      exact probeMem_congr hsp (hsl h a ha)
    · exact (L.retAt_enterAt_iff).1 ((htb N' hpre).1.1 ((L.retAt_enterAt_iff).2 hret))
    · have hpre'' : ∀ j < N'', ¬ L.RetAt h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
          (runX (L.mach M h) j (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))) :=
        fun j hj => hpre j (by omega)
      exact hpre N'' hN'' ((htb N'' hpre'').1.2 ((L.retAt_enterAt_iff).2 hr))
    · exact tabUpTo_twin M h _ _ b _ N' _ htw' hpre htab

/-- **The table of a run carries over to its twin.** -/
theorem tableOf_twin {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState} {ini : Clif.SlotInit}
    (htw : L.Twin M g s s₀) (ht : L.TableOf M g s ini) : L.TableOf M g s₀ ini := by
  intro N hN
  have hN' := L.noRetAt_twin (Twin.base L htw) hN
  obtain ⟨e, he⟩ := ht N hN'
  exact ⟨e, L.tabUpTo_twin M g s s₀ _ _ N e htw hN' he⟩

/-- **`DetTabPRB` for any table predicate `T`** (`DetTabPRB` is the instance at `TableOf`; the
#700 continuation's `DetTabPRBE` the one at `TableOfE`). -/
def DetTabPRBG (T : Nat → Clif.Function → Arm.ArmState → Clif.SlotInit → Prop)
    (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
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
      T (M - 1) h (enterAt (L.A h) t) (calleeIni h ini) →
      T (M - 1) h (enterAt (L.A h) (L.canon h uses w)) (calleeIni h ini)

theorem detTabPRB_iff {M : Nat} : L.DetTabPRB κ M ↔ L.DetTabPRBG L.TableOf κ M := Iff.rfl

/-- **The determinism step at a call, as twin runs** (call-shaped with `DetTabPRB`'s premises):
the callee runs from the actual call state `t` and from the canonical one are twins. -/
def CallTwin (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
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
      L.Twin (M - 1) h (enterAt (L.A h) t) (enterAt (L.A h) (L.canon h uses w))

/-- **`DetTabPRBG` from the determinism step**, for any table predicate carried along twins. -/
theorem detTabPRBG_of (T : Nat → Clif.Function → Arm.ArmState → Clif.SlotInit → Prop)
    (hT : ∀ M h s s₀ ini, L.Twin M h s s₀ → T M h s ini → T M h s₀ ini) {M : Nat}
    (hd : L.CallTwin κ M) : L.DetTabPRBG T κ M :=
  fun n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini hmr hargs hsav hpl
    hslotb hinit hrun t ht hmsk hrgn htab =>
    hT _ _ _ _ _ (hd n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini hmr
      hargs hsav hpl hslotb hinit hrun t ht hmsk hrgn) htab

/-- **`DetTabPRB` from the determinism step** (`detTabPRBG_of` at `TableOf`, `tableOf_twin`). -/
theorem detTabPRB_of {M : Nat} (hd : L.CallTwin κ M) : L.DetTabPRB κ M :=
  L.detTabPRBG_of L.TableOf (fun _ _ _ _ _ htw ht => L.tableOf_twin htw ht) hd

/-- **Twin runs are symmetric, one level.** -/
theorem TwinBase.symm {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState}
    (h : L.TwinBase M g s s₀) : L.TwinBase M g s₀ s := by
  intro i hi
  have hi' := L.noRetAt_twin h hi
  obtain ⟨h1, h2⟩ := h i hi'
  refine ⟨h1.symm, fun hn => ?_⟩
  obtain ⟨a, b, c, d⟩ := h2 (fun hr => hn (h1.1 hr))
  exact ⟨a.symm, b.symm, fun h => (c h).symm, fun h x hx => (d h x (b ▸ hx)).symm⟩

/-- **Twin runs are symmetric.** -/
theorem Twin.symm : ∀ {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState},
    L.Twin M g s s₀ → L.Twin M g s₀ s
  | 0, _, _, _, h => TwinBase.symm L h
  | _ + 1, _, _, _, ⟨h1, h2⟩ => ⟨TwinBase.symm L h1, fun i hi h hc => by
      have hi' := L.noRetAt_twin h1 hi
      have hn : ¬ L.RetAt _ _ _ := hi' i (Nat.lt_succ_self i)
      have hct := ((h1 i fun j hj => hi' j (by omega)).2 hn).2.2.1 h
      exact Twin.symm (h2 i hi' h (hct.2 hc))⟩

/-- **`DetTabPRBG` in reverse**: the table of the canonical callee run is the actual one's. -/
def DetTabPRBGr (T : Nat → Clif.Function → Arm.ArmState → Clif.SlotInit → Prop)
    (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
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
      T (M - 1) h (enterAt (L.A h) (L.canon h uses w)) (calleeIni h ini) →
      T (M - 1) h (enterAt (L.A h) t) (calleeIni h ini)

/-- **`DetTabPRBGr` from the determinism step** (`Twin.symm`), for any table predicate carried
along twins. -/
theorem detTabPRBGr_of (T : Nat → Clif.Function → Arm.ArmState → Clif.SlotInit → Prop)
    (hT : ∀ M h s s₀ ini, L.Twin M h s s₀ → T M h s ini → T M h s₀ ini) {M : Nat}
    (hd : L.CallTwin κ M) : L.DetTabPRBGr T κ M :=
  fun n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals cm' ini hmr hargs hsav hpl
    hslotb hinit hrun t ht hmsk hrgn htab =>
    hT _ _ _ _ _ (Twin.symm L (hd n h hpf hcal F himgF uses w herr hal hroom hdead vals cm cs rvals
      cm' ini hmr hargs hsav hpl hslotb hinit hrun t ht hmsk hrgn)) htab

/-- **Every run is its own twin** (the twin relation is not empty). -/
theorem twin_refl : ∀ (M : Nat) (g : Clif.Function) (s : Arm.ArmState), L.Twin M g s s
  | 0, _, _ => fun _ _ => ⟨Iff.rfl, fun _ => ⟨rfl, rfl, fun _ => Iff.rfl, fun _ _ _ => rfl⟩⟩
  | M + 1, _, _ => ⟨fun _ _ => ⟨Iff.rfl, fun _ => ⟨rfl, rfl, fun _ => Iff.rfl, fun _ _ _ => rfl⟩⟩,
      fun _ _ h _ => twin_refl M h _⟩

end LinkSys

end E2E
