import FV.E2E.LinkArmTwin

/-!
# `DetPRB` from the determinism step, generic over the table predicates
(SEM1 #537, `docs/plans/uninit.md` §5.9, item (4): `detPRB_of`)

`DetPRB` asks, for an actual entry `s` agreeing with a canonical `ThmPRB` entry `s₀`, the
canonical outcome (`ActRet`, `PostTrace`) and the canonical table count (`TabUpTo`) on the run from
`s`. The first part is the determinism of the run; the table count only reads the run's shape up
to the return, which the two runs share. Split accordingly:

* `TwinN M g s s₀ n`: before step `n` the two runs agree on the pc, `sp`, the program calls and
  their slot bytes, and the callee runs at those calls are twins (`Twin`, one level down);
  `tabUpTo_twinN` (`TabUpTo` up to `n` carries over);
* `DetRunPRB κ M`: `DetPRB` without the table premises and with the conclusion "the actual run
  returns at the canonical index `n₀` with the canonical outcome, and the two runs are twins up to
  `n₀`" (the determinism step, to be given by the machine lock, `backend_twoRunLERW`);
* `DetPRBG T U` (`DetPRB` for a run-table predicate `T` and prefix-table predicate `U`;
  `DetPRB = DetPRBG TableOf TabUpTo`, `detPRB_iff`), **`detPRBG_of`** (any `U` carried along
  `TwinN`), **`detPRB_of`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **Twin runs up to step `n`** (module doc). -/
def TwinN (M : Nat) (g : Clif.Function) (s s₀ : Arm.ArmState) (n : Nat) : Prop :=
  (∀ i < n, Arm.r .PC (runX (L.mach M g) i s) = Arm.r .PC (runX (L.mach M g) i s₀) ∧
    spv (runX (L.mach M g) i s) = spv (runX (L.mach M g) i s₀) ∧
    (∀ h, L.CallsTo g (runX (L.mach M g) i s) h ↔ L.CallsTo g (runX (L.mach M g) i s₀) h) ∧
    ∀ h a, L.SlotByte h (spv (runX (L.mach M g) i s)) a →
      (runX (L.mach M g) i s).mem (BitVec.ofNat 64 a) =
        (runX (L.mach M g) i s₀).mem (BitVec.ofNat 64 a)) ∧
  ∀ M', M = M' + 1 → ∀ i < n, ∀ h, L.CallsTo g (runX (L.mach M g) i s) h →
    L.Twin M' h (enterAt (L.A h) (runX (L.mach M g) i s))
      (enterAt (L.A h) (runX (L.mach M g) i s₀))

/-- **The table of a run prefix carries over to its twin up to the prefix's end.** -/
theorem tabUpTo_twinN {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState}
    {b : Nat → Nat → BitVec 8} {k N e : Nat} (htw : L.TwinN M g s s₀ N)
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
    · exact L.tabUpTo_twin M h _ _ b _ N' _ htw' hpre htab

/-- **Every run prefix is its own twin.** -/
theorem twinN_refl (M : Nat) (g : Clif.Function) (s : Arm.ArmState) (n : Nat) :
    L.TwinN M g s s n :=
  ⟨fun _ _ => ⟨rfl, rfl, fun _ => Iff.rfl, fun _ _ _ => rfl⟩,
    fun M' _ _ _ h _ => L.twin_refl M' h _⟩

/-- **The determinism step of `DetPRB`** (module doc): from a canonical entry's outcome, the
actual entry's run returns at the same index with that outcome, and the two runs are twins up to
there. No table premise. -/
def DetRunPRB (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
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
          L.TwinN M g s₀ s n₀

/-- **`DetPRB` for a run-table predicate `T` and a prefix-table predicate `U`** (`DetPRB` is the
instance at `TableOf`, `TabUpTo`). -/
def DetPRBG (T : Nat → Clif.Function → Arm.ArmState → Clif.SlotInit → Prop)
    (U : Nat → Clif.Function → Arm.ArmState → (Nat → Nat → BitVec 8) → Nat → Nat → Nat → Prop)
    (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (ini : Clif.SlotInit) (G₀ : BitVec 64 → Prop) (ra₀ : BitVec 64)
    (s₀ : Arm.ArmState) (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState)
    (n₀ e : Nat),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G₀ ra₀ s₀ w₀ (prophOf (L.mach M g) (L.A g).fa (L.A g).base s₀)
      (prophStOf (L.mach M g) (L.A g).fa (L.A g).base s₀) →
    T M g s₀ ini →
    ActRet ra₀ F G₀ us outs wf s₀ (runX (L.mach M g) n₀ s₀) →
    PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s₀ n₀ →
    U M g s₀ ini.bytes ini.next n₀ e →
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
        ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n s) ∧
          PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n ∧
          U M g s ini.bytes ini.next n e

theorem detPRB_iff {M : Nat} : L.DetPRB κ M ↔ L.DetPRBG L.TableOf L.TabUpTo κ M := Iff.rfl

/-- **`DetPRBG` from the determinism step**, for any prefix-table predicate carried along
`TwinN`. -/
theorem detPRBG_of (T : Nat → Clif.Function → Arm.ArmState → Clif.SlotInit → Prop)
    (U : Nat → Clif.Function → Arm.ArmState → (Nat → Nat → BitVec 8) → Nat → Nat → Nat → Prop)
    (hU : ∀ M g s s₀ b k N e, L.TwinN M g s s₀ N → U M g s b k N e → U M g s₀ b k N e)
    {M : Nat} (hd : L.DetRunPRB κ M) : L.DetPRBG T U κ M :=
  fun g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ e hWE hME₀ _ hret₀ hpt₀ htab D w₀' hrel hsw
    hreg hstk G ra s hME hag =>
    let ⟨hret, hpt, htw⟩ := hd g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ hWE hME₀ hret₀ hpt₀ D
      w₀' hrel hsw hreg hstk G ra s hME hag
    ⟨n₀, hret, hpt, hU _ _ _ _ _ _ _ _ htw htab⟩

/-- **`DetPRB` from the determinism step** (`detPRBG_of` at `TabUpTo`, `tabUpTo_twinN`). -/
theorem detPRB_of {M : Nat} (hd : L.DetRunPRB κ M) : L.DetPRB κ M :=
  L.detPRBG_of L.TableOf L.TabUpTo (fun _ _ _ _ _ _ _ _ htw ht => L.tabUpTo_twinN htw ht) hd

end LinkSys

end E2E
