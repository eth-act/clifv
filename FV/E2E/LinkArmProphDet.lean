import FV.E2E.LinkArmProphThm

/-!
# Prophecy determinism: transfer of a prophecy along a lock-step run (SEM1 #537, step 2m)

`docs/plans/uninit.md` §5.6–§5.7. `progCallP` picks the callee prophecy `P' := prophOf` of the
canonical callee run and needs it to be a prophecy of the run from every caller state of its
family. Two runs whose states agree, step by step, on the pc and, at the call states with
`sp = c`, on `sp` and on the `K` bytes below `c`, have the same calls and the same call
bytes, so a prophecy of one is a prophecy of the other:

* `runX_lockstep`: a relation kept by the steps relates the two runs at every index;
* `ProphStep K c fa base u u'`: the per-state agreement the prophecy reads;
* `callsBefore_congr`, `prophOkUpTo_congr`, `prophOk_congr`: the calls before a step and the
  prophecy (up to step `n`: `ProphOkUpTo`; of the whole run: `ProphOk`) transfer;
  `prophOkUpTo_prophOf`/`prophOk_prophOf_congr`: **the prophecy of the first run is one of the
  second** (`P' := prophOf` of the canonical run, carried to the family);
* `ThmPD`: `ThmP` whose non-interference clause takes `MachEntry` (no prophecy), with a
  determinism clause: from a body-entry world that also agrees on the masked registers (but
  `x30`, the pc) and on the bytes of the activation's frame and callee region (§5.7), the run has
  the prophecy `P` of the run from `w₀` up to its return; `ThmPD.thmP`, `Thm.thmPD_of_not_needNI`.
-/

namespace E2E

open Backend Backend.Proof

/-! ## Lock-step runs -/

/-- **Two runs in lock-step**: a relation that the steps keep (from the related states of the
runs) relates the runs at every index. -/
theorem runX_lockstep {Mm Mm' : Arm.ArmState → Arm.ArmState} {R : Arm.ArmState → Arm.ArmState → Prop}
    {s s' : Arm.ArmState} (h0 : R s s')
    (hstep : ∀ i, R (runX Mm i s) (runX Mm' i s') → R (Mm (runX Mm i s)) (Mm' (runX Mm' i s'))) :
    ∀ i, R (runX Mm i s) (runX Mm' i s')
  | 0 => h0
  | i + 1 => by
    rw [runX_add Mm i 1, runX_add Mm' i 1]
    exact hstep i (runX_lockstep h0 hstep i)

/-- **The agreement of two states that the prophecy reads**: the same pc; at a call state the
same `sp`, and with `sp = c` the same `K` bytes below `c`. -/
structure ProphStep (K : Nat) (c : BitVec 64) (fa : FnAsm) (base : BitVec 64)
    (u u' : Arm.ArmState) : Prop where
  pc : Arm.r .PC u = Arm.r .PC u'
  sp : CallPc fa base (Arm.r .PC u) → spv u = spv u'
  mem : CallPc fa base (Arm.r .PC u) → spv u = c → ∀ a, StackBelow K c a → u.mem a = u'.mem a

theorem ProphStep.symm {K : Nat} {c : BitVec 64} {fa : FnAsm} {base : BitVec 64}
    {u u' : Arm.ArmState} (h : ProphStep K c fa base u u') : ProphStep K c fa base u' u where
  pc := h.pc.symm
  sp hc := (h.sp (h.pc ▸ hc)).symm
  mem hc hsp a ha := (h.mem (h.pc ▸ hc) ((h.sp (h.pc ▸ hc)).trans hsp) a ha).symm

/-- **The prophecy of a run up to step `n`** (`ProphOk` at the states `i ≤ n`). -/
def ProphOkUpTo (K : Nat) (c : BitVec 64) (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm)
    (base : BitVec 64) (s : Arm.ArmState) (P : Nat → BitVec 64 → BitVec 8) (n : Nat) : Prop :=
  ∀ i ≤ n, CallPc fa base (Arm.r .PC (runX Mm i s)) → spv (runX Mm i s) = c →
    ∀ a, StackBelow K c a → (runX Mm i s).mem a = P (callsBefore Mm fa base s i) a

theorem ProphOk.upTo {K : Nat} {c : BitVec 64} {Mm : Arm.ArmState → Arm.ArmState} {fa : FnAsm}
    {base : BitVec 64} {s : Arm.ArmState} {P : Nat → BitVec 64 → BitVec 8}
    (h : ProphOk K c Mm fa base s P) (n : Nat) : ProphOkUpTo K c Mm fa base s P n :=
  fun i _ => h i

theorem prophOk_iff_upTo {K : Nat} {c : BitVec 64} {Mm : Arm.ArmState → Arm.ArmState} {fa : FnAsm}
    {base : BitVec 64} {s : Arm.ArmState} {P : Nat → BitVec 64 → BitVec 8} :
    ProphOk K c Mm fa base s P ↔ ∀ n, ProphOkUpTo K c Mm fa base s P n :=
  ⟨fun h n => h.upTo n, fun h i => h i i (Nat.le_refl i)⟩

/-- **Lock-step runs make the same calls**: with the same pc at every state before step `n`,
the calls before every step up to `n` agree. -/
theorem callsBefore_congr {Mm Mm' : Arm.ArmState → Arm.ArmState} {fa : FnAsm} {base : BitVec 64}
    {s s' : Arm.ArmState} {n : Nat}
    (hpc : ∀ i < n, Arm.r .PC (runX Mm i s) = Arm.r .PC (runX Mm' i s')) :
    ∀ i ≤ n, callsBefore Mm fa base s i = callsBefore Mm' fa base s' i
  | 0, _ => rfl
  | i + 1, hi => by
    simp only [callsBefore, callsBefore_congr hpc i (by omega)]
    rw [hpc i (by omega)]

/-- **A prophecy (up to step `n`) of a run is one of a lock-step run.** -/
theorem prophOkUpTo_congr {K : Nat} {c : BitVec 64} {Mm Mm' : Arm.ArmState → Arm.ArmState}
    {fa : FnAsm} {base : BitVec 64} {s s' : Arm.ArmState} {P : Nat → BitVec 64 → BitVec 8}
    {n : Nat} (hst : ∀ i ≤ n, ProphStep K c fa base (runX Mm i s) (runX Mm' i s'))
    (h : ProphOkUpTo K c Mm fa base s P n) : ProphOkUpTo K c Mm' fa base s' P n := by
  intro i hi hc' hsp' a ha
  have hs := hst i hi
  have hc : CallPc fa base (Arm.r .PC (runX Mm i s)) := hs.pc ▸ hc'
  have hsp : spv (runX Mm i s) = c := (hs.sp hc).trans hsp'
  rw [← hs.mem hc hsp a ha, h i hi hc hsp a ha,
    callsBefore_congr (fun j hj => (hst j (by omega)).pc) i (Nat.le_refl i)]

/-- **A prophecy of a run is one of a run in lock-step with it at every step.** -/
theorem prophOk_congr {K : Nat} {c : BitVec 64} {Mm Mm' : Arm.ArmState → Arm.ArmState}
    {fa : FnAsm} {base : BitVec 64} {s s' : Arm.ArmState} {P : Nat → BitVec 64 → BitVec 8}
    (hst : ∀ i, ProphStep K c fa base (runX Mm i s) (runX Mm' i s'))
    (h : ProphOk K c Mm fa base s P) : ProphOk K c Mm' fa base s' P :=
  prophOk_iff_upTo.mpr fun n => prophOkUpTo_congr (fun i _ => hst i) (h.upTo n)

/-- **The prophecy of a run carried to a lock-step run** (up to step `n`): `prophOf` of the
first run is a prophecy of the second. -/
theorem prophOkUpTo_prophOf {K : Nat} {c : BitVec 64} {Mm Mm' : Arm.ArmState → Arm.ArmState}
    {fa : FnAsm} {base : BitVec 64} {s s' : Arm.ArmState} {n : Nat}
    (hst : ∀ i ≤ n, ProphStep K c fa base (runX Mm i s) (runX Mm' i s')) :
    ProphOkUpTo K c Mm' fa base s' (prophOf Mm fa base s) n :=
  prophOkUpTo_congr hst ((prophOk_prophOf K c Mm fa base s).upTo n)

/-- **The prophecy of a run carried to a run in lock-step with it at every step.** -/
theorem prophOk_prophOf_congr {K : Nat} {c : BitVec 64} {Mm Mm' : Arm.ArmState → Arm.ArmState}
    {fa : FnAsm} {base : BitVec 64} {s s' : Arm.ArmState}
    (hst : ∀ i, ProphStep K c fa base (runX Mm i s) (runX Mm' i s')) :
    ProphOk K c Mm' fa base s' (prophOf Mm fa base s) :=
  prophOk_congr hst (prophOk_prophOf K c Mm fa base s)

/-- **Equal states step in lock-step** (the trivial instance: a deterministic machine from one
state). -/
theorem prophStep_refl (K : Nat) (c : BitVec 64) (fa : FnAsm) (base : BitVec 64) (u : Arm.ArmState) :
    ProphStep K c fa base u u :=
  ⟨rfl, fun _ => rfl, fun _ _ _ _ => rfl⟩

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-! ## The linking statement with prophecy determinism -/

/-- **The linking statement at depth `M` with prophecies and their determinism**: `ThmP`, its
non-interference clause for every `MachEntry` activation (no prophecy assumed), and the
determinism clause: an activation entered with a body-entry world `w₀'` as in the
non-interference clause that moreover agrees with `w₀` on the masked registers but `x30` and
the pc (callee-saved registers are saved into frames inside the callee region) and on the bytes
of the activation's frame and callee region (`StackBelow (frameDrop + κ M g)` below the entry
`sp`) has, up to its return, the prophecy `P` of every activation entered from `w₀` with the
prophecy `P`. -/
def ThmPD (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat)
    (rvals : List Clif.Val) (cm' : Clif.Mem) (P : Nat → BitVec 64 → BitVec 8),
    L.WorldEntry κ M g F vals cs w₀ →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
      RetPins rvals us ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A g).vc.RetsSite us ∧
      (∀ G ra s, L.MachEntryP κ M g F G ra s w₀ P →
        ∃ n, ActRet ra F G us outs wf s (runX (L.mach M g) n s) ∧
          PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n) ∧
      (L.NeedNI → ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
        RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
          g (spv w₀) cs.frame.slots cs.mem w₀' →
        SameWorld (fun a => F a ∨ D a) w₀ w₀' →
        (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip vals → regVal w₀' r = regVal w₀ r) →
        (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip vals → ∀ k < v.ty.bytes,
          w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
            w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
        (∀ G ra s, L.MachEntry κ M g F G ra s w₀' →
          ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n s) ∧
            PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n) ∧
        ((∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f w₀' = Arm.r f w₀) →
          (∀ a, StackBelow (frameDrop (L.A g).af + κ M g)
              (spv w₀ + BitVec.ofNat 64 (frameDrop (L.A g).af)) a → w₀'.mem a = w₀.mem a) →
          (∃ G₀ ra₀ s₀, L.MachEntryP κ M g F G₀ ra₀ s₀ w₀ P) →
          ∀ G ra s, L.MachEntry κ M g F G ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n s) ∧
              ProphOkUpTo (κ M g) (spv w₀) (L.mach M g) (L.A g).fa (L.A g).base s P n))

/-- **`ThmPD` gives `ThmP`.** -/
theorem ThmPD.thmP {M : Nat} (h : L.ThmPD κ M) : L.ThmP κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' P hWE hrun
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, hni⟩ :=
    h g hg F vals cs w₀ fuel rvals cm' P hWE hrun
  exact ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall,
    fun hN D w₀' hrel hsw hreg hstk G ra s hME =>
      (hni hN D w₀' hrel hsw hreg hstk).1 G ra s hME.entry⟩

/-- **Without non-interference today's statement gives `ThmPD`** (the determinism clause sits
under `NeedNI`). -/
theorem Thm.thmPD_of_not_needNI {M : Nat} (hN : ¬ L.NeedNI) (h : L.Thm κ M) : L.ThmPD κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' P hWE hrun
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, -⟩ :=
    h g hg F vals cs w₀ fuel rvals cm' hWE hrun
  exact ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, fun G ra s hME => hall G ra s hME.entry,
    fun hN' => absurd hN' hN⟩

end LinkSys

end E2E
