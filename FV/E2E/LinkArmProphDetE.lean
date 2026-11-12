import FV.E2E.LinkArmProphDet

/-!
# Prophecy determinism at the machine entry (SEM1 step 2p, `docs/plans/uninit.md` §5.8)

`ThmPD`'s determinism clause (step 2m) assumes the agreement on the masked registers and the
callee-region bytes of the two *body-entry worlds* `w₀`, `w₀'`. `MachEntry s w₀` relates the
machine entry `s` to `w₀` only outside `F` and on the unmasked registers (`BodyEntryW`), and the
callee region lies in `F`: two entries with the same `w₀` may hold different stale bytes there,
so their prophecies differ. The clause is therefore unprovable as soon as a callee calls before
overwriting its region. The agreement belongs to the machine entries:

* `EntryAgree K s s₀`: the masked registers but `x30`/pc, and the `K` bytes below `sp`;
* `ThmPDE κ M`: `ThmP`'s outcome and first clause; without `NeedNI` every `MachEntry` activation
  realises it (no prophecy: the outcome reads no stale bytes, `Thm.thmP`); with `NeedNI`, `ThmP`'s
  non-interference clause (with the prophecy `P`: `ThmPD`'s, for every `MachEntry`, fails for the
  same reason as its determinism clause) and the **entry-level determinism**: a `MachEntry` activation `s` from
  `w₀'` whose entry agrees with that of a `MachEntryP … P` activation `s₀` from `w₀`
  (`EntryAgree (frameDrop + κ M g)`) realises the outcome (with its trace) with the prophecy `P` up to its return,
  and at the return agrees with `s₀`'s run at the same step on every register but `x30`/pc and on
  the caller's region below the entry `sp` (what a caller's lock-step needs to continue past the
  call, §5.8 (2));
* `ThmPDE.thmP`, `Thm.thmPDE_of_not_needNI`.
-/

namespace E2E

open Backend Backend.Proof

/-- **Two machine entries agree where a prophecy can see them**: same masked registers but `x30`
and the pc, same `K` bytes below `sp` (`s`'s). -/
def EntryAgree (K : Nat) (s s₀ : Arm.ArmState) : Prop :=
  (∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f s = Arm.r f s₀) ∧
    ∀ a, StackBelow K (spv s) a → s.mem a = s₀.mem a

theorem EntryAgree.refl (K : Nat) (s : Arm.ArmState) : EntryAgree K s s :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => rfl⟩

/-- **Two states at the return agree for the caller**: every register but `x30` and the pc, and
the `K` bytes below `c`. -/
def RetAgree (K : Nat) (c : BitVec 64) (u u₀ : Arm.ArmState) : Prop :=
  (∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f u = Arm.r f u₀) ∧
    ∀ a, StackBelow K c a → u.mem a = u₀.mem a

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The linking statement at depth `M` with entry-level prophecy determinism** (module doc). -/
def ThmPDE (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
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
      (¬ L.NeedNI → ∀ G ra s, L.MachEntry κ M g F G ra s w₀ →
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
        (∀ G ra s, L.MachEntryP κ M g F G ra s w₀' P →
          ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n s) ∧
            PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n) ∧
        (∀ G₀ ra₀ s₀, L.MachEntryP κ M g F G₀ ra₀ s₀ w₀ P →
          ∀ G ra s, L.MachEntry κ M g F G ra s w₀' →
            EntryAgree (frameDrop (L.A g).af + κ M g) s s₀ →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n s) ∧
              PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n ∧
              ProphOkUpTo (κ M g) (spv w₀) (L.mach M g) (L.A g).fa (L.A g).base s P n ∧
              RetAgree (frameDrop (L.A g).af + κ M g) (spv s) (runX (L.mach M g) n s)
                (runX (L.mach M g) n s₀)))

/-- **`ThmPDE` gives `ThmP`.** -/
theorem ThmPDE.thmP {M : Nat} (h : L.ThmPDE κ M) : L.ThmP κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' P hWE hrun
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, -, hni⟩ :=
    h g hg F vals cs w₀ fuel rvals cm' P hWE hrun
  exact ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall,
    fun hN D w₀' hrel hsw hreg hstk G ra s hME =>
      (hni hN D w₀' hrel hsw hreg hstk).1 G ra s hME⟩

/-- **Without non-interference today's statement gives `ThmPDE`.** -/
theorem Thm.thmPDE_of_not_needNI {M : Nat} (hN : ¬ L.NeedNI) (h : L.Thm κ M) : L.ThmPDE κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' P hWE hrun
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, -⟩ :=
    h g hg F vals cs w₀ fuel rvals cm' hWE hrun
  exact ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, fun G ra s hME => hall G ra s hME.entry,
    fun _ => hall, fun hN' => absurd hN' hN⟩

end LinkSys

end E2E
