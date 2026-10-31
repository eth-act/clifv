import FV.E2E.LinkArmProphDetE
import FV.E2E.RegLevelCorrectPR

/-!
# The linking statement with byte and register prophecies (SEM1 step 2v, `docs/plans/uninit.md` §5.8 (4))

With the register prophecy the activation's VCode run uses `XPRI … P R`, so its outcome is a
function of the byte prophecy `P` *and* the register prophecy `R` of the activation's machine run.
`ThmP`/`ThmPDE` choose it per `P` only; here per `(P, R)`:

* `MachEntryPR`: `MachEntryP … P` and the register prophecy `R` of the run (`ProphRegOkM` at the
  body `sp`);
* `ProphRegOkUpTo`: `ProphRegOkM` up to step `n`;
* `ThmPR κ M`: `ThmP` with the outcome per `(P, R)` and `MachEntryPR`;
* `ThmPDER κ M`: `ThmPDE` likewise; its determinism clause also transfers `R` (up to the return);
* `Thm.thmPR`, `ThmPDER.thmPR`, `Thm.thmPDER_of_not_needNI`.

`ThmPR → ThmP` does not follow (activations with one `P` may have different `R`); the top-level
statement instantiates `(P, R)` with the actual run's prophecies (`prophOf`, `prophStOf`).
-/

namespace E2E

open Backend Backend.Proof

/-- **The register prophecy of a run up to step `n`.** -/
def ProphRegOkUpTo (c : BitVec 64) (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm)
    (base : BitVec 64) (s : Arm.ArmState) (R : Nat → Arm.ArmState) (n : Nat) : Prop :=
  ∀ i ≤ n, CallPc fa base (Arm.r .PC (runX Mm i s)) → spv (runX Mm i s) = c →
    ∀ f, Masked f → f ≠ .PC → Arm.r f (runX Mm i s) = Arm.r f (R (callsBefore Mm fa base s i))

theorem ProphRegOkM.upTo {c : BitVec 64} {Mm : Arm.ArmState → Arm.ArmState} {fa : FnAsm}
    {base : BitVec 64} {s : Arm.ArmState} {R : Nat → Arm.ArmState}
    (h : ProphRegOkM c Mm fa base s R) (n : Nat) : ProphRegOkUpTo c Mm fa base s R n :=
  fun i _ => h i

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The machine side of an activation with both prophecies.** -/
structure MachEntryPR (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F G : BitVec 64 → Prop) (ra : BitVec 64) (s w₀ : Arm.ArmState)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) : Prop where
  entryP : L.MachEntryP κ M g F G ra s w₀ P
  reg : ProphRegOkM (spv w₀) (L.mach M g) (L.A g).fa (L.A g).base s R

/-- **The linking statement at depth `M` with both prophecies**: `ThmP` with the outcome chosen
per byte and register prophecy. -/
def ThmPR (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat)
    (rvals : List Clif.Val) (cm' : Clif.Mem) (P : Nat → BitVec 64 → BitVec 8)
    (R : Nat → Arm.ArmState),
    L.WorldEntry κ M g F vals cs w₀ →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
      RetPins rvals us ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A g).vc.RetsSite us ∧
      (∀ G ra s, L.MachEntryPR κ M g F G ra s w₀ P R →
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
        ∀ G ra s, L.MachEntryPR κ M g F G ra s w₀' P R →
          ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n s) ∧
            PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n)

/-- **The linking statement at depth `M` with both prophecies and entry-level determinism**:
`ThmPDE` with the outcome per `(P, R)`; the determinism clause also carries `R` to the run from
the agreeing entry, up to its return. -/
def ThmPDER (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat)
    (rvals : List Clif.Val) (cm' : Clif.Mem) (P : Nat → BitVec 64 → BitVec 8)
    (R : Nat → Arm.ArmState),
    L.WorldEntry κ M g F vals cs w₀ →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
      RetPins rvals us ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A g).vc.RetsSite us ∧
      (∀ G ra s, L.MachEntryPR κ M g F G ra s w₀ P R →
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
        (∀ G ra s, L.MachEntryPR κ M g F G ra s w₀' P R →
          ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n s) ∧
            PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n) ∧
        (∀ G₀ ra₀ s₀, L.MachEntryPR κ M g F G₀ ra₀ s₀ w₀ P R →
          ∀ G ra s, L.MachEntry κ M g F G ra s w₀' →
            EntryAgree (frameDrop (L.A g).af + κ M g) s s₀ →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n s) ∧
              PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n ∧
              ProphOkUpTo (κ M g) (spv w₀) (L.mach M g) (L.A g).fa (L.A g).base s P n ∧
              ProphRegOkUpTo (spv w₀) (L.mach M g) (L.A g).fa (L.A g).base s R n ∧
              RetAgree (frameDrop (L.A g).af + κ M g) (spv s) (runX (L.mach M g) n s)
                (runX (L.mach M g) n s₀)))

/-- **Today's linking statement is the case of one outcome for every pair of prophecies.** -/
theorem Thm.thmPR {M : Nat} (h : L.Thm κ M) : L.ThmPR κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' _ _ hWE hrun
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, hni⟩ :=
    h g hg F vals cs w₀ fuel rvals cm' hWE hrun
  exact ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, fun G ra s hME => hall G ra s hME.entryP.entry,
    fun hN D w₀' hrel hsw hreg hstk G ra s hME =>
      hni hN D w₀' hrel hsw hreg hstk G ra s hME.entryP.entry⟩

/-- **`ThmPDER` gives `ThmPR`.** -/
theorem ThmPDER.thmPR {M : Nat} (h : L.ThmPDER κ M) : L.ThmPR κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' P R hWE hrun
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, -, hni⟩ :=
    h g hg F vals cs w₀ fuel rvals cm' P R hWE hrun
  exact ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall,
    fun hN D w₀' hrel hsw hreg hstk G ra s hME =>
      (hni hN D w₀' hrel hsw hreg hstk).1 G ra s hME⟩

/-- **Without non-interference today's statement gives `ThmPDER`.** -/
theorem Thm.thmPDER_of_not_needNI {M : Nat} (hN : ¬ L.NeedNI) (h : L.Thm κ M) :
    L.ThmPDER κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' _ _ hWE hrun
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, -⟩ :=
    h g hg F vals cs w₀ fuel rvals cm' hWE hrun
  exact ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs,
    fun G ra s hME => hall G ra s hME.entryP.entry, fun _ => hall, fun hN' => absurd hN' hN⟩

end LinkSys

end E2E
