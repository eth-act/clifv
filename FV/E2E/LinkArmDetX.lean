import FV.E2E.LinkArmProphDetR
import FV.E2E.LinkArmStepLine

/-!
# The determinism clause up to the return address (SEM1 #537, item (3), issue #689)

`ThmPDER`'s determinism clause compares a run from `s` (return address `ra`) with one from `s₀`
(`ra₀`); `EntryAgree` leaves `x30` free and the consumer (`progCallPR`) pairs the canonical entry
(`ra₀ = raStar`) with the actual call (`ra = pc + 4`). Two of its conclusions then fail when
`ra ≠ ra₀`: the register prophecy covers `x30` (the body keeps the entry `x30` up to its first
call), and `RetAgree` covers the frame record's saved-LR word. `ThmPDERX` states the clause
without them, and with them when the two entries' `x30` agree (a caller's nested calls from one
call site):

* `ProphRegOkUpToX`: `ProphRegOkUpTo` on the masked registers but the pc and `x30`;
* `RetAgreeX`: `RetAgree` but for the saved-LR word, the 8 bytes below `c`;
* `ThmPDERX`, `ThmPDER.thmPDERX`, `ThmPDERX.thmPR`, `Thm.thmPDERX_of_not_needNI`;
* the transfers along an `x30` lock-step (`StEqOutX (Zs i)` at every index):
  `prophStep_of_stEqOutX`, `prophOkUpTo_of_lockstepX`, `prophRegOkUpToX_of_lockstepX`,
  `prophRegOkUpTo_of_lockstepX` (equal `x30` at the call states), `retAgreeX_of_ret`,
  `retAgree_of_ret`.
-/

namespace E2E

open Backend Backend.Proof

/-- **The register prophecy up to step `n`, but `x30`.** -/
def ProphRegOkUpToX (c : BitVec 64) (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm)
    (base : BitVec 64) (s : Arm.ArmState) (R : Nat → Arm.ArmState) (n : Nat) : Prop :=
  ∀ i ≤ n, CallPc fa base (Arm.r .PC (runX Mm i s)) → spv (runX Mm i s) = c →
    ∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 →
      Arm.r f (runX Mm i s) = Arm.r f (R (callsBefore Mm fa base s i))

theorem ProphRegOkUpTo.toX {c : BitVec 64} {Mm : Arm.ArmState → Arm.ArmState} {fa : FnAsm}
    {base : BitVec 64} {s : Arm.ArmState} {R : Nat → Arm.ArmState} {n : Nat}
    (h : ProphRegOkUpTo c Mm fa base s R n) : ProphRegOkUpToX c Mm fa base s R n :=
  fun i hi hc hsp f hf hpc _ => h i hi hc hsp f hf hpc

/-- **Two states at the return agree for the caller, but for the saved return address**: every
register but `x30` and the pc, and the `K` bytes below `c` but the 8 just below `c` (the frame
record's saved-LR word). -/
def RetAgreeX (K : Nat) (c : BitVec 64) (u u₀ : Arm.ArmState) : Prop :=
  (∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f u = Arm.r f u₀) ∧
    ∀ a, StackBelow K c a → ¬ StackBelow 8 c a → u.mem a = u₀.mem a

theorem RetAgree.toX {K : Nat} {c : BitVec 64} {u u₀ : Arm.ArmState} (h : RetAgree K c u u₀) :
    RetAgreeX K c u u₀ :=
  ⟨h.1, fun a ha _ => h.2 a ha⟩

theorem gpr31_ne_gpr30 : (Arm.StateField.GPR 31#5) ≠ .GPR 30#5 := by decide

theorem pc_ne_gpr30 : (Arm.StateField.PC) ≠ .GPR 30#5 := by decide

/-! ## Transfers along an `x30` lock-step -/

/-- **`StEqOutX` gives the prophecy's agreement** when `Z` avoids the call region at the call
states. -/
theorem prophStep_of_stEqOutX {K : Nat} {c : BitVec 64} {fa : FnAsm} {base : BitVec 64}
    {Z : BitVec 64 → Prop} {u u' : Arm.ArmState} (h : StEqOutX Z u u')
    (hZ : CallPc fa base (Arm.r .PC u) → spv u = c → ∀ a, StackBelow K c a → ¬ Z a) :
    ProphStep K c fa base u u' :=
  ⟨h.1 .PC pc_ne_gpr30, fun _ => h.1 _ gpr31_ne_gpr30, fun hc hsp a ha => h.2.2 a (hZ hc hsp a ha)⟩

/-- **The byte prophecy along an `x30` lock-step**: a prophecy (up to `n`) of the run from `s₀` is
one of the run from `s` when the runs are `StEqOutX (Zs i)` at every index up to `n` and `Zs i`
avoids the call region at the call states. -/
theorem prophOkUpTo_of_lockstepX {K : Nat} {c : BitVec 64} {Mm : Arm.ArmState → Arm.ArmState}
    {fa : FnAsm} {base : BitVec 64} {s s₀ : Arm.ArmState} {P : Nat → BitVec 64 → BitVec 8}
    {n : Nat} {Zs : Nat → BitVec 64 → Prop}
    (hst : ∀ i ≤ n, StEqOutX (Zs i) (runX Mm i s₀) (runX Mm i s))
    (hZ : ∀ i ≤ n, CallPc fa base (Arm.r .PC (runX Mm i s₀)) → spv (runX Mm i s₀) = c →
      ∀ a, StackBelow K c a → ¬ Zs i a)
    (h : ProphOkUpTo K c Mm fa base s₀ P n) : ProphOkUpTo K c Mm fa base s P n :=
  prophOkUpTo_congr (fun i hi => prophStep_of_stEqOutX (hst i hi) (hZ i hi)) h

/-- **The register prophecy (but `x30`) along an `x30` lock-step.** -/
theorem prophRegOkUpToX_of_lockstepX {c : BitVec 64} {Mm : Arm.ArmState → Arm.ArmState}
    {fa : FnAsm} {base : BitVec 64} {s s₀ : Arm.ArmState} {R : Nat → Arm.ArmState} {n : Nat}
    {Zs : Nat → BitVec 64 → Prop}
    (hst : ∀ i ≤ n, StEqOutX (Zs i) (runX Mm i s₀) (runX Mm i s))
    (h : ProphRegOkUpToX c Mm fa base s₀ R n) : ProphRegOkUpToX c Mm fa base s R n := by
  intro i hi hc hsp f hf hpc h30
  have hs := hst i hi
  have hpcE : Arm.r .PC (runX Mm i s₀) = Arm.r .PC (runX Mm i s) := hs.1 .PC pc_ne_gpr30
  have hc₀ : CallPc fa base (Arm.r .PC (runX Mm i s₀)) := hpcE ▸ hc
  have hsp₀ : spv (runX Mm i s₀) = c := (hs.1 _ gpr31_ne_gpr30).trans hsp
  rw [← hs.1 f h30, h i hi hc₀ hsp₀ f hf hpc h30,
    callsBefore_congr (fun j hj => (hst j (by omega)).1 .PC pc_ne_gpr30) i (Nat.le_refl i)]

/-- **The register prophecy along an `x30` lock-step whose call states agree on `x30`.** -/
theorem prophRegOkUpTo_of_lockstepX {c : BitVec 64} {Mm : Arm.ArmState → Arm.ArmState}
    {fa : FnAsm} {base : BitVec 64} {s s₀ : Arm.ArmState} {R : Nat → Arm.ArmState} {n : Nat}
    {Zs : Nat → BitVec 64 → Prop}
    (hst : ∀ i ≤ n, StEqOutX (Zs i) (runX Mm i s₀) (runX Mm i s))
    (h30 : ∀ i ≤ n, CallPc fa base (Arm.r .PC (runX Mm i s₀)) → spv (runX Mm i s₀) = c →
      Arm.r (.GPR 30#5) (runX Mm i s₀) = Arm.r (.GPR 30#5) (runX Mm i s))
    (h : ProphRegOkUpTo c Mm fa base s₀ R n) : ProphRegOkUpTo c Mm fa base s R n := by
  intro i hi hc hsp f hf hpc
  have hs := hst i hi
  have hpcE : Arm.r .PC (runX Mm i s₀) = Arm.r .PC (runX Mm i s) := hs.1 .PC pc_ne_gpr30
  have hc₀ : CallPc fa base (Arm.r .PC (runX Mm i s₀)) := hpcE ▸ hc
  have hsp₀ : spv (runX Mm i s₀) = c := (hs.1 _ gpr31_ne_gpr30).trans hsp
  have hfE : Arm.r f (runX Mm i s₀) = Arm.r f (runX Mm i s) := by
    by_cases hf30 : f = .GPR 30#5
    · subst hf30; exact h30 i hi hc₀ hsp₀
    · exact hs.1 f hf30
  rw [← hfE, h i hi hc₀ hsp₀ f hf hpc,
    callsBefore_congr (fun j hj => (hst j (by omega)).1 .PC pc_ne_gpr30) i (Nat.le_refl i)]

/-- **`RetAgreeX` at the return**: from `StEqOutX Z` at the `ret` line, with `Z` meeting the
`K` bytes below `c` at most in the saved-LR word. -/
theorem retAgreeX_of_ret {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64} {Z : BitVec 64 → Prop} {s t : Arm.ArmState}
    {K : Nat} {c : BitVec 64} (ht : OnLine fa fb lm base t .ret) (h : StEqOutX Z s t)
    (hZ : ∀ a, StackBelow K c a → ¬ StackBelow 8 c a → ¬ Z a) :
    RetAgreeX K c (ArmStepX X H fa s) (ArmStepX X H fa t) := by
  obtain ⟨hr, -, hm⟩ := retAgree_line_ret (X := X) (H := H) ht h
  exact ⟨hr, fun a ha h8 => hm a (hZ a ha h8)⟩

/-- **`RetAgree` at the return**: from `StEqOutX Z` at the `ret` line, with `Z` avoiding the `K`
bytes below `c`. -/
theorem retAgree_of_ret {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64} {Z : BitVec 64 → Prop} {s t : Arm.ArmState}
    {K : Nat} {c : BitVec 64} (ht : OnLine fa fb lm base t .ret) (h : StEqOutX Z s t)
    (hZ : ∀ a, StackBelow K c a → ¬ Z a) :
    RetAgree K c (ArmStepX X H fa s) (ArmStepX X H fa t) := by
  obtain ⟨hr, -, hm⟩ := retAgree_line_ret (X := X) (H := H) ht h
  exact ⟨hr, fun a ha => hm a (hZ a ha)⟩

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **`ThmPDER` with the determinism clause up to the return address** (module doc): without
`x30` in the register prophecy and the saved-LR word in the return agreement, and with both
when the two entries agree on `x30`. -/
def ThmPDERX (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
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
              ProphRegOkUpToX (spv w₀) (L.mach M g) (L.A g).fa (L.A g).base s R n ∧
              RetAgreeX (frameDrop (L.A g).af + κ M g) (spv s) (runX (L.mach M g) n s)
                (runX (L.mach M g) n s₀) ∧
              (Arm.r (.GPR 30#5) s = Arm.r (.GPR 30#5) s₀ →
                ProphRegOkUpTo (spv w₀) (L.mach M g) (L.A g).fa (L.A g).base s R n ∧
                RetAgree (frameDrop (L.A g).af + κ M g) (spv s) (runX (L.mach M g) n s)
                  (runX (L.mach M g) n s₀))))

/-- **`ThmPDER` gives `ThmPDERX`** (its clause is the stronger one). -/
theorem ThmPDER.thmPDERX {M : Nat} (h : L.ThmPDER κ M) : L.ThmPDERX κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' P R hWE hrun
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, hnn, hni⟩ :=
    h g hg F vals cs w₀ fuel rvals cm' P R hWE hrun
  refine ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, hnn,
    fun hN D w₀' hrel hsw hreg hstk => ⟨(hni hN D w₀' hrel hsw hreg hstk).1, ?_⟩⟩
  intro G₀ ra₀ s₀ hME₀ G ra s hME hag
  obtain ⟨n, hret, htr, hP, hR, hRA⟩ := (hni hN D w₀' hrel hsw hreg hstk).2 G₀ ra₀ s₀ hME₀ G ra s hME hag
  exact ⟨n, hret, htr, hP, hR.toX, hRA.toX, fun _ => ⟨hR, hRA⟩⟩

/-- **`ThmPDERX` gives `ThmPR`.** -/
theorem ThmPDERX.thmPR {M : Nat} (h : L.ThmPDERX κ M) : L.ThmPR κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' P R hWE hrun
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, -, hni⟩ :=
    h g hg F vals cs w₀ fuel rvals cm' P R hWE hrun
  exact ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall,
    fun hN D w₀' hrel hsw hreg hstk G ra s hME =>
      (hni hN D w₀' hrel hsw hreg hstk).1 G ra s hME⟩

/-- **Without non-interference today's statement gives `ThmPDERX`.** -/
theorem Thm.thmPDERX_of_not_needNI {M : Nat} (hN : ¬ L.NeedNI) (h : L.Thm κ M) :
    L.ThmPDERX κ M :=
  ThmPDER.thmPDERX L (Thm.thmPDER_of_not_needNI L hN h)

end LinkSys

end E2E
