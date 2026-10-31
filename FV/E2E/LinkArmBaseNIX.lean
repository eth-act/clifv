import FV.E2E.LinkArmBaseDetX
import FV.E2E.LinkArmDetX

/-!
# Base hooks that do not observe the activations' exteriors; `ThmPDERX` with equal entry `x29`
(SEM1 #537, `docs/plans/uninit.md` §5.9, issues #704 and #705)

**#704.** The machine lock of two activations (`backend_twoRunLER`) needs, at a base call, that the
base hook keeps states equal but for `x30` and the lock set. The lock set contains bytes of the
activation's exterior `F` above `sp` (the callers' frames, which differ between the canonical and
the actual entry), so `HookDetX` (differences below `sp` or saved-LR bytes) does not apply. Decided
(conservative, generated code unchanged): a new trusted premise beside `HookDetX`, the
machine-level analogue of `XNI`:

* `HookNIX Hb BD F`: from two states equal but for `x30` and bytes `Z ⊆ F`, a base call (`BD d`) and
  a TLS hook give states equal but for `x30` and `Z`: the extern observes neither return addresses
  nor bytes outside the world (stack frames of program activations, the code), as `XNI` states for
  the CLIF semantics of the externs;
* `LinkSys.OkDNX`: `OkDX` plus `HookNIX L.Hb L.BaseDest F` for the exterior `F` of every machine
  entry, under `NeedNI`; `OkDNX.okDX`, `Ok.okDNX_of_not_needNI`, `hookNIX_id`.

**#705.** `ThmPDERX`'s non-interference clause relates the actual entry's run to the canonical
one's with `RetAgreeX`, which compares `x29`; the entries' `x29` are unconstrained, and the prologue
saves `x29` in the frame record, the epilogue reloads it. `ThmPDERX29` is `ThmPDERX` with the clause
also assuming equal entry `x29` (the caller's lock gives it at every program call: all registers
but `x30` agree); `ThmPDERX.thmPDERX29` (the old clause is stronger).
-/

namespace E2E

open Backend Backend.Proof

/-- **The base hooks do not observe `x30` nor the bytes of `F`** (module doc, #704): from two
states equal but for `x30` and bytes `Z` inside `F`, a call of a destination `BD d` and a TLS hook
give states equal but for `x30` and `Z`. -/
def HookNIX (Hb : ArmHooks) (BD : Option String → Prop) (F : BitVec 64 → Prop) : Prop :=
  (∀ d, BD d → ∀ (Z : BitVec 64 → Prop) (s t : Arm.ArmState), StEqOutX Z s t →
      (∀ a, Z a → F a) → StEqOutX Z (Hb.call d s) (Hb.call d t)) ∧
    (∀ n r (Z : BitVec 64 → Prop) (s t : Arm.ArmState), StEqOutX Z s t →
      (∀ a, Z a → F a) → StEqOutX Z (Hb.tls n r s) (Hb.tls n r t))

/-- The hooks that change nothing do not observe anything. -/
theorem hookNIX_id (BD : Option String → Prop) (F : BitVec 64 → Prop) :
    HookNIX ⟨fun _ s => s, fun _ _ s => s⟩ BD F :=
  ⟨fun _ _ _ _ _ h _ => h, fun _ _ _ _ _ h _ => h⟩

/-- `HookNIX` on a smaller exterior. -/
theorem HookNIX.mono {Hb : ArmHooks} {BD : Option String → Prop} {F F' : BitVec 64 → Prop}
    (h : HookNIX Hb BD F) (hF : ∀ a, F' a → F a) : HookNIX Hb BD F' :=
  ⟨fun d hd Z s t hs hZ => h.1 d hd Z s t hs fun a ha => hF a (hZ a ha),
    fun n r Z s t hs hZ => h.2 n r Z s t hs fun a ha => hF a (hZ a ha)⟩

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The premises of the linked program with base hooks that observe neither return addresses
nor the activations' exteriors** (#704): `OkDX`, and under `NeedNI`, `HookNIX` at the exterior `F`
of every machine entry. Trusted (a property of the externs' machine code, as `XNI` is of their
CLIF semantics); `docs/contracts` and `docs/plans/uninit.md` §5.9. -/
structure OkDNX : Prop extends L.OkDX where
  baseNIX : L.NeedNI → ∀ (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F G : BitVec 64 → Prop) (ra : BitVec 64) (s w₀ : Arm.ArmState),
    L.MachEntry κ M g F G ra s w₀ → HookNIX L.Hb L.BaseDest F

theorem OkDNX.okDX {L : LinkSys} (h : L.OkDNX) : L.OkDX := h.toOkDX

/-- **Without non-interference, `OkDNX` is `Ok`.** -/
theorem Ok.okDNX_of_not_needNI {L : LinkSys} (hL : L.Ok) (hN : ¬ L.NeedNI) : L.OkDNX :=
  { hL.okDX_of_not_needNI hN with baseNIX := fun h => absurd h hN }

/-- **`ThmPDERX` with equal entry `x29`** (#705): the non-interference clause also assumes that the
canonical and the actual entry agree on `x29`. -/
def ThmPDERX29 (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
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
            Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) s₀ →
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

/-- **`ThmPDERX` gives `ThmPDERX29`** (its clause assumes less). -/
theorem ThmPDERX.thmPDERX29 {M : Nat} (h : L.ThmPDERX κ M) : L.ThmPDERX29 κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' P R hWE hrun
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, hnn, hni⟩ :=
    h g hg F vals cs w₀ fuel rvals cm' P R hWE hrun
  exact ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, hnn,
    fun hN D w₀' hrel hsw hreg hstk => ⟨(hni hN D w₀' hrel hsw hreg hstk).1,
      fun G₀ ra₀ s₀ hME₀ G ra s hME hag _ =>
        (hni hN D w₀' hrel hsw hreg hstk).2 G₀ ra₀ s₀ hME₀ G ra s hME hag⟩⟩

/-- **`ThmPDERX29` gives `ThmPR`.** -/
theorem ThmPDERX29.thmPR {M : Nat} (h : L.ThmPDERX29 κ M) : L.ThmPR κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' P R hWE hrun
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, -, hni⟩ :=
    h g hg F vals cs w₀ fuel rvals cm' P R hWE hrun
  exact ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall,
    fun hN D w₀' hrel hsw hreg hstk G ra s hME =>
      (hni hN D w₀' hrel hsw hreg hstk).1 G ra s hME⟩

/-- **Without non-interference today's statement gives `ThmPDERX29`.** -/
theorem Thm.thmPDERX29_of_not_needNI {M : Nat} (hN : ¬ L.NeedNI) (h : L.Thm κ M) :
    L.ThmPDERX29 κ M :=
  ThmPDERX.thmPDERX29 L (Thm.thmPDERX_of_not_needNI L hN h)

end LinkSys

end E2E
