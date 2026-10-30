import FV.E2E.LinkArmDetPRBR
import FV.E2E.LinkArmTwinC

/-!
# The determinism step for returning CLIF runs (SEM1 #537, #719)

`DetRunPRBC` (`LinkArmTwinC.lean`) has `DetPRB`'s defect (#719): no premise that the canonical
activation's CLIF run returns, so it is false for programs that read memory the CLIF run
does not validate. **`DetRunPRBCR`**: `DetRunPRBC` with `DetPRBR`'s extra premises (the canonical
table, the returning CLIF run, both return addresses linked calls', equal frame pointers);
`DetRunPRBC.toR`, **`detPRBR_ofC`** (`DetPRBR` from `DetRunPRBCR`, `tabUpTo_twinNC`),
**`detPRBGR_ofC`** (any prefix-table predicate carried along `TwinNC`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The determinism step for returning CLIF runs** (module doc). -/
def DetRunPRBCR (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (ini : Clif.SlotInit) (G₀ : BitVec 64 → Prop) (ra₀ : BitVec 64)
    (s₀ : Arm.ArmState) (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState)
    (n₀ fuel : Nat) (rvals : List Clif.Val) (cm' : Clif.Mem),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G₀ ra₀ s₀ w₀ (prophOf (L.mach M g) (L.A g).fa (L.A g).base s₀)
      (prophStOf (L.mach M g) (L.A g).fa (L.A g).base s₀) →
    L.TableOf M g s₀ ini →
    ActRet ra₀ F G₀ us outs wf s₀ (runX (L.mach M g) n₀ s₀) →
    PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s₀ n₀ →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    RaOk (L.A g) (ra₀ - 4) →
    ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState), (∀ a, D a → F a) →
      RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g (spv w₀) cs.frame.slots cs.mem w₀' →
      SameWorld (fun a => F a ∨ D a) w₀ w₀' →
      (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip vals → regVal w₀' r = regVal w₀ r) →
      (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip vals → ∀ k < v.ty.bytes,
        w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
          w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
      ∀ G ra s, L.MachEntry κ M g F G ra s w₀' →
        EntryAgree (frameDrop (L.A g).af + κ M g) s s₀ →
        RaOk (L.A g) (ra - 4) →
        Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) s₀ →
        ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n₀ s) ∧
          PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n₀ ∧
          L.TwinNC M g s₀ s n₀

/-- Every `DetRunPRBC` is a `DetRunPRBCR`. -/
theorem DetRunPRBC.toR {M : Nat} (h : L.DetRunPRBC κ M) : L.DetRunPRBCR κ M :=
  fun g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ _ _ _ hWE hME₀ _ hret₀ hpt₀ _ _ D w₀' _ hrel
    hsw hreg hstk G ra s hME hag _ _ =>
    h g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ hWE hME₀ hret₀ hpt₀ D w₀' hrel hsw hreg hstk
      G ra s hME hag

/-- **`DetPRBR`'s shape for any prefix-table predicate, from `DetRunPRBCR`.** -/
theorem detPRBGR_ofC
    (U : Nat → Clif.Function → Arm.ArmState → (Nat → Nat → BitVec 8) → Nat → Nat → Nat → Prop)
    (hU : ∀ M g s s₀ b k N e, L.TwinNC M g s s₀ N → U M g s b k N e → U M g s₀ b k N e)
    {M : Nat} (hd : L.DetRunPRBCR κ M) :
    ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
      (w₀ : Arm.ArmState) (ini : Clif.SlotInit) (G₀ : BitVec 64 → Prop) (ra₀ : BitVec 64)
      (s₀ : Arm.ArmState) (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState)
      (n₀ e fuel : Nat) (rvals : List Clif.Val) (cm' : Clif.Mem),
      L.WorldEntryB κ M g F vals cs w₀ ini →
      L.MachEntryPR κ M g F G₀ ra₀ s₀ w₀ (prophOf (L.mach M g) (L.A g).fa (L.A g).base s₀)
        (prophStOf (L.mach M g) (L.A g).fa (L.A g).base s₀) →
      L.TableOf M g s₀ ini →
      ActRet ra₀ F G₀ us outs wf s₀ (runX (L.mach M g) n₀ s₀) →
      PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s₀ n₀ →
      U M g s₀ ini.bytes ini.next n₀ e →
      Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
      RaOk (L.A g) (ra₀ - 4) →
      ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState), (∀ a, D a → F a) →
        RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
          g (spv w₀) cs.frame.slots cs.mem w₀' →
        SameWorld (fun a => F a ∨ D a) w₀ w₀' →
        (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip vals → regVal w₀' r = regVal w₀ r) →
        (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip vals → ∀ k < v.ty.bytes,
          w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
            w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
        ∀ G ra s, L.MachEntry κ M g F G ra s w₀' →
          EntryAgree (frameDrop (L.A g).af + κ M g) s s₀ →
          RaOk (L.A g) (ra - 4) →
          Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) s₀ →
          ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n s) ∧
            PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n ∧
            U M g s ini.bytes ini.next n e :=
  fun g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ e fuel rvals cm' hWE hME₀ htab hret₀ hpt₀ hU₀
    hrun hra₀ D w₀' hD hrel hsw hreg hstk G ra s hME hag hra hx29 =>
    let ⟨hret, hpt, htw⟩ := hd g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ fuel rvals cm' hWE
      hME₀ htab hret₀ hpt₀ hrun hra₀ D w₀' hD hrel hsw hreg hstk G ra s hME hag hra hx29
    ⟨n₀, hret, hpt, hU _ _ _ _ _ _ _ _ htw hU₀⟩

/-- **`DetPRBR` from `DetRunPRBCR`** (`tabUpTo_twinNC`). -/
theorem detPRBR_ofC {M : Nat} (hd : L.DetRunPRBCR κ M) : L.DetPRBR κ M :=
  L.detPRBGR_ofC L.TabUpTo (fun _ _ _ _ _ _ _ _ htw ht => L.tabUpTo_twinNC htw ht) hd

/-- **The determinism step for returning CLIF runs at result registers of a `rets` site**
(#732): `DetRunPRBCR` with the canonical outcome's `us` those of a `rets` instruction of `g`'s
VCode. `DetRunPRBCR` itself is false: for `us` naming `x30` the second return holds its own return
address there. -/
def DetRunPRBCRU (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (ini : Clif.SlotInit) (G₀ : BitVec 64 → Prop) (ra₀ : BitVec 64)
    (s₀ : Arm.ArmState) (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState)
    (n₀ fuel : Nat) (rvals : List Clif.Val) (cm' : Clif.Mem),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G₀ ra₀ s₀ w₀ (prophOf (L.mach M g) (L.A g).fa (L.A g).base s₀)
      (prophStOf (L.mach M g) (L.A g).fa (L.A g).base s₀) →
    L.TableOf M g s₀ ini →
    ActRet ra₀ F G₀ us outs wf s₀ (runX (L.mach M g) n₀ s₀) →
    (L.A g).vc.RetsSite us →
    PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s₀ n₀ →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    RaOk (L.A g) (ra₀ - 4) →
    ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState), (∀ a, D a → F a) →
      RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g (spv w₀) cs.frame.slots cs.mem w₀' →
      SameWorld (fun a => F a ∨ D a) w₀ w₀' →
      (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip vals → regVal w₀' r = regVal w₀ r) →
      (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip vals → ∀ k < v.ty.bytes,
        w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
          w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
      ∀ G ra s, L.MachEntry κ M g F G ra s w₀' →
        EntryAgree (frameDrop (L.A g).af + κ M g) s s₀ →
        RaOk (L.A g) (ra - 4) →
        Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) s₀ →
        ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n₀ s) ∧
          PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n₀ ∧
          L.TwinNC M g s₀ s n₀

/-- Every `DetRunPRBCR` is a `DetRunPRBCRU`. -/
theorem DetRunPRBCR.toU {M : Nat} (h : L.DetRunPRBCR κ M) : L.DetRunPRBCRU κ M :=
  fun g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ fuel rvals cm' hWE hME₀ htab hret₀ _ hpt₀ =>
    h g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ fuel rvals cm' hWE hME₀ htab hret₀ hpt₀

/-- **`DetPRBRU` from `DetRunPRBCRU`** (`tabUpTo_twinNC`, #732). -/
theorem detPRBRU_ofC {M : Nat} (hd : L.DetRunPRBCRU κ M) : L.DetPRBRU κ M :=
  fun g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ e fuel rvals cm' hWE hME₀ htab hret₀ hrs hpt₀
    htab₀ hrun hra₀ D w₀' hD hrel hsw hreg hstk G ra s hME hag hra hx29 =>
    let ⟨hret, hpt, htw⟩ := hd g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ fuel rvals cm' hWE
      hME₀ htab hret₀ hrs hpt₀ hrun hra₀ D w₀' hD hrel hsw hreg hstk G ra s hME hag hra hx29
    ⟨n₀, hret, hpt, L.tabUpTo_twinNC htw htab₀⟩

end LinkSys

end E2E
