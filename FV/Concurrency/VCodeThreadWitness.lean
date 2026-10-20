import FV.Concurrency.VCodeThread
import FV.Concurrency.ArmThreadWitness

/-!
# Non-vacuity of the VCode event semantics (T2h, #311, layer 1)

* `stepEvs_ldaxr`: the precise footprint of the `ldaxr` of `ArmThread.Witness` is its read of 8
  bytes at `0x8000` (an `acqXR` event);
* `cEvs_ldar`: the `csem` footprint of `ldar` of the address `0x8000` (VCode `loadAcquire`) is its
  `acqR` read of 8 bytes there;
* `ldar_vtstep`: a one-block VCode thread (`ldar`, return) steps with the read of `5` at `0x8000`
  that the environment wrote, while the thread's own memory holds `0` (`cEvs_patch`: the footprint
  on the patched world).
-/

namespace Concurrency.VCodeThread.Witness

open Arm ArmFoot ArmThread ArmInstFoot Backend Backend.Proof

/-- The events of the `ldaxr` of `ArmThread.Witness`. -/
theorem stepEvs_ldaxr : (stepEvs (ArmThread.Witness.st 0x1000#64 0#64)).map (fun e => (e.k, e.addr, e.n)) =
    [(.acqXR, 0x8000#64, 8)] := by
  decide +kernel

/-- A world with x0 = 0: memory zero. -/
def w0 : ArmState := ArmState.default

def ctx0 : FnCtx := { k := 0, slotBase := 0 }

/-- `ldar` of the address in vreg 1 into vreg 0. -/
def iLdar : MInst := .loadAcquire (.int 64) (.vreg 0 .int) (.vreg 1 .int) {}

theorem cEvs_ldar :
    (cEvs (fun _ => False) ctx0 iLdar [ofX 0x8000#64] w0).map (fun e => (e.k, e.addr, e.n)) =
      [(.acqR, 0x8000#64, 8)] := by
  decide +kernel

/-- The environment wrote `5` at `0x8000`; the thread's own memory still holds `0`. -/
def ev5 : Ev := ⟨.acqR, 0x8000#64, 8, 5#64⟩

/-- The data of an event. -/
def evData (e : Ev) : AKind × BitVec 64 × Nat × Nat := (e.k, e.addr, e.n, e.val.toNat)

theorem ev_ext {e e' : Ev} (h : evData e = evData e') : e = e' := by
  obtain ⟨k, a, n, v⟩ := e
  obtain ⟨k', a', n', v'⟩ := e'
  simp only [evData, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, hv⟩ := h
  rw [BitVec.eq_of_toNat_eq hv]

theorem evs_ext : ∀ {l l' : List Ev}, l.map evData = l'.map evData → l = l'
  | [], [], _ => rfl
  | e :: l, e' :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [ev_ext h.1, evs_ext h.2]

theorem cEvs_patch_data :
    (cEvs (fun _ => False) ctx0 iLdar [ofX 0x8000#64] (patch [ev5] w0)).map evData =
      [ev5].map evData := by
  decide +kernel

/-- **The `ldar` reads the environment's bytes**: on the thread's world patched with the
environment's `5` (its own memory holds `0`), its footprint is the read of `5`. -/
theorem cEvs_patch : cEvs (fun _ => False) ctx0 iLdar [ofX 0x8000#64] (patch [ev5] w0) = [ev5] :=
  evs_ext cEvs_patch_data

/-- One block: the `ldar`, then return. -/
def vc0 : VCode :=
  { name := "w", blocks := #[{ label := 0, insts := #[iLdar, .rets []] }], classes := #[.int, .int],
    slotBytes := 0, outgoing := 0, rulesFired := #[] }

/-- vreg 1 holds the address `0x8000`. -/
def ρ0 : Nat → CV := fun v => if v = 1 then ofX 0x8000#64 else 0

/-- No callee; symbols at 0; constant TLS flags. -/
def X0 : ExtSem := ⟨fun _ _ _ => none, fun _ _ => 0, 0, fun _ _ => PState.zero⟩

theorem X0_tls : TlsMemFree X0 := fun _ _ _ => rfl

/-- Whether an `Except` is a value. -/
def isOkB {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

theorem ok_of_isOkB {ε α : Type} {e : Except ε α} (d : α) (h : isOkB e = true) :
    e = .ok (match e with | .ok x => x | .error _ => d) := by
  cases e with
  | ok x => rfl
  | error _ => cases h

def ops0 : Array Operand := match iLdar.operands with
  | .ok ops => ops
  | .error _ => #[]

theorem ops0_eq : iLdar.operands = .ok ops0 := ok_of_isOkB #[] (by decide +kernel)

theorem uses0 : (ops0.toList.filter Operand.isUse).map (ρ0 ·.vreg) = [ofX 0x8000#64] := by
  decide +kernel

theorem straightSem_eq {F : BitVec 64 → Prop} {ctx : FnCtx} {i : MInst} {uses : List CV}
    {w : ArmState} {ops : Array Operand} {ic : MInst} {t' : ArmState}
    (hops : i.operands = .ok ops) (hic : i.assign (canonRegs ops) = .ok ic)
    (hacc : AccessOk F ctx ic (placeUses ops (canonRegs ops) uses w))
    (hex : execMInst ctx env0 ic (placeUses ops (canonRegs ops) uses w) = some t')
    (herr : Arm.r .ERR t' = .None) (hprog : t'.program = w.program) :
    straightSem F ctx i uses w = some (defVals ops (canonRegs ops) t', t', .next) := by
  unfold straightSem
  simp only [hops, hic]
  split
  · simp only [hex]
    split
    · rfl
    · rename_i h; exact absurd ⟨herr, hprog⟩ h
  · rename_i h; exact absurd hacc h

def ic0 : MInst := match iLdar.assign (canonRegs ops0) with
  | .ok ic => ic
  | .error _ => .fence

theorem ic0_eq : iLdar.assign (canonRegs ops0) = .ok ic0 :=
  ok_of_isOkB .fence (by decide +kernel)

/-- The patched world: the environment's `5` at `0x8000`. -/
def w5 : ArmState := patch [ev5] w0

def t5 : ArmState :=
  (execMInst ctx0 env0 ic0 (placeUses ops0 (canonRegs ops0) [ofX 0x8000#64] w5)).getD w5

theorem exec_t5 : execMInst ctx0 env0 ic0 (placeUses ops0 (canonRegs ops0) [ofX 0x8000#64] w5) =
    some t5 := by
  have h : (execMInst ctx0 env0 ic0 (placeUses ops0 (canonRegs ops0) [ofX 0x8000#64] w5)).isSome := by
    decide +kernel
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
  rw [ht]; simp only [t5, ht, Option.getD_some]

theorem csem_ldar : csem (fun _ => False) ctx0 X0 iLdar [ofX 0x8000#64] w5 =
    some (defVals ops0 (canonRegs ops0) t5, t5, .next) := by
  rw [csem_of_wf (by decide) (by decide +kernel) (by decide +kernel)
    (by unfold Arm.CheckSPAlignment; decide +kernel)]
  exact straightSem_eq ops0_eq ic0_eq (fun _ _ _ _ h => h) exec_t5 (by decide +kernel)
    (by
      have h : @BEq.beq (List (BitVec 64 × BitVec 32)) _ t5.program w5.program = true := by
        decide +kernel
      exact @eq_of_beq (List (BitVec 64 × BitVec 32)) _ _ _ _ h)

/-- **Non-vacuity of `VTStep`**: the thread's `ldar` steps reading the environment's `5` at `0x8000`
(its own memory holds `0`), with the precise footprint `cEvs`. -/
theorem ldar_vtstep : ∃ c', VTStep vc0 (csem (fun _ => False) ctx0 X0) (cEvs (fun _ => False) ctx0)
    (.run ⟨0, 0, ρ0, w0⟩) [ev5] c' := by
  have hlen : (defVals ops0 (canonRegs ops0) t5).length =
      (ops0.toList.filter Operand.isDef).length := by decide +kernel
  have hb : vc0.blocks[0]? = some { label := 0, insts := #[iLdar, .rets []] } := rfl
  have hi : ({ label := 0, insts := #[iLdar, .rets []] } : VBlock).insts[0]? = some iLdar := rfl
  have hsem : csem (fun _ => False) ctx0 X0 iLdar ((ops0.toList.filter Operand.isUse).map
      (ρ0 ·.vreg)) w5 = some (defVals ops0 (canonRegs ops0) t5, t5, .next) := by
    rw [uses0]; exact csem_ldar
  have hnx : VNext vc0 0 0 ({ label := 0, insts := #[iLdar, .rets []] } : VBlock).insts.size iLdar
      ((ops0.toList.filter Operand.isUse).map (ρ0 ·.vreg))
      (writeV (writeV ρ0 (((ops0.toList.filter Operand.isDef).zip
        (defVals ops0 (canonRegs ops0) t5)).filter (·.1.isEarly)))
        (((ops0.toList.filter Operand.isDef).zip (defVals ops0 (canonRegs ops0) t5)).filter
          (·.1.isLate))) t5 .next
      (.run ⟨0, 0 + 1, writeV (writeV ρ0 (((ops0.toList.filter Operand.isDef).zip
        (defVals ops0 (canonRegs ops0) t5)).filter (·.1.isEarly)))
        (((ops0.toList.filter Operand.isDef).zip (defVals ops0 (canonRegs ops0) t5)).filter
          (·.1.isLate)), t5⟩) := .next (by decide)
  have hst : VStep vc0 (csem (fun _ => False) ctx0 X0) (.run ⟨0, 0, ρ0, patch [ev5] w0⟩) _ :=
    VStep.step hb hi ops0_eq hsem hlen hnx
  have hev : [ev5] = cEvs (fun _ => False) ctx0 iLdar ((ops0.toList.filter Operand.isUse).map
      (ρ0 ·.vreg)) (patch [ev5] w0) := by
    rw [uses0]; exact cEvs_patch.symm
  have hfoot : IFoot (csem (fun _ => False) ctx0 X0) iLdar ((ops0.toList.filter Operand.isUse).map
      (ρ0 ·.vreg)) (patch [ev5] w0) [ev5] := by
    rw [uses0]
    have h := ifoot_csem (F := fun _ => False) (ctx := ctx0) (i := iLdar) (uses := [ofX 0x8000#64])
      (w := patch [ev5] w0) X0_tls (by decide +kernel) (fun _ h => nomatch h)
      (fun _ _ h => nomatch h)
      (fun _ => ⟨by decide +kernel, by unfold Arm.CheckSPAlignment; decide +kernel⟩)
    rwa [cEvs_patch] at h
  exact ⟨_, .mk hb hi ops0_eq hev hfoot hst⟩

end Concurrency.VCodeThread.Witness
