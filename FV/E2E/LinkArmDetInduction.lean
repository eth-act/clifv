import FV.E2E.LinkArmDetRunPRBCR
import FV.E2E.LinkArmDetTabE

/-!
# The determinism induction (SEM1 #537, #713)

The determinism premises of the oracle route (`DetPRBRU`, `DetTabPRBE`, `DetTabPRBr`; #719, #716,
#732) follow, at every depth, from the scope conditions and three decidable checks on the compiled
code, by one induction on the depth `M` over `ThmPRBRLE κ M ∧ LockRet κ M`:

* depth `0`: `ThmPRBRLE κ 0` (`thmPRBRL_ofZSERU` with the zero scope facts), `LockRet κ 0`
  (`lockRet_of`: no program callee returns at depth `0`, `callLock_zero`);
* step: `LockRet κ M` gives `DetRunPRBCRU κ M` (`detRunPRBCRU_of_lockRet`: `TwinNC` from `TwinCE`
  before the canonical return), hence `DetPRBRU κ M` (`detPRBRU_ofC`); with `ThmPRBRLE κ M` the
  call lock `CallLock κ (M + 1)` (`callLock_of`), its twins `CallTwinCET κ (M + 1)`, and the
  canonical callee's table from the actual one `DetTabPRBE κ (M + 1)` (`detTabPRBE_of`); then
  `ThmPRBRLE κ (M + 1)` (`thmPRBRLE_succSRU`) and `LockRet κ (M + 1)` (`lockRet_of`).

Premises: `L.Ok`, `CrunOk`, the budget `κ`, the scope conditions `NeedSlots`, `BaseRetOk`,
`RetCount` (as `thmPRBRLE_allCRU`), `HooksKeep`, `NeedNI` with the trusted base-hook fact
`BaseNIX` (`OkDNX.baseNIX`), and the decidable checks on every function's compiled code:
`FnAsm.x30Free` (the code outside the frame-record and call lines does not touch `x30`),
`FnAsm.blrLow` (every `blr` through `x0`–`x28`), `VCode.retsLow` (no `rets` register is `x30`).

`CallTwinCE κ M` itself (no table premise) is not among the results: its callee CLIF run answers
the slot reads of nested callees from an arbitrary table, so the canonical callee machine run has
no CLIF counterpart (#713); `CallTwinCET` (the canonical table given) and the two table transfers
are what the consumers use.

* `twinNC_of_twinCE`, **`detRunPRBCRU_of_lockRet`**;
* **`detInduction`**; **`thmPRBRLE_allK`**, **`detRunPRBCRU_allK`**, **`detPRBRU_allK`**,
  **`callTwinCET_allK`**, **`detTabPRBE_allK`**, **`detTabPRBr_allK`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **Twins relating the errors give the twins up to the first return.** -/
theorem twinNC_of_twinCE {M : Nat} {g : Clif.Function} {s₀ s : Arm.ArmState} {n : Nat}
    (htw : L.TwinCE M g s₀ s) (hn : ∀ j < n, ¬ L.RetAt g s₀ (runX (L.mach M g) j s₀)) :
    L.TwinNC M g s₀ s n := by
  refine ⟨fun i hi => ((TwinCE.base L htw).1 i (fun j hj => hn j (by omega))).2 (hn i hi),
    fun M' hM i hi h hc => ?_⟩
  subst hM
  exact TwinCE.twinC L (htw.2 i (fun j hj => hn j (by omega)) h hc)

/-- **The determinism step from the lock to the return** (`TwinNC` from `LockRet`'s twins). -/
theorem detRunPRBCRU_of_lockRet (hL : L.Ok) {M : Nat} (h : L.LockRet κ M) :
    L.DetRunPRBCRU κ M :=
  fun g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ fuel rvals cm' hWE hME₀ htab hret₀ hrs hpt₀
    hrun hra₀ D w₀' hD hrel hsw hreg hstk G ra s hME hag hra hx29 =>
    let ⟨_, _, _, _, hret, hpt, htw⟩ := h g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ fuel rvals
      cm' hWE hME₀ (L.tableOfE_of htab) hret₀ hrs hpt₀ hrun hra₀ D w₀' hD hrel hsw hreg hstk G ra
      s hME hag hra hx29
    ⟨hret, hpt, L.twinNC_of_twinCE (TwinCE.symm L htw)
      (L.noRetAt_of hL hg hME₀.entryP.entry hra₀ hpt₀ hret₀.ret.err)⟩

/-- **The determinism induction** (module doc). -/
theorem detInduction (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hK : L.HooksKeep)
    (hNS : L.NeedSlots) (hN : L.NeedNI) (hNX : L.BaseNIX) (hB : L.BaseRetOk)
    (hC : ∀ g ∈ L.P.funcs, L.RetCount g)
    (hx30 : ∀ g ∈ L.P.funcs, ∀ lm, labelOffsets (L.A g).fa.lines = .ok lm →
      (L.A g).fa.x30Free lm = true)
    (hrl : ∀ g ∈ L.P.funcs, (L.A g).vc.retsLow = true)
    (hblr : ∀ g ∈ L.P.funcs, (L.A g).fa.blrLow = true) :
    ∀ M, L.ThmPRBRLE κ M ∧ L.LockRet κ M := by
  intro M
  induction M with
  | zero =>
    exact ⟨L.thmPRBRL_ofZSERU hL hκ (fun h => absurd h (Nat.lt_irrefl 0))
        (fun h => absurd h (Nat.lt_irrefl 0)) (L.retOkPRB_zero hB hC) (L.stage2PRBZSE_zero hL)
        (L.countPRBE_zero hL),
      L.lockRet_of hL hκ hK hN hNX hx30 hrl hblr (fun h => absurd h (Nat.lt_irrefl 0))
        (fun h => absurd h (Nat.lt_irrefl 0)) (fun h => absurd h (Nat.lt_irrefl 0)) L.callLock_zero
        (L.retOkPRB_zero hB hC) (L.stage2PRBZSE_zero hL)⟩
  | succ M ih =>
    obtain ⟨hT, hLk⟩ := ih
    have hdet : L.DetPRBRU κ M := L.detPRBRU_ofC (L.detRunPRBCRU_of_lockRet hL hLk)
    have hT1 : L.ThmPRBRLE κ (M + 1 - 1) := by rw [Nat.add_sub_cancel]; exact hT
    have hLk1 : L.LockRet κ (M + 1 - 1) := by rw [Nat.add_sub_cancel]; exact hLk
    have hdt : L.DetTabPRBE κ (M + 1) := L.detTabPRBE_of hL hκ (Nat.succ_pos M) hT1 hLk1
    have hcl : L.CallLock κ (M + 1) := L.callLock_of hL hκ (Nat.succ_pos M) hT1 hLk1
    have hret := L.retOkPRB_of (κ := κ) hL hNS hB hC (M + 1)
    have h2 := L.stage2PRBZS_ofERU hL hκ hNS hT hdet hdt hret
    refine ⟨L.thmPRBRLE_succSRU hL hκ hNS hT hdet hdt hret,
      L.lockRet_of hL hκ hK hN hNX hx30 hrl hblr
        (fun _ => by rw [Nat.add_sub_cancel]; exact ThmPRBRLE.toThmPRBRL L hT)
        (fun _ => by rw [Nat.add_sub_cancel]; exact hdet) (fun _ => CallLock.callTwinCET L hcl)
        hcl hret h2⟩

section
variable (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hK : L.HooksKeep)
  (hNS : L.NeedSlots) (hN : L.NeedNI) (hNX : L.BaseNIX) (hB : L.BaseRetOk)
  (hC : ∀ g ∈ L.P.funcs, L.RetCount g)
  (hx30 : ∀ g ∈ L.P.funcs, ∀ lm, labelOffsets (L.A g).fa.lines = .ok lm →
    (L.A g).fa.x30Free lm = true)
  (hrl : ∀ g ∈ L.P.funcs, (L.A g).vc.retsLow = true)
  (hblr : ∀ g ∈ L.P.funcs, (L.A g).fa.blrLow = true)
include hL hκ hK hNS hN hNX hB hC hx30 hrl hblr

/-- **`ThmPRBRLE` at every depth without determinism premises** (module doc). -/
theorem thmPRBRLE_allK (M : Nat) : L.ThmPRBRLE κ M :=
  (L.detInduction hL hκ hK hNS hN hNX hB hC hx30 hrl hblr M).1

/-- **The determinism step at every depth** (module doc). -/
theorem detRunPRBCRU_allK (M : Nat) : L.DetRunPRBCRU κ M :=
  L.detRunPRBCRU_of_lockRet hL (L.detInduction hL hκ hK hNS hN hNX hB hC hx30 hrl hblr M).2

/-- **`DetPRBRU` at every depth** (`detPRBRU_ofC` unconditional). -/
theorem detPRBRU_allK (M : Nat) : L.DetPRBRU κ M :=
  L.detPRBRU_ofC (L.detRunPRBCRU_allK hL hκ hK hNS hN hNX hB hC hx30 hrl hblr M)

/-- **The call twins, given the canonical callee's table, at every depth.** -/
theorem callTwinCET_allK : ∀ M, L.CallTwinCET κ M
  | 0 => CallLock.callTwinCET L (L.callLock_zero (κ := κ))
  | M + 1 => CallLock.callTwinCET L (L.callLock_of hL hκ (Nat.succ_pos M)
      (by rw [Nat.add_sub_cancel]; exact L.thmPRBRLE_allK hL hκ hK hNS hN hNX hB hC hx30 hrl hblr M)
      (by rw [Nat.add_sub_cancel]
          exact (L.detInduction hL hκ hK hNS hN hNX hB hC hx30 hrl hblr M).2))

/-- **`DetTabPRBE` at every depth** (`detTabPRBE_ofCE`'s conclusion without `CallTwinCE`). -/
theorem detTabPRBE_allK : ∀ M, L.DetTabPRBE κ M
  | 0 => L.detTabPRBE_zero
  | M + 1 => L.detTabPRBE_of hL hκ (Nat.succ_pos M)
      (by rw [Nat.add_sub_cancel]; exact L.thmPRBRLE_allK hL hκ hK hNS hN hNX hB hC hx30 hrl hblr M)
      (by rw [Nat.add_sub_cancel]
          exact (L.detInduction hL hκ hK hNS hN hNX hB hC hx30 hrl hblr M).2)

/-- **`DetTabPRBr` at every depth** (`detTabPRBr_ofCE`'s conclusion without `CallTwinCE`). -/
theorem detTabPRBr_allK (M : Nat) : L.DetTabPRBr κ M :=
  L.detTabPRBr_ofCT (L.callTwinCET_allK hL hκ hK hNS hN hNX hB hC hx30 hrl hblr M)

end

end LinkSys

end E2E
