import FV.E2E.BackendTwoRunEitherK
import FV.E2E.LinkArmDetRunTwin
import FV.E2E.LinkArmHCallLock
import FV.E2E.LinkArmStage2E
import FV.E2E.LinkArmIniOf
import FV.E2E.IselCallsOneAll
import FV.E2E.LinkArmXNIF
import FV.E2E.LinkArmTwinCRun

/-!
# The lock to the return from the two-run theorem (SEM1 #537, #713, step 5)

**`lockRet_of`**: `LockRet κ M` (`LinkArmLockRet.lean`) from `backend_twoRunLERWZIUPF_either` at
the link's external semantics `XPBTGY` with the canonical activation's prophecies (as in
`thmPRBRL_ofZSERU`): the first entry is the canonical one (`ActEntryPR` with the stage-2 call
contracts), the second the agreeing entry with the prophecies of its own run (`ActEntryPRN … 0`;
its contracts at locked call states by `calleeOkLockedRU`), the pair run's non-interference by
`xnifXPBTGY`, the call hook by `hcallLockXP`, TLS by `HookNIX`. The two-run return index is the
canonical `n₀` (`noRetAt_of` both ways; the program persists, `HooksKeep`), and the second run's
`ActRet` follows from the first's: registers by `RetAgreeX` (the result registers of a `rets` site
are not `x30`, the decidable check `VCode.retsLow`, #732), callee-saved ones by `EntryAgree`.

New premises (decidable checks on the compiled code): `FnAsm.x30Free` (as `backend_twoRunL*`),
`VCode.retsLow`; trusted: `BaseNIX` (`OkDNX.baseNIX`, the base hooks do not observe the exterior,
#704), under `NeedNI`; `HooksKeep` (as `InitOkR`).

* `VCode.retsLow`, `retsLow_sound`, `regVal_eq_of_ne30`, `EntryAgree.symm_of_sp`,
  `armRet_of_retAgreeX`, `BaseNIX`, `OkDNX.baseNIX'`, `MachEntry.ofWithCrun`, `BaseNIX.withCrun`,
  `BaseNIX.std`, `OkDNX.stdBaseNIX` (`L.std.BaseNIX` for `InitOkRU.of_checks`), `callLock_zero`,
  `zc_sub_F`;
* **`lockRet_of`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **No `rets` site of `vc` returns in `x30`** (decidable): every register of a `rets`
instruction is `x0`–`x29` or not a general register. -/
def _root_.Backend.VCode.retsLow (vc : VCode) : Bool :=
  vc.blocks.toList.all fun vb => vb.insts.toList.all fun i => match i with
    | .rets us => us.all fun p => match p.2 with
      | .x n => decide (n < 30)
      | _ => true
    | _ => true

/-- **The result registers of a `rets` site of a checked `vc` are not `x30`.** -/
theorem retsLow_sound {vc : VCode} (h : vc.retsLow = true) {us : List (Reg × Reg)}
    (hrs : vc.RetsSite us) : ∀ p ∈ us, ∀ n, p.2 = .x n → n < 30 := by
  obtain ⟨b, vb, k, hb, hk⟩ := hrs
  have h1 := List.all_eq_true.mp h vb (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hb))
  have h2 := List.all_eq_true.mp h1 _ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk))
  simp only at h2
  intro p hp n hn
  have h3 := List.all_eq_true.mp h2 p hp
  rw [hn] at h3
  simpa using h3

/-- **`EntryAgree` is symmetric between entries with the same `sp`.** -/
theorem EntryAgree.symm_of_sp {K : Nat} {s s₀ : Arm.ArmState} (h : EntryAgree K s s₀)
    (hsp : spv s = spv s₀) : EntryAgree K s₀ s :=
  ⟨fun f hf hpc h30 => (h.1 f hf hpc h30).symm, fun a ha => (h.2 a (hsp ▸ ha)).symm⟩

/-- **An AAPCS64 return carries over to a state equal but for `x30`/pc** from an entry agreeing
on the masked registers, with the entry's `x29`, `sp`, the return address and no error. -/
theorem armRet_of_retAgreeX {ra ra₀ : BitVec 64} {s s₀ t t₀ : Arm.ArmState} (h₀ : ArmRet ra₀ s₀ t₀)
    (hagr : ∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f t₀)
    (hag : ∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f s = Arm.r f s₀)
    (hpc : Arm.r .PC t = ra) (herr : Arm.r .ERR t = .None) (hsp : spv t = spv s)
    (hx29 : xreg 29 t = xreg 29 s) : ArmRet ra s t := by
  refine ⟨hpc, herr, hsp, fun n hn => ?_, fun n h8 h16 => ?_⟩
  · simp only [calleeSavedX, List.mem_map, List.mem_range] at hn
    obtain ⟨j, hj, rfl⟩ := hn
    by_cases h29 : j = 10
    · subst h29; exact hx29
    · have hne : Arm.StateField.GPR (BitVec.ofNat 5 (19 + j)) ≠ .GPR 30#5 := by
        intro e
        have := congrArg (fun f => match f with | Arm.StateField.GPR i => i.toNat | _ => 0) e
        simp at this; omega
      simp only [xreg]
      rw [hagr _ (by simp) hne]
      have e₀ := h₀.savedX (19 + j) (by simp [calleeSavedX]; omega)
      simp only [xreg] at e₀
      rw [e₀]
      refine (hag _ ?_ (by simp) hne).symm
      simp only [Masked, BitVec.toNat_ofNat]
      omega
  · rw [hagr _ (by simp) (by simp), h₀.savedV n h8 h16, hag _ (by simp [Masked]) (by simp) (by simp)]

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The base hooks do not observe the exterior of a machine entry** (`OkDNX.baseNIX`, trusted,
#704; under `NeedNI`). -/
def BaseNIX : Prop :=
  L.NeedNI → ∀ (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F G : BitVec 64 → Prop) (ra : BitVec 64) (s w₀ : Arm.ArmState),
    L.MachEntry κ M g F G ra s w₀ → HookNIX L.Hb L.BaseDest F

theorem _root_.E2E.LinkSys.OkDNX.baseNIX' {L : LinkSys} (h : L.OkDNX) : L.BaseNIX := h.baseNIX

/-- **A machine entry of `L` with other callee runs is one of `L`** (`MachEntry` does not mention
the callee runs). -/
theorem MachEntry.ofWithCrun {c : Nat → Clif.State → Clif.Outcome} {M : Nat} {g : Clif.Function}
    {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (h : (L.withCrun c).MachEntry κ M g F G ra s w₀) : L.MachEntry κ M g F G ra s w₀ :=
  { abi := h.abi, stack := h.stack, gfree := h.gfree, hF := h.hF, imgG := h.imgG,
    imgS := h.imgS, body := h.body }

/-- **`BaseNIX` does not depend on the callee runs.** -/
theorem BaseNIX.withCrun {L : LinkSys} (h : L.BaseNIX) (c : Nat → Clif.State → Clif.Outcome) :
    (L.withCrun c).BaseNIX :=
  fun hN κ M g F G ra s w₀ hME => h hN κ M g F G ra s w₀ (MachEntry.ofWithCrun L hME)

/-- **`BaseNIX` of the default callee runs** (`L.std`, the system the determinism induction runs
over in `InitOkRU.of_checks`) from `L`'s. -/
theorem BaseNIX.std {L : LinkSys} (h : L.BaseNIX) : L.std.BaseNIX := h.withCrun _

/-- **`BaseNIX` of the default callee runs from the trusted `OkDNX`.** -/
theorem _root_.E2E.LinkSys.OkDNX.stdBaseNIX {L : LinkSys} (h : L.OkDNX) : L.std.BaseNIX :=
  h.baseNIX'.std

/-- **`CallLock` at depth `0`**: no callee run returns at depth `0`. -/
theorem callLock_zero [hR : L.CrunOk] : L.CallLock κ 0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ cs rvals cm' _ _ _ _ _ _ _ _ hrun =>
    absurd hrun (hR.zero cs rvals cm')

/-- **The lock set is inside the exterior** when the worlds differ inside `F ∪ D`, `D ⊆ F`. -/
theorem zc_sub_F {R : RL} {F D : BitVec 64 → Prop} (hRF : R.F = F) (hD : ∀ a, D a → F a)
    {c c' : MConf CV Arm.ArmState} (hwd : ∀ a, MConf.WDiff c c' a → F a ∨ D a) :
    ∀ a, R.Zc c c' a → F a := by
  intro a ⟨_, _, _, h⟩
  rcases h with hf | hw
  · rw [← hRF]; exact hf
  · exact (hwd a hw).elim id (hD a)

set_option maxHeartbeats 8000000 in
/-- **The lock to the return** (module doc): `LockRet κ M` from the two-run theorem, given the
level-`M - 1` linking statement and determinism, the call twins and the call lock at `M`, the
stage-2 and return scope at `M`. -/
theorem lockRet_of (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) (hK : L.HooksKeep)
    (hN : L.NeedNI) (hNX : L.BaseNIX)
    (hx30 : ∀ g ∈ L.P.funcs, ∀ lm, labelOffsets (L.A g).fa.lines = .ok lm →
      (L.A g).fa.x30Free lm = true)
    (hrl : ∀ g ∈ L.P.funcs, (L.A g).vc.retsLow = true)
    (hblr : ∀ g ∈ L.P.funcs, (L.A g).fa.blrLow = true) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBRU κ (M - 1))
    (htw : 0 < M → L.CallTwinCET κ M) (hcl : L.CallLock κ M) (hret : L.RetOkPRB κ M)
    (h2 : L.Stage2PRBZSE κ M) : L.LockRet κ M := by
  intro g hg F vals cs w₀ ini G₀ ra₀ s₀ us outs wf n₀ fuel rvals cm' hWE hME₀ htab hret₀ hrs hpt₀
    hrun hra₀ D w₀' hD hrel hsw hreg hstk G ra s hME hag hra hx29
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInvB g (spv w₀) cs := ⟨hI, hWE.clif.callers, fun hN => ⟨ini, hWE.place hN⟩⟩
  have hrun' : Clif.runLoop (L.envOfB M g (spv w₀)) L.P.bare fuel cs = .returned rvals cm' := by
    rw [L.runLoop_envOfB hL hg fuel cs hJ]; exact hrun
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hL.free f hg
  have hnrc : NoRetCall (L.envOfB M g (spv w₀)) L.P.bare cs :=
    noRetCall_of_linv hPf (fun _ h => by simp at h) hI
  have he := hME₀.entryP.entry
  have hQ := L.callStPRB_q (κ := κ) (M := M) he.body.sp
  have hS2 := h2 g hg F vals cs w₀ fuel rvals cm' ini G₀ ra₀ s₀ hWE hME₀ hra₀ htab hrun
  -- the canonical (first) entry
  have hAE : ActEntryPR (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G₀
      (L.XPBTGY κ M g F (L.BP M g s₀) (L.RP M g s₀) (L.envOfB M g (spv w₀)) cs (spv w₀))
      (L.hooks M) (L.A g).base ra₀ (κ M g) (spv w₀) (L.BP M g s₀) (L.RP M g s₀) s₀ w₀ :=
    ⟨he.abi, he.stack, he.gfree, he.hF, hME₀.entryP.proph, hME₀.reg,
      fun n => L.calleeOkXPBTGZSRU hL hκ ih hdet hg he (hQ n) (hS2 n),
      fun _ n => L.calleeTryOkXPBTGZSRU hL hκ ih hdet hg he (hQ n) (hS2 n),
      fun ht _ => by
        have h0 := hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)
        cases M <;> exact ⟨h0.pc, h0.seq, h0.flags⟩,
      he.body⟩
  -- the agreeing (second) entry, with the prophecies of its own run
  have hspw : spv w₀ = spv w₀' := hsw.1 (.GPR 31#5) (by simp [Masked])
  have hsps : spv s = spv s₀ := by
    have e := (he.body.sp.symm.trans hspw).trans hME.body.sp
    have := congrArg (· + BitVec.ofNat 64 (frameDrop (L.A g).af)) e
    simpa using this.symm
  have hpc := (L.calleeOkPRBRLRU hL hκ ih hdet hg he (Q := fun _ => False) (P := L.BP M g s₀)
    (R := L.RP M g s₀) (n := 0) (fun _ h => h.elim)).pc
  have he0 : ActEntryPRN (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G
      (L.XPBTGY κ M g F (L.BP M g s₀) (L.RP M g s₀) (L.envOfB M g (spv w₀)) cs (spv w₀))
      (L.hooks M) (L.A g).base ra (κ M g) (spv w₀')
      (prophOf (ArmStepX ((L.XPBTGY κ M g F (L.BP M g s₀) (L.RP M g s₀) (L.envOfB M g (spv w₀))
        cs (spv w₀)).at 0) (L.hooks M) (L.A g).fa) (L.A g).fa (L.A g).base s)
      (prophStOf (ArmStepX ((L.XPBTGY κ M g F (L.BP M g s₀) (L.RP M g s₀) (L.envOfB M g (spv w₀))
        cs (spv w₀)).at 0) (L.hooks M) (L.A g).fa) (L.A g).fa (L.A g).base s) s w₀' 0 :=
    ⟨hME.abi, hME.stack, hME.gfree, hME.hF, prophOk_prophOf _ _ _ _ _ _,
      fun _ hcp _ _ _ _ => by rw [prophStOf_call hcp],
      fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _), hpc,
      fun ht _ => by
        have h0 := hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)
        cases M <;> exact ⟨h0.pc, h0.seq, h0.flags⟩,
      hME.body⟩
  have hNXF : HookNIX L.Hb L.BaseDest F := hNX hN κ M g F G₀ ra₀ s₀ w₀ he
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨body, psF, hpsF, -, hk⟩ := emitFunc_ok hc.emit
  have hpsF' : blocksLinesE ⟨(L.A g).fa.k, (L.A g).af.slotBase⟩ (L.A g).af
      (L.A g).af.blocks.toList {} = .ok (body, psF) := by
    rw [hk]; exact hpsF
  have hx30g : (L.A g).fa.x30Free lm = true := hx30 g hg lm hlm
  have hRF : (Backend.Proof.actRL (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb lm
      (L.A g).base s₀ (L.XPBTGY κ M g F (L.BP M g s₀) (L.RP M g s₀) (L.envOfB M g (spv w₀)) cs
        (spv w₀)) (L.hooks M) psF (κ M g) G₀ (GotV (L.A g).vcp)).F = F := he.hF
  obtain ⟨T, hpc1, hpc2, hagr, hmo, -, hsv2, -, hG2, herr2, hsp2, hx292, hgood, hlk⟩ :=
    backend_twoRunLERWZIUPF_eitherK (hL.subset g hg) hc (instCallsOne_all g) (tryCallsOne_all g)
      (XI := L.XPBTGY κ M g F (L.BP M g s₀) (L.RP M g s₀) (L.envOfB M g (spv w₀)) cs (spv w₀))
      (syms := L.syms) (env := L.envOfB M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀)
      (hX_guardRXRI (L.XPBTI κ M g F (L.BP M g s₀) (L.RP M g s₀)) hnrc
        (hret g hg F vals cs w₀ ini hWE))
      (fun _ _ hs => L.xnifXPBTGY hL hκ hN ih hdet htw hg hWE.img _ _ hnrc hs)
      (fun _ => hL.baseTlsNI hN F) (fun n b hn => hL.symOk n b hn) rfl hD (fun _ => 0) hWE.clif
      hWE.rel hrel hWE.args hsw hreg hstk (trapsExplicit_of_returned hrun') fuel hrun' hlm hpsF'
      hAE he0
      (fun n => L.calleeOkLockedRU hL hκ ih hdet hg hME₀ hME hsps hD (hS2 n)
        (fun _ hu => hu.1.2) (fun _ hu hcp => hu.2 hcp))
      (fun _ n => L.calleeTryOkLockedRU hL hκ ih hdet hg hME₀ hME hsps hD (hS2 n)
        (fun _ hu => hu.1.2) (fun _ hu hcp => hu.2 hcp))
      rfl (hL.covered g hg) hx30g
      (L.hcallLockXP hL hκ hcl hg hME₀ hME hD hNXF hS2 rfl rfl)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ hz hwd _ m r =>
        L.hooks_lock_tls hNXF M m r hz (zc_sub_F hRF hD hwd))
      (hag.symm_of_sp hsps) hx29.symm
  -- the return index `k` of both runs, on the machines `L.mach M g`
  obtain ⟨k, hkdef⟩ : ∃ k, k = (prologueLines (Backend.Proof.actRL (L.A g).vcp (L.A g).rf
      (L.A g).af (L.A g).fa (L.A g).fb lm (L.A g).base s₀
      (L.XPBTGY κ M g F (L.BP M g s₀) (L.RP M g s₀) (L.envOfB M g (spv w₀)) cs (spv w₀))
      (L.hooks M) psF (κ M g) G₀ (GotV (L.A g).vcp)).af.saves (Backend.Proof.actRL (L.A g).vcp
      (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb lm (L.A g).base s₀
      (L.XPBTGY κ M g F (L.BP M g s₀) (L.RP M g s₀) (L.envOfB M g (spv w₀)) cs (spv w₀))
      (L.hooks M) psF (κ M g) G₀ (GotV (L.A g).vcp)).af.frameSize (Backend.Proof.actRL (L.A g).vcp
      (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb lm (L.A g).base s₀
      (L.XPBTGY κ M g F (L.BP M g s₀) (L.RP M g s₀) (L.envOfB M g (spv w₀)) cs (spv w₀))
      (L.hooks M) psF (κ M g) G₀ (GotV (L.A g).vcp)).af.isCaller).length + T +
      (Backend.Proof.actRL (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb lm (L.A g).base
        s₀ (L.XPBTGY κ M g F (L.BP M g s₀) (L.RP M g s₀) (L.envOfB M g (spv w₀)) cs (spv w₀))
        (L.hooks M) psF (κ M g) G₀ (GotV (L.A g).vcp)).retLen := ⟨_, rfl⟩
  rw [← hkdef] at hpc1 hpc2 hagr hmo hsv2 hG2 herr2 hsp2 hx292 hgood hlk
  have hpc1' : Arm.r .PC (runX (L.mach M g) k s₀) = ra₀ := by rw [runX_eq]; exact hpc1
  have hpc2' : Arm.r .PC (runX (L.mach M g) k s) = ra := by rw [runX_eq]; exact hpc2
  have hagr' : RetAgreeX (frameDrop (L.A g).af + κ M g) (spv s₀) (runX (L.mach M g) k s)
      (runX (L.mach M g) k s₀) := by rw [runX_eq, runX_eq]; exact hagr
  have hmo' : ∀ a, ¬ F a → ¬ D a → (runX (L.mach M g) k s).mem a = (runX (L.mach M g) k s₀).mem a :=
    by rw [runX_eq, runX_eq]; exact hmo
  have hsv2' : Arm.read_mem_bytes 16 (spv s - 16#64) (runX (L.mach M g) k s) =
      xreg 30 s ++ xreg 29 s := by rw [runX_eq]; exact hsv2
  have hG2' : ∀ a, G a → (runX (L.mach M g) k s).mem a = s.mem a := by rw [runX_eq]; exact hG2
  have herr2' : Arm.r .ERR (runX (L.mach M g) k s) = .None := by rw [runX_eq]; exact herr2
  have hsp2' : spv (runX (L.mach M g) k s) = spv s := by rw [runX_eq]; exact hsp2
  have hx292' : xreg 29 (runX (L.mach M g) k s) = xreg 29 s := by rw [runX_eq]; exact hx292
  have hgood' : ∀ i < k, (¬ PostCall (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) i s₀)) ∨
      spOf (runX (L.mach M g) i s₀) = spv s₀ - BitVec.ofNat 64 (frameDrop (L.A g).af)) ∧
      (¬ PostCall (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) i s)) ∨
      spOf (runX (L.mach M g) i s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)) := by
    intro i hi
    rw [runX_eq, runX_eq]; exact ⟨(hgood i hi).1.1, (hgood i hi).2.1⟩
  have hlk' : ∀ i < k, ∃ Z, StEqOutX Z (runX (L.mach M g) i s) (runX (L.mach M g) i s₀) ∧
      ∀ a, StackBelow (κ M g) (spv s₀ - BitVec.ofNat 64 (frameDrop (L.A g).af)) a → ¬ Z a := by
    intro i hi
    obtain ⟨d, d', hz⟩ := hlk i hi
    rw [runX_eq, runX_eq]
    exact ⟨_, hz, fun a ha hzz => hzz.1.2.2.1 ha⟩
  -- the lock with its set inside `F` (canonical run first), the second run's code image
  have hlkF : ∀ i < k, ∃ Z, StEqOutX Z (runX (L.mach M g) i s₀) (runX (L.mach M g) i s) ∧
      (∀ a, Z a → F a) ∧
      ∀ a, StackBelow (κ M g) (spv s₀ - BitVec.ofNat 64 (frameDrop (L.A g).af)) a → ¬ Z a := by
    intro i hi
    obtain ⟨d, d', hz⟩ := hlk i hi
    rw [runX_eq, runX_eq]
    exact ⟨_, hz.symm, fun a hzz => hzz.2.elim id (hD a), fun a ha hzz => hzz.1.2.2.1 ha⟩
  have himgS : ∀ i < k, CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) i s)) →
      ∀ a, L.Img a → (runX (L.mach M g) i s).mem a = L.imgMem a := by
    intro i hi hcp a ha
    have hG := (hgood i hi).2.2
    rw [runX_eq] at hcp ⊢
    exact (hG hcp a (hME.imgG a ha)).trans (hME.imgS a ha)
  -- `k` is the canonical return index `n₀`
  have herr1 : Arm.r .ERR (runX (L.mach M g) k s₀) = .None :=
    (hagr'.1 .ERR (by simp) (by simp)).symm.trans herr2'
  have hsp1 : spv (runX (L.mach M g) k s₀) = spv s₀ :=
    ((hagr'.1 (.GPR 31#5) (by simp) (by simp)).symm.trans hsp2').trans hsps
  have hret1 : L.RetAt g s₀ (runX (L.mach M g) k s₀) :=
    ⟨hpc1'.trans he.abi.lr.symm, herr1, (L.runX_progK hK M g k s₀).trans he.abi.program, hsp1⟩
  have hretn : L.RetAt g s₀ (runX (L.mach M g) n₀ s₀) :=
    ⟨hret₀.ret.pc.trans he.abi.lr.symm, hret₀.ret.err, hret₀.prog.trans he.abi.program,
      hret₀.ret.sp⟩
  have hpt1 : PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s₀ k :=
    fun i _ hik hpcall => (hgood' i hik).1.resolve_left (not_not_intro hpcall)
  have hkn : k = n₀ := by
    rcases Nat.lt_trichotomy k n₀ with h | h | h
    · exact absurd hret1 (L.noRetAt_of hL hg he hra₀ hpt₀ hret₀.ret.err k h)
    · exact h
    · exact absurd hretn (L.noRetAt_of hL hg he hra₀ hpt1 herr1 n₀ h)
  subst hkn
  have hcan := L.canonCallTwin hL hκ ih hdet hret h2 htw hg hWE hME₀ hra₀ htab hrun
  have htwin : L.TwinCE M g s₀ s := L.twinCE_of_lockK hL hg (hblr g hg)
    (K := κ M g) (c := spv s₀ - BitVec.ofNat 64 (frameDrop (L.A g).af))
    (by rw [← he.body.sp]; exact hWE.room) hlkF himgS
    (fun i hi hcp => hcan i (fun j hj => L.noRetAt_of hL hg he hra₀ hpt₀ hret₀.ret.err j
      (by omega)) hcp)
    (fun i hi => ⟨L.noRetAt_of hL hg he hra₀ hpt₀ hret₀.ret.err i hi,
      fun hr => L.noRetAt_of hL hg hME hra (fun i' _ hik hpcall => (hgood' i' hik).2.resolve_left
        (not_not_intro hpcall)) herr2' i hi hr⟩)
    ⟨hretn, ⟨hpc2'.trans hME.abi.lr.symm, herr2', (L.runX_progK hK M g k s).trans hME.abi.program,
      hsp2'⟩⟩
  refine ⟨hlk', hagr', hmo', hsv2', ⟨armRet_of_retAgreeX hret₀.ret hagr'.1 hag.1 hpc2' herr2'
    hsp2' hx292', fun j v p x hj hx => ?_, fun a ha => ?_, fun f hf h29 h31 => ?_, hG2',
    L.runX_progK hK M g k s⟩, fun i _ hik hpcall => (hgood' i hik).2.resolve_left
      (not_not_intro hpcall), TwinCE.symm L htwin⟩
  · rw [regVal_eq_of_ne30 hagr'.1 (retsLow_sound (hrl g hg) hrs (v, p) (List.mem_of_getElem? hj))]
    exact hret₀.regs j v p x hj hx
  · rw [hmo' a (fun h => ha (.inl h)) (fun h => ha (.inr h))]
    exact hret₀.mem a (fun h => ha (.inl h))
  · rw [hagr'.1 f (fun e => hf (e ▸ by simp [Masked])) (fun e => hf (e ▸ by simp [Masked]))]
    exact hret₀.fields f hf h29 h31

end LinkSys

end E2E
