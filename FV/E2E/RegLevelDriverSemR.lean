import FV.E2E.RegLevelDriverSem
import FV.E2E.GotFlow
import FV.Backend.Proof.IselContractPR
import FV.Backend.Proof.IselFloatConstPool

/-!
# The register-guarded VCode semantics (#753, stage R2)

At a `blr` through a vreg that is no GOT load (a vtable slot), the typed link's model of a call
may enter any function of the program at the target address, whatever the site's registers
(#753). Stage R1 (`IselContractPR`) made the call contracts ask for the callee only at sites with
the callee's registers (`SiteRegsR`). This module gives the VCode semantics that only makes such
calls:

* `RegGuard P info uses`: at a call through a register (`info.dest = .reg r`), every function
  `P` places at the target address (the low 64 bits of the first use) has the site's registers
  (`SiteRegsR` of its signature); `RegGuardI` is it per instruction (`True` but at `call` and
  `try_call`);
* `regG P sem`: `sem` where `RegGuardI` holds, undefined elsewhere (the pattern of `csemVG`,
  `RegLevelCorrectCY`); `csemR P F ctx X := regG P (csem F ctx X)` and
  `csemVR P gv F ctx X := regG P (csemV gv F ctx X)`;
* the facts of the base semantics that do not concern calls hold for `regG P sem`
  (`DriverSem.regG`, `Refines.regG`, `MemRefines.regG`, `MemRefinesR.regG`, `MemRefinesFP.regG`,
  `PoolRefinesFP.regG`), and the call contracts become the contracts with registers
  (`CallsRefineP.regG`, `IndCallsRefineP.regG`) where the functions at an address have the
  registers of the declaration the call is checked against (`RegCompatGot`, `RegCompatInd`,
  through `SigRegsEq`);
* `callsRefinePR_csemR`, `indCallsRefinePR_csemR`: `callsRefine_csem`, `indCallsRefine_csem` for
  `csemR`.
-/

namespace Backend.Proof

open Backend Backend.Proof.Driver

set_option autoImplicit false

/-! ## The guard -/

/-- Two signatures with the same parameter registers and the same return classes: a call site
with the registers of one has those of the other (`SiteRegsR.of_sigRegsEq`). -/
def SigRegsEq (s t : Clif.Signature) : Prop :=
  E2E.regLocs s = E2E.regLocs t ∧ s.returns.map retClass = t.returns.map retClass

theorem SiteRegsR.of_sigRegsEq {s t : Clif.Signature} (h : SigRegsEq s t)
    {us ds : List (Reg × Reg)} (hs : SiteRegsR t us ds) : SiteRegsR s us ds := by
  obtain ⟨h1, h2⟩ := hs
  have hl : s.returns.length = t.returns.length := by
    have := congrArg List.length h.2
    simpa using this
  exact ⟨h1.trans h.1.symm, by rw [hl, h.2]; exact h2⟩

/-- `abiMatch` with the same return classes is `SigRegsEq`. -/
theorem sigRegsEq_of_abiMatch {d t : Clif.Signature} (h : d.abiMatch t = true)
    (hr : d.returns.map retClass = t.returns.map retClass) : SigRegsEq t d :=
  ⟨(regLocs_of_abiMatch h).symm, hr.symm⟩

/-- **The register guard of a call**: at a call through a register, every function `P` places at
the target address (the low 64 bits of the first use value) has the site's registers. -/
def RegGuard (P : BitVec 64 → Clif.Signature → Prop) (info : CallInfo) (uses : List CV) : Prop :=
  ∀ r u, info.dest = .reg r → uses.head? = some u → ∀ s, P (lo64 u) s →
    SiteRegsR s info.uses info.defs

/-- The register guard of an instruction: `RegGuard` at `call` and `try_call`, `True` elsewhere. -/
def RegGuardI (P : BitVec 64 → Clif.Signature → Prop) : MInst → List CV → Prop
  | .call info, us => RegGuard P info us
  | .tryCall info _, us => RegGuard P info us
  | _, _ => True

open Classical in
/-- **The register-guarded semantics**: `sem` where `RegGuardI` holds, undefined elsewhere. -/
noncomputable def regG {W : Type} (P : BitVec 64 → Clif.Signature → Prop) (sem : ISem CV W) :
    ISem CV W :=
  fun i us w => if RegGuardI P i us then sem i us w else none

/-- **`csem` with the register guard.** -/
noncomputable def csemR (P : BitVec 64 → Clif.Signature → Prop) (F : BitVec 64 → Prop)
    (ctx : FnCtx) (X : ExtSem) : Sem :=
  regG P (csem F ctx X)

/-- **`csemV` with the register guard** (M6's semantics of the calls the VCode run makes with the
registers of every function at their target). -/
noncomputable def csemVR (P : BitVec 64 → Clif.Signature → Prop) (gv : Nat → String → Prop)
    (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) : Sem :=
  regG P (csemV gv F ctx X)

section
variable {W : Type} {P : BitVec 64 → Clif.Signature → Prop} {sem : ISem CV W}

theorem regG_of {i : MInst} {us : List CV} {w : W} (h : RegGuardI P i us) :
    regG P sem i us w = sem i us w := by
  simp [regG, h]

theorem regG_inv {i : MInst} {us : List CV} {w : W} {r : List CV × W × Ctl}
    (h : regG P sem i us w = some r) : RegGuardI P i us ∧ sem i us w = some r := by
  unfold regG at h
  split at h
  · exact ⟨‹_›, h⟩
  · cases h

theorem regG_sub {i : MInst} {us : List CV} {w : W} {r : List CV × W × Ctl}
    (h : regG P sem i us w = some r) : sem i us w = some r :=
  (regG_inv h).2

/-- `regG` is monotone in the semantics. -/
theorem regG_mono {sem' : ISem CV W}
    (h : ∀ i us w r, sem i us w = some r → sem' i us w = some r) :
    ∀ i us w r, regG P sem i us w = some r → regG P sem' i us w = some r := by
  intro i us w r hr
  obtain ⟨hg, hs⟩ := regG_inv hr
  rw [regG_of hg]
  exact h i us w r hs

theorem regGuard_mapRegs (f : Reg → Reg) (info : CallInfo) (us : List CV) :
    RegGuard P { info with
      dest := match info.dest with
        | .reg r => .reg (f r)
        | d => d
      uses := info.uses.map fun (v, p) => (f v, p)
      defs := info.defs.map fun (p, v) => (p, f v) } us = RegGuard P info us := by
  obtain ⟨dest, uses, defs⟩ := info
  have e1 : (uses.map fun (v, p) => (f v, p)).map (·.2) = uses.map (·.2) := by
    simp [List.map_map, Function.comp_def]
  have e2 : (defs.map fun (p, v) => (p, f v)).map (·.1) = defs.map (·.1) := by
    simp [List.map_map, Function.comp_def]
  cases dest with
  | reg r0 =>
    apply propext
    simp only [RegGuard, SiteRegsR, CallDest.reg.injEq, e1, e2]
    constructor
    · intro h r u _ hu s hs
      exact h _ u rfl hu s hs
    · intro h r u _ hu s hs
      exact h r0 u rfl hu s hs
  | sym n =>
    apply propext
    simp [RegGuard]

theorem regGuardI_mapRegs (f : Reg → Reg) (i : MInst) (us : List CV) :
    RegGuardI P (i.mapRegs f) us = RegGuardI P i us := by
  cases i with
  | call info => exact regGuard_mapRegs f info us
  | tryCall info ti => exact regGuard_mapRegs f info us
  | _ => rfl

theorem regGuardI_setTargets {i i' : MInst} {ls : List Label} (h : MInst.setTargets i ls = some i')
    (us : List CV) : RegGuardI P i' us = RegGuardI P i us := by
  unfold MInst.setTargets at h
  split at h
  all_goals first
    | (cases h; rfl)
    | (split at h
       · cases h; rfl
       · cases h)
    | cases h

/-- `DriverSemG` of the base semantics gives that of the guarded one. -/
theorem Driver.DriverSemG.regG (h : DriverSemG sem) : DriverSemG (Backend.Proof.regG P sem) where
  jump := fun l w => by rw [regG_of (i := .jump l) trivial]; exact h.jump l w
  rename := fun g gn hg i => by
    funext us w
    unfold Backend.Proof.regG
    have e := regGuardI_mapRegs (P := P) g i us
    by_cases hc : RegGuardI P i us
    · rw [if_pos (e ▸ hc), if_pos hc, h.rename g gn hg i]
    · rw [if_neg (e ▸ hc), if_neg hc]
  retarget := fun i ls i' hs => by
    funext us w
    unfold Backend.Proof.regG
    have e := regGuardI_setTargets (P := P) hs us
    by_cases hc : RegGuardI P i us
    · rw [if_pos (e ▸ hc), if_pos hc, h.retarget i ls i' hs]
    · rw [if_neg (e ▸ hc), if_neg hc]

end

/-- `DriverSem` of the base semantics gives that of the guarded one. -/
theorem Driver.DriverSem.regG {P : BitVec 64 → Clif.Signature → Prop} {sem : Sem} (h : DriverSem sem) :
    DriverSem (Backend.Proof.regG P sem) :=
  { h.toDriverSemG.regG with
    args := fun ds w => by rw [regG_of (i := .args ds) trivial]; exact h.args ds w }

section
variable {P : BitVec 64 → Clif.Signature → Prop} {sem : Sem} {F : BitVec 64 → Prop}

/-- The forms `ispec` specifies are no calls: the register guard holds there. -/
theorem regGuardI_of_ispec {i : MInst} {us : List CV} {w : Arm.ArmState}
    {r : List CV × Arm.ArmState × Ctl} (h : ispec i us w = some r) : RegGuardI P i us := by
  unfold RegGuardI
  split
  all_goals first
    | trivial
    | (simp [ispec] at h)

theorem Refines.regG (h : Refines F sem) : Refines F (Backend.Proof.regG P sem) := by
  intro i us w outs w' ctl hs
  obtain ⟨w'', h1, h2⟩ := h i us w outs w' hs
  exact ⟨w'', by rw [regG_of (regGuardI_of_ispec hs)]; exact h1, h2⟩

section NC
variable {W : Type} {sem : ISem CV W} {us : List CV} {w : W}

@[simp] theorem regG_load {op : LoadOp} {rd : Reg} {am : AMode} {fl : Clif.MemFlags} :
    Backend.Proof.regG P sem (.load op rd am fl) us w = sem (.load op rd am fl) us w :=
  regG_of trivial
@[simp] theorem regG_store {op : StoreOp} {rd : Reg} {am : AMode} {fl : Clif.MemFlags} :
    Backend.Proof.regG P sem (.store op rd am fl) us w = sem (.store op rd am fl) us w :=
  regG_of trivial
@[simp] theorem regG_loadAddr {rd : Reg} {am : AMode} :
    Backend.Proof.regG P sem (.loadAddr rd am) us w = sem (.loadAddr rd am) us w :=
  regG_of trivial
@[simp] theorem regG_loadExtNameGot {rd : Reg} {n : String} :
    Backend.Proof.regG P sem (.loadExtNameGot rd n) us w = sem (.loadExtNameGot rd n) us w :=
  regG_of trivial
@[simp] theorem regG_loadAcquire {ty : CTy} {rt rn : Reg} {fl : Clif.MemFlags} :
    Backend.Proof.regG P sem (.loadAcquire ty rt rn fl) us w = sem (.loadAcquire ty rt rn fl) us w :=
  regG_of trivial
@[simp] theorem regG_storeRelease {ty : CTy} {rt rn : Reg} {fl : Clif.MemFlags} :
    Backend.Proof.regG P sem (.storeRelease ty rt rn fl) us w =
      sem (.storeRelease ty rt rn fl) us w :=
  regG_of trivial
@[simp] theorem regG_atomicRmwLoop {ty : CTy} {op : AtomicRmwLoopOp} {fl : Clif.MemFlags}
    {a o1 o2 s1 s2 : Reg} :
    Backend.Proof.regG P sem (.atomicRmwLoop ty op fl a o1 o2 s1 s2) us w =
      sem (.atomicRmwLoop ty op fl a o1 o2 s1 s2) us w :=
  regG_of trivial
@[simp] theorem regG_atomicCasLoop {ty : CTy} {fl : Clif.MemFlags} {a e r o s : Reg} :
    Backend.Proof.regG P sem (.atomicCasLoop ty fl a e r o s) us w =
      sem (.atomicCasLoop ty fl a e r o s) us w :=
  regG_of trivial
@[simp] theorem regG_elfTlsGetAddr {n : String} {rd tmp : Reg} :
    Backend.Proof.regG P sem (.elfTlsGetAddr n rd tmp) us w = sem (.elfTlsGetAddr n rd tmp) us w :=
  regG_of trivial
@[simp] theorem regG_fpuLoad {sz : ScalarSize} {rd : Reg} {am : AMode} {fl : Clif.MemFlags} :
    Backend.Proof.regG P sem (.fpuLoad sz rd am fl) us w = sem (.fpuLoad sz rd am fl) us w :=
  regG_of trivial
@[simp] theorem regG_fpuStore {sz : ScalarSize} {rd : Reg} {am : AMode} {fl : Clif.MemFlags} :
    Backend.Proof.regG P sem (.fpuStore sz rd am fl) us w = sem (.fpuStore sz rd am fl) us w :=
  regG_of trivial

end NC

theorem MemRefines.regG {sb : Nat} {syms : String → Option Nat} (h : MemRefines F sb syms sem) :
    MemRefines F sb syms (Backend.Proof.regG P sem) := by
  simpa only [MemRefines, regG_load, regG_store, regG_loadAddr, regG_loadExtNameGot,
    regG_loadAcquire, regG_storeRelease, regG_atomicRmwLoop, regG_atomicCasLoop,
    regG_elfTlsGetAddr] using h

theorem MemRefinesR.regG {Rd : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (h : MemRefinesR Rd F sb syms sem) : MemRefinesR Rd F sb syms (Backend.Proof.regG P sem) := by
  simpa only [MemRefinesR, regG_load, regG_store, regG_loadAddr, regG_loadExtNameGot,
    regG_loadAcquire, regG_storeRelease, regG_atomicRmwLoop, regG_atomicCasLoop,
    regG_elfTlsGetAddr] using h

theorem MemRefinesFP.regG {Rd : BitVec 64 → Prop} {sb : Nat} (h : MemRefinesFP Rd F sb sem) :
    MemRefinesFP Rd F sb (Backend.Proof.regG P sem) := by
  simpa only [MemRefinesFP, regG_fpuLoad, regG_fpuStore] using h

theorem PoolRefinesFP.regG (h : PoolRefinesFP F sem) :
    PoolRefinesFP F (Backend.Proof.regG P sem) := by
  simpa only [PoolRefinesFP, regG_fpuLoad] using h

end

/-! ## The call contracts with registers -/

/-- **The functions at a GOT callee's address have its registers**: for every non-colocated
extern of `exts` (called through the GOT, `blr` of its address `addr`), every function `P`
places at that address has the extern's parameter registers and return classes. -/
def RegCompatGot (P : BitVec 64 → Clif.Signature → Prop) (exts : List Clif.ExtFunc)
    (addr : String → BitVec 64) : Prop :=
  ∀ ext ∈ exts, ext.colocated = false → ∀ s, P (addr ext.name) s → SigRegsEq s ext.sig

/-- **The functions at an indirect callee's address have the site's registers**: for every
call-site signature `sig ∈ sigs` and every extern `n` an indirect call of `sig` may enter (its
signature, if known, `abiMatch`es), every function `P` places at `n`'s address (`syms`) has the
parameter registers and return classes of `sig`. -/
def RegCompatInd (P : BitVec 64 → Clif.Signature → Prop) (env : Clif.Env)
    (sigs : List Clif.Signature) (syms : String → Option Nat) : Prop :=
  ∀ sig ∈ sigs, ∀ (n : String) g, env.extern n = some g →
    (∀ s, env.sigOf n = some s → sig.abiMatch s = true) →
    ∀ b, syms n = some b → ∀ s, P (BitVec.ofNat 64 b) s → SigRegsEq s sig

theorem lo64_ofX_r (x : BitVec 64) : lo64 (ofX x) = x := by
  simp [lo64, ofX, BitVec.setWidth_setWidth_of_le]

section
variable {P : BitVec 64 → Clif.Signature → Prop}
  {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {F : BitVec 64 → Prop}
  {env : Clif.Env} {MR : MemRelT} {sem : Sem}

/-- **The pinned callee contract of the base semantics gives the one with registers of the
guarded semantics**, when the base semantics' GOT loads give the addresses `addr` and the
functions at a non-colocated extern's address have its registers (`RegCompatGot`). -/
theorem CallsRefineP.regG {exts : List Clif.ExtFunc} (h : CallsRefineP Pc F env exts MR sem)
    {addr : String → BitVec 64}
    (haddr : ∀ rd n w r, sem (.loadExtNameGot rd n) [] w = some r → r.1 = [ofX (addr n)])
    (hP : RegCompatGot P exts addr) : CallsRefinePR Pc F env exts MR (Backend.Proof.regG P sem) := by
  obtain ⟨sym, h1, h2, h3⟩ := h
  have hsym : ∀ (n : String) (w : Arm.ArmState), sym n = addr n := by
    intro n w
    obtain ⟨w', e, -⟩ := h1 (.vreg 0 .int) n w
    have := haddr (.vreg 0 .int) n w _ e
    simp only [List.cons.injEq, and_true] at this
    have := congrArg lo64 this
    rwa [lo64_ofX_r, lo64_ofX_r] at this
  have hguard : ∀ ext ∈ exts, ∀ (w : Arm.ArmState) (dest : CallDest) (us ds : List (Reg × Reg))
      (uses args : List CV),
      (∃ r, dest = .reg r ∧ ext.colocated = false ∧ uses = ofX (sym ext.name) :: args ∧
        SiteRegsR ext.sig us ds) → RegGuard P ⟨dest, us, ds⟩ uses := by
    rintro ext hin w dest us ds uses args ⟨r, rfl, hcol, rfl, hs⟩
    unfold RegGuard
    intro r' u _ hu s hPs
    simp only [List.head?_cons, Option.some.injEq] at hu
    subst hu
    rw [lo64_ofX_r, hsym ext.name w] at hPs
    exact hs.of_sigRegsEq (hP ext hin hcol s hPs)
  refine ⟨sym, fun rd n w => ?_, fun ext hin g sl cm w dest us ds uses args vals rvals cm' a1 a2 =>
    ?_, fun ext hin g sl cm w dest us ds ti uses args vals rvals cm' a1 a2 => ?_⟩
  · rw [regG_of (i := .loadExtNameGot rd n) trivial]
    exact h1 rd n w
  · have a2' : dest = .sym ext.name ∧ uses = args ∨
        ∃ r, dest = .reg r ∧ ext.colocated = false ∧ uses = ofX (sym ext.name) :: args := by
      rcases a2 with a2 | ⟨r, e1, e2, e3, -⟩
      · exact .inl a2
      · exact .inr ⟨r, e1, e2, e3⟩
    have hg : RegGuardI P (.call ⟨dest, us, ds⟩) uses := by
      rcases a2 with ⟨rfl, -⟩ | a2
      · exact fun r u hd => by cases hd
      · exact hguard ext hin w dest us ds uses args a2
    intro a3 a4 a5 a6 a7 a8
    rw [regG_of hg]
    exact h2 ext hin g sl cm w dest us ds uses args vals rvals cm' a1 a2' a3 a4 a5 a6 a7 a8
  · have a2' : dest = .sym ext.name ∧ uses = args ∨
        ∃ r, dest = .reg r ∧ ext.colocated = false ∧ uses = ofX (sym ext.name) :: args := by
      rcases a2 with a2 | ⟨r, e1, e2, e3, -⟩
      · exact .inl a2
      · exact .inr ⟨r, e1, e2, e3⟩
    have hg : RegGuardI P (.tryCall ⟨dest, us, ds⟩ ti) uses := by
      rcases a2 with ⟨rfl, -⟩ | a2
      · exact fun r u hd => by cases hd
      · exact hguard ext hin w dest us ds uses args a2
    intro a3 a4 a5 a6 a7 a8 a9
    rw [regG_of hg]
    exact h3 ext hin g sl cm w dest us ds ti uses args vals rvals cm' a1 a2' a3 a4 a5 a6 a7 a8 a9

/-- **The pinned indirect-call contract of the base semantics gives the one with registers of the
guarded semantics**, when the memory relation's CLIF memory has the link-time symbols `syms` and
the functions at an indirect callee's address have the site's registers (`RegCompatInd`). -/
theorem IndCallsRefineP.regG {sigs : List Clif.Signature} (h : IndCallsRefineP Pc env sigs MR sem)
    {syms : String → Option Nat} (hMRs : ∀ sl cm w, MR sl cm w → cm.symbols = syms)
    (hP : RegCompatInd P env sigs syms) : IndCallsRefinePR Pc env sigs MR (Backend.Proof.regG P sem) := by
  have hguard : ∀ sig ∈ sigs, ∀ (n : String) g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem)
      (w : Arm.ArmState) (a : Nat) (r : Reg) (us ds : List (Reg × Reg)) (u : CV) (args : List CV),
      env.extern n = some g → (∀ s, env.sigOf n = some s → sig.abiMatch s = true) →
      cm.symbols n = some a → lo64 u = BitVec.ofNat 64 a → MR sl cm w → SiteRegsR sig us ds →
      RegGuard P ⟨.reg r, us, ds⟩ (u :: args) := by
    intro sig hin n g sl cm w a r us ds u args hg hsg ha hu hmr hs
    unfold RegGuard
    intro r' u' _ hu' s hPs
    simp only [List.head?_cons, Option.some.injEq] at hu'
    subst hu'
    rw [hu] at hPs
    exact hs.of_sigRegsEq (hP sig hin n g hg hsg a (by rw [← hMRs sl cm w hmr]; exact ha) s hPs)
  refine ⟨fun sig hin n g sl cm w a r us ds u args vals rvals cm' a1 a1' a2 a3 a4 a5 a7 a8 a9
    a10 a11 a12 => ?_, fun sig hin n g sl cm w a r us ds ti u args vals rvals cm' a1 a1' a2 a3 a4
    a0 a5 a7 a8 a9 a10 a11 a12 => ?_⟩
  · have hg : RegGuardI P (.call ⟨.reg r, us, ds⟩) (u :: args) :=
      hguard sig hin n g sl cm w a r us ds u args a1 a1' a2 a3 a7 a12
    rw [regG_of hg]
    exact h.1 sig hin n g sl cm w a r us ds u args vals rvals cm' a1 a1' a2 a3 a4 a5 a7 a8 a9 a10 a11
  · have hg : RegGuardI P (.tryCall ⟨.reg r, us, ds⟩ ti) (u :: args) :=
      hguard sig hin n g sl cm w a r us ds u args a1 a1' a2 a3 a7 a12
    rw [regG_of hg]
    exact h.2 sig hin n g sl cm w a r us ds ti u args vals rvals cm' a1 a1' a2 a3 a4 a0 a5 a7 a8 a9
      a10 a11

end

/-! ## `csem` with the register guard -/

section
variable {P : BitVec 64 → Clif.Signature → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
  {X : ExtSem}

theorem driverSem_csemR (P : BitVec 64 → Clif.Signature → Prop) (F : BitVec 64 → Prop)
    (ctx : FnCtx) (X : ExtSem) : DriverSem (csemR P F ctx X) :=
  (driverSem_csem F ctx X).regG

theorem refines_csemR (P : BitVec 64 → Clif.Signature → Prop) (F : BitVec 64 → Prop)
    (ctx : FnCtx) (X : ExtSem) : Refines F (csemR P F ctx X) :=
  (refines_csem (F := F) (ctx := ctx) X).regG

/-- **`CallsRefinePR` for `csemR`**, from the external contract and the registers of the
functions at the GOT callees' addresses. -/
theorem callsRefinePR_csemR {env : Clif.Env} {exts : List Clif.ExtFunc} {MR : MemRelT}
    (hX : XCallsOk env exts MR X) (hP : RegCompatGot P exts (fun n => X.sym n 0))
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) :
    CallsRefinePR Pc F env exts MR (csemR P F ctx X) :=
  ((callsRefine_csem (F := F) (ctx := ctx) hX).toP Pc).regG
    (fun rd n w r h => by simp only [csem, Option.some.injEq] at h; rw [← h]) hP

/-- **`IndCallsRefinePR` for `csemR`**, from the external contract, the link-time symbol
addresses and the registers of the functions at the indirect callees' addresses. -/
theorem indCallsRefinePR_csemR {env : Clif.Env} {sigs : List Clif.Signature} {MR : MemRelT}
    {syms : String → Option Nat} (hX : XCallsIndOk env sigs MR X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRs : ∀ sl cm w, MR sl cm w → cm.symbols = syms) (hP : RegCompatInd P env sigs syms)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) :
    IndCallsRefinePR Pc env sigs MR (csemR P F ctx X) :=
  ((indCallsRefine_csem (F := F) (ctx := ctx) hX hsym hMRs).toP Pc).regG hMRs hP

end

end Backend.Proof
