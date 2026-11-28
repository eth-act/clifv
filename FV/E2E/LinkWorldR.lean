import FV.E2E.LinkWorld
import FV.E2E.DeadCleanupGot
import FV.E2E.DeadCleanupRegLevelX
import FV.E2E.RegLevelDriverSemR
import FV.Backend.Proof.LowerContractR
import FV.Backend.Proof.IselCtlCallPR

/-!
# The per-function theorem with the final world at the register-guarded semantics
(#753, stage R2)

`LinkWorld` at the register-guarded VCode semantics (`csemR P`/`csemVR P`, `RegLevelDriverSemR`):

* `CalleeOkGR`, `CalleeTryOkGR`: `CalleeOkG`, `CalleeTryOkG` whose call obligation is over the
  steps of `csemVR P gv` (the calls with the registers of every function `P` places at their
  target); the contracts without the guard give them (`CalleeOkG.r`, `CalleeTryOkG.r`), and at
  code without call sites they give those (`CalleeOkGR.toG`, `CalleeTryOkGR.toG`);
* `ActEntryR P`: `ActEntry` with `CalleeOkGR P`/`CalleeTryOkGR P` (`ActEntry.toR`;
  `ActEntryR.toActEntry` at code without call sites, `NoCallSites`);
* `RegLevelWorldR`, `RegLevelWorldXR`, `RegLevelWorldValueR`, `RegLevelWorldXValueR`, bundled in
  `RegLevelR`: `regLevelCorrect_world{,X}{,_value}` at `csemVR P gv` (`valueSemVR P gv`) under
  `CalleeOkGR P`/`CalleeTryOkGR P`, M6 for the register-guarded semantics (stage R3 of #753
  proves it); the world theorems of stage R2 take it as a premise;
* `vReturns_gotVR`, `vTraps_gotVR`, `vReturns_gotV_valueR`, `vTraps_gotV_valueR`: `GotFlow`'s
  lifts for the register-guarded semantics;
* `iselSim_relWR`, `backend_correct_worldR`: `iselSim_relW`, `backend_correct_world` at `csemR P`
  under `RegCompatGot`/`RegCompatInd` (the functions at the GOT callees' and indirect callees'
  addresses have their declarations' registers), for `ActEntryR P`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

set_option autoImplicit false

/-! ## The callee contracts over the register-guarded semantics -/

/-- `valueSemV` with the register guard. -/
noncomputable def valueSemVR (P : BitVec 64 → Clif.Signature → Prop) (gv : Nat → String → Prop)
    (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) : Sem :=
  regG P (valueSemV gv F ctx X)

/-- **`CalleeOkG` over the register-guarded semantics**: the call obligation only for the calls of
`csemVR P gv`. -/
structure CalleeOkGR (P : BitVec 64 → Clif.Signature → Prop) (F : BitVec 64 → Prop) (K : Nat)
    (G : BitVec 64 → Prop) (s0 : Arm.ArmState) (Pc : BitVec 64 → MInst → Prop) (X : ExtSem)
    (H : ArmHooks) (S : CallInfo → Prop) (gv : Nat → String → Prop) : Prop where
  os : ∀ ctx info, S info →
    CallSoundCtlG F K G s0 Pc (callExec H) (csemVR P gv F ctx X) (.call info) .next
  pc : ∀ d s, Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
    Arm.r .PC (H.call d s) = Arm.r .PC s + 4
  ext : ∀ d uses w outs w', X.call d uses w = some (outs, w') → Arm.r .ERR w = .None →
    Arm.r .ERR w' = .None ∧ w'.program = w.program

/-- **`CalleeTryOkG` over the register-guarded semantics.** -/
def CalleeTryOkGR (P : BitVec 64 → Clif.Signature → Prop) (F : BitVec 64 → Prop) (K : Nat)
    (G : BitVec 64 → Prop) (s0 : Arm.ArmState) (Pc : BitVec 64 → MInst → Prop) (X : ExtSem)
    (H : ArmHooks) (S : CallInfo → TryInfo → Prop) (gv : Nat → String → Prop) : Prop :=
  ∀ (ctx : FnCtx) (info : CallInfo) (ti : TryInfo), S info ti → ∀ (c : CheckCtx) (wh : String)
    (ops : Array Operand) (regs : Array Reg) (i' : MInst) (s w : Arm.ArmState) (outs : List CV)
    (w' s' : Arm.ArmState),
    K ≤ (spOf s).toNat → (∀ a, StackBelow K (spOf s) a → F a) →
    (∀ a, G a → s.mem a = s0.mem a) →
    (MInst.tryCall info ti).operands = .ok ops →
    c.checkStatic wh ops (regs.map .reg) (MInst.tryCall info ti).clobbers = .ok () →
    (MInst.tryCall info ti).assign regs = .ok i' → Pc (Arm.r .PC s) i' →
    SameWorld F s w → Arm.CheckSPAlignment s → Arm.r .ERR s = .None →
    csemVR P gv F ctx X (.tryCall info ti) (useVals ops regs s) w =
      some (outs, w', .goto ti.handlers.length) →
    callExec H i' s = some s' →
    ∀ p ∈ (defRegs ops regs outs).take ti.rets, regVal s' p.1.2 = p.2

section
variable {P : BitVec 64 → Clif.Signature → Prop} {F : BitVec 64 → Prop} {K : Nat}
  {G : BitVec 64 → Prop} {s0 : Arm.ArmState} {Pc : BitVec 64 → MInst → Prop} {X : ExtSem}
  {H : ArmHooks} {gv : Nat → String → Prop}

/-- `CallSoundCtlG` of a semantics gives that of its register-guarded form. -/
theorem CallSoundCtlG.regG {exec : MInst → Arm.ArmState → Option Arm.ArmState} {sem : Sem}
    {i : MInst} {ctl : Ctl} (h : CallSoundCtlG F K G s0 Pc exec sem i ctl) :
    CallSoundCtlG F K G s0 Pc exec (Backend.Proof.regG P sem) i ctl :=
  fun s h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg hp hw hal herr hsem =>
    h s h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg hp hw hal herr (regG_sub hsem)

theorem CalleeOkG.r {S : CallInfo → Prop} (h : CalleeOkG F K G s0 Pc X H S gv) :
    CalleeOkGR P F K G s0 Pc X H S gv :=
  ⟨fun ctx info hs => CallSoundCtlG.regG (h.os ctx info hs), h.pc, h.ext⟩

theorem CalleeTryOkG.r {S : CallInfo → TryInfo → Prop} (h : CalleeTryOkG F K G s0 Pc X H S gv) :
    CalleeTryOkGR P F K G s0 Pc X H S gv :=
  fun ctx info ti hS c wh ops regs i' s w outs w' s' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hsem a12 =>
    h ctx info ti hS c wh ops regs i' s w outs w' s' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
      (regG_sub hsem) a12

/-- At code without call sites the register-guarded callee contract is `CalleeOkG`. -/
theorem CalleeOkGR.toG {S : CallInfo → Prop} (h : CalleeOkGR P F K G s0 Pc X H S gv)
    (hS : ∀ info, ¬ S info) : CalleeOkG F K G s0 Pc X H S gv :=
  ⟨fun _ info hs => absurd hs (hS info), h.pc, h.ext⟩

theorem CalleeTryOkGR.toG {S : CallInfo → TryInfo → Prop} (hS : ∀ info ti, ¬ S info ti) :
    CalleeTryOkG F K G s0 Pc X H S gv :=
  fun _ info ti hs => absurd hs (hS info ti)

end

/-- `vc` has no call sites (no `call`, no `try_call`). -/
def NoCallSites (vc : VCode) : Prop := ∀ info, ¬ vc.CallSite info

/-- **`ActEntry` with the register-guarded callee contracts** (`CalleeOkGR P`, `CalleeTryOkGR P`). -/
structure ActEntryR (P : BitVec 64 → Clif.Signature → Prop) (vcp : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) (K : Nat) (F G : BitVec 64 → Prop) (X : ExtSem) (H : ArmHooks)
    (base ra : BitVec 64) (s w₀ : Arm.ArmState) : Prop where
  abi : AbiCall fb base ra s
  stack : StackAvail K af s
  gfree : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a
  hF : frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s = F
  calls : CalleeOkGR P F K G s (CallAt fa base) X H vcp.CallSite (GotV vcp)
  tries : vcp.hasTryCall = true → CalleeTryOkGR P F K G s (CallAt fa base) X H vcp.TrySite (GotV vcp)
  tls : vcp.hasTls = true → TlsOk F K X H
  body : BodyEntryW F vcp.EntryArg af s w₀

section
variable {P : BitVec 64 → Clif.Signature → Prop} {vcp : VCode} {rf : RFunc} {af : AFunc}
  {fa : FnAsm} {fb : FnBin} {K : Nat} {F G : BitVec 64 → Prop} {X : ExtSem} {H : ArmHooks}
  {base ra : BitVec 64} {s w₀ : Arm.ArmState}

theorem ActEntry.toR (h : ActEntry vcp rf af fa fb K F G X H base ra s w₀) :
    ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ :=
  ⟨h.abi, h.stack, h.gfree, h.hF, CalleeOkG.r h.calls, fun ht => CalleeTryOkG.r (h.tries ht), h.tls,
    h.body⟩

/-- **At code without call sites `ActEntryR` is `ActEntry`.** -/
theorem ActEntryR.toActEntry (h : ActEntryR P vcp rf af fa fb K F G X H base ra s w₀)
    (hnc : NoCallSites vcp) : ActEntry vcp rf af fa fb K F G X H base ra s w₀ :=
  ⟨h.abi, h.stack, h.gfree, h.hF, h.calls.toG hnc,
    fun _ => CalleeTryOkGR.toG fun info ti ⟨b, vb, k, hvb, hk⟩ => hnc info ⟨b, vb, k, hvb, .inr ⟨ti, hk⟩⟩,
    h.tls, h.body⟩

end

/-! ## M6 for the register-guarded semantics (stage R3's statements) -/

/-- `regLevelCorrect_world` at the register-guarded semantics `csemVR P gv` under the callee contracts with the register guard (`CalleeOkGR`, `CalleeTryOkGR`): M6 for `csemVR`, stage R3 of #753. -/
def RegLevelWorldR : Prop :=
  ∀ {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop} {P : BitVec 64 → Clif.Signature → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : CalleeOkGR P (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkGR P (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K X H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV),
    (∀ us vals w, VReturns vcp (csemVR P gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us vals w →
      ∃ n, ArmRet ra s (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX X H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a → (E2E.runX (ArmStepX X H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX X H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX X H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX X H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX X H fa) i s)) →
          spv (E2E.runX (ArmStepX X H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
    (∀ c, VTraps vcp (csemVR P gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX X H fa) n s))

/-- `regLevelCorrect_worldX` at `csemVR P gv` under `CalleeOkGR`/`CalleeTryOkGR` (R3 of #753). -/
def RegLevelWorldXR : Prop :=
  ∀ {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop} {P : BitVec 64 → Clif.Signature → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : CalleeOkGR P (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkGR P (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K X H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV),
    (∀ us vals w, VReturns vcp (csemVR P gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us vals w →
      ∃ n, (ArmRet ra s (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX X H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a → (E2E.runX (ArmStepX X H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX X H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX X H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX X H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX X H fa) i s)) →
          spv (E2E.runX (ArmStepX X H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
        ∀ i < n, actGoodX vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
    (∀ c, VTraps vcp (csemVR P gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ i < n, actGoodX vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
        ∀ m, Arm.r .ERR (E2E.runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None)

/-- `regLevelCorrect_world_value` at `valueSemVR P gv` under `CalleeOkGR`/`CalleeTryOkGR` (R3 of #753). -/
def RegLevelWorldValueR : Prop :=
  ∀ {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : AllocAF vcp rf af)
    (hleaf : af.frame = false → fa.leafChk = true)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop} {P : BitVec 64 → Clif.Signature → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : CalleeOkGR P (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkGR P (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K X H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV),
    (∀ us vals w, VReturns vcp (valueSemVR P gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us vals w →
      ∃ n, ArmRet ra s (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX X H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a → (E2E.runX (ArmStepX X H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX X H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX X H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX X H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX X H fa) i s)) →
          spv (E2E.runX (ArmStepX X H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
    (∀ c, VTraps vcp (valueSemVR P gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX X H fa) n s))

/-- `regLevelCorrect_worldX_value` at `valueSemVR P gv` under `CalleeOkGR`/`CalleeTryOkGR` (R3 of #753). -/
def RegLevelWorldXValueR : Prop :=
  ∀ {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop} {P : BitVec 64 → Clif.Signature → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : CalleeOkGR P (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkGR P (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K X H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV),
    (∀ us vals w, VReturns vcp (valueSemVR P gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us vals w →
      ∃ n, (ArmRet ra s (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX X H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a → (E2E.runX (ArmStepX X H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX X H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX X H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX X H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX X H fa) i s)) →
          spv (E2E.runX (ArmStepX X H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
        ∀ i < n, actGoodX vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
    (∀ c, VTraps vcp (valueSemVR P gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ i < n, actGoodX vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
        ∀ m, Arm.r .ERR (E2E.runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None)

/-- **M6 for the register-guarded semantics** (the four statements of stage R3 of #753). -/
structure RegLevelR : Prop where
  world : RegLevelWorldR
  worldX : RegLevelWorldXR
  world_value : RegLevelWorldValueR
  worldX_value : RegLevelWorldXValueR

/-! ## Calls through the GOT under the register guard -/

section
variable {vc : VCode} {P : BitVec 64 → Clif.Signature → Prop} {F : BitVec 64 → Prop}
  {ctx : FnCtx} {X : ExtSem}

theorem vstep_regG_sub {sem : Sem} {c c' : VConf CV Arm.ArmState}
    (h : VStep vc (regG P sem) c c') : VStep vc sem c c' := by
  cases h with
  | step hvb hi hops hsem hlen hnext => exact .step hvb hi hops (regG_sub hsem) hlen hnext

/-- A step of `sem'` from a configuration with a step of the guarded `regG P sem` is one of the
guarded `regG P sem'` (the guard reads only the instruction and its uses). -/
theorem vstep_regG_lift {sem sem' : Sem} {s : VState CV Arm.ArmState} {c c' : VConf CV Arm.ArmState}
    (h : VStep vc (regG P sem) (.run s) c) (h' : VStep vc sem' (.run s) c') :
    VStep vc (regG P sem') (.run s) c' := by
  cases h with
  | @step b k ρ w vb i ops outs w' ctl _ hvb hi hops hsem hlen hnext =>
    cases h' with
    | @step _ _ _ _ vb2 i2 ops2 outs2 w2 ctl2 _ hvb2 hi2 hops2 hsem2 hlen2 hnext2 =>
      rw [hvb] at hvb2; cases hvb2
      rw [hi] at hi2; cases hi2
      rw [hops] at hops2; cases hops2
      exact .step hvb hi hops (by rw [regG_of (regG_inv hsem).1]; exact hsem2) hlen2 hnext2

/-- Runs of `semA` along an invariant `I` that every step of `semA` keeps and turns into a step of
`semB` are runs of `semB`. -/
theorem star_lift_inv {semA semB : Sem} {I : VState CV Arm.ArmState → Prop}
    (hstep : ∀ s c', I s → VStep vc semA (.run s) c' →
      VStep vc semB (.run s) c' ∧ ∀ s', c' = .run s' → I s')
    {s s' : VState CV Arm.ArmState} (hI : I s) (h : Star (VStep vc semA) (.run s) (.run s')) :
    Star (VStep vc semB) (.run s) (.run s') ∧ I s' := by
  generalize ha : (VConf.run s : VConf CV Arm.ArmState) = a at h
  generalize hb : (VConf.run s' : VConf CV Arm.ArmState) = b at h
  induction h generalizing s with
  | refl => subst ha; cases hb; exact ⟨.refl _, hI⟩
  | @step a1 a2 a3 h1 h2 ih =>
    subst ha
    cases a2 with
    | run s2 =>
      obtain ⟨h1', hI2⟩ := hstep _ _ hI h1
      obtain ⟨h2', hI'⟩ := ih (hI2 s2 rfl) rfl hb
      exact ⟨.step h1' h2', hI'⟩
    | ret vals w => subst hb; cases h2 with | step h _ => cases h
    | halt w => subst hb; cases h2 with | step h _ => cases h

theorem gotInv_stepR {s : VState CV Arm.ArmState} {c' : VConf CV Arm.ArmState}
    (hI : GotInv vc X s) (h : VStep vc (csemR P F ctx X) (.run s) c') :
    VStep vc (csemVR P (GotV vc) F ctx X) (.run s) c' ∧ ∀ s', c' = .run s' → GotInv vc X s' := by
  obtain ⟨h1, h2⟩ := gotInv_step hI (vstep_regG_sub h)
  exact ⟨vstep_regG_lift h h1, h2⟩

theorem gotInv_step_valueR {s : VState CV Arm.ArmState} {c' : VConf CV Arm.ArmState}
    (hI : GotInv vc X s) (h : VStep vc (regG P (Backend.DeadCleanup.valueSem F ctx X)) (.run s) c') :
    VStep vc (valueSemVR P (GotV vc) F ctx X) (.run s) c' ∧ ∀ s', c' = .run s' → GotInv vc X s' := by
  obtain ⟨h1, h2⟩ := gotInv_step_value hI (vstep_regG_sub h)
  exact ⟨vstep_regG_lift h h1, h2⟩

/-- **A returning VCode run of `csemR P` is one of `csemVR P (GotV vc)`.** -/
theorem vReturns_gotVR {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} {us : List (Reg × Reg)}
    {vals : List CV} {w : Arm.ArmState} (h : VReturns vc (csemR P F ctx X) ρ₀ w₀ us vals w) :
    VReturns vc (csemVR P (GotV vc) F ctx X) ρ₀ w₀ us vals w := by
  obtain ⟨b, k, ρ, w₁, vb, ops, outs, hs, hvb, hk, hops, hvals, hsem⟩ := h
  obtain ⟨hs', -⟩ := star_lift_inv (fun _ _ hI h => gotInv_stepR hI h) (gotInv_entry vc X ρ₀ w₀) hs
  refine ⟨b, k, ρ, w₁, vb, ops, outs, hs', hvb, hk, hops, hvals, ?_⟩
  have h0 : csem F ctx X (.rets us) vals w₁ = some (outs, w, .ret) := regG_sub hsem
  show regG P (csemV (GotV vc) F ctx X) (.rets us) vals w₁ = some (outs, w, .ret)
  rw [regG_of (regG_inv hsem).1, csemV_eq fun info h => by rcases h with h | ⟨_, h⟩ <;> cases h]
  exact h0

/-- **A trapping VCode run of `csemR P` is one of `csemVR P (GotV vc)`.** -/
theorem vTraps_gotVR {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} {c : Clif.TrapCode}
    (h : VTraps vc (csemR P F ctx X) ρ₀ w₀ c) : VTraps vc (csemVR P (GotV vc) F ctx X) ρ₀ w₀ c := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, hvb, hi, hops, hsem, htc⟩ := h
  obtain ⟨hs', -⟩ := star_lift_inv (fun _ _ hI h => gotInv_stepR hI h) (gotInv_entry vc X ρ₀ w₀) hs
  refine ⟨b, k, ρ, w, vb, i, ops, outs, w', hs', hvb, hi, hops, ?_, htc⟩
  have h0 : csem F ctx X i (vuses ops ρ) w = some (outs, w', .halt) := regG_sub hsem
  obtain ⟨-, hform⟩ := csem_halt h0
  show regG P (csemV (GotV vc) F ctx X) i (vuses ops ρ) w = some (outs, w', .halt)
  rw [regG_of (regG_inv hsem).1, csemV_eq fun info h => by
    rcases h with rfl | ⟨_, rfl⟩ <;> rcases hform with ⟨_, e⟩ | ⟨_, _, e, _⟩ <;> cases e]
  exact h0

/-- **A returning VCode run of the register-guarded `valueSem` is one of `valueSemVR P (GotV vc)`.** -/
theorem vReturns_gotV_valueR {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} {us : List (Reg × Reg)}
    {vals : List CV} {w : Arm.ArmState}
    (h : VReturns vc (regG P (Backend.DeadCleanup.valueSem F ctx X)) ρ₀ w₀ us vals w) :
    VReturns vc (valueSemVR P (GotV vc) F ctx X) ρ₀ w₀ us vals w := by
  obtain ⟨b, k, ρ, w₁, vb, ops, outs, hs, hvb, hk, hops, hvals, hsem⟩ := h
  obtain ⟨hs', -⟩ := star_lift_inv (fun _ _ hI h => gotInv_step_valueR hI h)
    (gotInv_entry vc X ρ₀ w₀) hs
  refine ⟨b, k, ρ, w₁, vb, ops, outs, hs', hvb, hk, hops, hvals, ?_⟩
  have h0 := regG_sub hsem
  show regG P (valueSemV (GotV vc) F ctx X) (.rets us) vals w₁ = some (outs, w, .ret)
  rw [regG_of (regG_inv hsem).1]
  simp only [valueSemV, Backend.DeadCleanup.specForm, Backend.DeadCleanup.pureForm,
    Backend.DeadCleanup.cmpForm, Bool.false_or, ite_false]
  rw [csemV_eq fun info h => by rcases h with h | ⟨_, h⟩ <;> cases h]
  simpa only [Backend.DeadCleanup.valueSem, Backend.DeadCleanup.specForm,
    Backend.DeadCleanup.pureForm, Backend.DeadCleanup.cmpForm, Bool.false_or, ite_false] using h0

/-- **A trapping VCode run of the register-guarded `valueSem` is one of `valueSemVR P (GotV vc)`.** -/
theorem vTraps_gotV_valueR {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} {c : Clif.TrapCode}
    (h : VTraps vc (regG P (Backend.DeadCleanup.valueSem F ctx X)) ρ₀ w₀ c) :
    VTraps vc (valueSemVR P (GotV vc) F ctx X) ρ₀ w₀ c := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, hvb, hi, hops, hsem, htc⟩ := h
  obtain ⟨hs', -⟩ := star_lift_inv (fun _ _ hI h => gotInv_step_valueR hI h)
    (gotInv_entry vc X ρ₀ w₀) hs
  refine ⟨b, k, ρ, w, vb, i, ops, outs, w', hs', hvb, hi, hops, ?_, htc⟩
  have h0 := regG_sub hsem
  have hp : Backend.DeadCleanup.specForm i = false := by
    cases he : Backend.DeadCleanup.specForm i
    · rfl
    · have hs : mspec ctx.slotBase i (vuses ops ρ) w = some (outs, w', .halt) := by
        simpa [Backend.DeadCleanup.valueSem, he, vuses] using h0
      have hn := Backend.DeadCleanup.mspec_spec_next he hs
      cases hn
  have hsem0 : csem F ctx X i (vuses ops ρ) w = some (outs, w', .halt) := by
    simpa [Backend.DeadCleanup.valueSem, hp, vuses] using h0
  obtain ⟨-, hform⟩ := csem_halt hsem0
  show regG P (valueSemV (GotV vc) F ctx X) i (vuses ops ρ) w = some (outs, w', .halt)
  rw [regG_of (regG_inv hsem).1]
  simp only [valueSemV, hp, Bool.false_eq_true, ite_false]
  rw [csemV_eq fun info h => by
    rcases h with rfl | ⟨_, rfl⟩ <;> rcases hform with ⟨_, e⟩ | ⟨_, _, e, _⟩ <;> cases e]
  exact hsem0

end

/-! ## The world theorem at the register-guarded semantics -/

/-- **CLIF → VCode for the register-guarded `csemR P`** with a fixed set `F` of addresses outside
the world and the memory relation `RelW` (`iselSim_relW` under the call contracts with registers;
the functions `P` places at the GOT callees' and indirect callees' addresses have their
declarations' registers: `RegCompatGot`, `RegCompatInd`). -/
theorem iselSim_relWR {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64} {P : BitVec 64 → Clif.Signature → Prop}
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hPi : RegCompatInd P env (indSigs f) syms)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {args : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VReturns vc (csemR P F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us outs w ∧
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTraps vc (csemR P F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c') := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hRef : Refines F (csemR P F ⟨fa.k, af.slotBase⟩ X) := refines_csemR P F _ X
  have hmem : MemRefines F slotOff syms (csemR P F ⟨fa.k, af.slotBase⟩ X) :=
    (memRefines_csem _ _ X hslot hsym).regG
  have hcalls := callsRefinePR_csemR (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hX hPg
    (fun _ _ _ _ => True)
  have hicalls := indCallsRefinePR_csemR (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hXI hsym
    (fun _ _ _ h => h.1.1.symbols) hPi (fun _ _ _ _ => True)
  have houtB := outgoing_le_intBase hc
  have H : DriverHyp f vc ctx st0 R gn bl A (csemR P F ⟨fa.k, af.slotBase⟩ X) (RelW Γ f c) env p := {
    shape := hshape
    cert := hcert
    dsem := (driverSem_csemR P F ⟨fa.k, af.slotBase⟩ X).toDriverSemG
    insts := instCallsR_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrectPR
      indRulesCorrectPR memRulesCorrectR_program hRef (mrStable_relW Γ f c) hcalls hicalls hmem
      (outArgsOk_relW Γ f c) (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (indStack_mono (indStack_of_check hc.lowerOk) houtB)
      (memRelOk_relW Γ f c)
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef (mrStable_relW Γ f c)
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hc.lowerOk
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨_, tryCallsR_of_rules tryRulesCorrectPR tryUnmatchable hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) hcalls, tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCallsR_of_rules tryIndRulesCorrectPR tryIndUnmatchable hRef
      (mrStable_relW Γ f c) hmem (outArgsOk_relW Γ f c)
      (indStack_mono (indStack_of_check hc.lowerOk) houtB) hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := cfg_of_prepare hc.prepare }
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := by
    have hf := hce.func
    exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
        (hf ▸ hB),
      fun s c callee args et hr hs hb hT B hB =>
        htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
      fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
        htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
      fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
        htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩
  have hrun := driver_correct H (driverSem_csemR P F ⟨fa.k, af.slotBase⟩ X) hmem
    (mrStable_relW Γ f c) hB0 hce.callers hce.func rfl hbody hterm
    hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs hP fuel
  refine ⟨fun vals cm h => ?_, fun c' h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1.1 _)⟩
  · rw [h] at hrun
    exact hrun

/-- **The per-function theorem with the final world at the register-guarded semantics**
(`backend_correct_world` for activations with the register-guarded callee contracts,
`ActEntryR P`, given M6 for the register-guarded semantics, `RegLevelR`). -/
theorem backend_correct_worldR {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb) (hM6 : RegLevelR)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64} {P : BitVec 64 → Clif.Signature → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hPi : RegCompatInd P env (indSigs f) syms)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) := by
  have hI := iselSim_relWR hsub hc hX hXI hPg hPi hsym hslot (fun _ => 0) hcs hrel hargs htr fuel
  have hP := prepareCorrect_of_check (driverSem_csemR P F ⟨fa.k, af.slotBase⟩ X) hc.prepOk
    (fun _ => 0) w₀
  have hM6' : ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ → _ := fun H G base ra s he => by
    have h := hM6.world hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
      (K := K) (G := G) (gv := GotV vcp) (P := P) hcov he.abi he.stack he.gfree
      (by rw [he.hF]; exact he.calls)
      (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body)
      (fun _ => 0)
    rw [he.hF] at h
    exact h
  refine ⟨fun vals cm hrun => ?_, fun c' hrun H G base ra s he => ?_⟩
  · obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H G base ra s he => ?_⟩
    obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ :=
      (hM6' H G base ra s he).1 us outs w (vReturns_gotVR (hP.1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩
  · exact (hM6' H G base ra s he).2 c' (vTraps_gotVR (hP.2 c' (hI.2 c' hrun)))

end E2E
