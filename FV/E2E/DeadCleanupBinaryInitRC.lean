import FV.E2E.DeadCleanupBinaryInitRUOf
import FV.E2E.DeadCleanupBinaryInitTRU

/-!
# The executable under the slot-byte oracle on decidable checks (SEM1 #537, #713, #733)

`binary_correct_exec_initRU` / `binary_correct_exec_initTRU` take `InitOkRU`; `InitOkRU.of_checks`
builds it from the scope conditions of the base environment and checks on the compiled code. Here
the code checks are one decidable test of the computable system `sys I B` (it reads only the
program and its compilation), and the base conditions are stated on `sys I B` (they read only the
base environment):

* **`LinkSys.initChecksB`**: for every function `g` of the program, `retCountB g` (`RetCount`:
  the signatures an invocation of an extern outside the program can stand for agree on the ABI
  return count per numbers of parameters and returns, #733), `FnAsm.x30Free` at the label offsets
  of its lines (the code outside the frame-record and call lines does not touch `x30`),
  `VCode.retsLow` (no `rets` register is `x30`, #732), `FnAsm.blrLow` (every `blr` through
  `x0`–`x28`), and `slotsNIB` (a function with stack slots has an outgoing-argument area or a slot
  region in its compiled frame, so `NeedSlots → NeedNI`); `initChecksB_sound`,
  `needNI_of_slotsNIB`;
* `hookNIX_closed`, `baseNIX_closed`: the closed base's hooks satisfy the trusted base-hook fact;
* `initOkRU_sysS_of_checks`: `InitOkRU` of the proof's system from `okBCleanup`, `BaseOk`, the
  checks, `BaseRetOk` and `HooksKeep` of the base environment, and `BaseNIX` (trusted, #704);
* **`binary_correct_exec_initRC`**, **`binary_correct_exec_initTRC`**: `binary_correct_exec_initRU`
  / `binary_correct_exec_initTRU` with these premises in place of `InitOkRU`.
-/

namespace E2E

open Backend Backend.Proof E2E.LinkCheck

namespace LinkSys

variable (L : LinkSys)

/-- **A function with stack slots has a frame region its activations may differ in**
(decidable): its compiled frame has an outgoing-argument area or a slot region (`NeedNI`'s
disjuncts). -/
def slotsNIB (g : Clif.Function) : Bool :=
  g.slots.isEmpty || (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase != 0 ||
    (RAFrame.compute (L.A g).vcp (L.A g).rf).size != (L.A g).af.frameSize

theorem needNI_of_slotsNIB (h : ∀ g ∈ L.P.funcs, L.slotsNIB g = true) :
    L.NeedSlots → L.NeedNI := by
  rintro ⟨g, hg, k, hc, hs⟩
  have hk := h k (L.callee_mem hc)
  simp only [slotsNIB, Bool.or_eq_true, List.isEmpty_iff, bne_iff_ne, ne_eq] at hk
  rcases hk with (hk | hk) | hk
  · exact absurd hk hs
  · exact ⟨g, hg, k, hc, .inl hk⟩
  · exact ⟨g, hg, k, hc, .inr hk⟩

/-- **The decidable checks of the oracle route** on every function of the program (module doc). -/
def initChecksB : Bool :=
  L.P.funcs.all fun g => L.retCountB g &&
    (match labelOffsets (L.A g).fa.lines with
      | .ok lm => (L.A g).fa.x30Free lm
      | .error _ => true) &&
    (L.A g).vc.retsLow && (L.A g).fa.blrLow && L.slotsNIB g

theorem initChecksB_sound (h : L.initChecksB = true) :
    (∀ g ∈ L.P.funcs, L.RetCount g) ∧
    (∀ g ∈ L.P.funcs, ∀ lm, labelOffsets (L.A g).fa.lines = .ok lm →
      (L.A g).fa.x30Free lm = true) ∧
    (∀ g ∈ L.P.funcs, (L.A g).vc.retsLow = true) ∧
    (∀ g ∈ L.P.funcs, (L.A g).fa.blrLow = true) ∧
    (L.NeedSlots → L.NeedNI) := by
  have hg : ∀ g ∈ L.P.funcs, (((L.retCountB g = true ∧
      (match labelOffsets (L.A g).fa.lines with
        | .ok lm => (L.A g).fa.x30Free lm
        | .error _ => true) = true) ∧
      (L.A g).vc.retsLow = true) ∧ (L.A g).fa.blrLow = true) ∧ L.slotsNIB g = true :=
    fun g hm => by simpa only [Bool.and_eq_true] using List.all_eq_true.mp h g hm
  refine ⟨fun g hm => L.retCountB_sound (hg g hm).1.1.1.1, fun g hm lm hl => ?_,
    fun g hm => (hg g hm).1.1.2, fun g hm => (hg g hm).1.2,
    L.needNI_of_slotsNIB fun g hm => (hg g hm).2⟩
  have hb := (hg g hm).1.1.1.2
  rw [hl] at hb
  exact hb

end LinkSys

/-- **The closed base's hooks observe nothing outside the program counter.** -/
theorem hookNIX_closed (BD : Option String → Prop) (F : BitVec 64 → Prop) :
    HookNIX closedBase.hooks BD F := by
  refine ⟨fun d _ Z s t h _ => ⟨fun fl hfl => ?_, ?_, fun a ha => ?_⟩,
    fun _ _ _ _ _ h _ => h⟩
  · show Arm.r fl (Arm.w .PC (Arm.r .PC s + 4) s) = Arm.r fl (Arm.w .PC (Arm.r .PC t + 4) t)
    have hpc : Arm.r .PC s = Arm.r .PC t := h.1 .PC (by simp)
    by_cases hf : fl = .PC
    · subst hf
      rw [Arm.r_of_w_same, Arm.r_of_w_same, hpc]
    · rw [Arm.r_of_w_different hf, Arm.r_of_w_different hf]
      exact h.1 fl hfl
  · show (Arm.w .PC (Arm.r .PC s + 4) s).program = (Arm.w .PC (Arm.r .PC t + 4) t).program
    rw [Arm.w_program, Arm.w_program]
    exact h.2.1
  · show (Arm.w .PC (Arm.r .PC s + 4) s).mem a = (Arm.w .PC (Arm.r .PC t + 4) t).mem a
    simp only [Arm.w, Arm.write_base_pc]
    exact h.2.2 a ha

namespace DeadCleanupExecBytes
set_option autoImplicit false

open E2E.DeadCleanupBinary E2E.BinCheck

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **The closed base satisfies the trusted base-hook fact.** -/
theorem baseNIX_closed (f : Clif.Function) (r : Arm.ArmState) (S : BitVec 64 → Prop) :
    (sysS I closedBase f r S).std.BaseNIX :=
  fun _ _ _ _ F _ _ _ _ _ => hookNIX_closed _ F

/-- **`InitOkRU` of the proof's system from the checks** (module doc). -/
theorem initOkRU_sysS_of_checks (hI : okBCleanup I = true) (hB : BaseOk (sys I B))
    (f : Clif.Function) (r : Arm.ArmState) (S : BitVec 64 → Prop)
    (hchk : (sys I B).initChecksB = true) (hBR : (sys I B).BaseRetOk)
    (hK : (sys I B).HooksKeep) (hNX : (sysS I B f r S).std.BaseNIX) :
    InitOkRU (sysS I B f r S) (kapW I B f r) := by
  have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) :=
    baseOk_F hB
  have hL0 := okBCleanup_sound hI hB' fun _ h => .inr h
  have hL : (sysS I B f r S).Ok := LinkSys.Ok.extImg hL0
    (fun a ha => mem_modelOf_img ha) fun a ha => by
      rcases ha with ha | ha
      · exact .inr (.inl ha)
      · exact .inr (.inr ha)
  have hchk' : (sysS I B f r S).initChecksB = true := hchk
  have hBR' : (sysS I B f r S).BaseRetOk := hBR
  have hK' : (sysS I B f r S).HooksKeep := ⟨hK.err, hK.tlsErr, hK.prog, hK.tlsProg⟩
  obtain ⟨hC, hx30, hrl, hblr, hNI⟩ := LinkSys.initChecksB_sound _ hchk'
  exact InitOkRU.of_checks hL
    ((DeadCleanupStackBound.budget_of hI B (worldF I f (DeadCleanupStackBound.bud I f) r)).extImg
      _ _ _)
    hNI hNX (fun _ => hBR') (fun _ => hC) (fun _ => hK') hx30 hrl hblr

/-- **The executable refines a returning CLIF run under the slot-byte oracle, decidable checks**
(module doc): `binary_correct_exec_initRU` with the code checks `initChecksB`, the base conditions
`BaseRetOk`, `HooksKeep` and the trusted `BaseNIX` in place of `InitOkRU`. -/
theorem binary_correct_exec_initRC {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I B)) (hH : HooksSim I B) {n : String} {f : Clif.Function}
    (hf : (prog I).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRunB I B M f r args cs)
    (hchk : (sys I B).initChecksB = true) (hBR : (sys I B).BaseRetOk)
    (hK : (sys I B).HooksKeep) (hNX : (sysS I B f r (GotSlot I file)).std.BaseNIX)
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (E2E.DeadCleanupBinCheck.RelocAt I) (.returned vals cm) :=
  binary_correct_exec_initRU hI hcm hbin hgot B hB hH hf hc M hX ho hav hr
    (initOkRU_sysS_of_checks hI hB f r _ hchk hBR hK hNX) hrun

/-- **The executable reaches the trap of a trapping CLIF run under the slot-byte oracle,
decidable checks** (module doc). -/
theorem binary_correct_exec_initTRC {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I B)) (hH : HooksSim I B) {n : String} {f : Clif.Function}
    (hf : (prog I).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRunB I B M f r args cs)
    (hchk : (sys I B).initChecksB = true) (hBR : (sys I B).BaseRetOk)
    (hK : (sys I B).HooksKeep) (hNX : (sysS I B f r (GotSlot I file)).std.BaseNIX)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) {c : Clif.TrapCode}
    (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (E2E.DeadCleanupBinCheck.RelocAt I) (.trapped c) :=
  binary_correct_exec_initTRU hI hcm hbin hgot B hB hH hf hc M hX ho hav hr
    (initOkRU_sysS_of_checks hI hB f r _ hchk hBR hK hNX) htr hrun

end DeadCleanupExecBytes

end E2E
