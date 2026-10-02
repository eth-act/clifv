import FV.E2E.Final

/-! # The per-function theorem with the final world (for linking)

`backend_correct_final` fixes, of a returning Arm run, only the low bits of the results and the
live CLIF bytes. Linking the functions of a program (`FV/E2E/LinkArm.lean`) needs more of the
callee: its whole effect on the caller's world, determined by the caller's world alone.

`backend_correct_world` composes the same three layers (`IselSim`, `PrepareCorrect`,
`regLevelCorrect_world`) with the addresses outside the world a fixed set `F` (for an activation
inside a linked program: its frame, its callees' dead stack and the addresses `G` it keeps, its
callers' frames and the program's code: `frameWG`). For a returning CLIF run it gives **one**
VCode outcome — returned values `outs` (full 128-bit register values) and final world `w`,
determined by the body-entry world `w₀` — that **every** Arm activation entered with that
body-entry world realises (`ActEntry`): the results in their registers, the memory outside `F`
and every unmasked field but x29/`sp` as in `w`, the memory at `G` and the program as at entry
(`ActRet`). Two Arm entry states that share a body-entry world (they agree outside `F` and on
the argument registers) therefore return the same results and world: the non-interference the
linked callee contract needs.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- What an Arm activation of the compiled function needs: the ABI entry, stack (frame and the
callees' budget `K`), kept addresses `G` outside the frame and the dead stack, the addresses
outside the world are `F = frameWG K … G s`, the callee contracts (relative to `G`), and the
body-entry world `w₀`. -/
structure ActEntry (vcp : VCode) (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) (K : Nat)
    (F G : BitVec 64 → Prop) (X : ExtSem) (H : ArmHooks) (base ra : BitVec 64)
    (s w₀ : Arm.ArmState) : Prop where
  abi : AbiEntry fb base ra s
  stack : StackAvail K af s
  gfree : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a
  hF : frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s = F
  calls : CalleeOkG F K G s (CallPc fa base) X H vcp.CallSite
  tries : vcp.hasTryCall = true → CalleeTryOk F X H vcp.TrySite
  tls : vcp.hasTls = true → TlsOk F K X H
  body : BodyEntryW F vcp.EntryArg af s w₀

/-- The return of an activation entered in `s` at `t`, realising the VCode return `rets us` with
values `outs` and final world `w`: an AAPCS64 return, the results in their registers, the memory
outside `F` and the unmasked fields but x29/`sp` as in `w`, the kept addresses `G` and the
program as at entry. -/
structure ActRet (ra : BitVec 64) (F G : BitVec 64 → Prop) (us : List (Reg × Reg))
    (outs : List CV) (w s t : Arm.ArmState) : Prop where
  ret : ArmRet ra s t
  regs : ∀ (j : Nat) v p x, us[j]? = some (v, p) → outs[j]? = some x → regVal t p = x
  mem : ∀ a, ¬ F a → t.mem a = w.mem a
  fields : ∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f t = Arm.r f w
  gkeep : ∀ a, G a → t.mem a = s.mem a
  prog : t.program = s.program

/-- **CLIF → VCode for the backend's `csem`** with a fixed set `F` of addresses outside the
world: the driver simulation with every M4 obligation discharged (as `backend_correct_final`). -/
theorem iselSim_final {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop}
    (hX : XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff) :
    IselSim (csem F ⟨fa.k, af.slotBase⟩ X)
      ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ env p f vc := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hRef : Refines F (csem F ⟨fa.k, af.slotBase⟩ X) := refines_csem _ _ X
  have hmem : MemRefines F slotOff syms (csem F ⟨fa.k, af.slotBase⟩ X) :=
    memRefines_csem _ _ X hslot hsym
  have hcalls := callsRefine_csem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hX
  have hicalls := indCallsRefine_csem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hXI hsym
    (fun _ _ _ h => h.1.symbols)
  have houtB := outgoing_le_intBase hc
  refine iselSim_of_driver (ctx := ctx) (st0 := st0) (R := R) (gn := gn) (bl := bl) (A := A)
    ?_ hmem
  exact {
    shape := hshape
    cert := hcert
    dsem := driverSem_csem F ⟨fa.k, af.slotBase⟩ X
    insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
      indRulesCorrect memRulesCorrect_program hRef (mrStable_holds Γ f) hcalls hicalls hmem
      (outArgsOk_holds Γ f) (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (memRelOk_holds Γ f)
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef (mrStable_holds Γ f)
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hc.lowerOk
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨_, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_holds Γ f) hmem
      (outArgsOk_holds Γ f) hcalls, tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef (mrStable_holds Γ f)
      hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := cfg_of_prepare hc.prepare }

/-- **The per-function theorem with the final world** (see the module doc): for a returning
CLIF run, one VCode outcome (`us`, `outs`, `w`; related to the CLIF results and memory) that
every activation entered with the body-entry world `w₀` realises (`ActRet`); for a trapping run,
every such activation reaches a trap site with the code. -/
theorem backend_correct_world {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s)) ∧
    (∀ c, Clif.runLoop env p fuel cs = .trapped c →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c (runX (ArmStepX X H fa) n s)) := by
  have hI := iselSim_final hsub hc hX hXI hsym hslot args cs w₀ (fun _ => 0) hcs hrel hargs htr fuel
  have hP := prepareCorrect_of_check (driverSem_csem F ⟨fa.k, af.slotBase⟩ X) hc.prepOk
    (fun _ => 0) w₀
  have hM6 : ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntry vcp rf af fa fb K F G X H base ra s w₀ → _ := fun H G base ra s he => by
    have h := regLevelCorrect_world hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
      (K := K) (G := G) hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
      (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body)
      (fun _ => 0)
    rw [he.hF] at h
    exact h
  refine ⟨fun vals cm hrun => ?_, fun c hrun H G base ra s he => ?_⟩
  · obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, fun H G base ra s he => ?_⟩
    obtain ⟨n, h1, h2, h3, h4, h5, h6⟩ := (hM6 H G base ra s he).1 us outs w (hP.1 _ _ _ hv)
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩⟩
  · exact (hM6 H G base ra s he).2 c (hP.2 c (hI.2 c hrun))

/-- An `ActRet` return is an `ArmRefines` return: the results' low bits and the live CLIF bytes
(for a VCode outcome related to the CLIF one as `backend_correct_world` gives it). -/
theorem armRefines_of_actRet {fb : FnBin} {base ra : BitVec 64} {astep : Arm.ArmState → Arm.ArmState}
    {s : Arm.ArmState} {F G : BitVec 64 → Prop} {syms : String → Option Nat}
    {vals : List Clif.Val} {cm : Clif.Mem} {us : List (Reg × Reg)} {outs : List CV}
    {w : Arm.ArmState} (hus : us.map (·.2) = (List.range us.length).map Reg.x)
    (hlen : us.length = outs.length) (hhold : PrefixHold vals outs) (hm : MemRel F syms cm w)
    {n : Nat} (h : ActRet ra F G us outs w s (runX astep n s)) :
    ArmRefines fb base ra astep s (.returned vals cm) := by
  refine ⟨n, h.ret, ?_, memAgree_of hm h.mem⟩
  intro j v hj
  have hjv : j < vals.length := (List.getElem?_eq_some_iff.mp hj).1
  have hju : j < us.length := by have := hhold.1; omega
  obtain ⟨x, hx⟩ : ∃ x, outs[j]? = some x :=
    ⟨outs[j]'(by have := hhold.1; omega), List.getElem?_eq_getElem _⟩
  have hp : (us[j]'hju).2 = Reg.x j := by
    have := congrArg (fun l => l[j]?) hus
    simp only [List.getElem?_map, List.getElem?_range hju, List.getElem?_eq_getElem hju,
      Option.map_some] at this
    exact Option.some.inj this
  have hr := h.regs j (us[j]'hju).1 (us[j]'hju).2 x (by simp [List.getElem?_eq_getElem hju]) hx
  rw [hp, regVal_x] at hr
  show VHolds v (ofX (xreg j (runX astep n s)))
  rw [hr]
  exact hhold.2 j v x hj hx

end E2E
