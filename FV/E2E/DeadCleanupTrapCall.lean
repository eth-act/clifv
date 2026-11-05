import FV.E2E.DeadCleanupUnwindFinal
import FV.E2E.RegLevelTrapCall
import FV.E2E.TrapCallClifRun

/-!
# The shipped compiler's per-function theorem with callee traps (S9a, #33)

`backend_correct_final_cleanup` takes `TrapsExplicit`: a trap of the run of `f` must be an
explicitly trapping instruction of `f`. A run whose callee traps (a trapping `__*ti3` helper, a
panic, a callee of the linked program) is outside it. Here such a run is covered: under
`TrapsExplicitC` (the callee traps allowed) the machine run reaches either a trap site of `f`
with the trap code, or a **callee-trap state** (`CallTrapAt`): the pc at the call of `f` whose
callee traps with that code, with the callee contract's premises as at every call
(`TrapCallSem`: the extern's CLIF semantics traps on the call's arguments and memory, and its
machine semantics `X.call` gives no normal return there), every earlier state of the activation
`GoodX`.

* `TrapCallSem`: the trapping callees of a call (direct or indirect) on its operand values and
  world; `XTrapsOk`: **the trapping callees' contract** (a callee whose CLIF semantics traps
  does not return normally on the machine, `X.call = none`).
* `xCallsOk_trapEnv`, `xCallsIndOk_trapEnv`, `xRaiseOk_trapEnv`, `xRaiseIndOk_trapEnv`: the
  contracts of the proof device `trapEnv env c` (`FV/E2E/TrapCallClif.lean`) and of the
  raising semantics `xrT` of the trapping callees.
* **`backend_correct_final_cleanup_trapcall`**: the composition, for a function without
  `try_call` terminators, in a program without functions (the linked per-function theorems'
  `p.bare`): CLIF → VCode by the unwinding chain's `iselSimU_of_driver` on `trapEnv env c`
  (`trapEnv_of_trapped`), `prune` + `prepare` by `prepareCorrectU_cleanup_value`, the register
  level by `regLevel_trapCall_value`.
* Every run under the old premise is a run under the new one (`TrapsExplicit.toC`); the old
  theorem `backend_correct_final_cleanup` is unchanged. Non-vacuity, and a run the new theorem
  covers and the old one excludes: `FV/E2E/DeadCleanupTrapCallWitness.lean`.

Still excluded at this layer (later steps of S9, see `docs/TO-PROVE.md` S9): traps inside the
callees of `try_call`/`try_call_indirect` (the trap of such a callee is caught by the unwinding
chain's handler semantics: a different proof device is needed), memory-access traps
(`heap_oob`: no fault model), and the composition with the linked program (`LinkArm`: the
callee-trap state of a program callee continues in the callee's code) and the executable.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-! ## The trapping callees -/

/-- **The callees of a call that trap with `c`** on the call's operand values `uses` and world
`w` (callee descriptor `d`): the machine semantics `X.call` gives no normal return, and an
extern of `exts` (called by `bl`, or `blr` of its GOT address), or an extern at the callee
address of an indirect call with a signature of `sigs`, traps with `c` in its CLIF semantics on
arguments held by `uses` (`ArgsAt`, `AllHold`) and a memory related to `w` (`MR`). -/
def TrapCallSem (env : Clif.Env) (exts : List Clif.ExtFunc) (sigs : List Clif.Signature)
    (MR : MemRelT) (X : ExtSem) (c : Clif.TrapCode) (d : Option String) (uses : List CV)
    (w : Arm.ArmState) : Prop :=
  X.call d uses w = none ∧
  ((∃ ext ∈ exts, ∃ (g : List Clif.Val → Clif.Mem → Clif.Outcome) (sl : List (Clif.SlotId × Nat))
      (cm : Clif.Mem) (args : List CV) (vals : List Clif.Val), env.extern ext.name = some g ∧
      (d = some ext.name ∧ uses = args ∨
        d = none ∧ ext.colocated = false ∧ uses = ofX (X.sym ext.name 0) :: args) ∧
      ArgsAt ext.sig vals args w ∧ MR sl cm w ∧ g vals cm = .trapped c) ∨
    (∃ sig ∈ sigs, ∃ (n : String) (g : List Clif.Val → Clif.Mem → Clif.Outcome)
      (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (u : CV) (args : List CV)
      (vals : List Clif.Val), env.extern n = some g ∧
      (∀ s, env.sigOf n = some s → sig.abiMatch s = true) ∧ lo64 u = X.sym n 0 ∧
      vals.length ≤ 8 ∧ AllHold vals args ∧ MR sl cm w ∧ g vals cm = .trapped c ∧
      vals.map (·.ty) = Clif.AbiParam.tys sig.params ∧ d = none ∧ uses = u :: args))

/-- **The trapping callees' contract** (`XCallsOk`/`XCallsIndOk`'s counterpart for traps): at
a call of an extern (direct, or indirect at its link-time address with a signature of `sigs`)
whose CLIF semantics traps on the call's arguments and a memory related to the world, the
machine semantics of the callee gives no normal return (`X.call = none`): the outside code (a
`__*ti3` helper, a panic) does not return there. -/
def XTrapsOk (env : Clif.Env) (exts : List Clif.ExtFunc) (sigs : List Clif.Signature)
    (MR : MemRelT) (X : ExtSem) : Prop :=
  (∀ ext ∈ exts, ∀ g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (w : Arm.ArmState)
      (d : Option String) (uses args : List CV) (vals : List Clif.Val) (c : Clif.TrapCode),
    env.extern ext.name = some g →
    (d = some ext.name ∧ uses = args ∨
      d = none ∧ ext.colocated = false ∧ uses = ofX (X.sym ext.name 0) :: args) →
    ArgsAt ext.sig vals args w → MR sl cm w → g vals cm = .trapped c → X.call d uses w = none) ∧
  (∀ sig ∈ sigs, ∀ (n : String) g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem)
      (w : Arm.ArmState) (u : CV) (args : List CV) (vals : List Clif.Val) (c : Clif.TrapCode),
    env.extern n = some g → (∀ s, env.sigOf n = some s → sig.abiMatch s = true) →
    lo64 u = X.sym n 0 → vals.length ≤ 8 → AllHold vals args → MR sl cm w →
    g vals cm = .trapped c → vals.map (·.ty) = Clif.AbiParam.tys sig.params →
    X.call none (u :: args) w = none)

/-- Without trapping externs the contract holds. -/
theorem xTrapsOk_of_noTrap {env : Clif.Env} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
    {MR : MemRelT} {X : ExtSem}
    (h : ∀ n g, env.extern n = some g → ∀ vals cm c, g vals cm ≠ .trapped c) :
    XTrapsOk env exts sigs MR X :=
  ⟨fun _ _ g _ _ _ _ _ _ _ _ hg _ _ _ ht => absurd ht (h _ g hg _ _ _),
    fun _ _ _ g _ _ _ _ _ _ _ hg _ _ _ _ _ ht _ => absurd ht (h _ g hg _ _ _)⟩

/-! ## The contracts of the proof device -/

section
variable {env : Clif.Env} {c : Clif.TrapCode}

theorem trapEnv_extern {n : String} {g' : List Clif.Val → Clif.Mem → Clif.XOutcome}
    (h : (trapEnv env c).extern n = some g') :
    ∃ g, env.extern n = some g ∧ g' = fun vals mem => trapOut c (g vals mem) mem := by
  simp only [trapEnv, Option.map_eq_some_iff] at h
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g, hg, rfl⟩

theorem trapOut_unwound {o : Clif.Outcome} {mem : Clif.Mem} {e : Clif.Exn} {m : Clif.Mem}
    (h : trapOut c o mem = .unwound e m) : o = .trapped c ∧ e = trapExn ∧ m = mem := by
  cases o with
  | trapped c' =>
    simp only [trapOut] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨by rw [hc], rfl, rfl⟩
    · cases h
  | returned v m' => simp [trapOut] at h
  | stuck m' => simp [trapOut] at h
  | outOfFuel => simp [trapOut] at h

theorem trapOut_returned {o : Clif.Outcome} {mem : Clif.Mem} {v : List Clif.Val} {m : Clif.Mem}
    (h : (trapOut c o mem).toOutcome = .returned v m) : o = .returned v m := by
  cases o with
  | trapped c' =>
    simp only [trapOut] at h
    split at h <;> simp [Clif.XOutcome.toOutcome] at h
  | returned v' m' => simpa [trapOut, Clif.XOutcome.toOutcome] using h
  | stuck m' => simp [trapOut, Clif.XOutcome.toOutcome] at h
  | outOfFuel => simp [trapOut, Clif.XOutcome.toOutcome] at h

theorem trapEnv_toEnv_returned {n : String} {g'' : List Clif.Val → Clif.Mem → Clif.Outcome}
    (h : (trapEnv env c).toEnv.extern n = some g'') :
    ∃ g, env.extern n = some g ∧ ∀ vals cm v m, g'' vals cm = .returned v m → g vals cm = .returned v m := by
  rw [trapEnv_toEnv_extern] at h
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨g, hg, fun _ _ _ _ hr => trapOut_returned hr⟩

theorem xCallsOk_trapEnv {exts : List Clif.ExtFunc} {MR : MemRelT} {X : ExtSem}
    (h : XCallsOk env exts MR X) : XCallsOk (trapEnv env c).toEnv exts MR X := by
  intro ext hext g'' sl cm w d uses args vals rvals cm' hg hd hargs hmr hret hrl
  obtain ⟨g, hg0, hr⟩ := trapEnv_toEnv_returned hg
  exact h ext hext g sl cm w d uses args vals rvals cm' hg0 hd hargs hmr (hr _ _ _ _ hret) hrl

theorem xCallsIndOk_trapEnv {sigs : List Clif.Signature} {MR : MemRelT} {X : ExtSem}
    (h : XCallsIndOk env sigs MR X) : XCallsIndOk (trapEnv env c).toEnv sigs MR X := by
  intro sig hsig n g'' sl cm w u args vals rvals cm' hg hs hu h8 hall hmr hret hrl hty
  obtain ⟨g, hg0, hr⟩ := trapEnv_toEnv_returned hg
  exact h sig hsig n g sl cm w u args vals rvals cm' hg0 hs hu h8 hall hmr (hr _ _ _ _ hret) hrl hty

theorem xRaiseOk_trapEnv {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {MR : MemRelT}
    {X : ExtSem} (hT : XTrapsOk env exts sigs MR X) :
    XRaiseOk (trapEnv env c) exts MR X (xrT (TrapCallSem env exts sigs MR X c)) := by
  intro ext hext g' sl cm w d uses args vals e m hg hd hargs hmr hu
  obtain ⟨g, hg0, rfl⟩ := trapEnv_extern hg
  obtain ⟨htc, rfl, hm⟩ := trapOut_unwound hu
  exact ⟨0, w, xrT_of ⟨hT.1 ext hext g sl cm w d uses args vals c hg0 hd hargs hmr htc,
    .inl ⟨ext, hext, g, sl, cm, args, vals, hg0, hd, hargs, hmr, htc⟩⟩, exnRel_trapExn,
    hm ▸ hmr⟩

theorem xRaiseIndOk_trapEnv {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
    {MR : MemRelT} {X : ExtSem} (hT : XTrapsOk env exts sigs MR X) :
    XRaiseIndOk (trapEnv env c) sigs MR X (xrT (TrapCallSem env exts sigs MR X c)) := by
  intro sig hsig n g' sl cm w u args vals e m hg hs hu h8 hall hmr hun hty
  obtain ⟨g, hg0, rfl⟩ := trapEnv_extern hg
  obtain ⟨htc, rfl, hm⟩ := trapOut_unwound hun
  exact ⟨0, w, xrT_of ⟨hT.2 sig hsig n g sl cm w u args vals c hg0 hs hu h8 hall hmr htc hty,
    .inr ⟨sig, hsig, n, g, sl, cm, u, args, vals, hg0, hs, hu, h8, hall, hmr, htc, hty, rfl, rfl⟩⟩,
    exnRel_trapExn, hm ▸ hmr⟩

end

/-! ## The per-function theorem -/

/-- **The shipped compiler's per-function theorem with callee traps**: for a function `f`
compiled through the dead cleanup, without `try_call` terminators, in a program without
functions (`p.funcs = []`), whose lowering passes the unwinding validator (`lowerCheckU`), under
the premises of `backend_correct_final_cleanup` plus the trapping callees' contract
(`XTrapsOk`), a run of `f` that traps with `c` under `TrapsExplicitC` (explicit traps **and
traps inside the callees of `call`/`call_indirect` statements**) is matched by the machine run
from the ABI entry: it reaches a trap site of `f` with code `c`, or a callee-trap state
(`CallTrapAt` with `TrapCallSem … c`: the pc at a call of `f` whose callee traps with `c`, the
callee contract's premises holding there), every earlier state of the activation `GoodX`. -/
theorem backend_correct_final_cleanup_trapcall {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    -- the lowering's unwinding validator (decided by the compiler: `unwOkB`)
    (hlU : lowerCheckU f vc = true)
    -- a program without functions (`p.bare`), a function without `try_call` terminators
    (hp : p.funcs = []) (hft : ∀ B ∈ f.blocks, B.term.isTry = false)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- the trapping callees' contract
    (hXT : ∀ s, XTrapsOk env (f.externs.map (·.2)) (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitC env p cs) {fuel : Nat} {c : Clif.TrapCode}
    (hrun : Clif.runLoop env p fuel cs = .trapped c) :
    ∃ n, TrapAt fb base c (runX (ArmStepX X H fa) n s) ∨
      (CallTrapAt vcp (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
          K (fun _ => False) s fa base X (fun _ _ => False)
          (TrapCallSem env (f.externs.map (·.2)) (indSigs f) (fun sl cm w =>
            Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
              syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X c)
          (runX (ArmStepX X H fa) n s) ∧
        ∀ i < n, actGoodX vcp rf af fa fb base s X H K (fun _ => False) (fun _ _ => False)
          (runX (ArmStepX X H fa) i s)) := by
  obtain ⟨htrX, hout⟩ := trapEnv_of_trapped env c hp hft (noTail_of_subset hsub) hcs htr hrun
  let Γ : Rel := ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
    syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  let XT := TrapCallSem env (f.externs.map (·.2)) (indSigs f) (fun sl cm w => Γ.holds f sl cm w) X c
  let fctx : FnCtx := ⟨fa.k, af.slotBase⟩
  have hnt : vcp.hasTryCall = false :=
    noTryCall_of_prepCheck hc.prepOk (cleanupStage_noTryCall f (noTryCall_of_check hc.lowerOk hft))
  have hexcl : ∀ d uses w, X.call d uses w ≠ none → (xrT XT).raise d uses w = none :=
    fun _ _ _ hne => xrT_none fun h => hne h.1
  have houtB := outgoing_le_intBaseCleanupA hc
  have hRef := refines_valueSemU Γ.F fctx X (xrT XT)
  have hMem := memRefines_valueSemU Γ.F fctx X (xrT XT) hslot hsym
  have hcallsR := callsRefine_valueSemU (F := Γ.F) (ctx := fctx) (xCallsOk_trapEnv (c := c) (hX s))
    hexcl
  have hicallsR := indCallsRefine_valueSemU (F := Γ.F) (ctx := fctx)
    (xCallsIndOk_trapEnv (c := c) (hXI s)) hsym (fun _ _ _ h => h.1.symbols) hexcl
  -- CLIF → VCode with unwinding, on the proof device `trapEnv env c`
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hUs, hsk⟩ := skipStage_specU hlU
  have hIsel : IselSimU (valueSemU Γ.F fctx X (xrT XT)) (xrT XT) Γ (trapEnv env c) p f
      (skipStage f vc) :=
    iselSimU_of_driver_stage (ctx := ctx) (st0 := st0) (R := R) (gn := gn) (bl := bl) (A := A)
      { shape := hshape
        cert := hcert
        dsem := (driverSem_valueSemU Γ.F fctx X (xrT XT)).toDriverSemG
        insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
          indRulesCorrect memRulesCorrect_program hRef (mrStable_holds Γ f) hcallsR hicallsR hMem
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
        tries := ⟨Γ.out, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_holds Γ f)
          hMem (outArgsOk_holds Γ f) hcallsR, tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
        tryExt := hsub.tryExterns
        tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef
          (mrStable_holds Γ f) hicallsR
        tryIndSig := tryIndSig_of_subset hsub
        cfg := by
          obtain ⟨ss, ps, he⟩ := cfg_of_prepare hc.prepare
          exact ⟨ss, ps, (cleanupStage_cfg f vc).symm.trans he⟩ }
      hUs hsk (driverSem_valueSemU Γ.F fctx X (xrT XT)) hRef hMem (raiseSem_valueSemU _ _ _ _)
      (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (tryStack_mono (tryStack_of_check hc.lowerOk) houtB)
      (xRaiseOk_trapEnv (hXT s)) (xRaiseIndOk_trapEnv (hXT s)) hsym
  -- `prune` + `prepare`
  have hPrep := prepareCorrectU_cleanup_value hc Γ.F fctx X (xrT XT)
  -- the register level
  obtain ⟨ρ₀, hR1, hR2⟩ := regLevel_trapCall_value hc.check hc.alloc hc.emit hc.layout hcov hC
    (fun h => hTls (hasTls_of_vcodeCleanupA hc h)) hnt XT hent hres hbe
  have hI := hIsel args cs w₀ ρ₀ hcs hrel
    (argsAtEntry_body (lowerRFunc_frame hc.alloc) (entryRegs_of_check hc.lowerOk) hbe hargs
      (stackArgsAvoid_frameWCleanupA hc hres hent hargs)) htrX fuel
  rcases hout with h | ⟨e, m, h⟩
  · obtain ⟨n, hn⟩ := hR1 c ((hPrep.1 _ _).2 c (hI.2.1 c h))
    exact ⟨n, .inl hn⟩
  · obtain ⟨obj, w, hv, -, -⟩ := hI.2.2 e m h
    obtain ⟨n, hct, ht⟩ := hR2 obj w (hPrep.2 _ _ _ _ hv)
    exact ⟨n, .inr ⟨hct, ht⟩⟩

end E2E
