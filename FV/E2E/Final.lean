import FV.E2E.Main
import FV.E2E.RegLevelDriverSem
import FV.E2E.RegLevelCorrect
import FV.Backend.Proof.IselLowerAll
import FV.Backend.Proof.IselExcl
import FV.Backend.Proof.IselCtl
import FV.Backend.Proof.IselCtlUnmatch
import FV.Backend.Proof.IselCtlTryInd
import FV.Backend.Proof.IselAtomic
import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.RefinesCSem

/-! # `backend_correct` with every M4 obligation discharged

`backend_correct_of_rules` instantiated with M4's proven rule theorems and with the VCode
semantics fixed to M6's concrete `csem` (per activation `s`: frame `F s`, function context
`ctx s`, external semantics `X s`), which discharges `DriverSem` (`driverSem_csem`) and reduces
`CallsRefine` to the external contract `XCallsOk` (`callsRefine_csem`).

`backend_correct_final`: additionally the register-level layer (`RegLevelCorrect`, hypothesis
`hM6` of `backend_correct_m4`) is discharged by `regLevelCorrect_backend` for the backend's
concrete choices: frame addresses `frameF` of the allocated frame, function context
`⟨fa.k, af.slotBase⟩`, one external semantics `X` and the machine `ArmStepX X H fa`. -/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem backend_correct_m4 {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {F : Arm.ArmState → BitVec 64 → Prop} {ctx : Arm.ArmState → FnCtx}
    {X : Arm.ArmState → ExtSem}
    {syms : String → Option Nat} {slotOff out : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    -- M6 + M5
    (hM6 : RegLevelCorrect (fun s => csem (F s) (ctx s) (X s)) F astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (csem (F s) (ctx s) (X s)))
    -- the external contract (callees of `f`, linker)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    -- the external contract of the indirect calls (their call-site signatures `indSigs f`;
    -- vacuous without indirect calls, `xCallsIndOk_nil`) and the linker's symbol addresses
    (hXI : ∀ s, XCallsIndOk env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    (hsym : ∀ s n b, syms n = some b → (X s).sym n 0 = BitVec.ofNat 64 b)
    (hmem : ∀ s, MemRefines (F s) slotOff syms (csem (F s) (ctx s) (X s)))
    -- the relation's outgoing stack-argument area holds every call's stack arguments
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) :=
  backend_correct_of_rules hsub hc
    lowerRulesCorrect_program excludedUnmatchable callRulesCorrect indRulesCorrect
    memRulesCorrect_program lowerTermRulesCorrect termUnmatchable branchRulesCorrect
    branchExcludedUnmatchable tryRulesCorrect tryUnmatchable tryIndRulesCorrect tryIndUnmatchable
    hM6 hRef (fun s' => driverSem_csem (F s') (ctx s') (X s'))
    (fun s' => callsRefine_csem (hX s'))
    (fun s' => indCallsRefine_csem (hXI s') (hsym s') (fun _ _ _ h => h.1.symbols)) hmem houtB
    hent hres hbe hargs hargF hcs hrel htr fuel

/-- `hRef` of `backend_correct_m4` at the backend's concrete choices (`refines_csem`). -/
theorem refines_final (vcp : VCode) (rf : RFunc) (af : AFunc) (fa : FnAsm) (X : ExtSem) :
    ∀ s, Refines (frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
      (csem (frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        ⟨fa.k, af.slotBase⟩ X) :=
  fun _ => refines_csem _ _ X

/-- The prepared VCode has a `tryCall` only if the function has a `try_call` (the validators
`lowerCheck`/`prepCheck`). -/
theorem hasTry_of_hasTryCall {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : Compiled f k vc vcp rf af fa fb)
    (h : vcp.hasTryCall = true) : ∃ B ∈ f.blocks, B.term.isTry = true :=
  Classical.byContradiction fun hn => by
    have hf : ∀ B ∈ f.blocks, B.term.isTry = false := fun B hB =>
      Bool.eq_false_iff.mpr fun ht => hn ⟨B, hB, ht⟩
    rw [noTryCall_of_prepCheck hc.prepOk (noTryCall_of_check hc.lowerOk hf)] at h
    cases h

theorem le_alignTo (n a : Nat) (ha : 0 < a) : n ≤ alignTo n a := by
  unfold alignTo
  have := Nat.div_add_mod (n + a - 1) a
  have := Nat.mod_lt (n + a - 1) ha
  have : (n + a - 1) / a * a = a * ((n + a - 1) / a) := Nat.mul_comm _ _
  omega

/-- The allocated frame's outgoing area (`intBase`, below the spill slots) holds every call's
stack arguments: `prepare` keeps the VCode's outgoing area, which `intBase` rounds up. -/
theorem outgoing_le_intBase {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : Compiled f k vc vcp rf af fa fb) :
    vc.outgoing ≤ (RAFrame.compute vcp rf).intBase := by
  simp only [RAFrame.compute]
  rw [outgoing_of_prepCheck hc.prepOk]
  exact le_alignTo _ 16 (by decide)

/-- The stack-passed arguments of the ABI entry state lie above the entry `sp`, outside the
frame and the code (`StackAvail`, `StackArgAt`): they avoid the frame addresses `frameF`. -/
theorem stackArgsAvoid_frameF {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : Compiled f k vc vcp rf af fa fb)
    {s : Arm.ArmState} {base ra : BitVec 64} {args : List Clif.Val} (hres : StackAvail af s)
    (_hent : AbiEntry fb base ra s) (hargs : ArgsIn f.sig args s) :
    StackArgsAvoid (frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
      f.sig args s := by
  intro off v hm j hj hF
  have h := hargs _ _ hm
  simp only at h
  have hframe := lowerRFunc_frame hc.alloc
  have hfs := (lowerRFunc_ok hc.alloc).1.1
  have hD : frameDrop af = af.frameSize + 16 := by simp [frameDrop, hframe]
  have hsz : (RAFrame.compute vcp rf).size ≤ af.frameSize := by
    rw [hfs]; simp only [RAFrame.compute]
    exact Nat.le_trans (Nat.le_add_right _ _) (le_alignTo _ 16 (by decide))
  have hsp := hres.1
  have hfit := h.fits
  have hx : (spv s + BitVec.ofNat 64 off + BitVec.ofNat 64 j -
      (spv s - BitVec.ofNat 64 (frameDrop af))).toNat = off + j + frameDrop af := by
    rw [hD]
    bv_omega
  rcases hF with ⟨-, h2⟩ | ⟨-, h2⟩ | hcode
  · rw [hx] at h2; omega
  · rw [hx] at h2; omega
  · have e : spv s + BitVec.ofNat 64 off + BitVec.ofNat 64 j = spv s + BitVec.ofNat 64 (off + j) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
    rw [e] at hcode
    exact h.noCode j hj hcode

/-- **The backend's end-to-end theorem** (`docs/contracts/e2e.md`, "Final hypotheses"): the Arm
run of the compiled function refines the CLIF run (a `try_call`: its normal return). M6's `csem`
obligations are discharged (`refines_csem`, `memRefines_csem`). Remaining hypotheses: the form
coverage `FormsCovered` (decided per function by `formsCoveredB`), the callee contract `CalleeOk`
of the machine's call hook (and, for a function with a `try_call`, `CalleeTryOk`: the exception
payload registers), the external contract `XCallsOk`, and the link-time facts `hsym`/`hslot`. -/
theorem backend_correct_final {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    -- the straight-line forms of the prepared VCode are covered (decided by `formsCoveredB`)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    -- the callee contract of the machine's call hook (AAPCS64)
    (hC : ∀ s, CalleeOk
      (frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H)
    -- the callee contract of the call of a `try_call` (only for a function with one)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H)
    -- the external contract (callees of `f`, linker)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- the external contract of the indirect calls of `f` (`call_indirect`, `try_call_indirect`:
    -- the externs at their link-time addresses, with the call sites' signatures; vacuous
    -- without indirect calls, `xCallsIndOk_nil`)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- memory forms (`memRefines_csem`): the external semantics' symbol addresses are the linked
    -- ones, and the relation's slot-region offset is the frame's slot base
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_m4 (ctx := fun _ => ⟨fa.k, af.slotBase⟩) (X := fun _ => X) hsub hc
    (regLevelCorrect_backend hc.check hc.alloc hc.emit hc.layout hcov hC
      fun h => hCT (hasTry_of_hasTryCall hc h))
    (refines_final vcp rf af fa X) hX hXI (fun _ => hsym)
    (fun _ => memRefines_csem _ _ X hslot hsym) (outgoing_le_intBase hc)
    hent hres hbe hargs (stackArgsAvoid_frameF hc hres hent hargs) hcs hrel htr fuel

/-- **Specialisation**: for a signature with at most 8 parameters (all passed in registers),
`ArgsIn` is the former premise "argument `i` in `x (argIdx sig i)`" (low bits). -/
theorem argsIn_iff_of_regs {sig : Clif.Signature} {bytes : List Nat}
    (hb : sigParamBytes sig = .ok bytes) (h8 : bytes.length ≤ 8) {args : List Clif.Val}
    {s : Arm.ArmState} (hl : args.length = sig.params.length) :
    ArgsIn sig args s ↔ ∀ i v, args[i]? = some v → XHolds v (xreg (argIdx sig i) s) := by
  rw [ArgsIn, locsOf_of_regs hb h8]
  have hlen : (abiArgIdx sig.params 0).length = args.length := by rw [abiArgIdx_length, hl]
  constructor
  · intro h i v hv
    have hi : i < (abiArgIdx sig.params 0).length := by
      rw [hlen]; exact (List.getElem?_eq_some_iff.mp hv).1
    have hm : (ArgLoc.reg (.x (argIdx sig i)), v) ∈
        ((abiArgIdx sig.params 0).map fun n => ArgLoc.reg (.x n)).zip args := by
      apply List.mem_iff_getElem?.mpr
      refine ⟨i, ?_⟩
      simp [List.getElem?_zip_eq_some, hv, argIdx, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi]
    exact h _ _ hm
  · intro h loc v hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    rw [List.getElem?_zip_eq_some, List.getElem?_map] at hi
    obtain ⟨h1, h2⟩ := hi
    cases hn : (abiArgIdx sig.params 0)[i]? with
    | none => simp [hn] at h1
    | some n =>
      simp only [hn, Option.map_some, Option.some.injEq] at h1
      subst h1
      have hai : argIdx sig i = n := by simp [argIdx, List.getD_eq_getElem?_getD, hn]
      have := h i v h2
      rw [hai] at this
      exact this

/-- **Specialisation to functions without indirect calls**: `backend_correct_final` with the
former premises (no indirect-call contract `hXI`), for a function with no `call_indirect`
statement and no `try_call_indirect` terminator (`indSigs f = []`, `xCallsIndOk_nil`). With
`InSubset.of_indirectFree` and `TrapsExplicit.of_indirectFree` it is the former theorem. -/
theorem backend_correct_final_indirectFree {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hci : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ sig callee args, st.inst ≠ .callIndirect sig callee args)
    (htci : ∀ B ∈ f.blocks, ∀ callee args et, B.term ≠ .tryCallIndirect callee args et)
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_final hsub hc hcov hC hCT hX
    (fun _ => by rw [indSigs_eq_nil hci htci]; exact xCallsIndOk_nil _ _ _) hsym hslot hent hres
    hbe hargs hcs hrel htr fuel

end E2E
