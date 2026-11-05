import FV.Concurrency.RealizeCompiled
import FV.Concurrency.ArmAllocWitness
import FV.Concurrency.IselRefinesWitness

/-!
# Non-vacuity of `realizes_compiled` on compiled code (T2k, #311)

The CLIF function `fence; return` (`srcF`, parsed) as the pipeline compiles it: its lowering
`vcF`, `prepare`'s output `vcpF`, the spill allocation `rfF` (18 saves of the callee-saved
registers by moves, the `fence`, 18 restores, the return), lowered, emitted, laid out and loaded
as `ArmAllocThread.Witness.act` loads it (`RA`):

* `driverHyp_of`: the driver hypothesis of layer 2 for a function whose checks hold (the
  construction of `IselThread.Witness.driverHypA`, for any function);
* `compiledF`: **every premise of `RealizeCompiled.Compiled`** holds for `RA`, the CLIF entry
  state `csF` (block 0, no arguments, empty memory) and the Arm state after the prologue: `RA.Wf`,
  its moves' code (`moveCodeOk`), the memory scope, the driver hypothesis and checks, the memory
  relation `RelW` with the activation's private set `RA.F`, `Q ∧ AInv` (`q_init`).
  Checks by `native_decide` (witness only).
-/

namespace Concurrency.RealizeCompiled.Witness

open Arm ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine
  ArmAllocThread ThreadCompose E2E

/-! ## The driver hypothesis of a checked function -/

/-- A function without externs whose verifiability check holds is in the subset (for every
program). -/
theorem inSubset_of {f : Clif.Function} (hv : verifiable f = true) (hext : f.externs = [])
    (p : Clif.Program) : InSubset p f := by
  simp only [verifiable, abiSigs, indSigsOk, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, and_assoc] at hv
  obtain ⟨hE, hf, hext', hind⟩ := hv
  have hno : ∀ fn e, f.extern? fn = some e → False := fun fn e he => by
    simp [Clif.Function.extern?, hext] at he
  exact ⟨hE, fun _ _ _ _ fn _ _ e he => (hno fn e he).elim,
    fun _ _ fn _ _ _ e he => (hno fn e he).elim, ⟨hf, hext'⟩, hind⟩

/-- **The driver hypothesis of layer 2 for a checked function** (`IselThread.Witness.driverHypA`'s
construction): for `csem Γ.F fctx X` and `RelW Γ f c`, when `fctx`'s slot base is `Γ`'s slot
offset and `X`'s symbols are `Γ`'s. -/
theorem driverHyp_of {f : Clif.Function} {vc : VCode} {Γ : E2E.Rel} {fctx : FnCtx} {X : ExtSem}
    {c : BitVec 64} {env : Clif.Env} {p : Clif.Program}
    (hlow : lowerCheck f vc = true) (hthr : IselCheck.threadCheck f = true)
    (hext : f.externs = []) (hind : indSigs f = []) (hv : verifiable f = true)
    (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps)) (hout0 : vc.outgoing = 0)
    (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    ∃ ctx st0 R gn bl A, DriverHyp f vc ctx st0 R gn bl A (csem Γ.F fctx X) (RelW Γ f c) env p ∧
      IselCheck.threadCheckBl f bl = true := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hbl⟩ :=
    IselCheck.obligations_of_threadCheck hlow hthr
  have hsub := inSubset_of hv hext p
  have hX : XCallsOk env (f.externs.map (·.2)) (RelW Γ f c) X := by
    rw [hext]; intro ext h; cases h
  have hXI : XCallsIndOk env (indSigs f) (RelW Γ f c) X := by
    rw [hind]; intro s h; cases h
  have hRef : Refines Γ.F (csem Γ.F fctx X) := refines_csem Γ.F fctx X
  have hmem : MemRefines Γ.F Γ.slotOff Γ.syms (csem Γ.F fctx X) :=
    memRefines_csem Γ.F fctx X hslot hsym
  have hcalls := callsRefine_csem (F := Γ.F) (ctx := fctx) hX
  have hicalls := indCallsRefine_csem (F := Γ.F) (ctx := fctx) hXI hsym
    (fun _ _ _ h => h.1.1.symbols)
  have houtB : vc.outgoing ≤ Γ.out := by rw [hout0]; exact Nat.zero_le _
  refine ⟨ctx, st0, R, gn, bl, A, {
    shape := hshape
    cert := hcert
    dsem := (driverSem_csem Γ.F fctx X).toDriverSemG
    insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
      indRulesCorrect memRulesCorrect_program hRef (mrStable_relW Γ f c) hcalls hicalls hmem
      (outArgsOk_relW Γ f c) (callsStack_mono (callsStack_of_check hlow) houtB)
      (memRelOk_relW Γ f c)
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef (mrStable_relW Γ f c)
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hlow
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨_, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) hcalls, tryStack_mono (tryStack_of_check hlow) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef
      (mrStable_relW Γ f c) hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := hcfg }, hbl⟩

/-! ## `fence; return`, compiled -/

/-- `fence; return`. -/
def srcF : String := "function %fence() {
block0:
    fence
    return
}
"

/-- The parsed function. -/
def fF : Clif.Function :=
  match Clif.parse srcF with
  | .ok p => p.funcs.headD default
  | .error _ => default

/-- Its lowering. -/
def vcF : VCode := match lowerFunction fF with
  | .ok vc => vc
  | .error _ => default

/-- `prepare`'s output. -/
def vcpF : VCode := match Backend.prepare vcF with
  | .ok vcp => vcp
  | .error _ => default

/-- The spill allocation (saves, `fence`, restores, return). -/
def rfF : RFunc := spillAlloc vcpF

/-- The activation. -/
abbrev RA : RL := ArmAllocThread.Witness.act vcpF rfF

/-- The checks on `fF`, its lowering, `prepare` and the allocation. -/
theorem checksF : lowerCheck fF vcF = true ∧ IselCheck.threadCheck fF = true ∧
    fF.externs.isEmpty = true ∧ (indSigs fF).isEmpty = true ∧ verifiable fF = true ∧
    IselThread.Witness.isOkB vcF.cfg = true ∧ vcF.outgoing = 0 ∧ prepCheck vcF vcpF = true ∧
    (checkAlloc vcpF rfF).isOk = true ∧ rfF.blocks.size = 1 ∧ (rfF.blocks[0]!).size = 39 := by
  native_decide

theorem allocF : checkAlloc vcpF rfF = .ok () := by
  have h := checksF.2.2.2.2.2.2.2.2.1
  revert h
  cases checkAlloc vcpF rfF with
  | ok u => intro _; rfl
  | error e => intro h; cases h

theorem cfgF : ∃ ss ps, vcF.cfg = .ok (ss, ps) := by
  have hb := checksF.2.2.2.2.2.1
  revert hb
  cases vcF.cfg with
  | ok r => intro _; exact ⟨r.1, r.2, rfl⟩
  | error e => intro h; cases h

/-- The activation's lowering, emission and layout succeed (by evaluation). -/
theorem factsF : (lowerRFunc vcpF rfF).toBool = true ∧ (emitFunc 0 RA.af).toBool = true ∧
    RA.fa.k = 0 ∧ RA.fa.layout.toBool = true ∧ (labelOffsets RA.fa.lines).toBool = true ∧
    4 * RA.fb.words.size ≤ 2 ^ 64 ∧ RA.af.frameSize ≤ 0x100 ∧ 4 * RA.fb.words.size ≤ 0x10000 ∧
    (emitPlan RA.fa.k RA.af).toBool = true := by
  native_decide

theorem wfRA : RA.Wf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := factsF
  exact ArmAllocThread.Witness.wf_of allocF h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem codeRA : ∀ k < RA.fb.words.size,
    Arm.read_mem_bytes 4 (0x10000#64 + BitVec.ofNat 64 (4 * k)) RA.s0 = RA.fb.words[k]! := by
  native_decide

/-- The entry `args` of `vc` reads no register. -/
def entryNoArgs (vc : VCode) : Bool :=
  match vc.blocks[0]? with
  | some vb => match vb.insts[0]? with
    | some (MInst.args ds) => ds.isEmpty
    | _ => true
  | none => true

theorem not_entryArg {vc : VCode} (h : entryNoArgs vc = true) (r : Reg) : ¬ vc.EntryArg r := by
  rintro ⟨vb, ds, h1, h2, v, hv⟩
  simp only [entryNoArgs, h1, h2, List.isEmpty_iff] at h
  subst h
  cases hv

theorem entryArgRA : ∀ r, RA.vc.EntryArg r → r.isArgReg = true := fun r h =>
  absurd h (not_entryArg (by native_decide : entryNoArgs vcpF = true) r)

/-- The entry world of the body. -/
abbrev w₀F : ArmState := E2E.bodyOf RA.af RA.s0

/-- **`Q ∧ AInv` at the allocated code's entry configuration** after the prologue. -/
theorem qRA : ∃ n, Q RA (iterN RA.step n RA.s0)
      (MConf.init RA.rf (locVal RA.fr (iterN RA.step n RA.s0)) w₀F) ∧
    AInv RA (MConf.init RA.rf (locVal RA.fr (iterN RA.step n RA.s0)) w₀F) := by
  obtain ⟨n, -, hq, hA, -⟩ := q_init wfRA (ArmAllocThread.Witness.abi_of factsF.2.2.2.2.2.2.2.1 codeRA)
    ((E2E.Binary.bodyEntry_bodyOf RA.af RA.s0).w RA.F entryArgRA)
  exact ⟨n, hq, hA⟩

/-- The memory forms `MemScope` admits, as a check. -/
def memFormB : MInst → Bool
  | .fence | .args _ | .rets _ => true
  | _ => false

theorem memScope_of {R : RL} (h : R.vc.blocks.all (·.insts.all memFormB) = true) : MemScope R := by
  intro b vb k i hb hi
  obtain ⟨hb', rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨hk', rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  have h1 := (Array.all_eq_true.mp h) b hb'
  have h2 := (Array.all_eq_true.mp h1) k hk'
  revert h2
  generalize R.vc.blocks[b].insts[k] = i
  intro h2
  cases i with
  | fence => exact .inr (.inl rfl)
  | args ds => exact .inl (.inr (.inl ⟨ds, rfl⟩))
  | rets us => exact .inl (.inr (.inr (.inl ⟨us, rfl⟩)))
  | _ => simp [memFormB] at h2

theorem scopeRA : MemScope RA := memScope_of (by native_decide)

/-! ## The CLIF entry -/

/-- The function's entry block. -/
def B0F : Clif.Block := fF.blocks.headD default

/-- **The CLIF entry state**: block 0, no arguments, no slots, empty memory. -/
def csF : Clif.State :=
  { frame := { func := fF, regs := Clif.Regs.empty, slots := [], body := B0F.body, term := B0F.term }
    callers := []
    mem := Clif.Mem.empty }

/-- The memory relation's parameters: the activation's private set, no symbols, its slot base,
no outgoing area. -/
def ΓF : E2E.Rel := ⟨RA.F, fun _ => none, RA.ctx.slotBase, 0⟩

theorem shapeF : fF.blocks.isEmpty = false ∧ B0F.params.isEmpty = true ∧
    fF.sig.params.isEmpty = true ∧ (locsOf fF.sig).isEmpty = true ∧
    (E2E.spv w₀F).toNat % 16 = 0 := by
  native_decide

theorem b0F : fF.blocks[0]? = some B0F := by
  have h := shapeF.1
  unfold B0F
  revert h
  cases fF.blocks with
  | nil => intro h; cases h
  | cons b bs => intro _; rfl

theorem errW₀ : Arm.r .ERR w₀F = .None := by
  rw [E2E.r_bodyOf _ _ (by simp) (by simp)]
  exact (ArmAllocThread.Witness.abi_of factsF.2.2.2.2.2.2.2.1 codeRA).err

theorem relF : E2E.RelW ΓF fF (E2E.spv w₀F) [] Clif.Mem.empty w₀F :=
  ⟨⟨⟨fun a b hv _ => by simp [Clif.Mem.valid, Clif.Mem.empty] at hv,
      fun a n hv => by simp [Clif.Mem.valid, Clif.Mem.empty] at hv, rfl⟩,
    fun id b h => by simp at h, E2E.outRel_zero _ _ _⟩, rfl, errW₀⟩

theorem argsF : ArgsAtEntry RA.F fF.sig [] w₀F := fun loc v h => by simp at h

/-- `Compiled` for the compiled `fence; return` at every Arm state `Q`-related to its entry
configuration (with the store that state holds). -/
theorem compiled_of {s : ArmState} (hq : Q RA s (MConf.init RA.rf (locVal RA.fr s) w₀F))
    (hA : AInv RA (MConf.init RA.rf (locVal RA.fr s) w₀F)) (env : Clif.Env) (p : Clif.Program) :
    Compiled env p RA csF s := by
  obtain ⟨hlow, hthr, hext, hind, hv, -, hout, hprep, -⟩ := checksF
  obtain ⟨ctx, st0, R, gn, bl, A, H, hbl⟩ := driverHyp_of (Γ := ΓF) (fctx := RA.ctx) (X := RA.X)
    (c := E2E.spv w₀F) (env := env) (p := p) hlow hthr (List.isEmpty_iff.mp hext)
    (List.isEmpty_iff.mp hind) hv cfgF hout rfl (fun _ _ h => by cases h)
  obtain ⟨-, hpar, hsig, hlocs, hc⟩ := shapeF
  have hpar' : B0F.params = [] := List.isEmpty_iff.mp hpar
  exact {
    wf := wfRA
    scope := scopeRA
    gv := rfl
    front := ⟨fF, vcF, ctx, st0, R, gn, bl, A, _, [], ΓF.slotOff, ΓF.syms, B0F, [], _, w₀F, H, hbl,
      E2E.memRelOk_relW ΓF fF _, IselRefines.Witness.relW_wf hc,
      VCodeThread.Witness.X0_tls, memRefines_csem RA.F RA.ctx _ rfl (fun _ _ h => by cases h),
      E2E.mrStable_relW ΓF fF _,
      (fun off h => by simp [List.isEmpty_iff.mp hlocs] at h),
      hprep, allocF, b0F, rfl, rfl, rfl, rfl, rfl, by simp [hpar', csF], by simp [hpar'],
      by simp [List.isEmpty_iff.mp hsig], relF, argsF, hq, hA⟩ }

/-- **Non-vacuity of `Compiled`**: the compiled `fence; return` (`RA`), the CLIF entry state
`csF`, and the Arm state after the prologue. -/
theorem compiledF : ∃ n, ∀ (env : Clif.Env) (p : Clif.Program),
    Compiled env p RA csF (iterN RA.step n RA.s0) := by
  obtain ⟨n, hq, hA⟩ := qRA
  exact ⟨n, compiled_of hq hA⟩

/-- The allocation has moves (the saves of the callee-saved registers). -/
theorem not_noMovesF : ¬ NoMoves RA := by
  have h : (rfF.blocks[0]!).toList.any (fun it => match it with | .move .. => true | _ => false) =
      true := by native_decide
  intro hnm
  obtain ⟨it, hit, hm⟩ := List.any_eq_true.mp h
  have hb : rfF.blocks[0]? = some rfF.blocks[0]! := by
    rw [Array.getElem?_eq_getElem (by rw [checksF.2.2.2.2.2.2.2.2.2.1]; omega)]
    simp [getElem!_def, Array.getElem?_eq_getElem (by rw [checksF.2.2.2.2.2.2.2.2.2.1]; omega :
      0 < rfF.blocks.size)]
  cases it with
  | move src dst => exact hnm 0 _ hb src dst hit
  | op => simp at hm

/-- **Non-vacuity of `arm_alloc_refines_mv`** (beyond `arm_alloc_refines_mem`): the compiled
`fence; return` with its spill allocation (`RA`) satisfies its premises — `R.Wf`, the memory
scope, `Q ∧ AInv` at `MConf.init` after the prologue — and its allocation has moves. -/
theorem mv_premises : RA.Wf ∧ MemScope RA ∧ ¬ NoMoves RA ∧ ∃ n, Q RA (iterN RA.step n RA.s0)
      (MConf.init RA.rf (locVal RA.fr (iterN RA.step n RA.s0)) w₀F) ∧
    AInv RA (MConf.init RA.rf (locVal RA.fr (iterN RA.step n RA.s0)) w₀F) ∧
    ∀ (mon : Mon) (ls : List Lab) (t' : ArmState × Mon),
      PRun Policy.arm RA.step (OkPriv RA) (iterN RA.step n RA.s0, mon) ls t' →
      ∃ k trS cE ψ, k ≤ ls.length ∧ AllocThread.MTRun RA.vc RA.rf RA.sem ckeep (cEvs RA.F RA.ctx)
        (MConf.init RA.rf (locVal RA.fr (iterN RA.step n RA.s0)) w₀F) trS cE ∧
        Refines (· = ·) (PrivA RA) (MonPair (evTr (ls.take k))) (PrepThread.conv trS)
          (PrepThread.conv (evTr (ls.take k))) ψ ∧ (k = ls.length ∨ Done RA cE) := by
  obtain ⟨n, hq, hA⟩ := qRA
  exact ⟨wfRA, scopeRA, not_noMovesF, n, hq, hA, fun _ _ _ hr =>
    arm_alloc_refines_mv wfRA scopeRA hq hA hr⟩

/-! ## The contract on the empty run -/

/-- The Arm threads of the empty run: one thread after the prologue, no steps. -/
noncomputable def PA0 (n : Nat) : Traces ProgE2E.AState AKind BVal :=
  ⟨1, fun _ => [], fun _ _ => (RA.step, iterN RA.step n RA.s0, none)⟩

/-- **Non-vacuity of `realizes_compiled`** (one thread, the compiled `fence; return`, the empty Arm
run): the empty execution is realized by a CLIF thread from `csF`. -/
theorem realizes_nil : ∃ n, ∀ (env : Clif.Env) (p : Clif.Program),
    ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧ PC.st 0 0 = .run csF ∧
      PC.Runs (CStep env p) ∧
      Realizes (PA0 n) [] (fun _ => none) (fun _ _ => False) (coW (PA0 n)) (fun _ _ => False) PC []
        (fun _ => none) φ (fun _ _ _ => True) := by
  obtain ⟨n, hc⟩ := compiledF
  refine ⟨n, fun env p => ?_⟩
  obtain ⟨k, -, hR⟩ := realizes_compiled (n := 1) (env := env) (p := p) (RA := fun _ => RA)
    (cs := fun _ => csF) (sA := fun _ => iterN RA.step n RA.s0) (fun _ _ => hc env p)
    (mon := fun _ => none) (ls := fun _ => []) (t' := fun _ => (iterN RA.step n RA.s0, none))
    (fun _ _ => .nil)
  obtain ⟨PC, φ, h1, h2, h3, h4⟩ := hR (PA0 n) [] [] (fun _ => none) (fun _ => none)
    (fun _ _ => False) (coW (PA0 n)) (fun _ _ => False) rfl (fun _ _ => by simp [PA0, evTr, conv])
    (wf_noReads _ fun e x h => by cases e <;> simp [Traces.evAt, PA0] at h)
    (fun i _ a b => ⟨False.elim, fun ⟨⟨x, hx, _⟩, _⟩ => by simp [evAt, evTr] at hx⟩)
    (List.nil_prefix) (fun q h => absurd h (Nat.not_lt_zero _))
    (fun q h => absurd h (Nat.not_lt_zero _)) (fun i hi j hj hne => by omega)
  exact ⟨PC, φ, h1, h2 0 (by omega), h3, h4⟩

end Concurrency.RealizeCompiled.Witness
