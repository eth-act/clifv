import FV.E2E.PassTypedCleanup
import FV.E2E.ConstPhiE2EWitness
import FV.E2E.TypedRulesProg

/-! # Witness: the typed theorems composed with constant-phi removal and `i128` legalisation (#1112)

Each theorem of `FV/E2E/PassTypedCleanup.lean` applies to functions outside subset E that the
transformation really changes, compiled by the shipped typed pipeline with the dead cleanup
(closed receipts by `native_decide`, the convention of `FV/E2E/ConstPhiE2EWitness.lean`):

* constant-phi removal: `E2E.ConstPhiE2EWitness.fwdF` (`block1(v1: f64)` receives only `v0`; the
  pass removes `v1`), `T := Opt.ConstPhi.run`;
* legalisation: `srcL` (`(i128, f64) -> f64`, returns its `f64` argument; the legalisation splits
  the `i128` parameter), accepted by `Opt.Legal.checkW`;
* both: `srcLP` (`srcL` with the `f64` passed through a block parameter that only receives it),
  legalised, then constant-phi removal.

Discharged: the subset (`InSubsetT/TC/TCF.of_verifiable…`), the artifact (`CompiledCleanupT/TC/TCF`
of the receipt's objects), `FormsCovered`, the `try_call`, TLS, extern and indirect-call contracts
(none of these functions has one), the legalisation's program conditions (a function-free
program). Left open, as in `ConstPhiE2EWitness`: the machine's callee contract (`hC`), the
linker's symbol addresses (`hsym`) and the run's entry premises. -/

namespace FVTest.Backend.TypedPassWitness

open _root_.Backend _root_.Backend.Proof _root_.Backend.Proof.Driver _root_.Backend.DeadCleanup E2E
open E2E.DeadCleanupUnwindWitness (ok_getD ok_unit)
open E2E.ConstPhiE2EWitness (fwdF cp)
set_option autoImplicit false

/-! ## The compiled objects and their receipts -/

/-- What the typed pipeline with the dead cleanup computes for a function. -/
structure Objs where
  vc : VCode
  vcp : VCode
  rf : RFunc
  af : AFunc
  fa : FnAsm
  fb : FnBin

/-- The objects for `f` with the cleanup stage `st` (`cleanupStage f` for `CompiledCleanupT`,
`DeadCleanup.prune` for `CompiledCleanupTC`/`TCF`) and the spill allocation. -/
def objs (st : VCode → VCode) (f : Clif.Function) : Objs :=
  let vc := (lowerFunction f).toOption.getD default
  let vcp := (Backend.prepare (st vc)).toOption.getD default
  let rf := spillAlloc vcp
  let af := (lowerRFunc vcp rf).toOption.getD default
  let fa := (emitFunc 0 af).toOption.getD default
  ⟨vc, vcp, rf, af, fa, fa.layout.toOption.getD default⟩

/-- The checks every receipt has: no extern, indirect call, `try_call` or TLS; the pipeline runs,
`formsCoveredB`. -/
def pipe (st : VCode → VCode) (f : Clif.Function) : Bool :=
  f.externs.isEmpty && (indSigs f).isEmpty && f.blocks.all (fun B => !B.term.isTry) &&
  !hasTls f && (lowerFunction f).toBool && (Backend.prepare (st (objs st f).vc)).toBool &&
  prepCheck (st (objs st f).vc) (objs st f).vcp && (checkAlloc (objs st f).vcp (objs st f).rf).toBool &&
  (lowerRFunc (objs st f).vcp (objs st f).rf).toBool && (emitFunc 0 (objs st f).af).toBool &&
  (objs st f).fa.layout.toBool &&
  formsCoveredB ⟨(objs st f).fa.k, (objs st f).af.slotBase⟩ (objs st f).vcp

def recT (f : Clif.Function) : Bool :=
  verifiableT f && lowerCheckT f (objs (cleanupStage f) f).vc && pipe (cleanupStage f) f

def recTC (f : Clif.Function) : Bool :=
  verifiableTC f && lowerCheckTC f (objs DeadCleanup.prune f).vc && pipe DeadCleanup.prune f

def recTCF (f : Clif.Function) : Bool :=
  verifiableTCF f && lowerCheckTCF f (objs DeadCleanup.prune f).vc && pipe DeadCleanup.prune f

/-- The contract facts of a receipt. -/
structure Shape (f : Clif.Function) : Prop where
  externs : f.externs = []
  ind : indSigs f = []
  noTry : ¬ ∃ B ∈ f.blocks, B.term.isTry = true
  tls : hasTls f = false

theorem shape_of {st : VCode → VCode} {f : Clif.Function} (h : pipe st f = true) : Shape f := by
  simp only [pipe, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, List.all_eq_true,
    and_assoc] at h
  obtain ⟨hext, hind, htry, htls, -⟩ := h
  refine ⟨hext, hind, ?_, htls⟩
  rintro ⟨B, hB, hT⟩
  have := htry B hB
  simp [hT] at this

theorem factsT {f : Clif.Function} (h : recT f = true) {p : Clif.Program}
    (hp : ∀ n, p.func? n = none) :
    InSubsetT p f ∧ CompiledCleanupT f 0 (objs (cleanupStage f) f).vc (objs (cleanupStage f) f).vcp
      (objs (cleanupStage f) f).rf (objs (cleanupStage f) f).af (objs (cleanupStage f) f).fa
      (objs (cleanupStage f) f).fb ∧
    FormsCovered ⟨(objs (cleanupStage f) f).fa.k, (objs (cleanupStage f) f).af.slotBase⟩
      (objs (cleanupStage f) f).vcp ∧ Shape f := by
  have hS : Shape f := shape_of (by simp only [recT, Bool.and_eq_true] at h; exact h.2)
  simp only [recT, pipe, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hv, hlc, -, -, -, -, hl, hpr, hpc, hca, hal, hem, hla, hcov⟩ := h
  exact ⟨InSubsetT.of_verifiableT hv hp, ⟨ok_getD hl, hlc, ok_getD hpr, hpc, ok_unit hca,
    ok_getD hal, ok_getD hem, ok_getD hla⟩, (formsCoveredB_iff _ _).mp hcov, hS⟩

theorem factsTC {f : Clif.Function} (h : recTC f = true) {p : Clif.Program}
    (hp : ∀ n, p.func? n = none) :
    InSubsetTC p f ∧ CompiledCleanupTC f 0 (objs DeadCleanup.prune f).vc
      (objs DeadCleanup.prune f).vcp (objs DeadCleanup.prune f).rf (objs DeadCleanup.prune f).af
      (objs DeadCleanup.prune f).fa (objs DeadCleanup.prune f).fb ∧
    FormsCovered ⟨(objs DeadCleanup.prune f).fa.k, (objs DeadCleanup.prune f).af.slotBase⟩
      (objs DeadCleanup.prune f).vcp ∧ Shape f := by
  have hS : Shape f := shape_of (by simp only [recTC, Bool.and_eq_true] at h; exact h.2)
  simp only [recTC, pipe, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hv, hlc, -, -, -, -, hl, hpr, hpc, hca, hal, hem, hla, hcov⟩ := h
  exact ⟨InSubsetTC.of_verifiableTC hv hp, ⟨ok_getD hl, hlc, ok_getD hpr, hpc, ok_unit hca,
    ok_getD hal, ok_getD hem, ok_getD hla⟩, (formsCoveredB_iff _ _).mp hcov, hS⟩

theorem factsTCF {f : Clif.Function} (h : recTCF f = true) {p : Clif.Program}
    (hp : ∀ n, p.func? n = none) :
    InSubsetTCF p f ∧ CompiledCleanupTCF f 0 (objs DeadCleanup.prune f).vc
      (objs DeadCleanup.prune f).vcp (objs DeadCleanup.prune f).rf (objs DeadCleanup.prune f).af
      (objs DeadCleanup.prune f).fa (objs DeadCleanup.prune f).fb ∧
    FormsCovered ⟨(objs DeadCleanup.prune f).fa.k, (objs DeadCleanup.prune f).af.slotBase⟩
      (objs DeadCleanup.prune f).vcp ∧ Shape f := by
  have hS : Shape f := shape_of (by simp only [recTCF, Bool.and_eq_true] at h; exact h.2)
  simp only [recTCF, pipe, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hv, hlc, -, -, -, -, hl, hpr, hpc, hca, hal, hem, hla, hcov⟩ := h
  exact ⟨InSubsetTCF.of_verifiableTCF hv hp, ⟨ok_getD hl, hlc, ok_getD hpr, hpc, ok_unit hca,
    ok_getD hal, ok_getD hem, ok_getD hla⟩, (formsCoveredB_iff _ _).mp hcov, hS⟩

/-! ## The functions -/

/-- `function %lt(i128, f64) -> f64 { block0(v0: i128, v1: f64): return v1 }`. -/
def srcL : Clif.Function where
  name := "lt"
  sig := { params := [{ ty := .i128 }, { ty := .f64 }], returns := [{ ty := .f64 }] }
  blocks := [{ id := 0, params := [(0, .i128), (1, .f64)], term := .ret [1] }]

/-- `srcL` with the `f64` passed through `block1(v2: f64)`, which only receives `v1`. -/
def srcLP : Clif.Function where
  name := "lp"
  sig := { params := [{ ty := .i128 }, { ty := .f64 }], returns := [{ ty := .f64 }] }
  blocks := [
    { id := 0, params := [(0, .i128), (1, .f64)], term := .jump ⟨1, [1]⟩ },
    { id := 1, params := [(2, .f64)], term := .ret [2] }]

/-- The legalisation (`Opt.Legalize128.function128Cert`) and its certificate. -/
def legalOf (f : Clif.Function) : Clif.Function × Opt.Legalize128.Cert :=
  match Opt.Legalize128.function128Cert f with
  | .ok r => r
  | .error _ => (f, {})

/-- The receipts, closed by `native_decide`: the validators accept the legalisations, constant-phi
removal changes `fwdF` and the legalisation of `srcLP`, and the typed pipeline compiles every
compiled function in each scope. Not used by any compiler correctness theorem. -/
def receipts : Bool :=
  Opt.Legal.checkW srcL (legalOf srcL).1 (legalOf srcL).2 &&
  Opt.Legal.checkW srcLP (legalOf srcLP).1 (legalOf srcLP).2 &&
  decide (cp fwdF ≠ fwdF) && decide (cp (legalOf srcLP).1 ≠ (legalOf srcLP).1) &&
  [cp fwdF, (legalOf srcL).1, cp (legalOf srcLP).1].all fun f => recT f && recTC f && recTCF f

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem receipts_true : receipts = true := by native_decide -- witness: native_decide

theorem rec_all : Opt.Legal.checkW srcL (legalOf srcL).1 (legalOf srcL).2 = true ∧
    Opt.Legal.checkW srcLP (legalOf srcLP).1 (legalOf srcLP).2 = true ∧
    ∀ f ∈ [cp fwdF, (legalOf srcL).1, cp (legalOf srcLP).1],
      recT f = true ∧ recTC f = true ∧ recTCF f = true := by
  have h := receipts_true
  simp only [receipts, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h3⟩ := h
  exact ⟨h1, h2, fun f hf => by simpa only [Bool.and_eq_true, and_assoc] using h3 f hf⟩

theorem nil_func (n : String) : ({ funcs := [] } : Clif.Program).func? n = none := rfl

/-- The world conclusion of `backend_correct_world_cleanupTCF` (returns of `rets`) for the
objects `o`, written once for the witnesses below. -/
def WorldR (env : Clif.Env) (p : Clif.Program) (fuel : Nat) (cs : Clif.State)
    (rets : List Clif.AbiParam) (o : Objs) (K : Nat) (F : BitVec 64 → Prop)
    (syms : String → Option Nat) (X : ExtSem) (w₀ : Arm.ArmState) : Prop :=
  (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
    ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
      RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys rets ∧
      us.length = outs.length ∧
      PrefixHold vals outs ∧ MemRel F syms cm w ∧ o.vc.RetsSite us ∧
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry o.vcp o.rf o.af o.fa o.fb K F G X H base ra s w₀ →
        ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H o.fa) n s) ∧
          PostTrace o.fa o.af base (ArmStepX X H o.fa) s n) ∧
  (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
    ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntry o.vcp o.rf o.af o.fa o.fb K F G X H base ra s w₀ →
      ∃ n, TrapAt o.fb base c' (runX (ArmStepX X H o.fa) n s))

/-- `WorldR` for a legalised function: returns expanded by the ABI groups `rg`. -/
def WorldLR (rg : List (List Opt.Legalize128.SlotEl)) (env : Clif.Env) (p : Clif.Program)
    (fuel : Nat) (cs : Clif.State) (rets : List Clif.AbiParam) (o : Objs) (K : Nat)
    (F : BitVec 64 → Prop) (syms : String → Option Nat) (X : ExtSem) (w₀ : Arm.ArmState) : Prop :=
  (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
    ∃ vals', Opt.Legal.ExpRel rg vals vals' ∧
    ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
      RetRegsOk vals' us ∧ vals'.map (·.ty) = Clif.AbiParam.tys rets ∧
      us.length = outs.length ∧
      PrefixHold vals' outs ∧ MemRel F syms cm w ∧ o.vc.RetsSite us ∧
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry o.vcp o.rf o.af o.fa o.fb K F G X H base ra s w₀ →
        ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H o.fa) n s) ∧
          PostTrace o.fa o.af base (ArmStepX X H o.fa) s n) ∧
  (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
    ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntry o.vcp o.rf o.af o.fa o.fb K F G X H base ra s w₀ →
      ∃ n, TrapAt o.fb base c' (runX (ArmStepX X H o.fa) n s))

/-! ## Constant-phi removal: `fwdF` -/

abbrev oPT : Objs := objs (cleanupStage (cp fwdF)) (cp fwdF)
abbrev oPC : Objs := objs DeadCleanup.prune (cp fwdF)

/-- **`backend_correct_pass_final_cleanupT` applies** to the compiled constant-phi removal of
`fwdF`. -/
theorem pass_final_cleanupT_applies {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat}
    {K : Nat} {env : Clif.Env} (hE : Opt.EnvKeepsSymbols env)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute oPT.vcp oPT.rf).intBase (RAFrame.compute oPT.vcp oPT.rf).size
        oPT.af s) K X H oPT.vcp.CallSite)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry oPT.fb base ra s) (hres : StackAvail K oPT.af s) (hbe : BodyEntry oPT.af s w₀)
    (hargs : ArgsIn fwdF.sig args s) (hcs : ClifEntry fwdF args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute oPT.vcp oPT.rf).intBase
      (RAFrame.compute oPT.vcp oPT.rf).size oPT.af s, syms, oPT.af.slotBase,
      (RAFrame.compute oPT.vcp oPT.rf).intBase⟩ fwdF cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env (passProg cp { funcs := [] }) (passEntry cp fwdF cs)) (fuel : Nat) :
    ArmRefinesT oPT.fb base ra (ArmStepX X H oPT.fa) s (Clif.runLoop env { funcs := [] } fuel cs) := by
  obtain ⟨hsub, hc, hcov, hS⟩ :=
    factsT ((rec_all.2.2 (cp fwdF) (by simp)).1) (p := passProg cp { funcs := [] }) nil_func
  exact backend_correct_pass_final_cleanupT (T := cp) Opt.ConstPhi.run_simX Opt.ConstPhi.run_shape
    hsub hc typedRules_program hcov hC (fun h => absurd h hS.noTry)
    (fun h => absurd h (by rw [hS.tls]; decide))
    (fun _ ext hin => by simp [fwdF] at hin)
    (fun _ => by rw [hS.ind]; exact xCallsIndOk_nil _ _ _) hsym rfl hE hent hres hbe hargs hcs hrel
    htr fuel

/-- **`backend_correct_pass_world_cleanupTCF` applies** to the compiled constant-phi removal of
`fwdF`. -/
theorem pass_world_cleanupTCF_applies {X : ExtSem} {syms : String → Option Nat} {K : Nat}
    {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64} (hE : Opt.EnvKeepsSymbols env)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry fwdF args cs)
    (hrel : RelW ⟨F, syms, oPC.af.slotBase, (RAFrame.compute oPC.vcp oPC.rf).intBase⟩ fwdF c
      cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fwdF.sig args w₀)
    (htr : TrapsExplicit env (passProg cp { funcs := [] }) (passEntry cp fwdF cs)) (fuel : Nat) :
    WorldR env { funcs := [] } fuel cs fwdF.sig.returns oPC K F syms X w₀ := by
  obtain ⟨hsub, hc, hcov, hS⟩ :=
    factsTCF ((rec_all.2.2 (cp fwdF) (by simp)).2.2) (p := passProg cp { funcs := [] }) nil_func
  exact backend_correct_pass_world_cleanupTCF (T := cp) (K := K) Opt.ConstPhi.run_simX
    Opt.ConstPhi.run_shape hsub hc typedRules_program hcov (fun ext hin => by simp [fwdF] at hin)
    (by rw [hS.ind]; exact xCallsIndOk_nil _ _ _) hsym rfl hE hcs hrel hargs htr fuel

/-- **`backend_correct_pass_world_cleanupTC` applies** to the compiled constant-phi removal of
`fwdF`. -/
theorem pass_world_cleanupTC_applies {X : ExtSem} {syms : String → Option Nat} {K : Nat}
    {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64} (hE : Opt.EnvKeepsSymbols env)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry fwdF args cs)
    (hrel : RelW ⟨F, syms, oPC.af.slotBase, (RAFrame.compute oPC.vcp oPC.rf).intBase⟩ fwdF c
      cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fwdF.sig args w₀)
    (htr : TrapsExplicit env (passProg cp { funcs := [] }) (passEntry cp fwdF cs)) (fuel : Nat) :
    WorldR env { funcs := [] } fuel cs fwdF.sig.returns oPC K F syms X w₀ := by
  obtain ⟨hsub, hc, hcov, hS⟩ :=
    factsTC ((rec_all.2.2 (cp fwdF) (by simp)).2.1) (p := passProg cp { funcs := [] }) nil_func
  exact backend_correct_pass_world_cleanupTC (T := cp) (K := K) Opt.ConstPhi.run_simX
    Opt.ConstPhi.run_shape hsub hc typedRules_program hcov (fun ext hin => by simp [fwdF] at hin)
    (by rw [hS.ind]; exact xCallsIndOk_nil _ _ _) hsym rfl hE hcs hrel hargs htr fuel

/-! ## Legalisation: `srcL` -/

abbrev gL : Clif.Function := (legalOf srcL).1
abbrev oLT : Objs := objs (cleanupStage gL) gL
abbrev oLC : Objs := objs DeadCleanup.prune gL

/-- **`backend_correct_legal_wide_final_cleanupT` applies** to the compiled legalisation of
`srcL`. -/
theorem legal_wide_final_cleanupT_applies {X : ExtSem} {H : ArmHooks}
    {syms : String → Option Nat} {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute oLT.vcp oLT.rf).intBase (RAFrame.compute oLT.vcp oLT.rf).size
        oLT.af s) K X H oLT.vcp.CallSite)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val}
    {cs cs' : Clif.State}
    (hent : AbiEntry oLT.fb base ra s) (hres : StackAvail K oLT.af s) (hbe : BodyEntry oLT.af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups srcL.sig.params).getD []) args args')
    (hargs : ArgsIn gL.sig args' s) (hcs : ClifEntry srcL args cs) (hcs' : ClifEntry gL args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute oLT.vcp oLT.rf).intBase
      (RAFrame.compute oLT.vcp oLT.rf).size oLT.af s, syms, oLT.af.slotBase,
      (RAFrame.compute oLT.vcp oLT.rf).intBase⟩ gL cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicit Clif.Rust.env { funcs := [] } cs)
    (htr : TrapsExplicit Clif.Rust.env { funcs := [] } cs') (fuel : Nat) :
    ArmRefinesLegalT ((Opt.Legal.groups srcL.sig.returns).getD []) oLT.fb base ra
      (ArmStepX X H oLT.fa) s (Clif.runLoop Clif.Rust.env { funcs := [] } fuel cs) := by
  obtain ⟨hsub, hc, hcov, hS⟩ := factsT ((rec_all.2.2 gL (by simp)).1) (p := { funcs := [] })
    nil_func
  exact backend_correct_legal_wide_final_cleanupT rec_all.1 hsub hc typedRules_program
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => ⟨rfl, List.prefix_refl _⟩) hcov hC
    (fun h => absurd h hS.noTry) (fun h => absurd h (by rw [hS.tls]; decide))
    (fun _ ext hin => by simp [hS.externs] at hin)
    (fun _ => by rw [hS.ind]; exact xCallsIndOk_nil _ _ _) hsym rfl hent hres hbe hexp hargs hcs
    hcs' hsl hmem hrel htrS htr fuel

/-- **`backend_correct_legal_wide_world_cleanupTCF` applies** to the compiled legalisation of
`srcL`. -/
theorem legal_wide_world_cleanupTCF_applies {X : ExtSem} {syms : String → Option Nat} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups srcL.sig.params).getD []) args args')
    (hcs : ClifEntry srcL args cs) (hcs' : ClifEntry gL args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : RelW ⟨F, syms, oLC.af.slotBase, (RAFrame.compute oLC.vcp oLC.rf).intBase⟩ gL c
      cs'.frame.slots cs'.mem w₀)
    (hargs : ArgsAtEntry F gL.sig args' w₀)
    (htrS : TrapsExplicit Clif.Rust.env { funcs := [] } cs)
    (htr : TrapsExplicit Clif.Rust.env { funcs := [] } cs') (fuel : Nat) :
    WorldLR ((Opt.Legal.groups srcL.sig.returns).getD []) Clif.Rust.env { funcs := [] } fuel cs
      gL.sig.returns oLC K F syms X w₀ := by
  obtain ⟨hsub, hc, hcov, hS⟩ := factsTCF ((rec_all.2.2 gL (by simp)).2.2) (p := { funcs := [] })
    nil_func
  exact backend_correct_legal_wide_world_cleanupTCF (K := K) rec_all.1 hsub hc typedRules_program
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => ⟨rfl, List.prefix_refl _⟩) hcov
    (fun ext hin => by simp [hS.externs] at hin)
    (by rw [hS.ind]; exact xCallsIndOk_nil _ _ _) hsym rfl hexp hcs hcs' hsl hmem hrel hargs htrS
    htr fuel

/-- **`backend_correct_legal_wide_world_cleanupTC` applies** to the compiled legalisation of
`srcL`. -/
theorem legal_wide_world_cleanupTC_applies {X : ExtSem} {syms : String → Option Nat} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups srcL.sig.params).getD []) args args')
    (hcs : ClifEntry srcL args cs) (hcs' : ClifEntry gL args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : RelW ⟨F, syms, oLC.af.slotBase, (RAFrame.compute oLC.vcp oLC.rf).intBase⟩ gL c
      cs'.frame.slots cs'.mem w₀)
    (hargs : ArgsAtEntry F gL.sig args' w₀)
    (htrS : TrapsExplicit Clif.Rust.env { funcs := [] } cs)
    (htr : TrapsExplicit Clif.Rust.env { funcs := [] } cs') (fuel : Nat) :
    WorldLR ((Opt.Legal.groups srcL.sig.returns).getD []) Clif.Rust.env { funcs := [] } fuel cs
      gL.sig.returns oLC K F syms X w₀ := by
  obtain ⟨hsub, hc, hcov, hS⟩ := factsTC ((rec_all.2.2 gL (by simp)).2.1) (p := { funcs := [] })
    nil_func
  exact backend_correct_legal_wide_world_cleanupTC (K := K) rec_all.1 hsub hc typedRules_program
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => ⟨rfl, List.prefix_refl _⟩) hcov
    (fun ext hin => by simp [hS.externs] at hin)
    (by rw [hS.ind]; exact xCallsIndOk_nil _ _ _) hsym rfl hexp hcs hcs' hsl hmem hrel hargs htrS
    htr fuel

/-! ## Legalisation, then constant-phi removal: `srcLP` -/

abbrev gLP : Clif.Function := (legalOf srcLP).1
abbrev oQT : Objs := objs (cleanupStage (cp gLP)) (cp gLP)
abbrev oQC : Objs := objs DeadCleanup.prune (cp gLP)

/-- **`backend_correct_legal_pass_wide_final_cleanupT` applies** to the compiled constant-phi
removal of the legalisation of `srcLP`. -/
theorem legal_pass_wide_final_cleanupT_applies {X : ExtSem} {H : ArmHooks}
    {syms : String → Option Nat} {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute oQT.vcp oQT.rf).intBase (RAFrame.compute oQT.vcp oQT.rf).size
        oQT.af s) K X H oQT.vcp.CallSite)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val}
    {cs cs' : Clif.State}
    (hent : AbiEntry oQT.fb base ra s) (hres : StackAvail K oQT.af s) (hbe : BodyEntry oQT.af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups srcLP.sig.params).getD []) args args')
    (hargs : ArgsIn gLP.sig args' s) (hcs : ClifEntry srcLP args cs)
    (hcs' : ClifEntry gLP args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute oQT.vcp oQT.rf).intBase
      (RAFrame.compute oQT.vcp oQT.rf).size oQT.af s, syms, oQT.af.slotBase,
      (RAFrame.compute oQT.vcp oQT.rf).intBase⟩ gLP cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicit Clif.Rust.env { funcs := [] } cs)
    (htr : TrapsExplicit Clif.Rust.env (passProg cp { funcs := [] }) (passEntry cp gLP cs'))
    (fuel : Nat) :
    ArmRefinesLegalT ((Opt.Legal.groups srcLP.sig.returns).getD []) oQT.fb base ra
      (ArmStepX X H oQT.fa) s (Clif.runLoop Clif.Rust.env { funcs := [] } fuel cs) := by
  obtain ⟨hsub, hc, hcov, hS⟩ :=
    factsT ((rec_all.2.2 (cp gLP) (by simp)).1) (p := passProg cp { funcs := [] }) nil_func
  have hext' : gLP.externs = [] := by
    rw [← (Opt.ConstPhi.run_shape gLP).externs]; exact hS.externs
  exact backend_correct_legal_pass_wide_final_cleanupT (T := cp) rec_all.2.1 Opt.ConstPhi.run_simX
    Opt.ConstPhi.run_shape hsub hc typedRules_program (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ => ⟨rfl, List.prefix_refl _⟩) hcov hC (fun h => absurd h hS.noTry)
    (fun h => absurd h (by rw [hS.tls]; decide))
    (fun _ ext hin => by simp [hext'] at hin)
    (fun _ => by rw [hS.ind]; exact xCallsIndOk_nil _ _ _) hsym rfl hent hres hbe hexp hargs hcs
    hcs' hsl hmem hrel htrS htr fuel

/-- **`backend_correct_legal_pass_wide_world_cleanupTCF` applies** to the compiled constant-phi
removal of the legalisation of `srcLP`. -/
theorem legal_pass_wide_world_cleanupTCF_applies {X : ExtSem} {syms : String → Option Nat}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups srcLP.sig.params).getD []) args args')
    (hcs : ClifEntry srcLP args cs) (hcs' : ClifEntry gLP args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : RelW ⟨F, syms, oQC.af.slotBase, (RAFrame.compute oQC.vcp oQC.rf).intBase⟩ gLP c
      cs'.frame.slots cs'.mem w₀)
    (hargs : ArgsAtEntry F gLP.sig args' w₀)
    (htrS : TrapsExplicit Clif.Rust.env { funcs := [] } cs)
    (htr : TrapsExplicit Clif.Rust.env (passProg cp { funcs := [] }) (passEntry cp gLP cs'))
    (fuel : Nat) :
    WorldLR ((Opt.Legal.groups srcLP.sig.returns).getD []) Clif.Rust.env { funcs := [] } fuel cs
      gLP.sig.returns oQC K F syms X w₀ := by
  obtain ⟨hsub, hc, hcov, hS⟩ :=
    factsTCF ((rec_all.2.2 (cp gLP) (by simp)).2.2) (p := passProg cp { funcs := [] }) nil_func
  have hext' : gLP.externs = [] := by
    rw [← (Opt.ConstPhi.run_shape gLP).externs]; exact hS.externs
  exact backend_correct_legal_pass_wide_world_cleanupTCF (T := cp) (K := K) rec_all.2.1
    Opt.ConstPhi.run_simX Opt.ConstPhi.run_shape hsub hc typedRules_program (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => ⟨rfl, List.prefix_refl _⟩) hcov
    (fun ext hin => by simp [hext'] at hin)
    (by rw [hS.ind]; exact xCallsIndOk_nil _ _ _) hsym rfl hexp hcs hcs' hsl hmem hrel hargs htrS
    htr fuel

/-- **`backend_correct_legal_pass_wide_world_cleanupTC` applies** to the compiled constant-phi
removal of the legalisation of `srcLP`. -/
theorem legal_pass_wide_world_cleanupTC_applies {X : ExtSem} {syms : String → Option Nat}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups srcLP.sig.params).getD []) args args')
    (hcs : ClifEntry srcLP args cs) (hcs' : ClifEntry gLP args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : RelW ⟨F, syms, oQC.af.slotBase, (RAFrame.compute oQC.vcp oQC.rf).intBase⟩ gLP c
      cs'.frame.slots cs'.mem w₀)
    (hargs : ArgsAtEntry F gLP.sig args' w₀)
    (htrS : TrapsExplicit Clif.Rust.env { funcs := [] } cs)
    (htr : TrapsExplicit Clif.Rust.env (passProg cp { funcs := [] }) (passEntry cp gLP cs'))
    (fuel : Nat) :
    WorldLR ((Opt.Legal.groups srcLP.sig.returns).getD []) Clif.Rust.env { funcs := [] } fuel cs
      gLP.sig.returns oQC K F syms X w₀ := by
  obtain ⟨hsub, hc, hcov, hS⟩ :=
    factsTC ((rec_all.2.2 (cp gLP) (by simp)).2.1) (p := passProg cp { funcs := [] }) nil_func
  have hext' : gLP.externs = [] := by
    rw [← (Opt.ConstPhi.run_shape gLP).externs]; exact hS.externs
  exact backend_correct_legal_pass_wide_world_cleanupTC (T := cp) (K := K) rec_all.2.1
    Opt.ConstPhi.run_simX Opt.ConstPhi.run_shape hsub hc typedRules_program (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => ⟨rfl, List.prefix_refl _⟩) hcov
    (fun ext hin => by simp [hext'] at hin)
    (by rw [hS.ind]; exact xCallsIndOk_nil _ _ _) hsym rfl hexp hcs hcs' hsl hmem hrel hargs htrS
    htr fuel

end FVTest.Backend.TypedPassWitness
