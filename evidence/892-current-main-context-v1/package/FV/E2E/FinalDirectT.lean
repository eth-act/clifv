import FV.E2E.FinalT
import FV.Backend.Proof.LowerCompleteT
import FV.Backend.Proof.SpillInstCheck
import FV.Backend.Proof.SpillLocalPipeT
import FV.Backend.Proof.SpillArity

/-!
# The typed final theorem without the lowering and `prepare` validators (S11e5 Stage C, slice 7)

On `Dominated` input in the typed scope (`LowerScopeT`) the typed lowering validator accepts
`lowerFunction`'s output (`lowerCheckT_complete`) and `prepCheck` accepts `prepare`'s
(`prepCheck_complete` on the typed `PrepDomain`, `prepDomain_ofT`): `CompiledAT.of_lowerT`,
`CompiledT.of_lowerT`. With slice 6's typed spill chain (`allocChecked_allocResultT`, under the
run-time-decided premises `arityOkB`, `tryArgClassOk`, `resClassOkB`, `ctlSpillB`,
`formsCoveredB`, `killFreeB`), the allocation the backend lowers is `AllocChecked` whatever the
untrusted allocator answered: `backend_correct_finalT_alloc`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Prep

/-- **`CompiledAT` without the validator premises**: the pipeline's results and the typed input
conditions `Dominated f`, `LowerScopeT f`. -/
theorem CompiledAT.of_lowerT {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hd : Dominated f) (hs : LowerScopeT f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hch : AllocChecked vcp rf) (ha : lowerRFunc vcp rf = .ok af)
    (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb) :
    CompiledAT f k vc vcp rf af fa fb :=
  ⟨hl, lowerCheckT_complete hd hs hl, hp, prepCheck_complete hp (prepDomain_ofT hd hs hl), hch,
    ha, he, hla⟩

/-- **`CompiledT` without the validator premises** (`checkAlloc`'s verdict). -/
theorem CompiledT.of_lowerT {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hd : Dominated f) (hs : LowerScopeT f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hch : checkAlloc vcp rf = .ok ()) (ha : lowerRFunc vcp rf = .ok af)
    (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb) :
    CompiledT f k vc vcp rf af fa fb :=
  ⟨hl, lowerCheckT_complete hd hs hl, hp, prepCheck_complete hp (prepDomain_ofT hd hs hl), hch,
    ha, he, hla⟩

/-- **The typed final theorem for the fallback-composed allocation**: `backend_correct_final_exT`
with `rf := allocResult vcp ra` for any answer `ra` of the untrusted allocator and no
allocation-checker premise (slice 6's `allocChecked_allocResultT`), from the pipeline's results,
the typed input conditions and the run-time-decided spill/control facts. -/
theorem backend_correct_finalT_alloc {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {ra : Except String RFunc} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} (hsub : InSubsetT p f) (hT : TypedRules) (hd : Dominated f) (hs : LowerScopeT f)
    (har : arityOkB f = true) (htc : Compile.tryArgClassOk f = true) (hrc : resClassOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hctl : ctlSpillB vc = true) (hform : formsCoveredB default vcp = true)
    (hk : killFreeB vcp = true)
    (hrf : rf = allocResult vcp ra) (ha : lowerRFunc vcp rf = .ok af)
    (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb)
    (hcov : formsCoveredB ⟨fa.k, af.slotBase⟩ vcp = true)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra' : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra' s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesT fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  have hch : AllocChecked vcp rf := hrf ▸ allocChecked_allocResultT hd hs (arityOk_of har) htc
    (resClassOk_of_resClassOkB hrc) hl hp (ctlSpill_of_ctlSpillB hctl)
    ((formsCoveredB_iff _ _).mp hform) hk ra
  exact backend_correct_final_exT hsub (CompiledAT.of_lowerT hd hs hl hp hch ha he hla) hT
    ((formsCoveredB_iff _ _).mp hcov) hC hCT hTls hX hXI hsym hslot hent hres hbe hargs hcs hrel
    htr fuel

end E2E
