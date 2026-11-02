import FV.E2E.StockVoidCallDomain
import FV.E2E.StockVoidCallWitness
import FV.E2E.ABIReadOnlyTransport
import FV.E2E.PairDriverF

namespace Backend.Stock.VoidCall.NI
set_option autoImplicit false
set_option Elab.async false

def instruction (sig : Clif.Signature) (b k : Nat) (i : MInst) : Bool :=
  match i with
  | .call _ => true
  | _ => Backend.ABIReadOnly.instruction sig b k i

def codeCheck (sig : Clif.Signature) (vc : VCode) : Bool :=
  vc.blocks.toList.zipIdx.all fun (block,b) =>
    block.insts.toList.zipIdx.all fun (i,k) => instruction sig b k i

/-- Actual checked code retains a finite read boundary at every non-call instruction. -/
theorem checked_instruction {sig : Clif.Signature} {vc : VCode}
    (checked : codeCheck sig vc = true) {b k : Nat} {vb : VBlock} {i : MInst}
    (block : vc.blocks[b]? = some vb) (inst : vb.insts[k]? = some i) :
    instruction sig b k i = true := by
  have bm : (vb,b) ∈ vc.blocks.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using block)
  have im : (i,k) ∈ vb.insts.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using inst)
  exact List.all_eq_true.mp (List.all_eq_true.mp checked (vb,b) bm) (i,k) im

/-- The internal class derives absence of try-calls from actual code checks. -/
theorem noTryCall_of_codeCheck {sig : Clif.Signature} {vc : VCode}
    (checked : codeCheck sig vc = true) : vc.hasTryCall = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  simp only [VCode.hasTryCall,Array.any_eq_true] at present
  obtain ⟨b,hb,k,hk,flag⟩ := present
  generalize atInst : vc.blocks[b].insts[k] = i at flag
  cases i <;> try cases flag
  rename_i info ti
  have found := checked_instruction checked
    (Array.getElem?_eq_some_iff.mpr ⟨hb,rfl⟩)
    (Array.getElem?_eq_some_iff.mpr ⟨hk,atInst⟩)
  change false = true at found
  cases found

end Backend.Stock.VoidCall.NI

namespace E2E.ABIReadOnly
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Exact original argument agreement transfers a finite ABI prelude, including stack reads. -/
theorem seqRun_fall_transport {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {F Z : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {w w' : Arm.ArmState}
    (worlds : SameWorld Z w w')
    (registers : ∀ r v,(.reg r,v) ∈ (locsOf sig).zip args → regVal w' r = regVal w r)
    (stack : ∀ (off : Nat) (v : Clif.Val),(.stack off,v) ∈ (locsOf sig).zip args → ∀ j < v.ty.bytes,
      w'.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      w.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j))
    {ms : List MInst} {b start : Nat}
    (checked : ∀ j i,ms[j]? = some i → Backend.ABIReadOnly.instruction sig b (start+j) i = true)
    {ρ ρ' : Nat → CV} {final : Arm.ArmState}
    (run : seqRun (sem F ctx X) ms ρ w = some (.fall ρ' final)) :
    final = w ∧ seqRun (sem F ctx X) ms ρ w' = some (.fall ρ' w') := by
  induction ms generalizing start ρ with
  | nil =>
    obtain ⟨rfl,rfl⟩ := SeqEnd.fall.inj (Option.some.inj run)
    exact ⟨rfl,rfl⟩
  | cons i rest ih =>
    have head := checked 0 i (by simp)
    simp only [Nat.add_zero] at head
    obtain ⟨ops,outs,middle,operands,first,arity,tail⟩ := seqRun_cons_fall run
    have same := step_world head first
    subst middle
    have transferred := step_transport types head worlds registers stack first
    have remaining : ∀ j item,rest[j]? = some item →
        Backend.ABIReadOnly.instruction sig b (start+1+j) item = true := by
      intro j item found
      have next := checked (j+1) item (by simpa using found)
      simpa only [Nat.add_assoc,Nat.add_comm 1 j] using next
    obtain ⟨finalWorld,other⟩ := ih remaining tail
    refine ⟨finalWorld,?_⟩
    simp only [seqRun,operands,transferred,arity,↓reduceIte,other,Option.map_some,SeqEnd.succ]

end E2E.ABIReadOnly

namespace E2E.VoidCallPairedWitness
open Backend Backend.Proof Backend.Proof.Driver LinkCheck
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Additional fixture. The original captured caller remains unchanged. -/
def stackCaller : Clif.Function :=
  let original := VoidCallViewWitness.caller
  {original with
    name := "stock_void_stack_caller"
    sig := {original.sig with params := List.replicate 9 ⟨.i64,.none,.normal⟩}
    blocks := [{original.blocks[0]! with
      params := (List.range 9).map (fun i => (i,Clif.Ty.i64))
      body := [⟨[],.call 0 [0,8]⟩]
      term := .ret []}]}

private def checked (f : Clif.Function) : Bool := match Stock.lower f with
  | .error _ => false
  | .ok result => Stock.VoidCall.check f result.code && Stock.VoidCall.NI.codeCheck f.sig result.code
attribute [local irreducible] checked
-- witness: native_decide (the original caller and one additional consumed-stack-argument fixture)
private theorem checked_true : (checked VoidCallViewWitness.caller && checked stackCaller) = true := by
  native_decide

/-- The unchanged caller and an actually consumed stack argument satisfy the finite read boundary. -/
theorem caller_boundaries (f : Clif.Function)
    (member : f = VoidCallViewWitness.caller ∨ f = stackCaller) :
    ∃ result,Stock.lower f = .ok result ∧ Stock.VoidCall.check f result.code = true ∧
      Stock.VoidCall.NI.codeCheck f.sig result.code = true ∧ result.code.hasTryCall = false := by
  have both := Bool.and_eq_true_iff.mp checked_true
  have accepted : checked f = true := by
    rcases member with rfl | rfl
    · exact both.1
    · exact both.2
  unfold checked at accepted
  cases lowered : Stock.lower f with
  | error message => simp only [lowered,Bool.false_eq_true] at accepted
  | ok result =>
    simp only [lowered,Bool.and_eq_true] at accepted
    exact ⟨result,rfl,accepted.1,accepted.2,Stock.VoidCall.NI.noTryCall_of_codeCheck accepted.2⟩

end E2E.VoidCallPairedWitness

#print axioms Backend.Stock.VoidCall.NI.checked_instruction
#print axioms Backend.Stock.VoidCall.NI.noTryCall_of_codeCheck
#print axioms E2E.ABIReadOnly.seqRun_fall_transport
#print axioms E2E.VoidCallPairedWitness.caller_boundaries -- witness: native_decide
