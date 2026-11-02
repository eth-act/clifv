import FV.E2E.UnwindValueSem
import FV.E2E.UnwindStatement
import FV.Backend.Proof.LowerSeq

namespace Backend.Stock.CallStore
open Backend Backend.Proof Backend.Proof.Driver E2E Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- A raising callee ends the actual caller before its store continuation executes. -/
theorem trap_call_tail {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {vc : VCode} {block : VBlock} (placed : vc.blocks[0]? = some block)
    {prelude rest : List MInst} {info : CallInfo}
    (code : block.insts.toList = prelude ++ .call info :: rest)
    {seed values : Nat → CV} {initial before after : Arm.ArmState} {obj : BitVec 64}
    (preRun : seqRun (valueSemU F ctx X XR) prelude seed initial = some (.fall values before))
    {ops : Array Operand} (operands : (MInst.call info).operands = .ok ops)
    (raised : XR.raise (callDest info) (vuses ops values) before = some (obj,after)) :
    VUnwinds vc (valueSemU F ctx X XR) XR seed initial obj after := by
  have segment : SegAt block 0 (prelude ++ [.call info]) :=
    segAt_of_toList (L₁ := []) (by simpa only [List.nil_append,List.append_assoc,List.cons_append,List.nil_append] using code)
  have prefix : SegAt block 0 prelude := segment.append_left
  have instruction : block.insts[0+prelude.length]? = some (.call info) := segment.append_right.head
  have room := (Array.getElem?_eq_some_iff.mp instruction).1
  have path := seqRun_fall_star (vc := vc) placed prefix room preRun
  refine ⟨0,0+prelude.length,values,before,block,info,ops,
    (defCons (.call info)).map (fun _ => ofX 0),path,placed,instruction,operands,raised,
    valueSemU_call_raise raised,?_⟩
  simp [defCons,operands]

end Backend.Stock.CallStore
