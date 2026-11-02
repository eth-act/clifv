import FV.Backend.Proof.StockLiveCallArithmetic
import FV.E2E.Statement

namespace Backend.Stock.LiveCall
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false

/-- One execution kernel composes the actual call, existing addition semantics, and ABI return. -/
theorem execute_tail {F : BitVec 64 → Prop} {isem : Sem} (refines : Refines F isem)
    (retSem : ∀ (us : List (Reg × Reg)) uses world,isem (.rets us) uses world = some ([],world,.ret))
    {vc : VCode} {block : VBlock} (placed : vc.blocks[0]? = some block)
    {name : String} {live called sum : Nat} (separate : live ≠ called)
    {prelude suffix : List MInst}
    (code : block.insts.toList = (prelude ++
      [.call ⟨.sym name,retPairs [(live,.x 0)],callDefs [(.x 0,called)]⟩,
       .aluRRR .add .size64 (.vreg sum .int) (.vreg called .int) (.vreg live .int),
       .rets (retPairs [(sum,.x 0)])]) ++ suffix)
    {seed values : Nat → CV} {initial before after : Arm.ArmState} {output : CV}
    (preRun : seqRun isem prelude seed initial = some (.fall values before))
    (callRun : isem (.call ⟨.sym name,retPairs [(live,.x 0)],callDefs [(.x 0,called)]⟩)
      ([(live,Reg.x 0)].map (values ·.1)) before = some ([output],after,.next)) :
    ∃ final,VReturns vc isem seed initial (retPairs [(sum,.x 0)])
      [resX .size64 (opnd .size64 output + opnd .size64 (values live))] final ∧
      SameWorld F final after := by
  obtain ⟨final,callAdd,world⟩ := LiveCallArithmetic.call_then_add refines separate (sum := sum) callRun
  let value := resX .size64 (opnd .size64 output + opnd .size64 (values live))
  let updated := upd (fun key => if key = called then output else values key) sum value
  have returned : seqRun isem [.rets (retPairs [(sum,.x 0)])] updated final =
      some (.stop 0 (.rets (retPairs [(sum,.x 0)]))
        (retOps [(sum,.x 0)]).toArray updated final [] final .ret) := by
    simp [seqRun,operands_rets,retSem,retOps,Operand.isDef]
  have bodyRun := seqRun_append_fall_stop isem callAdd returned
  have complete := seqRun_append_fall_stop isem preRun bodyRun
  have segment : SegAt block 0 (prelude ++
      [.call ⟨.sym name,retPairs [(live,.x 0)],callDefs [(.x 0,called)]⟩,
       .aluRRR .add .size64 (.vreg sum .int) (.vreg called .int) (.vreg live .int),
       .rets (retPairs [(sum,.x 0)])]) :=
    segAt_of_toList (L₁ := []) (by simpa only [List.nil_append] using code)
  obtain ⟨path,_,instruction,operands,ran,_,_⟩ := seqRun_stop_star placed segment complete
  refine ⟨final,?_,world⟩
  refine ⟨0,_,updated,final,block,(retOps [(sum,.x 0)]).toArray,[],path,placed,instruction,rfl,?_,retSem _ _ _⟩
  simp [vuses_retOps,updated,upd,value]

end Backend.Stock.LiveCall
