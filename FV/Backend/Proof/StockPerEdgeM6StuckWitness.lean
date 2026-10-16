import FV.Backend.Proof.PerEdgeRegallocSound
import FV.Backend.Proof.RegallocCSem
import FV.Backend.Proof.StockSourceCallWitness
namespace Backend.Stock.Proof.PerEdgeM6StuckWitness
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def signature : Clif.Signature := {
  params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV }
private def statement : Clif.Stmt := ⟨[31],.call 0 [7]⟩
private def caller : Clif.Function := {
  name := "stock_source_call_result",sig := signature
  externs := [(0,{name := "stock_source_identity",sig := signature,colocated := true})]
  blocks := [{id := 0,params := [(7,.i64)],body := [statement],term := .ret [31]}] }

private def callInfo : CallInfo := {
  dest := .sym "stock_source_identity",uses := [(.vreg 192 .int,.x 0)],defs := [(.x 0,.vreg 194 .int)] }
private def allocated : RFunc := {spillSlots := 0,saved := [],blocks := #[#[
  .op 0 #[.reg (.x 0)],.op 1 #[.reg (.x 0),.reg (.x 0)],.op 2 #[.reg (.x 0)]]]}
private def external : ExtSem := {
  call := fun _ _ _ => none,sym := fun _ _ => 0,tp := 0,tlsFlags := fun _ w => Arm.read_pstate w }
private def store (w : Arm.ArmState) : Loc → CV
  | .reg r => regVal w r
  | _ => 0
private theorem write_same (w : Arm.ArmState) :
    upd (store w) (.reg (.x 0)) (regVal w (.x 0)) = store w := by
  funext l
  by_cases same : l = .reg (.x 0) <;> simp [upd,same,store]
private theorem step_args {vc : VCode} {rf : RFunc} {vb : VBlock}
    (placed : vc.blocks[0]? = some vb)
    (code : vb.insts = #[.args [(.vreg 192 .int,.x 0)],.call callInfo,.rets [(.vreg 194 .int,.x 0)]])
    (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState) :
    MStep vc (csem F ctx X) ckeep rf
      (.run ⟨0,[.op 0 #[.reg (.x 0)],.op 1 #[.reg (.x 0),.reg (.x 0)],.op 2 #[.reg (.x 0)]],store w,w⟩)
      (.run ⟨0,[.op 1 #[.reg (.x 0),.reg (.x 0)],.op 2 #[.reg (.x 0)]],store w,w⟩) := by
  have run : MStep vc (csem F ctx X) ckeep rf
      (.run ⟨0,[.op 0 #[.reg (.x 0)],.op 1 #[.reg (.x 0),.reg (.x 0)],.op 2 #[.reg (.x 0)]],store w,w⟩)
      (.run ⟨0,[.op 1 #[.reg (.x 0),.reg (.x 0)],.op 2 #[.reg (.x 0)]],upd (store w) (.reg (.x 0)) (regVal w (.x 0)),w⟩) := by
    exact MStep.op placed (by rw [code]; rfl) (ops := #[⟨192,.int,.def,.late,.fixed (.x 0)⟩])
      rfl rfl (by rfl) (by simp [Operand.isDef]) (HavocOuts.refl _ _ _)
      ⟨fun _ _ => rfl,fun _ h => by cases h⟩ (by simp [Operand.isDef,Operand.isEarly,Operand.isLate,writeM]; apply MNext.next; rw [code]; decide)
  simpa only [write_same] using run
local instance : DecidableEq (Except String Unit) := fun a b =>
  match a,b with
  | .ok (),.ok () => isTrue rfl
  | .error a,.error b =>
    if h : a = b then isTrue (congrArg Except.error h)
    else isFalse (fun eq => h (Except.error.inj eq))
  | .ok (),.error _ => isFalse (fun h => by cases h)
  | .error _,.ok () => isFalse (fun h => by cases h)

private def Observed : Prop := (Stock.lower caller).toOption.map (fun (result : Result) => decide (
  checkAllocAt result.code result.edgeArgs allocated = .ok () ∧ result.code.blocks.size = 1 ∧
  (result.code.blocks[0]!).insts = #[.args [(.vreg 192 .int,.x 0)],.call callInfo,.rets [(.vreg 194 .int,.x 0)]])) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel
/-- A complete original Stock caller reaches its actual call after Args. When
the concrete external semantics supplies no call result, both allocated code
and per-successor VCode are stuck there; the prefix and stuckness are proved. -/
theorem stock_per_edge_m6_stuck_witness : ∃ result : Result,
    Stock.lower caller = .ok result ∧ LowerScope caller ∧ Dominated caller ∧
    checkAllocAt result.code result.edgeArgs allocated = .ok () ∧
    ∀ (F : BitVec 64 → Prop) (ctx : FnCtx) (w : Arm.ArmState) (ρ : Nat → CV),
      ∃ stopped : MState CV Arm.ArmState,
        Star (MStep result.code (csem F ctx external) ckeep allocated)
          (MConf.init allocated (store w) w) (.run stopped) ∧
        (∀ c',¬ MStep result.code (csem F ctx external) ckeep allocated (.run stopped) c') ∧
        ∃ vs,Star (VStepAt result.code result.edgeArgs (csem F ctx external))
          (VConf.init ρ w) (.run vs) ∧
          ∀ v',¬ VStepAt result.code result.edgeArgs (csem F ctx external) (.run vs) v' := by
  obtain ⟨result,callee,run,_,scope,_,dominated,_⟩ := SourceCallWitness.stock_source_call_result_witness 0
  change Stock.lower caller = .ok result at run
  change LowerScope caller at scope
  change Dominated caller at dominated
  have actual := observed
  unfold Observed at actual
  rw [run] at actual
  simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
  obtain ⟨accepted,size,code⟩ := actual
  refine ⟨result,run,scope,dominated,accepted,?_⟩
  intro F ctx w ρ
  have placed : result.code.blocks[0]? = some result.code.blocks[0]! := by
    have bound : 0 < result.code.blocks.size := by omega
    simp [getElem!_def,Array.getElem?_eq_getElem bound]
  let stopped : MState CV Arm.ArmState :=
    ⟨0,[.op 1 #[.reg (.x 0),.reg (.x 0)],.op 2 #[.reg (.x 0)]],store w,w⟩
  have execution : Star (MStep result.code (csem F ctx external) ckeep allocated)
      (MConf.init allocated (store w) w) (.run stopped) :=
    Star.single (step_args (rf := allocated) placed code F ctx external w)
  have stuck : ∀ c',¬ MStep result.code (csem F ctx external) ckeep allocated (.run stopped) c' := by
    intro next step
    change MStep result.code (csem F ctx external) ckeep allocated
      (.run ⟨0,[.op 1 #[.reg (.x 0),.reg (.x 0)],.op 2 #[.reg (.x 0)]],store w,w⟩) next at step
    cases step with
    | op block instruction operands length semantics =>
      rw [placed] at block
      cases block
      simp [code] at instruction
      subst instruction
      simp [csem,external] at semantics
  exact ⟨stopped,execution,stuck,PerEdge.checkAlloc_stuck (sem := csem F ctx external)
    (keep := ckeep) accepted ρ execution stuck⟩
end Backend.Stock.Proof.PerEdgeM6StuckWitness
