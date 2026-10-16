import FV.Backend.Proof.PerEdgeRegallocSound
import FV.Backend.Proof.RegallocCSem
import FV.Backend.Proof.StockPerEdgeCheckerWitness
namespace Backend.Stock.Proof.PerEdgeM6Witness
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function : Clif.Function := {
  name := "stock_per_successor_migration"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩},
    {id := 1,params := [(31,.i64)],term := .ret [31]}, {id := 2,params := [(47,.i64)],term := .ret [47]}] }
private def allocated : RFunc := { spillSlots := 0,saved := [],blocks := #[
  #[.op 0 #[.reg (.x 0)],.op 1 #[.reg (.x 0)]],
  #[.op 0 #[.reg (.x 0)]],#[.op 0 #[.reg (.x 0)]]] }
private def store (w : Arm.ArmState) : Loc → CV
  | .reg r => regVal w r
  | _ => 0
private def selected (w : Arm.ArmState) : Nat :=
  if lo64 (regVal w (.x 0)) != (0#64) then 0 else 1
private theorem write_same (w : Arm.ArmState) :
    upd (store w) (.reg (.x 0)) (regVal w (.x 0)) = store w := by
  funext l
  by_cases same : l = .reg (.x 0) <;> simp [upd,same,store]
private theorem step_args {vc : VCode} {rf : RFunc} {vb : VBlock}
    (placed : vc.blocks[0]? = some vb)
    (code : vb.insts = #[.args [(.vreg 192 .int,.x 0)],.condBr 2 1 (.notZero (.vreg 192 .int) .size64)])
    (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState) :
    MStep vc (csem F ctx X) ckeep rf
      (.run ⟨0,[.op 0 #[.reg (.x 0)],.op 1 #[.reg (.x 0)]],store w,w⟩)
      (.run ⟨0,[.op 1 #[.reg (.x 0)]],store w,w⟩) := by
  have run : MStep vc (csem F ctx X) ckeep rf
      (.run ⟨0,[.op 0 #[.reg (.x 0)],.op 1 #[.reg (.x 0)]],store w,w⟩)
      (.run ⟨0,[.op 1 #[.reg (.x 0)]],upd (store w) (.reg (.x 0)) (regVal w (.x 0)),w⟩) := by
    exact MStep.op placed (by rw [code]; rfl) (ops := #[⟨192,.int,.def,.late,.fixed (.x 0)⟩])
      rfl rfl (by rfl) (by simp [Operand.isDef]) (HavocOuts.refl _ _ _)
      ⟨fun _ _ => rfl,fun _ h => by cases h⟩ (by simp [Operand.isDef,Operand.isEarly,Operand.isLate,writeM]; apply MNext.next; rw [code]; decide)
  simpa only [write_same] using run
private theorem step_cond {vc : VCode} {rf : RFunc} {vb : VBlock}
    (placed : vc.blocks[0]? = some vb)
    (code : vb.insts = #[.args [(.vreg 192 .int,.x 0)],.condBr 2 1 (.notZero (.vreg 192 .int) .size64)])
    (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState)
    (succ : succOf vc 0 (selected w) = some (2-selected w))
    (items : rf.blocks[2-selected w]? = some #[.op 0 #[.reg (.x 0)]]) :
    MStep vc (csem F ctx X) ckeep rf
      (.run ⟨0,[.op 1 #[.reg (.x 0)]],store w,w⟩)
      (.run ⟨2-selected w,[.op 0 #[.reg (.x 0)]],store w,w⟩) := by
  exact MStep.op placed (by rw [code]; rfl) (ops := #[⟨192,.int,.use,.early,.reg⟩]) rfl rfl
    (by rfl) (by simp [Operand.isDef]) (HavocOuts.refl _ _ _) ⟨fun _ _ => rfl,fun _ h => by cases h⟩
    (by simp [Operand.isDef,Operand.isEarly,Operand.isLate,writeM]; apply MNext.goto _ succ items; rw [code]; rfl)
private theorem step_ret {vc : VCode} {rf : RFunc} {vb : VBlock} {b key : Nat}
    (placed : vc.blocks[b]? = some vb) (code : vb.insts = #[.rets [(.vreg key .int,.x 0)]])
    (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState) :
    MStep vc (csem F ctx X) ckeep rf (.run ⟨b,[.op 0 #[.reg (.x 0)]],store w,w⟩)
      (.ret [regVal w (.x 0)] (store w) w) := by
  exact MStep.op placed (by rw [code]; rfl) (ops := #[⟨key,.int,.use,.early,.fixed (.x 0)⟩]) rfl rfl
    (by rfl) (by simp [Operand.isDef]) (HavocOuts.refl _ _ _) ⟨fun _ _ => rfl,fun _ h => by cases h⟩ (by simp [Operand.isUse,Operand.isDef,Operand.isEarly,Operand.isLate,writeM,store]; apply MNext.ret; rfl)

local instance {α : Type} [DecidableEq α] : DecidableEq (Except String α) := fun a b =>
  match a,b with
  | .ok a,.ok b =>
    if h : a = b then isTrue (congrArg Except.ok h)
    else isFalse (fun eq => h (Except.ok.inj eq))
  | .error a,.error b =>
    if h : a = b then isTrue (congrArg Except.error h)
    else isFalse (fun eq => h (Except.error.inj eq))
  | .ok _,.error _ => isFalse (fun h => by cases h)
  | .error _,.ok _ => isFalse (fun h => by cases h)

private def Observed : Prop := (Stock.lower function).toOption.map (fun (result : Result) => decide (
  result.code.blocks.size = 3 ∧
  (result.code.blocks[0]!).insts = #[.args [(.vreg 192 .int,.x 0)],.condBr 2 1 (.notZero (.vreg 192 .int) .size64)] ∧
  (result.code.blocks[1]!).insts = #[.rets [(.vreg 194 .int,.x 0)]] ∧
  (result.code.blocks[2]!).insts = #[.rets [(.vreg 193 .int,.x 0)]] ∧
  result.code.cfg = .ok (#[#[2,1],#[],#[]],#[#[],#[0],#[0]]))) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel

/-- A complete original-scope Stock conditional executes from Args at function
entry to the selected return under concrete csem, for every Arm world. The new
per-successor M6 theorem yields the same complete VCode return and preserves
the actual ABI callee-saved parts. Both branch outcomes remain admitted. -/
theorem stock_per_edge_m6_return_witness : ∃ result : Result,
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    checkAllocAt result.code result.edgeArgs allocated = .ok () ∧
    ∀ (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState) (ρ₀ : Nat → CV),
      Star (MStep result.code (csem F ctx X) ckeep allocated)
        (MConf.init allocated (store w) w) (.ret [regVal w (.x 0)] (store w) w) ∧
      Star (VStepAt result.code result.edgeArgs (csem F ctx X))
        (VConf.init ρ₀ w) (.ret [regVal w (.x 0)] w) ∧
      (∀ r ∈ calleeSaved,ckeep r (store w (.reg r)) = ckeep r (store w (.reg r))) := by
  obtain ⟨result,run,scope,dominated,accepted,_⟩ := PerEdgeCheckerWitness.stock_per_edge_checker_witness
  change Stock.lower function = .ok result at run
  change LowerScope function at scope
  change Dominated function at dominated
  change checkAllocAt result.code result.edgeArgs allocated = .ok () at accepted
  have actual := observed
  unfold Observed at actual
  rw [run] at actual
  simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
  obtain ⟨size,code0,code1,code2,cfg⟩ := actual
  refine ⟨result,run,scope,dominated,accepted,?_⟩
  intro F ctx X w ρ₀
  have position : selected w = 0 ∨ selected w = 1 := by
    unfold selected
    split <;> simp
  have source : result.code.blocks[0]? = some result.code.blocks[0]! := by
    have bound : 0 < result.code.blocks.size := by omega
    simp [getElem!_def,Array.getElem?_eq_getElem bound]
  have target : result.code.blocks[2-selected w]? = some result.code.blocks[2-selected w]! := by
    have bound : 2-selected w < result.code.blocks.size := by omega
    simp [getElem!_def,Array.getElem?_eq_getElem bound]
  have targetCode : (result.code.blocks[2-selected w]!).insts =
      #[.rets [(.vreg (if selected w = 0 then 193 else 194) .int,.x 0)]] := by
    rcases position with h | h <;> simp [h,code1,code2]
  have successor : succOf result.code 0 (selected w) = some (2-selected w) := by
    rcases position with h | h <;> simp [succOf,cfg,h]
  have items : allocated.blocks[2-selected w]? = some #[.op 0 #[.reg (.x 0)]] := by
    rcases position with h | h <;> simp [allocated,h]
  have argsStep := step_args (rf := allocated) source code0 F ctx X w
  have branchStep := step_cond source code0 F ctx X w successor items
  have returnStep := step_ret (rf := allocated) target targetCode F ctx X w
  have execution : Star (MStep result.code (csem F ctx X) ckeep allocated)
      (MConf.init allocated (store w) w) (.ret [regVal w (.x 0)] (store w) w) :=
    .step argsStep (.step branchStep (.single returnStep))
  obtain ⟨virtual,preserved⟩ := PerEdge.checkAlloc_ret (sem := csem F ctx X) (keep := ckeep) accepted ρ₀ execution
  exact ⟨execution,virtual,preserved⟩
/-- The same complete accepted Stock program inhabits the checked-state entry,
forward-step and progress interfaces and the allocation-certificate variant.
The first matched step is the real Args instruction, not a supplied semantic step. -/
theorem stock_per_edge_m6_checked_witness : ∃ result : Result,
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    checkAllocAt result.code result.edgeArgs allocated = .ok () ∧
    ∀ (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState) (ρ : Nat → CV),
      ∃ c ins a0,
        PerEdge.Checked result.code result.edgeArgs allocated c ins ∧
        PerEdge.CheckedAt result.code result.edgeArgs allocated c ins a0 ∧ EntryOk a0 ∧
        PerEdge.MatchRun c result.edgeArgs ins ckeep (fun r => store w (.reg r))
          ⟨0,[.op 0 #[.reg (.x 0)],.op 1 #[.reg (.x 0)]],store w,w⟩ ⟨0,0,ρ,w⟩ ∧
        (∃ v',VStepAt result.code result.edgeArgs (csem F ctx X) (VConf.init ρ w) v' ∧
          PerEdge.Match c result.edgeArgs ins ckeep (fun r => store w (.reg r))
            (.run ⟨0,[.op 1 #[.reg (.x 0)]],store w,w⟩) v' ∧
          ∃ next,MStep result.code (csem F ctx X) ckeep allocated
            (MConf.init allocated (store w) w) next) ∧
        ∃ ρ₀ R,PerEdge.IsSimulation result.code allocated (csem F ctx X) ckeep result.edgeArgs R ∧
          R (MConf.init allocated (store w) w) (VConf.init ρ₀ w) := by
  obtain ⟨result,run,scope,dominated,accepted,_⟩ := stock_per_edge_m6_return_witness
  refine ⟨result,run,scope,dominated,accepted,?_⟩
  intro F ctx X w ρ
  have actual := observed
  unfold Observed at actual
  rw [run] at actual
  simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
  obtain ⟨size,code0,_⟩ := actual
  have source : result.code.blocks[0]? = some result.code.blocks[0]! := by
    have bound : 0 < result.code.blocks.size := by omega
    simp [getElem!_def,Array.getElem?_eq_getElem bound]
  obtain ⟨c,ins,hc⟩ := PerEdge.checked_of_checkAlloc accepted
  obtain ⟨a0,hat,le⟩ := hc.at
  have entry := hat.entry
  obtain ⟨items,found,matched⟩ := PerEdge.enter_block ckeep hc
    (show 0 < result.code.blocks.size by omega) entry le
    (Inv_entryState (keep := ckeep) (m := store w) (ρ := ρ))
  have concrete : items = #[.op 0 #[.reg (.x 0)],.op 1 #[.reg (.x 0)]] := by
    change some #[.op 0 #[.reg (.x 0)],.op 1 #[.reg (.x 0)]] = some items at found
    exact (Option.some.inj found).symm
  rw [concrete] at matched
  have args := step_args (rf := allocated) source code0 F ctx X w
  have forward := PerEdge.sim_step (csem F ctx X) ckeep hc matched args
  have virtual : ∃ v',VStepAt result.code result.edgeArgs (csem F ctx X) (VConf.init ρ w) v' ∧
      PerEdge.Match c result.edgeArgs ins ckeep (fun r => store w (.reg r))
        (.run ⟨0,[.op 1 #[.reg (.x 0)]],store w,w⟩) v' := by
    rcases forward with ⟨ms,equal,moved,_⟩ | ⟨v',step,related⟩
    · cases equal
      obtain ⟨_,_,vb,a,out,placed,checked,inv,edges⟩ := moved
      have impossible := (runItems_op checked).2.1
      exact False.elim (by simpa using impossible)
    · exact ⟨v',step,related⟩
  obtain ⟨v',step,related⟩ := virtual
  have progress := PerEdge.sim_progress (csem F ctx X) ckeep hc matched step
  obtain ⟨ρ₀,R,simulation,initial,_⟩ := PerEdge.allocChecked_sound result.code allocated
    (csem F ctx X) ckeep (PerEdge.allocChecked_of_checkAlloc accepted) (store w) w
  exact ⟨c,ins,a0,hc,hat,entryOk_of_le le,matched,⟨v',step,related,progress⟩,ρ₀,R,simulation,initial⟩
end Backend.Stock.Proof.PerEdgeM6Witness
