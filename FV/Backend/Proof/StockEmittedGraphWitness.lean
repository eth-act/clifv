module

public import FV.Backend.Proof.StockTryCfg
public import FV.Backend.Proof.StockOrderGraphWitness

@[expose] public section

namespace Backend.Stock.Proof.EmittedGraphWitness
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

/-- A complete actual critical-edge driver inhabits dense labels and every
field of the synthetic emitted-CFG clause. -/
theorem stock_critical_cfg_witness :
    ∃ (f : Clif.Function) (result : Result) (label pred index target : Nat),
      Stock.lower f = .ok result ∧ LowerScope f ∧
      (∀ (k : Nat) (hk : k < result.code.blocks.size),result.code.blocks[k].label = k) ∧
      (result.order.successors.size = result.code.blocks.size ∧
        ∀ (i : Nat) (row : Array Nat),result.order.successors[i]? = some row →
          ∀ v ∈ row.toList,v < result.code.blocks.size) ∧
      result.order.nodes[label]? = some (.edge pred index target) ∧
      ∃ (block : VBlock) (t : MInst) (row : Array Nat),
        result.code.blocks[label]? = some block ∧ block.insts.back? = some t ∧
        t.isTerminator = true ∧ result.order.successors[label]? = some row ∧
        row.size = t.targets.length ∧
        ∀ (j : Nat) (l : Label),t.targets[j]? = some l →
          ∃ k,row[j]? = some k ∧ Prep.lab result.code.blocks l = some k := by
  obtain ⟨f,result,label,pred,index,target,targetLabel,run,scope,node,_,_⟩ :=
    OrderGraphWitness.stock_critical_order_witness
  exact ⟨f,result,label,pred,index,target,run,scope,stock_lower_dense_labels run,stock_lower_graph_bounds run,node,
    stock_lower_critical_cfg run scope node⟩

private def sig : Clif.Signature := {callConv := some .systemV}
private def table : Clif.ExnTable := {sig := 0,normal := ⟨1,[]⟩,items := [.tag 7 ⟨2,[]⟩,.default ⟨3,[]⟩]}
private def term (indirect : Bool) : Clif.Terminator :=
  if indirect then .tryCallIndirect 0 [] table else .tryCall 0 [] table
private def function (indirect : Bool) : Clif.Function := {
  name := "stock_try_cfg",sig := sig,sigDecls := [(0,sig)],externs := [(0,{name := "callee",sig := sig})]
  blocks := [{id := 0,body := if indirect then [⟨[0],.iconst .i64 4096⟩] else [],term := term indirect},
    {id := 1,term := .ret []},{id := 2,term := .ret []},{id := 3,term := .ret []}] }
private def Observed (indirect : Bool) : Prop := (Stock.lower (function indirect)).toOption.map
  (fun result => decide (result.order.nodes[0]? = some (.original 0))) = some true
private theorem observed (indirect : Bool) : Observed indirect := by
  cases indirect <;> unfold Observed <;> decide +kernel
private theorem scope (indirect : Bool) : LowerScope (function indirect) := by
  cases indirect <;> apply lowerScope_of <;> decide +kernel
private theorem dominated (indirect : Bool) : Dominated (function indirect) := by
  cases indirect with
  | false => apply dominated_of; decide +kernel
  | true =>
    constructor
    · change ([0] : List Nat).Nodup; decide +kernel
    · intro ctx ranges st build bi b found
      have bound : bi < 4 := by have h := lt_of_getElem? found; simpa [function] using h
      have choices : bi = 0 ∨ bi = 1 ∨ bi = 2 ∨ bi = 3 := by omega
      rcases choices with rfl | rfl | rfl | rfl
      all_goals
        simp [function] at found
        subst b
        constructor
        · intro j stm present y member
          cases j <;> simp at present
          all_goals
            subst stm
            cases member
        · intro y member
          simp [abiTerm,Driver.termArgs,sretRet,sigRets,function,term,table,sig,
            Clif.ExnTable.vals,Clif.TryDest.vals] at member <;>
            subst y <;> simp [availOf,function,defsBefore,defsFrom]
    · intro ctx ranges st build tl x available notLocal y member
      have empty : parsOf (function true) tl = [] := by
        cases tl with
        | zero => rfl
        | succ tl => cases tl with
          | zero => rfl
          | succ tl => cases tl with
            | zero => rfl
            | succ tl => cases tl with
              | zero => rfl
              | succ tl => rfl
      simp [empty]

private def CfgClause (result : Result) (label : Nat) : Prop :=
  ∃ (block : VBlock) (t : MInst) (row : Array Nat),
    result.code.blocks[label]? = some block ∧ block.insts.back? = some t ∧
    t.isTerminator = true ∧ result.order.successors[label]? = some row ∧
    row.size = t.targets.length ∧
    ∀ (j : Nat) (l : Label),t.targets[j]? = some l →
      ∃ k,row[j]? = some k ∧ Prep.lab result.code.blocks l = some k

/-- Both direct and indirect complete original-scope/dominated source programs
have tag/default handlers and a normal continuation. The actual final emitted
terminator retains the computed successor ordering. A separately executed
replacement gate also inhabits the branchCode theorem without prior-code assumptions. -/
theorem stock_try_targets_witness (indirect : Bool) :
    ∃ (result : Result) (block : VBlock) (last : MInst) (replaced : Array MInst),
      Stock.lower (function indirect) = .ok result ∧ LowerScope (function indirect) ∧
      Dominated (function indirect) ∧
      result.order.nodes[0]? = some (.original 0) ∧
      result.code.blocks[0]? = some block ∧ block.insts.back? = some last ∧
      last.isTerminator = true ∧ last.targets = result.order.successors[0]!.toList ∧
      CfgClause result 0 ∧
      branchCode (function indirect) (term indirect) #[2,3,1] #[.call default] = .ok replaced ∧
      ∃ gateLast,replaced.back? = some gateLast ∧ gateLast.isTerminator = true ∧
        gateLast.targets = [2,3,1] := by
  have actual := observed indirect
  unfold Observed at actual
  cases run : Stock.lower (function indirect) with
  | error e => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    have isTry : (function indirect).blocks[0]!.term.isTry = true := by cases indirect <;> rfl
    obtain ⟨block,last,placed,atLast,terminal,targets⟩ := stock_lower_try_targets run actual isTry
    let replaced := #[MInst.tryCall default {continuation := 1,handlers := [.tag 7 2,.default 3]}]
    have gate : branchCode (function indirect) (term indirect) #[2,3,1] #[.call default] = .ok replaced := by
      cases indirect <;> rfl
    have gateTry : (term indirect).isTry = true := by cases indirect <;> rfl
    exact ⟨result,block,last,replaced,rfl,scope indirect,dominated indirect,actual,placed,atLast,terminal,targets,stock_lower_try_cfg run (scope indirect) actual isTry,
      gate,stock_branchCode_try_targets gateTry gate⟩

end Backend.Stock.Proof.EmittedGraphWitness
