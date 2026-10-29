module

public import FV.Backend.Proof.StockCriticalValues
public import FV.Backend.Proof.StockPerEdgeValues
public import FV.Backend.Proof.StockSelectedRoutes
public import FV.Backend.Proof.IselCtlBranch

@[expose] public section

namespace Backend.Stock.Proof.CriticalValuesWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def reduce : Clif.Stmt := ⟨[17],.ireduce .i8 7⟩
private def function : Clif.Function := {
  name := "stock_critical_values_alias"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],body := [reduce],term := .brif 7 ⟨1,[17]⟩ ⟨1,[17]⟩},
    {id := 1,params := [(31,.i8)],term := .ret [31]}] }
private def original : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx function).toOption.getD (sinkCtx,#[],default)
private theorem original_build : Backend.buildCtx function = .ok original := rfl
private def initial (word : BitVec 64) : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 7 ⟨.i64,word⟩,slots := [],body := [reduce],term := .brif 7 ⟨1,[17]⟩ ⟨1,[17]⟩ }
private def before (word : BitVec 64) : Clif.Frame := {
  initial word with regs := (initial word).regs.set 17 ⟨.i8,word.setWidth 8⟩,body := [] }
private def after (word : BitVec 64) : Clif.Frame := {
  before word with regs := (before word).regs.set 31 ⟨.i8,word.setWidth 8⟩,term := .ret [31] }
private def machine (word : BitVec 64) (key : Nat) : CV :=
  if key = 192 then BitVec.ofNat 128 (2^100 + word.toNat) else 0
private def needed (result : Result) (x : Nat) : Prop :=
  (x = 7 ∨ x = 17 ∨ x = 31) ∧ Demanded result.final x ∧ x ∈ availOf function (availIn function result.ctx) 1 0
private def Observed : Prop := (Stock.lower function).toOption.map (fun result => decide (
  result.ctx.valueReg? 7 = some (.vreg 192 .int) ∧ result.ctx.valueReg? 17 = some (.vreg 193 .int) ∧
  result.ctx.valueReg? 31 = some (.vreg 194 .int) ∧ (result.final.alias[193]?).join = some 192 ∧
  aliasNum result.final.alias 192 = 192 ∧ aliasNum result.final.alias 193 = 192 ∧ aliasNum result.final.alias 194 = 194 ∧
  result.final.demand[7]! ≠ 0 ∧ result.final.demand[17]! ≠ 0 ∧ result.final.demand[31]! ≠ 0 ∧
  (result.code.blocks[1]!).branchArgs = #[.vreg 192 .int] ∧
  (result.code.blocks[2]!).branchArgs = #[.vreg 192 .int] ∧
  (result.code.blocks[3]!).params = #[.vreg 194 .int] ∧
  succOf result.code 1 0 = some 3 ∧ succOf result.code 2 0 = some 3)) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel
private theorem dominated : Dominated function := by
  constructor
  · change ([7,17,31] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b found
    cases bi with
    | zero =>
      simp [function] at found
      subst b
      constructor
      · intro j stm present x member
        cases j with
        | zero =>
          simp at present
          subst stm
          have same : x = 7 := by simpa [reduce,Driver.instArgs] using member
          subst x
          simp [availOf,function,reduce,defsBefore,defsFrom]
        | succ j => simp at present
      · intro x member
        have cases : x = 7 ∨ x = 17 := by simpa [abiTerm,Driver.termArgs] using member
        rcases cases with rfl | rfl <;> simp [availOf,function,reduce,defsBefore,defsFrom]
    | succ bi =>
      cases bi with
      | zero =>
        simp [function] at found
        subst b
        constructor
        · intro j stm present; simp at present
        · intro x member
          have same : x = 31 := by simpa [abiTerm,Driver.termArgs,sretRet,sigRets,function] using member
          subst x
          simp [availOf,function,defsBefore,defsFrom]
      | succ bi => simp [function] at found
  · intro ctx ranges st build tl x available notLocal y member
    have fixed := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have length : function.blocks.length = 2 := rfl
    have same : tl = 1 := by omega
    subst tl
    have values : x = 7 ∨ x = 17 ∨ x = 31 := by simpa [valueDefs,function,reduce] using fixed.2.2.2.1
    have context : ctx = original.1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans original_build))
    rw [context] at member
    rcases values with rfl | rfl | rfl
    · change y ∈ ([] : List Nat) at member; cases member
    · change y ∈ [7] at member
      have same : y = 7 := List.mem_singleton.mp member
      subst y
      decide +kernel
    · have absent := fixed.2.2.2.2.1
      exact False.elim (absent (by decide +kernel))

private theorem entry_available {result : Result} (run : Stock.lower function = .ok result) :
    7 ∈ (availIn function result.ctx).getD 1 [] ∧ 17 ∈ (availIn function result.ctx).getD 1 [] := by
  have context : ∃ ranges,Stock.buildCtx function = .ok (result.ctx,ranges,result.initial) := by
    unfold Stock.lower at run
    dsimp only at run
    repeat' first
      | (solve | cases run)
      | simp only [bind,Except.bind,pure,Except.pure] at run
      | split at run
    cases run
    exact ⟨_,by assumption⟩
  obtain ⟨ranges,build⟩ := context
  obtain ⟨old,st,legacy,spec,view⟩ := buildCtx_source build
  have same : old = original.1 := congrArg Prod.fst (Except.ok.inj (legacy.symm.trans original_build))
  have size : result.ctx.valDef.size = 32 := by rw [view.valDef,same]; rfl
  have arguments : defArgs result.ctx = defArgs original.1 := by
    funext x
    simp only [defArgs,Ctx.defInst?,view.valDef,view.insts,same]
  let D : Nat → Nat → Prop := fun tl x => tl = 1 ∧ (x = 7 ∨ x = 17)
  have fixed : FixOk function result.ctx id D := by
    constructor
    · rintro tl x ⟨rfl,rfl | rfl⟩ <;> simp [size,function,valueDefs,reduce,parsOf]
    · rintro tl x ⟨rfl,hx⟩ p successor
      have pred : p = 0 := by
        cases p with
        | zero => rfl
        | succ p =>
          cases p with
          | zero => simp [succIdx,function,succIds,dests] at successor
          | succ p => simp [succIdx,function] at successor
      subst p
      rcases hx with rfl | rfl
      · exact .inl (by decide +kernel)
      · exact .inr (.inl (by decide +kernel))
    · rintro tl x ⟨rfl,hx⟩ y member
      rw [arguments] at member
      rcases hx with rfl | rfl
      · change y ∈ ([] : List Nat) at member; cases member
      · change y ∈ [7] at member
        have same : y = 7 := List.mem_singleton.mp member
        subst y
        exact ⟨.inr ⟨rfl,.inl rfl⟩,by decide +kernel⟩
  exact ⟨inFix_greatest fixed ⟨rfl,.inl rfl⟩,inFix_greatest fixed ⟨rfl,.inr rfl⟩⟩

private theorem low64 (word : BitVec 64) :
    (BitVec.ofNat 128 (2^100+word.toNat)).setWidth 64 = word := by
  rw [BitVec.setWidth_ofNat_of_le (by decide : 64 ≤ 128)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,Nat.add_mod,show 2^100 % 2^64 = 0 from by decide +kernel,
    Nat.zero_add,Nat.mod_eq_of_lt word.isLt]
private theorem low8 (word : BitVec 64) :
    (BitVec.ofNat 128 (2^100+word.toNat)).setWidth 8 = word.setWidth 8 := by
  rw [BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 128)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,BitVec.toNat_setWidth,Nat.add_mod,
    show 2^100 % 2^8 = 0 from by decide +kernel,Nat.zero_add,Nat.mod_mod]


/-- Every original word and either conditional successor inhabit a real
critical-edge copy, including the actual synthetic jump VStep, source
entry/reduction/branch/return, nonempty alias/copy and dirty upper machine bits. -/
theorem stock_critical_edge_env_witness (word : BitVec 64) (index : Nat) (bound : index < 2)
    (world : Arm.ArmState) : ∃ result : Result,
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    (result.final.alias[193]?).join = some 192 ∧ needed result 7 ∧ needed result 17 ∧ needed result 31 ∧
    (result.code.blocks[1]!).branchArgs = #[.vreg 192 .int] ∧
    (result.code.blocks[2]!).branchArgs = #[.vreg 192 .int] ∧ (result.code.blocks[3]!).params = #[.vreg 194 .int] ∧
    Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty = .ok (initial word,Clif.Mem.empty) ∧
    Clif.step Clif.Env.empty {funcs := []} ⟨initial word,[],Clif.Mem.empty⟩ = .next ⟨before word,[],Clif.Mem.empty⟩ ∧
    Clif.stepTerm Clif.Env.empty {funcs := []} ⟨before word,[],Clif.Mem.empty⟩
      (.brif 7 ⟨1,[17]⟩ ⟨1,[17]⟩) = .next ⟨after word,[],Clif.Mem.empty⟩ ∧
    Clif.step Clif.Env.empty {funcs := []} ⟨after word,[],Clif.Mem.empty⟩ = .done [⟨.i8,word.setWidth 8⟩] Clif.Mem.empty ∧
    ∃ ρ',edgeEnv result.code (1+index) 3 (machine word) = some ρ' ∧
      ValuesHeld (needed result) result.ctx (after word) (fun key => ρ' (aliasNum result.final.alias key)) ∧
      VStep result.code ispec (.run ⟨1+index,0,machine word,world⟩) (.run ⟨3,0,ρ',world⟩) := by
  have actual := observed
  unfold Observed at actual
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨map7,map17,map31,alias,resolve7,resolve17,resolve31,demand7,demand17,demand31,args1,args2,params,succ1,succ2⟩ := actual
    have block : function.blocks[1]? = some function.blocks[1]! := rfl
    obtain ⟨in7,in17⟩ := entry_available run
    have available7 : 7 ∈ availOf function (availIn function result.ctx) 1 0 := by
      refine (mem_av block).mpr ⟨.inr (.inl in7),?_⟩
      rintro ⟨j,stm,_,present,_⟩
      simp [function] at present
    have available17 : 17 ∈ availOf function (availIn function result.ctx) 1 0 := by
      refine (mem_av block).mpr ⟨.inr (.inl in17),?_⟩
      rintro ⟨j,stm,_,present,_⟩
      simp [function] at present
    have available31 : 31 ∈ availOf function (availIn function result.ctx) 1 0 := by
      simp [availOf,function,defsBefore,defsFrom]
    have need7 : needed result 7 := ⟨.inl rfl,demand7,available7⟩
    have need17 : needed result 17 := ⟨.inr (.inl rfl),demand17,available17⟩
    have need31 : needed result 31 := ⟨.inr (.inr rfl),demand31,available31⟩
    have held : ValuesHeld (fun x => x ∈ ([17] : List Nat) ∨
        (needed result x ∧ x ∉ (function.blocks[1]!).params.map (·.1))) result.ctx (before word)
        (fun key => machine word (aliasNum result.final.alias key)) := by
      intro x member value read
      have cases : x = 7 ∨ x = 17 := by
        rcases member with argument | ⟨need,notParameter⟩
        · exact Or.inr (List.mem_singleton.mp argument)
        · rcases need.1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · subst x; exact False.elim (notParameter (by decide +kernel))
      rcases cases with rfl | rfl
      · simp [Clif.Ty.width,before,initial,Clif.Regs.set,Clif.Regs.empty] at read
        subst value
        refine ⟨192,map7,?_⟩
        dsimp only
        rw [resolve7]
        exact low64 word
      · simp [Clif.Ty.width,before,initial,Clif.Regs.set,Clif.Regs.empty] at read
        subst value
        refine ⟨193,map17,?_⟩
        dsimp only
        rw [resolve17]
        exact low8 word
    have targetNumbers : edgeParamNumbers result function.blocks[1]! = [194] := by
      simp [edgeParamNumbers,function,edgeValueNum,map31,resolve31]
    have sourceNumbers : edgeArgumentNumbers result ⟨1,[17]⟩ = [192] := by
      simp [edgeArgumentNumbers,edgeValueNum,map17,resolve17]
    have computed : blockOrder function = .ok
        ⟨#[.original 0,.edge 0 0 1,.edge 0 1 1,.original 1],#[#[1,2],#[3],#[3],#[]]⟩ := by cbv
    have order := Except.ok.inj ((stock_lower_order run).symm.trans computed)
    have cases : index = 0 ∨ index = 1 := by omega
    have tag : result.order.nodes[1+index]? = some (.edge 0 index 1) := by
      rw [order]; rcases cases with rfl | rfl <;> rfl
    have selected : (dests function.blocks[0]!.term)[index]? = some (⟨1,[17]⟩ : Clif.BlockCall) := by
      rcases cases with rfl | rfl <;> rfl
    have target_eq : ∀ n,result.order.nodes[n]? = some (.original 1) → n = 3 := by
      intro n target
      have size : n < 4 := by have h := (Array.getElem?_eq_some_iff.mp target).1; simpa [order] using h
      have possibilities : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases possibilities with rfl | rfl | rfl | rfl
      · rw [order] at target; cases target
      · rw [order] at target; cases target
      · rw [order] at target; cases target
      · rfl
    obtain ⟨targetLabel,ρ',targetTag,successors,copy,transfer⟩ := stock_lower_critical_edge_values run
      (lowerScope_of (by decide +kernel)) dominated tag (by rfl) selected (by rfl)
      (fr := before word) rfl rfl rfl (fun x h => h.2.2) held
    have same := target_eq targetLabel targetTag
    subst targetLabel
    obtain ⟨input,next,registers,targetLabel,call,successors,targetTag,placed⟩ := stock_lower_critical_code run tag
    have same := target_eq targetLabel targetTag
    subst targetLabel
    have successor : succOf result.code (1+index) 0 = some 3 := by
      rcases cases with rfl | rfl <;> assumption
    have jump : VStep result.code ispec (.run ⟨1+index,0,machine word,world⟩) (.run ⟨3,0,ρ',world⟩) := by
      exact VStep.step placed rfl (ops := #[]) rfl (ispec_jump 3 world) rfl
        (VNext.goto rfl successor copy)
    have branch : Clif.stepTerm Clif.Env.empty {funcs := []} ⟨before word,[],Clif.Mem.empty⟩
        (.brif 7 ⟨1,[17]⟩ ⟨1,[17]⟩) = .next ⟨after word,[],Clif.Mem.empty⟩ := by
      simp only [Clif.stepTerm,ite_self]
      rfl
    exact ⟨result,rfl,lowerScope_of (by decide +kernel),dominated,alias,need7,need17,need31,
      args1,args2,params,rfl,rfl,branch,rfl,ρ',copy,transfer,jump⟩
/-- Every original word and either conditional successor inhabit a real
critical-edge copy, including the actual synthetic jump VStep, source
entry/reduction/branch/return, nonempty alias/copy and dirty upper machine bits. -/
theorem stock_critical_per_edge_step_witness (word : BitVec 64) (index : Nat) (bound : index < 2)
    (world : Arm.ArmState) : ∃ result : Result,
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    (result.final.alias[193]?).join = some 192 ∧ needed result 7 ∧ needed result 17 ∧ needed result 31 ∧
    (result.code.blocks[1]!).branchArgs = #[.vreg 192 .int] ∧
    (result.code.blocks[2]!).branchArgs = #[.vreg 192 .int] ∧ (result.code.blocks[3]!).params = #[.vreg 194 .int] ∧
    Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty = .ok (initial word,Clif.Mem.empty) ∧
    Clif.step Clif.Env.empty {funcs := []} ⟨initial word,[],Clif.Mem.empty⟩ = .next ⟨before word,[],Clif.Mem.empty⟩ ∧
    Clif.stepTerm Clif.Env.empty {funcs := []} ⟨before word,[],Clif.Mem.empty⟩
      (.brif 7 ⟨1,[17]⟩ ⟨1,[17]⟩) = .next ⟨after word,[],Clif.Mem.empty⟩ ∧
    Clif.step Clif.Env.empty {funcs := []} ⟨after word,[],Clif.Mem.empty⟩ = .done [⟨.i8,word.setWidth 8⟩] Clif.Mem.empty ∧
    ∃ ρ',outgoingAt result 0 index = some #[] ∧
      edgeEnvAt result.code result.edgeArgs (1+index) 3 0 (machine word) = some ρ' ∧
      ValuesHeld (needed result) result.ctx (after word) (fun key => ρ' (aliasNum result.final.alias key)) ∧
      VStepAt result.code result.edgeArgs ispec (.run ⟨1+index,0,machine word,world⟩) (.run ⟨3,0,ρ',world⟩) := by
  have actual := observed
  unfold Observed at actual
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨map7,map17,map31,alias,resolve7,resolve17,resolve31,demand7,demand17,demand31,args1,args2,params,succ1,succ2⟩ := actual
    have block : function.blocks[1]? = some function.blocks[1]! := rfl
    obtain ⟨in7,in17⟩ := entry_available run
    have available7 : 7 ∈ availOf function (availIn function result.ctx) 1 0 := by
      refine (mem_av block).mpr ⟨.inr (.inl in7),?_⟩
      rintro ⟨j,stm,_,present,_⟩
      simp [function] at present
    have available17 : 17 ∈ availOf function (availIn function result.ctx) 1 0 := by
      refine (mem_av block).mpr ⟨.inr (.inl in17),?_⟩
      rintro ⟨j,stm,_,present,_⟩
      simp [function] at present
    have available31 : 31 ∈ availOf function (availIn function result.ctx) 1 0 := by
      simp [availOf,function,defsBefore,defsFrom]
    have need7 : needed result 7 := ⟨.inl rfl,demand7,available7⟩
    have need17 : needed result 17 := ⟨.inr (.inl rfl),demand17,available17⟩
    have need31 : needed result 31 := ⟨.inr (.inr rfl),demand31,available31⟩
    have held : ValuesHeld (fun x => x ∈ ([17] : List Nat) ∨
        (needed result x ∧ x ∉ (function.blocks[1]!).params.map (·.1))) result.ctx (before word)
        (fun key => machine word (aliasNum result.final.alias key)) := by
      intro x member value read
      have cases : x = 7 ∨ x = 17 := by
        rcases member with argument | ⟨need,notParameter⟩
        · exact Or.inr (List.mem_singleton.mp argument)
        · rcases need.1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · subst x; exact False.elim (notParameter (by decide +kernel))
      rcases cases with rfl | rfl
      · simp [Clif.Ty.width,before,initial,Clif.Regs.set,Clif.Regs.empty] at read
        subst value
        refine ⟨192,map7,?_⟩
        dsimp only
        rw [resolve7]
        exact low64 word
      · simp [Clif.Ty.width,before,initial,Clif.Regs.set,Clif.Regs.empty] at read
        subst value
        refine ⟨193,map17,?_⟩
        dsimp only
        rw [resolve17]
        exact low8 word
    have targetNumbers : edgeParamNumbers result function.blocks[1]! = [194] := by
      simp [edgeParamNumbers,function,edgeValueNum,map31,resolve31]
    have sourceNumbers : edgeArgumentNumbers result ⟨1,[17]⟩ = [192] := by
      simp [edgeArgumentNumbers,edgeValueNum,map17,resolve17]
    have computed : blockOrder function = .ok
        ⟨#[.original 0,.edge 0 0 1,.edge 0 1 1,.original 1],#[#[1,2],#[3],#[3],#[]]⟩ := by cbv
    have order := Except.ok.inj ((stock_lower_order run).symm.trans computed)
    have cases : index = 0 ∨ index = 1 := by omega
    have tag : result.order.nodes[1+index]? = some (.edge 0 index 1) := by
      rw [order]; rcases cases with rfl | rfl <;> rfl
    have selected : (dests function.blocks[0]!.term)[index]? = some (⟨1,[17]⟩ : Clif.BlockCall) := by
      rcases cases with rfl | rfl <;> rfl
    have target_eq : ∀ n,result.order.nodes[n]? = some (.original 1) → n = 3 := by
      intro n target
      have size : n < 4 := by have h := (Array.getElem?_eq_some_iff.mp target).1; simpa [order] using h
      have possibilities : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases possibilities with rfl | rfl | rfl | rfl
      · rw [order] at target; cases target
      · rw [order] at target; cases target
      · rw [order] at target; cases target
      · rfl
    obtain ⟨targetLabel,ρ',targetTag,successors,copy,transfer⟩ := stock_lower_critical_per_edge_values run
      (lowerScope_of (by decide +kernel)) dominated tag (by rfl) selected (by rfl)
      (fr := before word) rfl rfl rfl (fun x h => h.2.2) held
    have same := target_eq targetLabel targetTag
    subst targetLabel
    obtain ⟨input,next,registers,targetLabel,call,successors,targetTag,placed⟩ := stock_lower_critical_code run tag
    have same := target_eq targetLabel targetTag
    subst targetLabel
    have successor : succOf result.code (1+index) 0 = some 3 := by
      rcases cases with rfl | rfl <;> assumption
    have sourceTag : result.order.nodes[0]? = some (.original 0) := by rw [order]; rfl
    have sourceSuccessor : result.order.successors[0]![index]? = some (1+index) := by
      rw [order]; rcases cases with rfl | rfl <;> rfl
    have deferred := stock_lower_deferred_outgoing run sourceTag sourceSuccessor tag
    have jump : VStepAt result.code result.edgeArgs ispec (.run ⟨1+index,0,machine word,world⟩) (.run ⟨3,0,ρ',world⟩) := by
      exact VStepAt.step placed rfl (ops := #[]) rfl (ispec_jump 3 world) rfl
        (VNextAt.goto rfl successor copy)
    have branch : Clif.stepTerm Clif.Env.empty {funcs := []} ⟨before word,[],Clif.Mem.empty⟩
        (.brif 7 ⟨1,[17]⟩ ⟨1,[17]⟩) = .next ⟨after word,[],Clif.Mem.empty⟩ := by
      simp only [Clif.stepTerm,ite_self]
      rfl
    exact ⟨result,rfl,lowerScope_of (by decide +kernel),dominated,alias,need7,need17,need31,
      args1,args2,params,rfl,rfl,branch,rfl,ρ',deferred,copy,transfer,jump⟩
/-- Complete actual critical-edge lowering also inhabits the automatically
derived route, retaining all three demanded/available alias/copy source values. -/
theorem stock_critical_selected_route_witness (word : BitVec 64) (index : Nat) (bound : index < 2) :
    ∃ (result : Result) (tl targetLabel : Nat) (ρ' : Nat → CV),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      (result.final.alias[193]?).join = some 192 ∧ needed result 7 ∧ needed result 17 ∧ needed result 31 ∧
      blockIdx? function 1 = some tl ∧ result.order.nodes[targetLabel]? = some (.original tl) ∧
      SelectedCopyRoute result 0 index (machine word) targetLabel ρ' ∧
      ValuesHeld (needed result) result.ctx (after word) (fun key => ρ' (aliasNum result.final.alias key)) ∧
      Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty = .ok (initial word,Clif.Mem.empty) ∧
      Clif.step Clif.Env.empty {funcs := []} ⟨initial word,[],Clif.Mem.empty⟩ = .next ⟨before word,[],Clif.Mem.empty⟩ ∧
      Clif.enterBlock (before word) ⟨1,[17]⟩ = .ok (after word) ∧
      Clif.step Clif.Env.empty {funcs := []} ⟨after word,[],Clif.Mem.empty⟩ = .done [⟨.i8,word.setWidth 8⟩] Clif.Mem.empty := by
  have actual := observed
  unfold Observed at actual
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨map7,map17,map31,alias,resolve7,resolve17,resolve31,demand7,demand17,demand31,args1,args2,params,succ1,succ2⟩ := actual
    have block : function.blocks[1]? = some function.blocks[1]! := rfl
    obtain ⟨in7,in17⟩ := entry_available run
    have available7 : 7 ∈ availOf function (availIn function result.ctx) 1 0 := by
      refine (mem_av block).mpr ⟨.inr (.inl in7),?_⟩
      rintro ⟨j,stm,_,present,_⟩
      simp [function] at present
    have available17 : 17 ∈ availOf function (availIn function result.ctx) 1 0 := by
      refine (mem_av block).mpr ⟨.inr (.inl in17),?_⟩
      rintro ⟨j,stm,_,present,_⟩
      simp [function] at present
    have available31 : 31 ∈ availOf function (availIn function result.ctx) 1 0 := by
      simp [availOf,function,defsBefore,defsFrom]
    have need7 : needed result 7 := ⟨.inl rfl,demand7,available7⟩
    have need17 : needed result 17 := ⟨.inr (.inl rfl),demand17,available17⟩
    have need31 : needed result 31 := ⟨.inr (.inr rfl),demand31,available31⟩
    have held : ValuesHeld (fun x => x ∈ ([17] : List Nat) ∨
        (needed result x ∧ x ∉ (function.blocks[1]!).params.map (·.1))) result.ctx (before word)
        (fun key => machine word (aliasNum result.final.alias key)) := by
      intro x member value read
      have cases : x = 7 ∨ x = 17 := by
        rcases member with argument | ⟨need,notParameter⟩
        · exact Or.inr (List.mem_singleton.mp argument)
        · rcases need.1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · subst x; exact False.elim (notParameter (by decide +kernel))
      rcases cases with rfl | rfl
      · simp [Clif.Ty.width,before,initial,Clif.Regs.set,Clif.Regs.empty] at read
        subst value
        refine ⟨192,map7,?_⟩
        dsimp only
        rw [resolve7]
        exact low64 word
      · simp [Clif.Ty.width,before,initial,Clif.Regs.set,Clif.Regs.empty] at read
        subst value
        refine ⟨193,map17,?_⟩
        dsimp only
        rw [resolve17]
        exact low8 word
    have targetNumbers : edgeParamNumbers result function.blocks[1]! = [194] := by
      simp [edgeParamNumbers,function,edgeValueNum,map31,resolve31]
    have sourceNumbers : edgeArgumentNumbers result ⟨1,[17]⟩ = [192] := by
      simp [edgeArgumentNumbers,edgeValueNum,map17,resolve17]
    have computed : blockOrder function = .ok
        ⟨#[.original 0,.edge 0 0 1,.edge 0 1 1,.original 1],#[#[1,2],#[3],#[3],#[]]⟩ := by cbv
    have order := Except.ok.inj ((stock_lower_order run).symm.trans computed)
    have cases : index = 0 ∨ index = 1 := by omega
    have tag : result.order.nodes[1+index]? = some (.edge 0 index 1) := by
      rw [order]; rcases cases with rfl | rfl <;> rfl
    have selected : (dests function.blocks[0]!.term)[index]? = some (⟨1,[17]⟩ : Clif.BlockCall) := by
      rcases cases with rfl | rfl <;> rfl
    have target_eq : ∀ n,result.order.nodes[n]? = some (.original 1) → n = 3 := by
      intro n target
      have size : n < 4 := by have h := (Array.getElem?_eq_some_iff.mp target).1; simpa [order] using h
      have possibilities : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases possibilities with rfl | rfl | rfl | rfl
      · rw [order] at target; cases target
      · rw [order] at target; cases target
      · rw [order] at target; cases target
      · rfl
    have sourceTag : result.order.nodes[0]? = some (.original 0) := by rw [order]; rfl
    obtain ⟨tl,targetLabel,ρ',targetIndex,original,route,transfer⟩ := stock_lower_selected_route_values run
      (lowerScope_of (by decide +kernel)) dominated sourceTag (by rfl) selected
      (fr := before word) rfl rfl (fun x h => h.2.2) held
    exact ⟨result,tl,targetLabel,ρ',rfl,lowerScope_of (by decide +kernel),dominated,alias,need7,need17,need31,
      targetIndex,original,route,transfer,rfl,rfl,rfl,rfl⟩
end Backend.Stock.Proof.CriticalValuesWitness
