module

public import FV.Backend.Proof.StockPerEdgeValues
public import FV.Backend.Proof.StockSelectedRoutes
public import FV.Backend.Proof.IselCtlBrif

@[expose] public section

/-! An accepted ordinary branching function exposes the remaining per-successor
consumer migration. Raw Stock keeps the correct vectors in Result.edgeArgs;
legacy VCode.edgeEnv alone cannot represent these nonsynthetic edges. -/
namespace Backend.Stock.Proof.PerEdgeDirectWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function : Clif.Function := {
  name := "stock_per_successor_migration"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩},
    {id := 1,params := [(31,.i64)],term := .ret [31]}, {id := 2,params := [(47,.i64)],term := .ret [47]}] }
private def original : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx function).toOption.getD (sinkCtx,#[],default)
private theorem original_build : Backend.buildCtx function = .ok original := rfl
private def first (word : BitVec 64) : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 7 ⟨.i64,word⟩,slots := [],body := [],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩ }
private def after (word : BitVec 64) (index : Nat) : Clif.Frame := {
  first word with regs := (first word).regs.set (if index = 0 then 31 else 47) ⟨.i64,word⟩,term := .ret [if index = 0 then 31 else 47] }
private def machine (word : BitVec 64) (key : Nat) : CV :=
  if key = 192 then BitVec.ofNat 128 (2^100+word.toNat) else 0
private def needed (result : Result) (index x : Nat) : Prop :=
  (x = 7 ∨ x = if index = 0 then 31 else 47) ∧ Demanded result.final x ∧
    x ∈ availOf function (availIn function result.ctx) (1+index) 0
private def Observed : Prop := (Stock.lower function).toOption.map (fun result => decide (
  result.ctx.valueReg? 7 = some (.vreg 192 .int) ∧ result.ctx.valueReg? 31 = some (.vreg 193 .int) ∧
  result.ctx.valueReg? 47 = some (.vreg 194 .int) ∧ aliasNum result.final.alias 192 = 192 ∧
  aliasNum result.final.alias 193 = 193 ∧ aliasNum result.final.alias 194 = 194 ∧
  result.final.demand[7]! ≠ 0 ∧ result.final.demand[31]! ≠ 0 ∧ result.final.demand[47]! ≠ 0 ∧
  result.code.blocks.size = 3 ∧ (result.code.blocks[0]!).insts =
    #[.args [(.vreg 192 .int,.x 0)],.condBr 2 1 (.notZero (.vreg 192 .int) .size64)] ∧
  succOf result.code 0 0 = some 2 ∧ succOf result.code 0 1 = some 1)) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel
private theorem dominated : Dominated function := by
  constructor
  · change ([7,31,47] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b found
    have bound : bi < 3 := by have h := lt_of_getElem? found; simpa [function] using h
    have cases : bi = 0 ∨ bi = 1 ∨ bi = 2 := by omega
    rcases cases with rfl | rfl | rfl
    all_goals
      simp [function] at found
      subst b
      constructor
      · intro j stm present; simp at present
      · intro x member
        simp [abiTerm,Driver.termArgs,sretRet,sigRets,function] at member
        subst x
        simp [availOf,function,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have fixed := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have values : x = 7 ∨ x = 31 ∨ x = 47 := by simpa [valueDefs,function] using fixed.2.2.2.1
    have context : ctx = original.1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans original_build))
    rw [context] at member
    rcases values with rfl | rfl | rfl
    all_goals change y ∈ ([] : List Nat) at member; cases member

private theorem low64 (word : BitVec 64) :
    (BitVec.ofNat 128 (2^100+word.toNat)).setWidth 64 = word := by
  rw [BitVec.setWidth_ofNat_of_le (by decide : 64 ≤ 128)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,Nat.add_mod,show 2^100 % 2^64 = 0 from by decide +kernel,
    Nat.zero_add,Nat.mod_eq_of_lt word.isLt]
private theorem inherited_available {result : Result} (run : Stock.lower function = .ok result)
    (index : Nat) (bound : index < 2) :
    7 ∈ availOf function (availIn function result.ctx) (1+index) 0 := by
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
  have size : result.ctx.valDef.size = 48 := by rw [view.valDef,same]; rfl
  have arguments : defArgs result.ctx = defArgs original.1 := by
    funext x
    simp only [defArgs,Ctx.defInst?,view.valDef,view.insts,same]
  let D : Nat → Nat → Prop := fun tl x => (tl = 1 ∨ tl = 2) ∧ x = 7
  have fixed : FixOk function result.ctx id D := by
    constructor
    · rintro tl x ⟨positions,rfl⟩
      rcases positions with rfl | rfl <;> simp [size,function,valueDefs,parsOf]
    · rintro tl x ⟨positions,rfl⟩ p successor
      have previous : p = 0 := by
        cases p with
        | zero => rfl
        | succ p =>
          cases p with
          | zero => simp [succIdx,function,succIds,dests] at successor
          | succ p =>
            cases p with
            | zero => simp [succIdx,function,succIds,dests] at successor
            | succ p => simp [succIdx,function] at successor
      subst p
      exact .inl (by decide +kernel)
    · rintro tl x ⟨_,rfl⟩ y member
      rw [arguments] at member
      change y ∈ ([] : List Nat) at member
      cases member
  have positions : 1+index = 1 ∨ 1+index = 2 := by omega
  have incoming := inFix_greatest fixed ⟨positions,rfl⟩
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl
  · refine (mem_av (by rfl : function.blocks[1]? = some function.blocks[1]!)).mpr ⟨.inr (.inl incoming),?_⟩
    rintro ⟨j,stm,_,present,_⟩
    simp [function] at present
  · refine (mem_av (by rfl : function.blocks[2]? = some function.blocks[2]!)).mpr ⟨.inr (.inl incoming),?_⟩
    rintro ⟨j,stm,_,present,_⟩
    simp [function] at present

private theorem branch_sem (word : BitVec 64) (world : Arm.ArmState) (a : CV) (low : opnd .size64 a = word) :
    ispec (.condBr 2 1 (.notZero (.vreg 192 .int) .size64)) [a] world =
      some ([],world,.goto (if word = (0#64) then 1 else 0)) := by
  by_cases zero : word = (0#64)
  · have holds : condBrHolds (.notZero (.vreg 192 .int) .size64) [a] world = false := by
      rw [condBrHolds_notZero]
      exact bne_eq_false_iff_eq.mpr (low.trans zero)
    simp only [ispec,holds,zero,ite_true,Bool.false_eq_true,ite_false]
  · have holds : condBrHolds (.notZero (.vreg 192 .int) .size64) [a] world = true := by
      rw [condBrHolds_notZero]
      exact bne_iff_ne.mpr (fun eq => zero (low.symm.trans eq))
    simp only [ispec,holds,zero,ite_true,ite_false]

private theorem source_branch (word : BitVec 64) :
    let index := if word = (0#64) then 1 else 0
    Clif.stepTerm Clif.Env.empty {funcs := []} ⟨first word,[],Clif.Mem.empty⟩
      (.brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩) = .next ⟨after word index,[],Clif.Mem.empty⟩ := by
  dsimp only
  by_cases zero : word = (0#64)
  · subst word; rfl
  · have truth : Clif.Sem.truthy (⟨.i64,word⟩ : Clif.Val).bits = true := by
      unfold Clif.Sem.truthy
      exact bne_iff_ne.mpr zero
    simp only [Clif.stepTerm]
    have get : (first word).get 7 = .ok (⟨.i64,word⟩ : Clif.Val) := rfl
    rw [get]
    simp only [Clif.StepResult.ofRes,truth,ite_true,zero,ite_false]
    rfl

/-- The complete three-block function requiring per-successor consumers now
has actual conditional VStepAt execution and held successor values for every
source word/world. Both source successors occur, with dirty upper bits and
all original demand/availability guards; no extra edge blocks are introduced. -/
theorem stock_direct_per_edge_step_witness (word : BitVec 64) (world : Arm.ArmState) :
    ∃ (result : Result) (index : Nat) (ρ' : Nat → CV),
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    index = (if word = (0#64) then 1 else 0) ∧ index < 2 ∧ needed result index 7 ∧
    needed result index (if index = 0 then 31 else 47) ∧
    edgeEnvAt result.code result.edgeArgs 0 (2-index) index (machine word) = some ρ' ∧
    ValuesHeld (needed result index) result.ctx (after word index) (fun key => ρ' (aliasNum result.final.alias key)) ∧
    Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty = .ok (first word,Clif.Mem.empty) ∧
    Clif.stepTerm Clif.Env.empty {funcs := []} ⟨first word,[],Clif.Mem.empty⟩
      (.brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩) = .next ⟨after word index,[],Clif.Mem.empty⟩ ∧
    Clif.stepTerm Clif.Env.empty {funcs := []} ⟨after word index,[],Clif.Mem.empty⟩
      (.ret [if index = 0 then 31 else 47]) = .done [⟨.i64,word⟩] Clif.Mem.empty ∧
    VStepAt result.code result.edgeArgs ispec (.run ⟨0,1,machine word,world⟩) (.run ⟨2-index,0,ρ',world⟩) := by
  let index := if word = (0#64) then 1 else 0
  have bound : index < 2 := by dsimp [index]; split <;> omega
  have positions : index = 0 ∨ index = 1 := by omega
  have actual := observed
  unfold Observed at actual
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨map7,map31,map47,resolve7,resolve31,resolve47,demand7,demand31,demand47,size,code,succ0,succ1⟩ := actual
    have available7 := inherited_available run index bound
    have availableParameter : (if index = 0 then 31 else 47) ∈
        availOf function (availIn function result.ctx) (1+index) 0 := by
      rcases positions with h | h <;> simp [h,availOf,function,defsBefore,defsFrom]
    have needed7 : needed result index 7 := ⟨.inl rfl,demand7,available7⟩
    have neededParameter : needed result index (if index = 0 then 31 else 47) := by
      refine ⟨.inr rfl,?_,availableParameter⟩
      rcases positions with h | h <;> simp only [h,ite_true,show (1 = 0) = False from by decide,ite_false] <;> assumption
    have parameter : (if index = 0 then 31 else 47) ∈ (function.blocks[1+index]!).params.map (·.1) := by
      rcases positions with h | h <;> simp [h,function]
    have held : ValuesHeld (fun x => x ∈ ([7] : List Nat) ∨
        (needed result index x ∧ x ∉ (function.blocks[1+index]!).params.map (·.1))) result.ctx (first word)
        (fun key => machine word (aliasNum result.final.alias key)) := by
      intro x member value read
      have same : x = 7 := by
        rcases member with arg | ⟨need,absent⟩
        · exact List.mem_singleton.mp arg
        · rcases need.1 with h | h
          · exact h
          · subst x; exact False.elim (absent parameter)
      subst x
      simp [first,Clif.Regs.set,Clif.Regs.empty] at read
      subst value
      refine ⟨192,map7,?_⟩
      dsimp only
      rw [resolve7]
      exact low64 word
    have order : result.order = ⟨#[.original 0,.original 2,.original 1],#[#[2,1],#[],#[]]⟩ :=
      Except.ok.inj ((stock_lower_order run).symm.trans (by cbv))
    have sourceTag : result.order.nodes[0]? = some (.original 0) := by rw [order]; rfl
    have targetTag : result.order.nodes[2-index]? = some (.original (1+index)) := by
      rw [order]; rcases positions with h | h <;> simp [h]
    have successor : result.order.successors[0]![index]? = some (2-index) := by
      rw [order]; rcases positions with h | h <;> simp [h]
    have selected : (dests function.blocks[0]!.term)[index]? = some (⟨1+index,[7]⟩ : Clif.BlockCall) := by
      rcases positions with h | h <;> simp [h,function,dests]
    have target : function.block? (1+index) = some function.blocks[1+index]! := by
      rcases positions with h | h <;> simp [h,function,Clif.Function.block?]
    have entered : Clif.enterBlock (first word) ⟨1+index,[7]⟩ = .ok (after word index) := by
      rcases positions with h | h <;> rw [h] <;> rfl
    obtain ⟨ρ',copy,transfer⟩ := stock_lower_direct_per_edge_values run (lowerScope_of (by decide +kernel))
      dominated sourceTag (by rfl) selected successor targetTag (by rcases positions with h | h <;> rw [h] <;> rfl)
      (fr := first word) rfl target entered (fun x h => h.2.2) held
    have sourcePlaced : result.code.blocks[0]? = some result.code.blocks[0]! := by
      have h : 0 < result.code.blocks.size := by omega
      simp [getElem!_def,Array.getElem?_eq_getElem h]
    have cfg : succOf result.code 0 index = some (2-index) := by rcases positions with h | h <;> simpa [h] using (by first | exact succ0 | exact succ1)
    have low : opnd .size64 (machine word 192) = word := by
      change ((machine word 192).setWidth 64).setWidth 64 = word
      rw [BitVec.setWidth_eq]
      simpa [machine] using low64 word
    have semantics : ispec (.condBr 2 1 (.notZero (.vreg 192 .int) .size64)) [machine word 192] world =
        some ([],world,.goto index) := branch_sem word world (machine word 192) low
    have step : VStepAt result.code result.edgeArgs ispec (.run ⟨0,1,machine word,world⟩)
        (.run ⟨2-index,0,ρ',world⟩) := by
      exact VStepAt.step sourcePlaced (by rw [code]; rfl) (ops := #[⟨192,.int,.use,.early,.reg⟩]) rfl semantics rfl
        (VNextAt.goto (by rw [code]; rfl) cfg copy)
    have branch : Clif.stepTerm Clif.Env.empty {funcs := []} ⟨first word,[],Clif.Mem.empty⟩
        (.brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩) = .next ⟨after word index,[],Clif.Mem.empty⟩ := source_branch word
    refine ⟨result,index,ρ',rfl,lowerScope_of (by decide +kernel),dominated,rfl,bound,needed7,neededParameter,
      copy,transfer,rfl,branch,?_,step⟩
    rcases positions with h | h <;> rw [h] <;> rfl
/-- A complete ordinary conditional inhabits automatic route classification
with no caller target index, lowered target label, vector or graph-case input. -/
theorem stock_direct_selected_route_witness (word : BitVec 64) :
    ∃ (result : Result) (index tl targetLabel : Nat) (ρ' : Nat → CV),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      index = (if word = (0#64) then 1 else 0) ∧ index < 2 ∧ needed result index 7 ∧
      needed result index (if index = 0 then 31 else 47) ∧
      blockIdx? function (1+index) = some tl ∧ result.order.nodes[targetLabel]? = some (.original tl) ∧
      SelectedCopyRoute result 0 index (machine word) targetLabel ρ' ∧
      ValuesHeld (needed result index) result.ctx (after word index) (fun key => ρ' (aliasNum result.final.alias key)) ∧
      Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty = .ok (first word,Clif.Mem.empty) ∧
      Clif.enterBlock (first word) ⟨1+index,[7]⟩ = .ok (after word index) ∧
      Clif.stepTerm Clif.Env.empty {funcs := []} ⟨first word,[],Clif.Mem.empty⟩
        (.brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩) = .next ⟨after word index,[],Clif.Mem.empty⟩ := by
  let index := if word = (0#64) then 1 else 0
  have bound : index < 2 := by dsimp [index]; split <;> omega
  have positions : index = 0 ∨ index = 1 := by omega
  have actual := observed
  unfold Observed at actual
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨map7,map31,map47,resolve7,resolve31,resolve47,demand7,demand31,demand47,size,code,succ0,succ1⟩ := actual
    have available7 := inherited_available run index bound
    have availableParameter : (if index = 0 then 31 else 47) ∈
        availOf function (availIn function result.ctx) (1+index) 0 := by
      rcases positions with h | h <;> simp [h,availOf,function,defsBefore,defsFrom]
    have needed7 : needed result index 7 := ⟨.inl rfl,demand7,available7⟩
    have neededParameter : needed result index (if index = 0 then 31 else 47) := by
      refine ⟨.inr rfl,?_,availableParameter⟩
      rcases positions with h | h <;> simp only [h,ite_true,show (1 = 0) = False from by decide,ite_false] <;> assumption
    have parameter : (if index = 0 then 31 else 47) ∈ (function.blocks[1+index]!).params.map (·.1) := by
      rcases positions with h | h <;> simp [h,function]
    have held : ValuesHeld (fun x => x ∈ ([7] : List Nat) ∨
        (needed result index x ∧ x ∉ (function.blocks[1+index]!).params.map (·.1))) result.ctx (first word)
        (fun key => machine word (aliasNum result.final.alias key)) := by
      intro x member value read
      have same : x = 7 := by
        rcases member with arg | ⟨need,absent⟩
        · exact List.mem_singleton.mp arg
        · rcases need.1 with h | h
          · exact h
          · subst x; exact False.elim (absent parameter)
      subst x
      simp [first,Clif.Regs.set,Clif.Regs.empty] at read
      subst value
      refine ⟨192,map7,?_⟩
      dsimp only
      rw [resolve7]
      exact low64 word
    have order : result.order = ⟨#[.original 0,.original 2,.original 1],#[#[2,1],#[],#[]]⟩ :=
      Except.ok.inj ((stock_lower_order run).symm.trans (by cbv))
    have sourceTag : result.order.nodes[0]? = some (.original 0) := by rw [order]; rfl
    have targetTag : result.order.nodes[2-index]? = some (.original (1+index)) := by
      rw [order]; rcases positions with h | h <;> simp [h]
    have successor : result.order.successors[0]![index]? = some (2-index) := by
      rw [order]; rcases positions with h | h <;> simp [h]
    have selected : (dests function.blocks[0]!.term)[index]? = some (⟨1+index,[7]⟩ : Clif.BlockCall) := by
      rcases positions with h | h <;> simp [h,function,dests]
    have target : function.block? (1+index) = some function.blocks[1+index]! := by
      rcases positions with h | h <;> simp [h,function,Clif.Function.block?]
    have entered : Clif.enterBlock (first word) ⟨1+index,[7]⟩ = .ok (after word index) := by
      rcases positions with h | h <;> rw [h] <;> rfl
    have available : ∀ x,needed result index x →
        x ∈ availOf function (availIn function result.ctx) (sourceTargetIndex function ⟨1+index,[7]⟩) 0 := by
      intro x need
      have targetIndex : blockIdx? function (1+index) = some (1+index) := by
        rcases positions with h | h <;> rw [h] <;> rfl
      simpa only [sourceTargetIndex,targetIndex,Option.getD_some] using need.2.2
    have held' : ValuesHeld (fun x => x ∈ ([7] : List Nat) ∨
        (needed result index x ∧ x ∉ sourceTargetParams function ⟨1+index,[7]⟩)) result.ctx (first word)
        (fun key => machine word (aliasNum result.final.alias key)) := by
      simpa only [sourceTargetParams,target,Option.getD_some] using held
    obtain ⟨tl,targetLabel,ρ',targetIndex,original,route,transfer⟩ := stock_lower_selected_route_values run
      (lowerScope_of (by decide +kernel)) dominated sourceTag (by rfl) selected rfl entered available held'
    exact ⟨result,index,tl,targetLabel,ρ',rfl,lowerScope_of (by decide +kernel),dominated,rfl,bound,
      needed7,neededParameter,targetIndex,original,route,transfer,rfl,entered,source_branch word⟩
end Backend.Stock.Proof.PerEdgeDirectWitness
