import FV.Backend.Proof.StockEdgeValues

namespace Backend.Stock.Proof.EdgeValuesWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def reduce : Clif.Stmt := ⟨[17],.ireduce .i8 7⟩
private def function : Clif.Function := {
  name := "stock_edge_values_alias"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],body := [reduce],term := .jump ⟨1,[17]⟩},
    {id := 1,params := [(31,.i8)],term := .ret [31]}] }
private def original : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx function).toOption.getD (sinkCtx,#[],default)
private theorem original_build : Backend.buildCtx function = .ok original := rfl
private def initial (word : BitVec 64) : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 7 ⟨.i64,word⟩,slots := [],body := [reduce],term := .jump ⟨1,[17]⟩ }
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
  (result.code.blocks[0]!).branchArgs = #[.vreg 192 .int] ∧
  (result.code.blocks[1]!).params = #[.vreg 194 .int])) = some true
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
        have same : x = 17 := by simpa [abiTerm,Driver.termArgs] using member
        subst x
        simp [availOf,function,reduce,defsBefore,defsFrom]
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

/-- Complete actual two-block lowering has a nonempty193→192 alias and a real
192→194 successor copy. For arbitrary words, both inherited source7/17 and new
parameter31 satisfy the demanded/available mapped-value relation after copying.
Real source entry/reduction/edge/return and original scope/dominance are included. -/
theorem stock_edge_values_alias_witness (word : BitVec 64) : ∃ result : Result,
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    (result.final.alias[193]?).join = some 192 ∧ needed result 7 ∧ needed result 17 ∧ needed result 31 ∧
    (result.code.blocks[0]!).branchArgs = #[.vreg 192 .int] ∧ (result.code.blocks[1]!).params = #[.vreg 194 .int] ∧
    Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty = .ok (initial word,Clif.Mem.empty) ∧
    Clif.step Clif.Env.empty {funcs := []} ⟨initial word,[],Clif.Mem.empty⟩ = .next ⟨before word,[],Clif.Mem.empty⟩ ∧
    Clif.enterBlock (before word) ⟨1,[17]⟩ = .ok (after word) ∧
    Clif.step Clif.Env.empty {funcs := []} ⟨after word,[],Clif.Mem.empty⟩ = .done [⟨.i8,word.setWidth 8⟩] Clif.Mem.empty ∧
    edgeParamNumbers result function.blocks[1]! = [194] ∧ edgeArgumentNumbers result ⟨1,[17]⟩ = [192] ∧
    aliasNum result.final.alias 193 ≠ aliasNum result.final.alias 194 ∧ aliasNum result.final.alias 194 = 194 ∧
    ValuesHeld (needed result) result.ctx (after word) (fun key =>
      parCopyEnv (machine word) [194] [192] (aliasNum result.final.alias key)) := by
  have actual := observed
  unfold Observed at actual
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨map7,map17,map31,alias,resolve7,resolve17,resolve31,demand7,demand17,demand31,args,params⟩ := actual
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
    have transfer := stock_lower_edge_values run (lowerScope_of (by decide +kernel)) dominated block
      (fr := before word) rfl (bc := ⟨1,[17]⟩) rfl rfl (fun x h => h.2.2) held
    rw [targetNumbers,sourceNumbers] at transfer
    have apart := stock_lower_entry_alias_apart run (lowerScope_of (by decide +kernel)) dominated block
      need17.2.2 (by decide +kernel) map17 (by decide +kernel) map31
    have fixed := stock_lower_parameter_resolves run dominated.ssa block (by decide +kernel) map31
    exact ⟨result,rfl,lowerScope_of (by decide +kernel),dominated,alias,need7,need17,need31,args,params,
      rfl,rfl,rfl,rfl,targetNumbers,sourceNumbers,apart,fixed,transfer⟩
end Backend.Stock.Proof.EdgeValuesWitness
