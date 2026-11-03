import FV.Clif.Parse
import FV.Backend.Proof.StockTableCore
import FV.Backend.Proof.LowerDecide

/-! Non-vacuity of the Stock `br_table` theorems on the real `%f` of
`third_party/wasmtime/cranelift/filetests/filetests/isa/aarch64/jumptable.clif` (#140, CB-14a).

```
function %f(i32) -> i32 {
block0(v0: i32):
  br_table v0, block4, [block1, block2, block3]
...
```

The text of `%f` parses to `function`. Its Stock lowering gives block 0 the successors
`[4, 3, 2, 1]` (the default, then the table in layout labels), and the final code of block 0 is the
entry argument move followed by `tableCode 4 [3, 2, 1] v192 204`: `emit_island 44`,
`subs wzr, v192, #3` and `jt_sequence` with the temporaries `v204`, `v205`, as in the filetest's
expected VCode (`jumptable_lowered`). In the real built context, the terminator slot of block 0
with its prepared data satisfies every premise of `table_named_code` and `table_named_values`, and
the actual named branch run succeeds (`jumptable_table_values`). The actual retained core of
block 0 satisfies the premises of `stock_lower_table_core` and `CoreOrigin.table_values`: its
retained emission is `tableCode 4 [3, 2, 1] r n` at the frontier `n` of its actual input, and it
takes the `branchIdx` edge of the source index (`jumptable_core`). One marked `native_decide`
evaluates the parse, the scope check, the context build, the named branch run and the lowering of
this fixed function. -/

namespace Backend.Stock.Proof.TableBranch.Witness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 ConditionalValues
set_option autoImplicit false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program

/-- The text of `%f` in `jumptable.clif`. -/
def source : String := "function %f(i32) -> i32 {
block0(v0: i32):
  br_table v0, block4, [block1, block2, block3]

block1:
  v1 = iconst.i32 1
  jump block5(v1)

block2:
  v2 = iconst.i32 2
  jump block5(v2)

block3:
  v3 = iconst.i32 3
  jump block5(v3)

block4:
  v4 = iconst.i32 4
  jump block5(v4)

block5(v5: i32):
  v6 = iadd.i32 v0, v5
  return v6
}
"

/-- `%f` as a `Clif.Function` literal. -/
def function : Clif.Function := {
  name := "f"
  sig := { params := [⟨.i32,.none,.normal⟩], returns := [⟨.i32,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i32)], body := [], term := .brTable 0 ⟨4,[]⟩ [⟨1,[]⟩,⟨2,[]⟩,⟨3,[]⟩] },
    { id := 1, params := [], body := [⟨[1],.iconst .i32 1⟩], term := .jump ⟨5,[1]⟩ },
    { id := 2, params := [], body := [⟨[2],.iconst .i32 2⟩], term := .jump ⟨5,[2]⟩ },
    { id := 3, params := [], body := [⟨[3],.iconst .i32 3⟩], term := .jump ⟨5,[3]⟩ },
    { id := 4, params := [], body := [⟨[4],.iconst .i32 4⟩], term := .jump ⟨5,[4]⟩ },
    { id := 5, params := [(5,.i32)], body := [⟨[6],.binary .iadd .i32 0 5⟩], term := .ret [6] }] }

/-- The successor labels of block 0: the default, then the table. -/
def labels : List Label := [4,3,2,1]

/-- The final code of block 0: the entry argument move, then the resolved table code. -/
def blockCode : Array MInst :=
  #[.args [(.vreg 192 .int,.x 0)]] ++ (tableCode 4 [3,2,1] (.vreg 192 .int) 204).toArray

@[irreducible] private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
private def ctx : Ctx := Driver.termCtx built.1 0 (tableData 0)

/-- The executable facts of the witness. -/
private def checks : Bool :=
  decide ((Clif.parseFile source).funcs.map (·.func.toOption) = [some function]) &&
  lowerScopeB function &&
  (Stock.buildCtx function).toOption.isSome &&
  decide (built.1.valueType? 0 = some (.int 32)) &&
  (match Stock.runTerm ctx "lower_branch" [.inst 0,.labels labels] built.2.2 with
    | .ok (some _,_,_) => true
    | _ => false) &&
  match Stock.lower function with
  | .ok result => decide (result.order.successors[0]? = some labels.toArray) &&
      decide (result.code.blocks[0]?.map (·.insts) = some blockCode) &&
      decide (result.order.nodes[0]? = some (.original 0))
  | .error _ => false

-- witness: native_decide (the parse, scope check, context build, named branch run and lowering of the fixed function %f only)
private theorem checks_true : checks = true := by native_decide -- witness: native_decide

private theorem parts :
    decide ((Clif.parseFile source).funcs.map (·.func.toOption) = [some function]) = true ∧
    lowerScopeB function = true ∧ (Stock.buildCtx function).toOption.isSome = true ∧
    decide (built.1.valueType? 0 = some (.int 32)) = true ∧
    (match Stock.runTerm ctx "lower_branch" [.inst 0,.labels labels] built.2.2 with
      | .ok (some _,_,_) => true
      | _ => false) = true ∧
    (match Stock.lower function with
      | .ok result => decide (result.order.successors[0]? = some labels.toArray) &&
          decide (result.code.blocks[0]?.map (·.insts) = some blockCode) &&
          decide (result.order.nodes[0]? = some (.original 0))
      | .error _ => false) = true := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨parse,scope⟩,build⟩,typed⟩,branch⟩,lowered⟩ := h
  exact ⟨parse,scope,build,typed,branch,lowered⟩

private theorem scope : LowerScope function := lowerScope_of parts.2.1

private theorem build : Stock.buildCtx function = .ok (built.1,built.2.1,built.2.2) := by
  have present := parts.2.2.1
  unfold built
  cases actual : Stock.buildCtx function with
  | error message => rw [actual] at present; cases present
  | ok value => rfl

private theorem placeholder : built.1.insts[0]? = some ⟨.op .unit,[],[],none⟩ := by
  obtain ⟨original,st0,_,ctxSpec,view⟩ := buildCtx_source build
  rw [view.insts]
  exact ctxSpec.facts.term 0 _ rfl

private theorem inv : MappedCtxInv function ctx := (buildCtx_mappedInv scope build).termCtx placeholder _

private theorem slot : ctx.insts[0]? = some ⟨tableData 0,[],[],none⟩ := by
  have inside := (Array.getElem?_eq_some_iff.mp placeholder).1
  change (built.1.insts.set! 0 ⟨tableData 0,[],[],none⟩)[0]? = _
  simp only [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt inside]

private theorem typed : ctx.valueType? 0 = some (.int 32) := of_decide_eq_true parts.2.2.2.1

private theorem lower_build {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) :
    ∃ ranges,Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,by assumption⟩

/-- The prepared data of the terminator of block 0 is `tableData 0`. -/
theorem prepared : Coverage.blockData function (function.blocks[0]!.term) = .ok (tableData 0) := by
  with_unfolding_all rfl

/-- **The real `%f` of `jumptable.clif` lowers to the table code.** The text parses to `function`,
which is in the lowering scope; Stock lowering succeeds, block 0 has the successors `[4, 3, 2, 1]`,
and its final code is the entry argument move followed by `tableCode 4 [3, 2, 1] v192 204`. -/
theorem jumptable_lowered :
    (Clif.parseFile source).funcs.map (·.func.toOption) = [some function] ∧ LowerScope function ∧
    ∃ result,Stock.lower function = .ok result ∧ result.order.successors[0]? = some labels.toArray ∧
      result.code.blocks[0]?.map (·.insts) = some blockCode := by
  have lowered := parts.2.2.2.2.2
  refine ⟨of_decide_eq_true parts.1,scope,?_⟩
  cases run : Stock.lower function with
  | error message => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    simp only [Bool.and_eq_true,decide_eq_true_eq] at lowered
    exact ⟨result,rfl,lowered.1.1,lowered.1.2⟩

/-- **The table theorems apply to the real terminator of `%f`.** In the built context of the real
lowering, the slot of the `br_table` of block 0 with its prepared data `tableData 0` satisfies the
premises of `table_named_code` and `table_named_values`, and the actual named branch run from the
initial state succeeds. Its code is exactly `tableCode 4 [3, 2, 1] r` at the initial frontier, and
from values held at its output it stops at the `jt_sequence` on the `branchIdx` edge of the source
index `bits` (`tableTarget bits.toNat 3`). -/
theorem jumptable_table_values :
    ∃ result,Stock.lower function = .ok result ∧ result.order.successors[0]? = some labels.toArray ∧
      MappedCtxInv function (Driver.termCtx result.ctx 0 (tableData 0)) ∧
      (Driver.termCtx result.ctx 0 (tableData 0)).insts[0]? = some ⟨tableData 0,[],[],none⟩ ∧
      (Driver.termCtx result.ctx 0 (tableData 0)).valueType? 0 = some (.int 32) ∧
      ∃ out next trace r,
        Stock.runTerm (Driver.termCtx result.ctx 0 (tableData 0)) "lower_branch"
          [.inst 0,.labels labels] result.initial = .ok (some out,next,trace) ∧
        (Driver.termCtx result.ctx 0 (tableData 0)).valueReg? 0 = some r ∧
        next.base = tableState result.initial.base 4 [3,2,1] r ∧
        next.base.emitted = result.initial.base.emitted ++
          (tableCode 4 [3,2,1] r result.initial.base.nextVreg).toArray ∧
        ∀ {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem},Refines F isem →
          ∀ {fr : Clif.Frame} {bits : BitVec 32},fr.getAs 0 .i32 = .ok bits →
          ∀ {aliases : Array (Option Nat)} {ρ : Nat → CV},aliases.size ≤ result.initial.base.nextVreg →
          (∀ value r,(Driver.termCtx result.ctx 0 (tableData 0)).valueReg? value = some r →
            value < result.initial.demand.size) →
          ValuesHeld (Demanded next) (Driver.termCtx result.ctx 0 (tableData 0)) fr
            (fun key => ρ (aliasNum aliases key)) →
          ∃ code : List MInst,next.base.emitted = result.initial.base.emitted ++ code.toArray ∧
            ∀ world,LastTableExecution F isem labels (code.map
              (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
              (tableTarget bits.toNat 3) ρ world := by
  have lowered := parts.2.2.2.2.2
  have success := parts.2.2.2.2.1
  cases run : Stock.lower function with
  | error message => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    simp only [Bool.and_eq_true,decide_eq_true_eq] at lowered
    obtain ⟨ranges,created⟩ := lower_build run
    have same := Except.ok.inj (created.symm.trans build)
    have context : result.ctx = built.1 := congrArg Prod.fst same
    have initial : result.initial = built.2.2 := congrArg (fun p => p.2.2) same
    cases branch : Stock.runTerm ctx "lower_branch" [.inst 0,.labels labels] built.2.2 with
    | error e => rw [branch] at success; cases success
    | ok q =>
      obtain ⟨out,next,trace⟩ := q
      cases out with
      | none => rw [branch] at success; cases success
      | some out =>
        obtain ⟨d,ts,r,labelsEq,mapped,_,state,emitted,_⟩ := table_named_code slot typed (by decide) branch
        simp only [labels,List.cons.injEq] at labelsEq
        obtain ⟨rfl,rfl⟩ := labelsEq
        refine ⟨result,rfl,lowered.1.1,?_⟩
        rw [context,initial]
        refine ⟨inv,slot,typed,out,next,trace,r,branch,mapped,state,emitted,?_⟩
        intro F isem refines fr bits getX aliases ρ bounded extent held
        obtain ⟨d',ts',code,labelsEq',codeEq,_,_,execution⟩ :=
          table_named_values inv slot typed (by decide) branch refines getX bounded extent held
        simp only [labels,List.cons.injEq] at labelsEq'
        obtain ⟨rfl,rfl⟩ := labelsEq'
        exact ⟨code,codeEq,execution⟩

/-- **The table theorems apply to the actual retained core of `%f`.** Block 0 is the original
block at label 0 of the real lowering. Its actual core retains its named branch run in the actual
terminator context, which satisfies `MappedCtxInv`; the retained code is exactly
`tableCode 4 [3, 2, 1] r n` at the frontier `n` of the actual core input, with `r` the register of
`v0`; and from values held at the emission output, the resolved retained code stops at its
`jt_sequence` on the `branchIdx` edge `tableTarget bits.toNat 3` of the source index `bits`. -/
theorem jumptable_core :
    ∃ result,Stock.lower function = .ok result ∧ result.order.nodes[0]? = some (.original 0) ∧
      result.code.blocks[0]?.map (·.insts) = some blockCode ∧
      ∃ (ranges : Array (Nat × Nat)) (input : State) (core : LoweredBlockCore)
        (origin : CoreOrigin {Driver.termCtx result.ctx (ranges[0]!.2-1) (tableData 0) with
            tryRegs := input.tryRegs[ranges[0]!.2-1]!}
          function 0 (ranges[0]!.2-1) result.order.successors[0]! input core),
        lowerBlockCore result.ctx result.order function function.blocks[0]! 0 ranges[0]!.1 ranges[0]!.2
          (tableData 0) result.order.successors[0]! input = .ok core ∧
        core.scan ∈ result.blockScans.toList ∧ MappedCtxInv function core.scan.ctx ∧
        ∃ r,result.ctx.valueReg? 0 = some r ∧
          origin.emission.code = (tableCode 4 [3,2,1] r input.base.nextVreg).toArray ∧
          origin.emission.state.base.nextVreg = input.base.nextVreg+2 ∧
          ∀ {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem},Refines F isem →
            ∀ {fr : Clif.Frame} {bits : BitVec 32},fr.getAs 0 .i32 = .ok bits →
            ∀ {aliases : Array (Option Nat)} {ρ : Nat → CV},aliases.size ≤ input.base.nextVreg →
            (∀ value r,core.scan.ctx.valueReg? value = some r → value < input.demand.size) →
            ValuesHeld (Demanded origin.emission.state) core.scan.ctx fr
              (fun key => ρ (aliasNum aliases key)) →
            ∀ world,LastTableExecution F isem labels (origin.emission.code.toList.map
              (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
              (tableTarget bits.toNat 3) ρ world := by
  have lowered := parts.2.2.2.2.2
  cases run : Stock.lower function with
  | error message => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    simp only [Bool.and_eq_true,decide_eq_true_eq] at lowered
    obtain ⟨⟨successors,code⟩,tag⟩ := lowered
    obtain ⟨ranges,created⟩ := lower_build run
    have same := Except.ok.inj (created.symm.trans build)
    have context : result.ctx = built.1 := congrArg Prod.fst same
    have typeX : result.ctx.valueType? 0 = some (.int 32) := by rw [context]; exact typed
    have successorsEq : result.order.successors[0]! = labels.toArray := by
      rw [getElem!_def,successors]
    have small : result.order.successors[0]!.size ≤ 4096 := by rw [successorsEq]; decide
    obtain ⟨ranges',input,core,origin,_,coreRun,events,_,scanCtx,inv',slot',typeHere,d,ts,r,labelsEq,
      mapped,emitted,frontier⟩ :=
      stock_lower_table_core run scope tag rfl rfl typeX small
    rw [successorsEq] at labelsEq
    simp only [labels,List.cons.injEq] at labelsEq
    obtain ⟨rfl,rfl⟩ := labelsEq
    refine ⟨result,rfl,tag,code,ranges',input,core,origin,coreRun,events,inv',r,mapped,emitted,frontier,?_⟩
    intro F isem refines fr bits getX aliases ρ bounded extent held world
    rw [scanCtx] at inv' slot' typeHere extent held
    obtain ⟨d,ts,labelsEq,_,_,execution⟩ :=
      origin.table_values inv' slot' typeHere small refines getX bounded extent held
    have labelsActual : labels = result.order.successors[0]!.toList := by rw [successorsEq]
    rw [successorsEq] at labelsEq
    simp only [labels,List.cons.injEq] at labelsEq
    obtain ⟨rfl,rfl⟩ := labelsEq
    rw [labelsActual]
    exact execution world

end Backend.Stock.Proof.TableBranch.Witness
