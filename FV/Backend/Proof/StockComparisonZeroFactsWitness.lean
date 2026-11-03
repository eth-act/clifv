import FV.Backend.Proof.StockComparisonZeroFacts
import FV.Backend.Proof.StockComparisonBranchSelection
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Proof.ComparisonBranch.ZeroWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- `block0(v0: i64): v1 = iconst.i64 0; v2 = icmp eq v0, v1;
brif v2, block1(v0), block2(v0)`, with both successors returning their
parameter. The constant is used only by the comparison. -/
def function : Clif.Function := {
  name := "stock_comparison_zero_witness"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(0,.i64)],body := [⟨[1],.iconst .i64 0⟩,⟨[2],.icmp .eq .i64 0 1⟩],term := .brif 2 ⟨1,[0]⟩ ⟨2,[0]⟩},
    {id := 1,params := [(3,.i64)],term := .ret [3]},{id := 2,params := [(4,.i64)],term := .ret [4]}] }

/-- The prepared data of the entry terminator, slot 2. -/
def brifData : V := .data 152 5 [.data 151 1 [],.value 2,.blockCalls [0,1]]

private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
private def ctx : Ctx := Driver.termCtx built.1 2 brifData
private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
private theorem build : Stock.buildCtx function = .ok built := by rfl
private theorem inv : MappedCtxInv function ctx := (buildCtx_mappedInv scope build).termCtx (by rfl) _
private theorem slot : ctx.insts[2]? = some ⟨brifData,[],[],none⟩ := by rfl
private theorem origin : ctx.defClif? 2 = some (.icmp .eq .i64 0 1) := by rfl
private theorem operand : ctx.defInst? 0 = none := by rfl
private theorem constant : ctx.defClif? 1 = some (.iconst .i64 0) := by rfl
private theorem typeX : ctx.valueType? 0 = some (.int (if true then 64 else 32)) := by rfl

section Kernel
attribute [local semireducible] Isle.Aarch64.program
private theorem prepared : Backend.termData (abiTerm function function.blocks[0]!.term) = .ok brifData := by
  rfl
private theorem entry : built.2.1[0]? = some (0,3) := by rfl
private theorem lowered : (Stock.lower function).toOption.isSome = true := by decide +kernel
private theorem branch_success :
    (Stock.runTerm ctx "lower_branch" [.inst 2,.labels [2,1]] built.2.2).toOption.map
      (fun q => q.1.isSome) = some true := by
  decide +kernel
end Kernel

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

/-- The zero-comparison brif of the complete lowered fixture satisfies
every premise of `comparison_named_calls`. Its actual `lower_branch` run at the
entry terminator slot therefore yields the ordinary helper-call packet with
condition value 2. -/
theorem comparison_zero_calls_witness : ∃ (result : Result) (out : V) (next : State) (trace : List RuleId),
    Stock.lower function = .ok result ∧ LowerScope function ∧
    (∃ ranges,Stock.buildCtx function = .ok (result.ctx,ranges,result.initial) ∧ ranges[0]? = some (0,3)) ∧
    Backend.termData (abiTerm function function.blocks[0]!.term) = .ok brifData ∧
    MappedCtxInv function (Driver.termCtx result.ctx 2 brifData) ∧
    (Driver.termCtx result.ctx 2 brifData).defClif? 2 = some (.icmp .eq .i64 0 1) ∧
    (Driver.termCtx result.ctx 2 brifData).defInst? 0 = none ∧
    Stock.runTerm (Driver.termCtx result.ctx 2 brifData) "lower_branch"
      [.inst 2,.labels [2,1]] result.initial = .ok (some out,next,trace) ∧
    ∃ calls : ConditionalCalls.Calls (Driver.termCtx result.ctx 2 brifData) 2 [2,1] result.initial out next,
      calls.source = .value 2 := by
  have actual := lowered
  cases run : Stock.lower function with
  | error err =>
    rw [run] at actual
    simp only [Except.toOption,Option.isSome_none,Bool.false_eq_true] at actual
  | ok result =>
    obtain ⟨ranges,created⟩ := lower_build run
    have same := Except.ok.inj (created.symm.trans build)
    have context : result.ctx = built.1 := congrArg Prod.fst same
    have initial : result.initial = built.2.2 := congrArg (fun p => p.2.2) same
    have success := branch_success
    cases branch : Stock.runTerm ctx "lower_branch" [.inst 2,.labels [2,1]] built.2.2 with
    | error e => simp only [branch,Except.toOption,Option.map_none,reduceCtorEq] at success
    | ok q =>
      obtain ⟨out,next,trace⟩ := q
      cases out with
      | none => simp [branch,Except.toOption] at success
      | some out =>
        obtain ⟨calls,source⟩ := comparison_named_calls inv slot origin operand branch
        have ranges_eq : ranges = built.2.1 := congrArg (fun p => p.2.1) same
        subst ranges_eq
        refine ⟨result,out,next,trace,rfl,scope,⟨_,created,entry⟩,prepared,?_⟩
        rw [context,initial]
        exact ⟨inv,origin,operand,branch,calls,source⟩

/-- The real calls packet of the entry `brif` on `icmp eq v0, v1` with
`v1 = iconst.i64 0` instantiates the zero comparison facts: the branch
appends exactly `cbz v0` (a `Zero` conditional branch on the register of
`v0`) and nothing else, allocates no virtual register, keeps the demand
extent, and its fragment defines no virtual register. -/
theorem comparison_zero_facts_witness : ∃ (result : Result) (out : V) (next : State) (trace : List RuleId)
    (calls : ConditionalCalls.Calls (Driver.termCtx result.ctx 2 brifData) 2 [2,1]
      result.initial out next),
    Stock.lower function = .ok result ∧
    Stock.runTerm (Driver.termCtx result.ctx 2 brifData) "lower_branch"
      [.inst 2,.labels [2,1]] result.initial = .ok (some out,next,trace) ∧
    calls.source = .value 2 ∧
    (∃ key,(Driver.termCtx result.ctx 2 brifData).valueReg? 0 = some (.vreg key .int) ∧
      next.base = result.initial.base.emit (.condBr calls.yes calls.no (.zero (.vreg key .int) .size64))) ∧
    next.base.nextVreg = result.initial.base.nextVreg ∧ next.demand.size = result.initial.demand.size ∧
    next.base.emitted.size = result.initial.base.emitted.size+1 ∧
    ∃ code,Frag result.initial.base next.base code ∧ ∀ inst ∈ code,vdefs inst = [] := by
  obtain ⟨result,out,next,trace,run,_,⟨ranges,created,_⟩,_,inv,origin,operand,branch,calls,source⟩ :=
    comparison_zero_calls_witness
  have same := Except.ok.inj (created.symm.trans build)
  have context : result.ctx = built.1 := congrArg Prod.fst same
  have constant' : (Driver.termCtx result.ctx 2 brifData).defClif? 1 = some (.iconst .i64 0) := by
    rw [context]
    exact constant
  have typeX' : (Driver.termCtx result.ctx 2 brifData).valueType? 0 =
      some (.int (if true then 64 else 32)) := by
    rw [context]
    exact typeX
  have equality : Clif.IntCC.eq = .eq ∨ Clif.IntCC.eq = .ne := Or.inl rfl
  have zero : (0 : BitVec Clif.Ty.i64.width) = 0 := rfl
  obtain ⟨key,mapped,emitted⟩ :=
    Calls.comparison_zero_emission inv calls source origin true typeX' operand constant' equality zero
  simp only [↓reduceIte] at emitted
  obtain ⟨frontier,extent⟩ :=
    calls.comparison_zero_bounds inv source origin true typeX' operand constant' equality zero
  have size := calls.comparison_zero_emitted_size inv source origin true typeX' operand constant' equality zero
  obtain ⟨code,fragment,noDefs⟩ :=
    calls.comparison_zero_no_defs inv source origin true typeX' operand constant' equality zero
  exact ⟨result,out,next,trace,calls,run,branch,source,⟨key,mapped,emitted⟩,frontier,extent,size,
    code,fragment,noDefs⟩

end Backend.Stock.Proof.ComparisonBranch.ZeroWitness
