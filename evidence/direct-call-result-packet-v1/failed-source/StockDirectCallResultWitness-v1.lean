import FV.Backend.Proof.StockDirectCallResult
import FV.Backend.Proof.StockSourceCallWitness
namespace Backend.Stock.Proof.DirectCallResultWitness
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.DirectCallResult
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def signature : Clif.Signature := {
  params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV }
def statement : Clif.Stmt := ⟨[31],.call 0 [7]⟩
def caller : Clif.Function := {
  name := "stock_source_call_result",sig := signature
  externs := [(0,{name := "stock_source_identity",sig := signature,colocated := true})]
  blocks := [{id := 0,params := [(7,.i64)],body := [statement],term := .ret [31]}] }
def callee : Clif.Function := {
  name := "stock_source_identity",sig := signature
  blocks := [{id := 0,params := [(101,.i64)],term := .ret [101]}] }
def value (word : BitVec 64) : Clif.Val := ⟨.i64,word⟩
def before (word : BitVec 64) : Clif.Frame := {
  func := caller,regs := Clif.Regs.empty.set 7 (value word),slots := [],body := [statement],term := .ret [31] }
def saved (word : BitVec 64) : Clif.Frame := {before word with body := []}
def after (word : BitVec 64) : Clif.Frame := {saved word with regs := (saved word).regs.set 31 (value word)}
def active (word : BitVec 64) : Clif.State := {
  frame := {func := callee,regs := Clif.Regs.empty.set 101 (value word),slots := [],body := [],term := .ret [101]}
  callers := [(saved word,[31])],mem := Clif.Mem.empty }
def program : Clif.Program := {funcs := [callee]}
def environment : Clif.Env := {extern := fun name =>
  if name = callee.name then Option.some (fun vals cm => .returned vals cm) else none}

def actualInfo : CallInfo := ⟨.sym callee.name,[(.vreg 192 .int,.x 0)],[(.x 0,.vreg 194 .int)]⟩
def checked (r : Stock.Result) : Bool :=
  decide (r.ctx.valueReg? 31 = some (.vreg 193 .int)) &&
  decide (Backend.lowerFunction.resolve r.final.alias (r.final.alias.size+1) (.vreg 193 .int) = .vreg 194 .int) &&
  (r.code.blocks[0]?).any fun block =>
    decide (.call actualInfo ∈ block.insts.toList) &&
    decide (block.insts.toList.getLast? = some (.rets [(.vreg 194 .int,.x 0)]))

-- witness: native_decide (the unchanged original-style complete caller only)
private theorem actual_checked : (Stock.lower caller).toOption.map checked = some true := by native_decide

private theorem binding_of_run {r : Stock.Result} (run : Stock.lower caller = .ok r) :
    Nonempty (Binding r.ctx r.final 31) ∧ ∃ block,r.code.blocks[0]? = some block ∧
      .call actualInfo ∈ block.insts.toList ∧
      block.insts.toList.getLast? = some (.rets [(.vreg 194 .int,.x 0)]) := by
  have good := actual_checked
  simp only [run,Except.toOption,Option.map_some,Option.some.injEq] at good
  simp only [checked,Bool.and_eq_true,decide_eq_true_eq] at good
  refine ⟨⟨⟨193,194,good.1.1,good.1.2⟩⟩,?_⟩
  cases found : r.code.blocks[0]? with
  | none => simp [found] at good
  | some block =>
    simp only [found,Option.any_some,Bool.and_eq_true,decide_eq_true_eq] at good
    exact ⟨block,rfl,good.2⟩

/-- Sparse source result31 resolves to virtual194, whose actual call definition and return use x0. -/
-- witness: native_decide (only fixed Stock metadata; every argument word remains arbitrary)
theorem original_call_binding (word : BitVec 64) : ∃ c d : Stock.Result,
    Stock.lower caller = .ok c ∧ Stock.lower callee = .ok d ∧
    Nonempty (Binding c.ctx c.final 31) ∧
    (∃ block,c.code.blocks[0]? = some block ∧ .call actualInfo ∈ block.insts.toList ∧
      block.insts.toList.getLast? = some (.rets [(.vreg 194 .int,.x 0)])) ∧
    Clif.enterFunc caller [value word] Clif.Mem.empty = .ok (before word,Clif.Mem.empty) ∧
    Clif.step environment {funcs := []} ⟨before word,[],Clif.Mem.empty⟩ =
      .next ⟨after word,[],Clif.Mem.empty⟩ ∧
    Clif.step Clif.Env.empty program ⟨before word,[],Clif.Mem.empty⟩ = .next (active word) ∧
    Clif.step Clif.Env.empty program (active word) = .next ⟨after word,[],Clif.Mem.empty⟩ ∧
    SourceDefinedAt caller c.ctx 0 1 (after word) ∧
    VHolds (value word)
      (vdefUpd (retOps [(192,.x 0)] ++ callDefOps [(.x 0,194)]).toArray [ofX word]
        (fun _ => 0) 194) := by
  obtain ⟨c,d,crun,drun,scope,scopeD,dominated,one,oneD,entered,external,internal,
    returned,done,definedBefore,definedAfter,kept,bound,restored⟩ :=
    SourceCallWitness.stock_source_call_result_witness word
  have crun' : Stock.lower caller = .ok c := crun
  have observed := binding_of_run crun'
  refine ⟨c,d,crun',drun,observed.1,observed.2,entered,external,internal,returned,definedAfter,?_⟩
  rw [virtual_result]
  simp [VHolds,value,ofX,Clif.Ty.width]

/-- The source binder keeps arbitrary returned memory; it preserves inherited source values. -/
theorem memory_effect (word : BitVec 64) (cm resultMemory : Clif.Mem) :
    let initial : Clif.State := ⟨before word,[],cm⟩
    let next : Clif.State := ⟨after word,[],resultMemory⟩
    Clif.continueWith initial [] [31] [value word] resultMemory = .next next ∧
      next.frame.regs 31 = some (value word) ∧ next.frame.regs 7 = some (value word) ∧
      next.mem = resultMemory := by
  exact ⟨rfl,rfl,rfl,rfl⟩

end Backend.Stock.Proof.DirectCallResultWitness
