import FV.Backend.Proof.StockDirectCallResult
namespace Backend.Stock.Proof.DirectCallResultFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.DirectCallResult
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower
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
def callData : Option MInst → Option (CallDest × List (Reg × Reg) × List (Reg × Reg))
  | some (.call info) => some (info.dest,info.uses,info.defs)
  | _ => none

def retData : Option MInst → Option (List (Reg × Reg))
  | some (.rets pairs) => some pairs
  | _ => none

def checked (r : Stock.Result) : Bool :=
  decide (r.ctx.valueReg? 31 = some (.vreg 193 .int)) &&
  decide (Backend.lowerFunction.resolve r.final.alias (r.final.alias.size+1) (.vreg 193 .int) = .vreg 194 .int) &&
  (r.code.blocks[0]?).any fun block =>
    decide (callData block.insts[1]? = some (actualInfo.dest,actualInfo.uses,actualInfo.defs)) &&
    decide (retData block.insts.toList.getLast? = some [(.vreg 194 .int,.x 0)])

attribute [local irreducible] checked
section KernelMetadata
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm Stock.lower checked
private theorem actual_checked : (Stock.lower caller).toOption.map checked = some true := by
  decide +kernel
end KernelMetadata
#eval IO.eprintln "CHECKPOINT: kernel metadata proved"

theorem binding_of_run {r : Stock.Result} (run : Stock.lower caller = .ok r) :
    Nonempty (Binding r.ctx r.final 31) ∧ ∃ block,r.code.blocks[0]? = some block ∧
      callData block.insts[1]? = some (actualInfo.dest,actualInfo.uses,actualInfo.defs) ∧
      retData block.insts.toList.getLast? = some [(.vreg 194 .int,.x 0)] := by
  have good := actual_checked
  simp only [run,Except.toOption,Option.map_some,Option.some.injEq] at good
  simp only [checked,Bool.and_eq_true,decide_eq_true_eq] at good
  refine ⟨⟨⟨193,194,good.1.1,good.1.2⟩⟩,?_⟩
  cases found : r.code.blocks[0]? with
  | none => simp [found] at good
  | some block =>
    simp only [found,Option.any_some,Bool.and_eq_true,decide_eq_true_eq] at good
    exact ⟨block,rfl,good.2⟩


end Backend.Stock.Proof.DirectCallResultFixture
