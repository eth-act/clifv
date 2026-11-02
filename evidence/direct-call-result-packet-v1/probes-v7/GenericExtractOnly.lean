import FV.Backend.Proof.StockDirectCallResult
namespace Backend.Stock.Proof.DirectCallResultFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.DirectCallResult
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower

#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/imports.done" "done"
def signature : Clif.Signature := {
  params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV }

#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/0-signature.done" "done"
def statement : Clif.Stmt := ⟨[31],.call 0 [7]⟩

#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/1-statement.done" "done"
def caller : Clif.Function := {
  name := "stock_source_call_result",sig := signature
  externs := [(0,{name := "stock_source_identity",sig := signature,colocated := true})]
  blocks := [{id := 0,params := [(7,.i64)],body := [statement],term := .ret [31]}] }

#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/2-caller.done" "done"
def callee : Clif.Function := {
  name := "stock_source_identity",sig := signature
  blocks := [{id := 0,params := [(101,.i64)],term := .ret [101]}] }

#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/3-callee.done" "done"
def value (word : BitVec 64) : Clif.Val := ⟨.i64,word⟩

#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/4-value.done" "done"
def before (word : BitVec 64) : Clif.Frame := {
  func := caller,regs := Clif.Regs.empty.set 7 (value word),slots := [],body := [statement],term := .ret [31] }

#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/5-before.done" "done"
def saved (word : BitVec 64) : Clif.Frame := {before word with body := []}

#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/6-saved.done" "done"
def after (word : BitVec 64) : Clif.Frame := {saved word with regs := (saved word).regs.set 31 (value word)}

#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/7-after.done" "done"
def active (word : BitVec 64) : Clif.State := {
  frame := {func := callee,regs := Clif.Regs.empty.set 101 (value word),slots := [],body := [],term := .ret [101]}
  callers := [(saved word,[31])],mem := Clif.Mem.empty }

#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/8-active.done" "done"
def program : Clif.Program := {funcs := [callee]}

#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/9-program.done" "done"
def environment : Clif.Env := {extern := fun name =>
  if name = callee.name then Option.some (fun vals cm => .returned vals cm) else none}


#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/10-environment.done" "done"
def actualInfo : CallInfo := ⟨.sym callee.name,[(.vreg 192 .int,.x 0)],[(.x 0,.vreg 194 .int)]⟩

#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/11-actualInfo.done" "done"
def callData : Option MInst → Option (CallDest × List (Reg × Reg) × List (Reg × Reg))
  | some (.call info) => some (info.dest,info.uses,info.defs)
  | _ => none


#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/12-callData.done" "done"
def retData : Option MInst → Option (List (Reg × Reg))
  | some (.rets pairs) => some pairs
  | _ => none


#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/13-retData.done" "done"
def checked (r : Stock.Result) : Bool :=
  decide (r.ctx.valueReg? 31 = some (.vreg 193 .int)) &&
  decide (Backend.lowerFunction.resolve r.final.alias (r.final.alias.size+1) (.vreg 193 .int) = .vreg 194 .int) &&
  (r.code.blocks[0]?).any fun block =>
    decide (callData block.insts[1]? = some (actualInfo.dest,actualInfo.uses,actualInfo.defs)) &&
    decide (retData block.insts.toList.getLast? = some [(.vreg 194 .int,.x 0)])

attribute [local irreducible] checked

#eval IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v1/14-checked.done" "done"

theorem checked_sound {r : Stock.Result} (good : checked r = true) :
    Nonempty (Binding r.ctx r.final 31) ∧ ∃ block,r.code.blocks[0]? = some block ∧
      callData block.insts[1]? = some (actualInfo.dest,actualInfo.uses,actualInfo.defs) ∧
      retData block.insts.toList.getLast? = some [(.vreg 194 .int,.x 0)] := by
  simp only [checked,Bool.and_eq_true,decide_eq_true_eq] at good
  refine ⟨⟨⟨193,194,good.1.1,good.1.2⟩⟩,?_⟩
  run_tac do let _ ← IO.FS.writeFile "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-result-packet-v1/probes-v7/binding-built.done" "done"; pure ()
  simpa only [Option.any_eq_true,Bool.and_eq_true,decide_eq_true_eq] using good.2
end Backend.Stock.Proof.DirectCallResultFixture
