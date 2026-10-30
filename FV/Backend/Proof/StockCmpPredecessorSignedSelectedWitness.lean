import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockCmpPredecessorSignedSelection
namespace Backend.Stock.Proof.ScalarCmp.PredecessorSignedSelectedWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def literal (second : Bool) : Nat := if second then 8193 else 4097
private def immediate (second : Bool) : Imm12 := ⟨if second then 2 else 1,true⟩
private def function (second : Bool) : Clif.Function := {
  name := "stock_predecessor_selected_original"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],body := [⟨[31],.iconst .i64 (BitVec.ofNat 64 (literal second))⟩,
    ⟨[100],.icmp .sge .i64 7 31⟩],term := .ret [100]}] }
private def built (second : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function second)).toOption.getD (sinkCtx,#[],sinkState)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem actual (second : Bool) : ∃ out next trace,
    ApplyInternal program (Stock.sem (built second).1) {} 999 123 652
      [.data 145 (ccIdx .sge) [],.value 7,.value 31] ((built second).2.2,#[]) out (next,trace) := by
  have success : (((applyTerm program (Stock.sem (built second).1) {} 1000 123 652
      [.data 145 (ccIdx .sge) [],.value 7,.value 31]).run ((built second).2.2,#[])).toOption.bind (fun r => r.1)).isSome = true := by
    cases second <;> decide +kernel
  cases run : (applyTerm program (Stock.sem (built second).1) {} 1000 123 652
      [.data 145 (ccIdx .sge) [],.value 7,.value 31]).run ((built second).2.2,#[]) with
  | error e => simp only [run,Except.toOption,Option.bind_none,Option.isSome_none] at success; cases success
  | ok r =>
    obtain ⟨out,next,trace⟩ := r
    cases out with
    | none => simp only [run,Except.toOption,Option.bind_some,Option.isSome_none] at success; cases success
    | some out => exact ⟨out,next,trace,run⟩
end Kernel
/-- Accepted original comparison contexts with4097/8193 really select the
predecessor rule: the original literal is nonencodable and its predecessor is
an encodable shifted immediate. This is a selected-helper witness, not a retained driver proof. -/
theorem stock_cmp_predecessor_signed_selected_source_witness (second : Bool) :
    LowerScope (function second) ∧ ∃ out next trace rhsTrace,
      ApplyInternal program (Stock.sem (built second).1) {} 999 123 652
        [.data 145 (ccIdx .sge) [],.value 7,.value 31] ((built second).2.2,#[]) out (next,trace) ∧
      (evalExpr program (Stock.sem (built second).1) {} 999 rule_inst_5160.rhs
        #[some (.ty (.int 64)),some (.value 7),some (.int (literal second)),some (.op (.imm12 (immediate second)))]).run
        ((built second).2.2,#[]) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push rule_inst_5160.id := by
  have scope : LowerScope (function second) := lowerScope_of (by cases second <;> decide +kernel)
  obtain ⟨out,next,trace,run⟩ := actual second
  let info := (built second).1.insts[0]!
  have typed : (built second).1.valueType? 7 = some (.int 64) := by cases second <;> rfl
  have defined : (built second).1.defInst? 31 = some 0 := by cases second <;> rfl
  have found : (built second).1.insts[0]? = some info := by cases second <;> rfl
  have data : info.data = .data 152 35 [.data 151 57 [],.int (literal second)] := by cases second <;> decide +kernel
  obtain ⟨rhsTrace,rhs,equal⟩ := stock_cmp_predecessor_signed_emitter_selected data_program (built second).1 .size64
    (by decide) typed defined found data (by cases second <;> decide +kernel)
    (imm := immediate second) (by cases second <;> decide +kernel) (by cases second <;> decide +kernel) run
  have normalized : u64 (literal second) = literal second := by cases second <;> decide +kernel
  rw [normalized] at rhs
  exact ⟨scope,out,next,trace,rhsTrace,run,rhs,equal⟩
end Backend.Stock.Proof.ScalarCmp.PredecessorSignedSelectedWitness
