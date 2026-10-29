module

public import FV.Backend.Proof.StockScalarGeneralDivDomain
public import FV.Backend.Proof.StockNoLoadDriverWitness

@[expose] public section

namespace Backend.Stock.Proof.SinkRules.DriverWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.lower Stock.runTerm

private def block : Clif.Block := function.blocks[0]!
private theorem scope_source : LowerScope function := lowerScope_of (by decide +kernel)
private theorem dominated_checked : dominatedB function = true := by native_decide
private theorem dominated_source : Dominated function := dominated_of dominated_checked
private theorem body_family : ∀ stm ∈ block.body,
    HighMulBody.Family stm.inst ∨ ∃ op ty x y,stm.inst = .div op ty x y := by
  intro stm member
  change stm ∈ [⟨[100],.div .sdiv .i64 1 8⟩,⟨[101],.div .udiv .i64 100 8⟩] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact Or.inr ⟨.sdiv,.i64,1,8,rfl⟩
  · exact Or.inr ⟨.udiv,.i64,100,8,rfl⟩

/-- The complete return/trap domain is inhabited for consumed and unused
division results using the original scope, dominance and ABI conditions. -/
theorem two_division_domain : Scalar.Domain function :=
  Scalar.domain_of_scalar_div scope_source dominated_source (by decide +kernel)
    (b := block) rfl body_family (xs := [1]) rfl (by rfl)

def arguments (input : Nat → BitVec 64) : List Clif.Val :=
  (List.range 9).map (fun i => ⟨.i64,input i⟩)
def frame (input : Nat → BitVec 64) (slot : Nat) : Clif.Frame := {
  func := function
  regs := (Clif.Regs.empty.setMany (List.range 9) (arguments input)).getD Clif.Regs.empty
  slots := [(7,slot)]
  body := block.body
  term := .ret [1] }

/-- Arbitrary original values and the original slot address inhabit source entry. -/
theorem two_division_source_entry (input : Nat → BitVec 64) (slot : Nat) :
    SourceEntry function (arguments input) (frame input slot) :=
  ⟨block,_,rfl,rfl,rfl,rfl,rfl⟩

/-- Actual source returns an original argument even though both divisions run. -/
theorem two_division_source_return :
    Clif.runLoop Clif.Env.empty {funcs := []} 3
      ⟨frame (fun i => if i = 1 then 42 else 2) 4096,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,42⟩] Clif.Mem.empty := by rfl

/-- An unused quotient does not suppress the original zero-divisor trap. -/
theorem two_division_source_zero :
    Clif.runLoop Clif.Env.empty {funcs := []} 3
      ⟨frame (fun _ => 0) 4096,[],Clif.Mem.empty⟩ = .trapped .intDivz := by rfl

/-- The consumed signed division retains the original minimum divided by -1 overflow. -/
theorem two_division_source_overflow :
    Clif.runLoop Clif.Env.empty {funcs := []} 3
      ⟨frame (fun i => if i = 1 then BitVec.intMin 64 else -1) 4096,[],Clif.Mem.empty⟩ =
      .trapped .intOvf := by rfl

/-- The complete actual body is classified through derived emission and
result binding; no result-demand or returned-division premise is supplied. -/
theorem two_division_records : ∃ output event term body,
    Stock.lower function = .ok output ∧ Scalar.Domain function ∧
    event ∈ output.blockScans.toList ∧ SourceBodySplit function event block term body ∧
    ∀ record ∈ body.records,MixedDivRecord function event.ctx event.block record := by
  obtain ⟨output,run,scope,blocks,emitted,demand,unsunk⟩ := two_division_driver_witness
  have bound : 0 < output.blockScans.size := by omega
  let event := output.blockScans[0]
  have lookup : output.blockScans[0]? = some event := Array.getElem?_eq_getElem bound
  have member : event ∈ output.blockScans.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup)
  obtain ⟨term,body,split,classified⟩ := DivBody.actual_scalar_div_families run scope
    (b := block) rfl body_family member
  exact ⟨output,event,term,body,run,two_division_domain,member,split,classified⟩

end Backend.Stock.Proof.SinkRules.DriverWitness
