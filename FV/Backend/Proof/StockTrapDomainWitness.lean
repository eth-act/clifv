import FV.Backend.Proof.StockTrapRefines
import FV.Backend.Proof.StockTrapProgress
import FV.Backend.Proof.StockScalarCheck

/-! Non-vacuity of `domain_of_maskTrap`: a real scalar function that ends in `trap` meets its
premises, and `Stock.lower` succeeds on the same function. -/

namespace Backend.Stock.Scalar
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

private def trapDomainFixture : Clif.Function := {
  name := "domain_of_maskTrap"
  sig := { params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0, .i64), (1, .i64)],
      body := [⟨[2], .binary .imul .i64 0 1⟩, ⟨[3], .binary .iadd .i64 2 0⟩], term := .trap (.user 9) }] }

private def trapDomainChecks : Bool :=
  trapDomainFixture.sig.params.all narrowAbiEligible && trapDomainFixture.sig.returns.all narrowAbiEligible &&
    Compile.functionE trapDomainFixture && dominatedB trapDomainFixture && lowerScopeB trapDomainFixture &&
    extendsWidenB trapDomainFixture && Prg.iselInB trapDomainFixture && driverInB trapDomainFixture &&
    sigAbiOk trapDomainFixture.sig && !((sigRets trapDomainFixture.sig).any (·.purpose == .sret))

-- witness: native_decide (the fixed function's input-condition checks only)
private theorem trapDomainChecks_true : trapDomainChecks = true := by native_decide

/-- Non-vacuity: a two-statement scalar function that ends in `trap` has the scalar `Domain`,
and `Stock.lower` succeeds on it. -/
theorem domain_of_maskTrap_witness : ∃ (f : Clif.Function) (b : Clif.Block) (c : Clif.TrapCode)
    (result : Stock.Result), f.blocks = [b] ∧ b.term = .trap c ∧ Domain f ∧
      Stock.lower f = .ok result := by
  have h := trapDomainChecks_true
  unfold trapDomainChecks at h
  simp only [Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hp,hr⟩,hE⟩,hdom⟩,hs⟩,hw⟩,hin⟩,hdrv⟩,abi⟩,ordinary⟩ := h
  have body : ∀ s ∈ (trapDomainFixture.blocks[0]!).body, maskMixedBodyEligible s = true := by
    intro s hs'
    simp only [trapDomainFixture,List.getElem!_cons_zero,List.mem_cons,List.not_mem_nil,or_false] at hs'
    rcases hs' with rfl | rfl <;> decide
  obtain ⟨result,run⟩ := stock_lower_trap_ok (b := trapDomainFixture.blocks[0]!) rfl rfl body hp hr hE
    hdom hs hw hin hdrv
  have domain := domain_of_maskTrap (lowerScope_of hs) (dominated_of hdom) abi
    (b := trapDomainFixture.blocks[0]!) rfl
    (fun stm member => maskMixedBodyEligible_sound (body stm member)) rfl ordinary
  exact ⟨trapDomainFixture,_,_,result,rfl,rfl,domain,run⟩

end Backend.Stock.Scalar
