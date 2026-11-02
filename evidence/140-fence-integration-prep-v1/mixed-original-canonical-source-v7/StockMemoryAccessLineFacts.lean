import FV.E2E.RegLevelTrap
import FV.ArmFault.Step

namespace Backend.Stock.Proof.MemoryFaults
open Backend Backend.Proof E2E
set_option autoImplicit false
set_option Elab.async false

/-- Any actual instruction line carrying a trap code has the same linked trap-table entry. -/
theorem access_trapAt_ins {R : RL} (wellFormed : R.Wf) {s : Arm.ArmState}
    {j : Nat} {inst : Insn} {code : Clif.TrapCode}
    (line : R.L[j]? = some (.ins inst (some code))) (pc : Arm.r .PC s = R.pcOf j)
    (clean : Arm.r .ERR s = .None) : TrapAt R.fb R.base code s := by
  refine ⟨clean,⟨lineOffset R.L j,code⟩,?_,rfl,pc⟩
  exact ((FnAsm.layout_traps wellFormed.layout).2 _).mpr ⟨j,_,line,rfl⟩

/-- The linked program decodes the actual instruction at its proved source line. -/
theorem access_decodeAt_line {R : RL} (wellFormed : R.Wf) {s : Arm.ArmState}
    {j : Nat} {inst : Insn} {code : Option Clif.TrapCode}
    (line : R.L[j]? = some (.ins inst code)) (program : s.program = R.fb.program R.base)
    (pc : Arm.r .PC s = R.pcOf j) :
    ∃ decoded,inst.toArmInst ⟨lineOffset R.fa.lines.toList j,(R.lm[·]?)⟩ = .ok decoded ∧
      Concurrency.ArmFoot.decodeAt s = some decoded := by
  obtain ⟨aligned,word,encoded,located⟩ := FnAsm.layout_word wellFormed.layout wellFormed.lm line rfl
  have fetched : Arm.fetch_inst (Arm.r .PC s) s = some word := by
    rw [Arm.fetch_inst_from_program,program,pc]
    have result := FnBin.program_find (base := R.base)
      (by have := (FnAsm.layout_size wellFormed.layout).1; have := wellFormed.fit; omega) located
    rwa [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero aligned)] at result
  obtain ⟨decoded,actual,correct⟩ := Insn.decode_encode encoded
  exact ⟨decoded,actual,by simp only [Concurrency.ArmFoot.decodeAt,fetched,correct]⟩

end Backend.Stock.Proof.MemoryFaults
