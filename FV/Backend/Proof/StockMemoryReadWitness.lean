import FV.Backend.Proof.StockMemoryReadTransport
import FV.Backend.Proof.StockMemoryLoadWitness
import FV.Backend.Proof.RefinesCSem

namespace Backend.Stock.Memory.LoadFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

private def otherWorld : Arm.ArmState := Arm.write_base_gpr 10#5 17 world
private theorem other_memory : relation.holds function frame.slots heap otherWorld := by
  refine ⟨⟨?_,memory_world.1.valid,rfl⟩,?_,E2E.outRel_zero _ _ _⟩
  · intro a b valid byte; exact memory_world.1.bytes a b valid byte
  · intro id b present; cases present

/-- Two distinct specification worlds with the same live source heap produce
one exact canonical machine load output. Masked physical state differs. -/
theorem paired_load_read_witness (X : ExtSem) :
    Arm.r (.GPR 10#5) otherWorld ≠ Arm.r (.GPR 10#5) world ∧
      ∃ out t t',csem relation.F ⟨0,0⟩ X
          (.load .uload32 (.vreg 194 .int) (.unsignedOffset (.vreg 192 .int) 0) flags)
          [ofX 4096] world = some ([out],t,.next) ∧
        csem relation.F ⟨0,0⟩ X
          (.load .uload32 (.vreg 194 .int) (.unsignedOffset (.vreg 192 .int) 0) flags)
          [ofX 4096] otherWorld = some ([out],t',.next) ∧
        SameWorld relation.F t world ∧ SameWorld relation.F t' otherWorld := by
  refine ⟨by decide +kernel,?_⟩
  apply load_source_result_pair
    (memRefines_csem relation.F ⟨0,0⟩ X (syms := fun _ => none) rfl (fun _ _ h => by cases h))
    (E2E.memRelOk_holds relation function) memory_world other_memory (fr := frame)
    (op := .load) (ty := .i32) (p := 0) (off := 0) (cm' := heap)
    (vals := [⟨.i32,2779096485⟩]) (by decide) rfl (by decide)
  · intro pv pointer
    have same : pv = ⟨.i64,4096⟩ := Option.some.inj pointer.symm
    subst pv
    rfl
  · intro pv pointer
    have same : pv = ⟨.i64,4096⟩ := Option.some.inj pointer.symm
    subst pv
    rfl
  · exact source_load

end Backend.Stock.Memory.LoadFixture
