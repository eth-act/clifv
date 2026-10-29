module

public import FV.Backend.Proof.StockCmpConditionValues

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- A real immediate-comparison condition call computes the original machine
word predicate through final aliases, preserving every other register. Both
shifted and unshifted valid immediates use the same standard-kernel contract. -/
theorem stock_cmp_predecessor_signed_condition_values {p : Program} (hp : Data p) (ctx : Ctx)
    (sz : OperandSize) {key fuel : Nat} {imm : Imm12}
    (validImm : imm.bits < 4096) (enough : 119 ≤ fuel)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 27 715
      [.data 123 2 [.data 47 1 [.data 58 4 [.data 59 10 [],
        .data 93 (if sz = .size32 then 0 else 1) [],.reg .xzr,.reg (.vreg key .int),.op (.imm12 imm)]],
        .data 96 (condOf .sgt).idx []]] (st,tr) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    {u v : BitVec sz.bits} (notMinimum : v ≠ BitVec.intMin sz.bits)
    (encoded : BitVec.ofNat sz.bits imm.value = v-1) (input : opnd sz (ρ (aliasNum aliases key)) = u) :
    ∃ d,out = .reg (.vreg d .int) ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [.aluRRImm12 .subS sz .xzr (.vreg key .int) imm,.cset (.vreg d .int) (condOf .sgt)] ∧
      ∀ world,Runs F isem ([MInst.aluRRImm12 .subS sz .xzr (.vreg key .int) imm,.cset (.vreg d .int) (condOf .sgt)].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc .sge u v)⟩ (ρ' d) ∧
          ∀ k,k ≠ d → ρ' k = ρ k) := by
  have decoded : MInst.ofV (.data 58 4 [.data 59 10 [],.data 93 (if sz = .size32 then 0 else 1) [],
      .reg .xzr,.reg (.vreg key .int),.op (.imm12 imm)]) = some (.aluRRImm12 .subS sz .xzr (.vreg key .int) imm) := by
    cases sz <;> rfl
  have flags := setsFlags_cmpImm sz key validImm (fun index => ρ (aliasNum aliases index))
  have truth := stock_cmp_signed_predecessor (n := sz.bits) (by cases sz <;> simp [OperandSize.bits]) u v notMinimum
  rw [← encoded] at truth
  conv at truth => lhs; rw [← input]
  exact stock_cmp_flag_condition_values hp ctx rfl enough decoded (condOf_ne_al .sgt) rfl run refines bounded flags truth
end Backend.Stock.Proof.ScalarCmp
