import FV.Backend.Proof.IselCmpExt

/-!
# Conditions (`CondResult`) and their consumers (flags/select family)

A `CondResult` value is what `emit_icmp`/`is_nonzero`/`is_nonzero_cmp` return: a register
tested against zero (`Zero`/`NotZero`, at an operand size), or a flag-setting instruction that
is not emitted yet together with the Arm condition to test (`Cond`). `CondShape c P` is its
structure (the vregs it mentions satisfy `P`), `CondSem ρ c b` its truth `b` in the vreg file
`ρ` (for `Cond`: the instruction sets flags on which the condition is `b`, whatever the
world). `Or`/`And` never arise in E.

Consumers: `with_flags` (producer + consumer instruction), `lower_cond_result_bool`
(`cset`, the condition as 0/1).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Flag-setting instructions and conditions -/

/-- `m` defines no vreg and, run on the use values of `ρ`, sets the flags to `ps` from any
world. -/
def SetsFlags (m : MInst) (ρ : Nat → CV) (ps : Arm.PState) : Prop :=
  ∃ ops, m.operands = .ok ops ∧ (ops.toList.filter Operand.isDef) = [] ∧
    ∀ w, ispec m (vuses ops ρ) w = some ([], Arm.write_pstate ps w, .next)

/-- Structure of a `CondResult` of E, with every vreg it mentions satisfying `P`. -/
def CondShape (c : V) (P : Nat → Prop) : Prop :=
  (∃ k i sz, c = .data 123 0 [.reg (.vreg k .int), .data 93 i []] ∧
      OperandSize.ofIdx? i = some sz ∧ P k) ∨
  (∃ k i sz, c = .data 123 1 [.reg (.vreg k .int), .data 93 i []] ∧
      OperandSize.ofIdx? i = some sz ∧ P k) ∨
  (∃ (mi : V) (m : MInst) (cond : Cond), c = .data 123 2 [.data 47 1 [mi], .data 96 cond.idx []] ∧
      MInst.ofV mi = some m ∧ cond ≠ .al ∧ cond ≠ .nv ∧ vdefs m = [] ∧ ∀ u ∈ vuseNums m, P u)

/-- The truth `b` of a `CondResult` in the vreg file `ρ`. -/
def CondSem (ρ : Nat → CV) (c : V) (b : Bool) : Prop :=
  (∃ k i sz, c = .data 123 0 [.reg (.vreg k .int), .data 93 i []] ∧
      OperandSize.ofIdx? i = some sz ∧ (opnd sz (ρ k) == 0) = b) ∨
  (∃ k i sz, c = .data 123 1 [.reg (.vreg k .int), .data 93 i []] ∧
      OperandSize.ofIdx? i = some sz ∧ (opnd sz (ρ k) != 0) = b) ∨
  (∃ (mi : V) (m : MInst) (cond : Cond) (ps : Arm.PState), c = .data 123 2 [.data 47 1 [mi], .data 96 cond.idx []] ∧
      MInst.ofV mi = some m ∧ SetsFlags m ρ ps ∧ condOn cond.bits ps = b)

theorem CondShape.mono {c : V} {P Q : Nat → Prop} (h : CondShape c P) (hPQ : ∀ k, P k → Q k) :
    CondShape c Q := by
  rcases h with ⟨k, i, sz, h1, h2, h3⟩ | ⟨k, i, sz, h1, h2, h3⟩ | ⟨mi, m, cond, h1, h2, h3, h4, h5, h6⟩
  · exact .inl ⟨k, i, sz, h1, h2, hPQ _ h3⟩
  · exact .inr (.inl ⟨k, i, sz, h1, h2, hPQ _ h3⟩)
  · exact .inr (.inr ⟨mi, m, cond, h1, h2, h3, h4, h5, fun u hu => hPQ _ (h6 u hu)⟩)

/-! ## `with_flags`, `lower_cond_result_bool` -/

section Cons
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 2000000 in
include hp hc in
/-- `with_flags` on a side-effect producer and a register-returning consumer (rule
`with_flags_consumer_reg`; the other 15 rules need other variants): emit both, return the
consumer's register. -/
theorem with_flags_ok {n : Nat} (hn : 40 ≤ n) {mi ci : V} {r : Reg} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 22 254 [.data 47 1 [mi], .data 49 3 [ci, .reg r]] s v s') :
    ∃ m1 m2, MInst.ofV mi = some m1 ∧ MInst.ofV ci = some m2 ∧ v = .regs [r] ∧
      s'.1 = (s.1.emit m1).emit m2 := by
  isel_split' hp hc h 254
  all_goals try (isel_refute hp at hm; done)
  case' inr.inr.inr.inr.inl =>
    isel_inv' hp [] at hm he
    exact ⟨_, ‹_›, _, ‹_›, rfl⟩
  all_goals sorry

end Cons

end Backend.Proof
