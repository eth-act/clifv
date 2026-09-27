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

/-! ## Running a flag producer and its consumer (`cset`, `csel`) -/

section Flags
variable {F : BitVec 64 → Prop} {isem : Sem}

theorem vdefUpd_nil (ops : Array Operand) (ρ : Nat → CV) : vdefUpd ops [] ρ = ρ := by
  simp [vdefUpd, writeV]

theorem ispec_cmp_imm0 (sz : OperandSize) (k : Nat) (a : CV) (w : Arm.ArmState) :
    ispec (.aluRRImm12 .subS sz .xzr (.vreg k .int) ⟨0, false⟩) [a] w =
      some ([], Arm.write_pstate (cmpFlags (opnd sz a) 0) w, .next) := by
  simp [ispec, defOut, cmpFlags, Imm12.value]

theorem setsFlags_cmp_imm0 (sz : OperandSize) (k : Nat) (ρ : Nat → CV) :
    SetsFlags (.aluRRImm12 .subS sz .xzr (.vreg k .int) ⟨0, false⟩) ρ (cmpFlags (opnd sz (ρ k)) 0) :=
  ⟨_, rfl, rfl, fun w => ispec_cmp_imm0 sz k (ρ k) w⟩

theorem ispec_cset (d : Nat) {c : Cond} (hc : c ≠ .al ∧ c ≠ .nv) (w : Arm.ArmState) :
    ispec (.cset (.vreg d .int) c) [] w =
      some ([ofX (if Arm.ConditionHolds c.invert.bits w then 0#64 else 1#64)], w, .next) := by
  simp [ispec, hc.1, hc.2, defOut]

theorem ispec_csel (d a b : Nat) (c : Cond) (x y : CV) (w : Arm.ArmState) :
    ispec (.csel (.vreg d .int) (.vreg a .int) (.vreg b .int) c) [x, y] w =
      some ([ofX (if Arm.ConditionHolds c.bits w then lo64 x else lo64 y)], w, .next) := rfl

/-- The flags a `SetsFlags` instruction produced decide every condition afterwards. -/
theorem Runs.flags (hR : Refines F isem) {m : MInst} {ρ : Nat → CV} {ps : Arm.PState}
    (hm : SetsFlags m ρ ps) (w : Arm.ArmState) :
    Runs F isem [m] ρ w (fun ρ' w' => ρ' = ρ ∧ ∀ c, Arm.ConditionHolds c w' = condOn c ps) := by
  obtain ⟨ops, hops, hdef, hs⟩ := hm
  refine Runs.one hR hops (hs w) (by simp [hdef]) (SameWorldNF.write_pstate F ps w) fun w'' hw => ?_
  refine ⟨vdefUpd_nil _ _, fun c => ?_⟩
  rw [SameWorld.conditionHolds hw, conditionHolds_write_pstate]

theorem Runs.cset (hR : Refines F isem) (d : Nat) {c : Cond} (hc : c ≠ .al ∧ c ≠ .nv)
    (ρ : Nat → CV) (w : Arm.ArmState) :
    Runs F isem [.cset (.vreg d .int) c] ρ w (fun ρ' w' =>
      ρ' = upd ρ d (ofX (if Arm.ConditionHolds c.invert.bits w then 0#64 else 1#64))) :=
  Runs.one hR rfl (ispec_cset d hc w) rfl (SameWorldNF.refl F w) fun _ _ => rfl

theorem Runs.csel (hR : Refines F isem) (d a b : Nat) (c : Cond) (ρ : Nat → CV)
    (w : Arm.ArmState) :
    Runs F isem [.csel (.vreg d .int) (.vreg a .int) (.vreg b .int) c] ρ w (fun ρ' w' =>
      ρ' = upd ρ d (ofX (if Arm.ConditionHolds c.bits w then lo64 (ρ a) else lo64 (ρ b)))) :=
  Runs.one hR rfl (ispec_csel d a b c (ρ a) (ρ b) w) rfl (SameWorldNF.refl F w) fun _ _ => rfl

/-- A flag producer then `cset`: the condition as 0/1. -/
theorem runs_flags_cset (hR : Refines F isem) {m : MInst} {ρ : Nat → CV} {ps : Arm.PState}
    {cond : Cond} {b : Bool} (hm : SetsFlags m ρ ps) (hb : condOn cond.bits ps = b)
    (hc : cond ≠ .al ∧ cond ≠ .nv) (d : Nat) (w : Arm.ArmState) :
    Runs F isem [m, .cset (.vreg d .int) cond] ρ w (fun ρ' _ =>
      ρ' = upd ρ d (ofX (if b then 1#64 else 0#64))) := by
  refine Runs.append (ms1 := [m]) (Runs.flags hR hm w) fun ρ1 w1 ⟨h1, h2⟩ => ?_
  subst h1
  refine (Runs.cset hR d hc ρ1 w1).imp fun ρ' _ _ h => ?_
  rw [h, h2, condOn_invert _ hc, hb]
  cases b <;> rfl

/-- A flag producer then `csel`. -/
theorem runs_flags_csel (hR : Refines F isem) {m : MInst} {ρ : Nat → CV} {ps : Arm.PState}
    {cond : Cond} {b : Bool} (hm : SetsFlags m ρ ps) (hb : condOn cond.bits ps = b)
    (d x y : Nat) (w : Arm.ArmState) :
    Runs F isem [m, .csel (.vreg d .int) (.vreg x .int) (.vreg y .int) cond] ρ w (fun ρ' _ =>
      ρ' = upd ρ d (ofX (if b then lo64 (ρ x) else lo64 (ρ y)))) := by
  refine Runs.append (ms1 := [m]) (Runs.flags hR hm w) fun ρ1 w1 ⟨h1, h2⟩ => ?_
  subst h1
  refine (Runs.csel hR d x y cond ρ1 w1).imp fun ρ' _ _ h => ?_
  rw [h, h2, hb]

end Flags

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
  all_goals done

end Cons

end Backend.Proof
