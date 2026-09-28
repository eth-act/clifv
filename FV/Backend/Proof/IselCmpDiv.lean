import FV.Backend.Proof.IselCmpVec
import FV.Backend.Proof.IselTermsImm

/-!
# Family C: division and remainder (`udiv`/`sdiv`/`urem`/`srem`)
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

theorem ctor_trap_divz_iff (ctx : Ctx) (st st' : LState) (v : V) :
    externCtor ctx T.trap_code_division_by_zero [] st = .ok (v, st') ↔
      v = .op (.trapCode .intDivz) ∧ st' = st := by
  have e : externCtor ctx T.trap_code_division_by_zero [] st = .ok (.op (.trapCode .intDivz), st) := rfl
  rw [e]; simp [eq_comm]

theorem ctor_trap_ovf_iff (ctx : Ctx) (st st' : LState) (v : V) :
    externCtor ctx T.trap_code_integer_overflow [] st = .ok (v, st') ↔
      v = .op (.trapCode .intOvf) ∧ st' = st := by
  have e : externCtor ctx T.trap_code_integer_overflow [] st = .ok (.op (.trapCode .intOvf), st) := rfl
  rw [e]; simp [eq_comm]

theorem ctor_cond_br_zero_iff (ctx : Ctx) (st st' : LState) (r s v : V) :
    externCtor ctx T.cond_br_zero [r, s] st = .ok (v, st') ↔
      v = .data tyCondBrKind VIdx.CondBrKind.Zero [r, s] ∧ st' = st := by
  have e : externCtor ctx T.cond_br_zero [r, s] st =
    .ok (.data tyCondBrKind VIdx.CondBrKind.Zero [r, s], st) := rfl
  rw [e]; simp [eq_comm]

theorem ofV_trapIf_zero (r : Reg) {i : Nat} {sz : OperandSize} (hi : OperandSize.ofIdx? i = some sz)
    (c : Clif.TrapCode) :
    MInst.ofV (.data 58 120 [.data tyCondBrKind VIdx.CondBrKind.Zero [.reg r, .data 93 i []],
      .op (.trapCode c)]) = some (.trapIf (.zero r sz) c) := by
  match i, hi with
  | 0, hi => cases hi; rfl
  | 1, hi => cases hi; rfl

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 4000000 in
include hp hc in
/-- **`trap_if_zero_divisor`** (rule 3838): `trapIf (zero r sz) int_divz`, returns `r`. -/
theorem trap_if_zero_divisor_ok {n : Nat} (hn : 40 ≤ n) {r : Reg} {i : Nat} {sz : OperandSize}
    (hi : OperandSize.ofIdx? i = some sz) {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 559 [.reg r, .data 93 i []] s v s') :
    v = .reg r ∧ s'.1 = s.1.emit (.trapIf (.zero r sz) .intDivz) := by
  isel_split' hp hc h 559
  all_goals isel_inv' hp [ctor_trap_divz_iff, ctor_cond_br_zero_iff] at hm he
  obtain ⟨h1⟩ : Nonempty (MInst.ofV _ = some _) := ⟨‹_›⟩
  rw [ofV_trapIf_zero r hi] at h1
  cases h1
  first | exact ⟨rfl, rfl⟩ | rfl

end

end Backend.Proof
