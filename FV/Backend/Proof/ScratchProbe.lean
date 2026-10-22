import FV.Backend.Proof.IselFloatBitcast

/-! Scratch probe (temporary, deleted before merge). -/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 4000000 in
include hp hc in
/-- Probe A: raw simp on the matchRule hypothesis. -/
theorem probeA {n : Nat} (hn : 40 ≤ n) {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 95 307 [V.ty CTy.invalid] s v s') : False := by
  isel_split hp hc h 307
  all_goals isel_inv [*, rule_inst_1623, rule_inst_1624, rule_inst_1625, rule_inst_1626,
    rule_inst_1627, rule_inst_1629, rule_inst_1630, rule_inst_1631] at hm he
  all_goals (exfalso; simp only [Backend.Proof.sem_eq] at *; simp only [V.beq] at *; simp)

include hp hc in
/-- Probe B: full isel_inv_simp with beq. -/
theorem probeB {n : Nat} (hn : 40 ≤ n) {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 95 307 [V.ty CTy.invalid] s v s') : False := by
  isel_split hp hc h 307
  all_goals
    (isel_inv_simp [*, rule_inst_1623, rule_inst_1624, rule_inst_1625, rule_inst_1626,
      rule_inst_1627, rule_inst_1629, rule_inst_1630, rule_inst_1631] at hm he
     simp only [V.beq, beq_iff_eq, reduceCtorEq, CTy.int.injEq, CTy.float.injEq] at hm he
     simp at hm he)

end

end Backend.Proof
