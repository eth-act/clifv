import FV.Backend.Proof.KillTab
import FV.Backend.Proof.KillOfV
import FV.Backend.Proof.IselShpBrTable

/-!
# Killed vregs of the ISLE lowering (V4, `SpillKillFree`): the oracle terms

The three terms that build data with killed defs (`killOracles`) are black boxes of the uniform
invariant (`KP`/`IsK`/`RsK`); each meets the oracle obligation `OracleK` at every fuel:

* `atomic_rmw_loop` (612): three fresh int vregs, one `emit` of the `AtomicRMWLoop` on the
  argument registers, killing the last two temporaries (`unstored_rmw`); the first returned;
* `atomic_cas_loop` (613): the same with two temporaries, the second killed (`unstored_cas`);
* `br_table_impl` (670): the bound check (`cmp_imm`, or `cmp` after `imm`, the only sub-run left
  as a hypothesis) and the `JTSequence` on two fresh temporaries, both killed; it returns no
  registers.

The helper terms (`cmp`, `cmp_imm`, `jt_sequence`, `with_flags_side_effect`, `emit_side_effect`)
are inverted at any fuel (`*_any`). Uses and kills of an instruction come from its operands by
register kind (`operands_kinds`, `KillOfV`).
-/

set_option maxRecDepth 20000

namespace Backend.Proof.Kill

open Backend Backend.Proof Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64

/-- **The oracle obligation** of term `t`: at every fuel, a run on values of the invariant from a
state of the invariant keeps it, is related by `RsK`, and returns a value of the invariant. -/
def OracleK (ctx : Ctx) (lo : Nat) (s0 : LState) (t : TermId) : Prop :=
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (n : Nat) (ty : TypeId) (vs : List V) (s : LState) (tr : Array RuleId) (r : Option V)
    (s' : LState) (tr' : Array RuleId),
    (∀ w ∈ vs, KP ctx lo s0 s w) → IsK ctx lo s0 s →
    (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    IsK ctx lo s0 s' ∧ RsK s s' ∧ ∀ w, r = some w → KP ctx lo s0 s' w

namespace Oracle

/-! ## The invariant through emitted code -/

theorem emittedSince_of {s0 s : LState} {ms : List MInst} (h : s.emitted = s0.emitted ++ ms.toArray) :
    emittedSince s0 s = ms := by
  simp [emittedSince, h]

theorem killedL_append (a b : List MInst) : killedL (a ++ b) = killedL a ++ killedL b :=
  List.flatMap_append

theorem mem_killedL {k : Nat} {ms : List MInst} : k ∈ killedL ms ↔ ∃ m ∈ ms, k ∈ unstored m :=
  List.mem_flatMap

section
variable {ctx : Ctx} {lo : Nat} {s0 : LState}

theorem isK_since {s : LState} (h : IsK ctx lo s0 s) :
    s.emitted = s0.emitted ++ (emittedSince s0 s).toArray := by
  obtain ⟨⟨ms, hms⟩, -⟩ := h
  rw [emittedSince_of hms, hms]

theorem vok_lt {s : LState} (hIs : IsK ctx lo s0 s) {K : List Nat} {u : Nat}
    (h : VOk ctx.valDef.size lo s.nextVreg K u) : u < s.nextVreg := by
  obtain ⟨-, hnV, hlo, -⟩ := hIs
  rcases h.1 with h | h <;> omega

theorem vok_lift {s : LState} (hIs : IsK ctx lo s0 s) {hi : Nat} (hv : s.nextVreg ≤ hi)
    {K K' : List Nat} (hK' : ∀ k ∈ K', s.nextVreg ≤ k) {u : Nat}
    (h : VOk ctx.valDef.size lo s.nextVreg K u) : VOk ctx.valDef.size lo hi (K ++ K') u := by
  have hu := vok_lt hIs h
  refine ⟨?_, ?_⟩
  · rcases h.1 with h1 | h1
    · exact .inl h1
    · exact .inr ⟨h1.1, by omega⟩
  · intro hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.2 hm
    · have := hK' u hm; omega

/-- **Code extending the invariant**: new code `ms` whose kills are fresh and whose uses are allowed
at the start. -/
theorem isK_ext {s s' : LState} {ms : List MInst} (hIs : IsK ctx lo s0 s)
    (hv : s.nextVreg ≤ s'.nextVreg) (he : s'.emitted = s.emitted ++ ms.toArray)
    (hkill : ∀ k ∈ killedL ms, s.nextVreg ≤ k ∧ k < s'.nextVreg)
    (huse : ∀ m ∈ ms, ∀ u ∈ useVregs m,
      VOk ctx.valDef.size lo s.nextVreg (killedL (emittedSince s0 s)) u)
    (hnt : ∀ m ∈ ms, ∀ c ti, m ≠ .tryCall c ti) (hcall : ∀ m ∈ ms, ∀ c, m ≠ .call c) :
    IsK ctx lo s0 s' ∧ RsK s s' := by
  have hsince := isK_since hIs
  obtain ⟨-, hnV, hlo, hall⟩ := hIs
  have hIs : IsK ctx lo s0 s := ⟨⟨_, hsince⟩, hnV, hlo, hall⟩
  have he' : s'.emitted = s0.emitted ++ (emittedSince s0 s ++ ms).toArray := by
    rw [he, hsince]; simp
  have hes := emittedSince_of he'
  have hK' : ∀ k ∈ killedL ms, s.nextVreg ≤ k := fun k hk => (hkill k hk).1
  refine ⟨⟨⟨_, he'⟩, hnV, by omega, ?_⟩, ⟨hv, ms, he, hkill⟩⟩
  rw [hes, killedL_append]
  intro m hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨h1, h2, h3, h4⟩ := hall m hm
    exact ⟨h1, fun k hk => ⟨(h2 k hk).1, by have := (h2 k hk).2; omega⟩,
      fun u hu => vok_lift hIs hv hK' (h3 u hu), h4⟩
  · refine ⟨hnt m hm, fun k hk => ?_, fun u hu => vok_lift hIs hv hK' (huse m hm u hu),
      fun _ c hc => absurd hc (hcall m hm c)⟩
    have := hkill k (mem_killedL.mpr ⟨m, hm, hk⟩)
    exact ⟨by omega, this.2⟩

theorem rsK_trans {s s1 s2 : LState} (h1 : RsK s s1) (h2 : RsK s1 s2) : RsK s s2 := by
  obtain ⟨hv1, ms1, he1, hk1⟩ := h1
  obtain ⟨hv2, ms2, he2, hk2⟩ := h2
  refine ⟨by omega, ms1 ++ ms2, by rw [he2, he1]; simp, ?_⟩
  intro k hk
  rw [killedL_append] at hk
  rcases List.mem_append.mp hk with hk | hk
  · have := hk1 k hk; omega
  · have := hk2 k hk; omega

/-- **Values stay in the invariant** along a run. -/
theorem kp_mono {s s' : LState} (hIs : IsK ctx lo s0 s) (hR : RsK s s') {w : V}
    (h : KP ctx lo s0 s w) : KP ctx lo s0 s' w := by
  obtain ⟨hv, ms, he, hk⟩ := hR
  have hsince := isK_since hIs
  have he' : s'.emitted = s0.emitted ++ (emittedSince s0 s ++ ms).toArray := by
    rw [he, hsince]; simp
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun n c hn => ?_, h3⟩
  rw [emittedSince_of he', killedL_append]
  exact vok_lift hIs hv (fun k hk' => (hk k hk').1) (h2 n c hn)

end

/-! ## Uses and kills of an instruction by register kind -/

theorem use_regsK {m : MInst} {u : Nat} (h : u ∈ useVregs m) : ∃ c, Reg.vreg u c ∈ useRegsK m := by
  unfold useVregs at h
  split at h
  · simp at h
  · rename_i ops hops
    simp only [List.mem_map, List.mem_filter, beq_iff_eq] at h
    obtain ⟨o, ⟨ho, hk⟩, rfl⟩ := h
    exact ⟨o.cls, ((operands_kinds hops) o ho).1 hk⟩

theorem unstored_regsK {m : MInst} {k : Nat} (h : k ∈ unstored m) :
    ∃ c, Reg.vreg k c ∈ defRegsK m := by
  unfold unstored at h
  split at h
  · simp at h
  · rename_i ops hops
    simp only [List.mem_filter, List.mem_map, beq_iff_eq] at h
    obtain ⟨⟨o, ⟨ho, hk⟩, rfl⟩, -⟩ := h
    exact ⟨o.cls, ((operands_kinds hops) o ho).2 hk⟩

theorem st_run_throw {α : Type} (e : String) (s : Array Operand) :
    (throw e : StateT (Array Operand) (Except String) α).run s = .error e := rfl

theorem unstored_rmw (t : CTy) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) (p x : Reg) (d d1 d2 : Nat) :
    ∀ k ∈ unstored (.atomicRmwLoop t op fl p x (.vreg d .int) (.vreg d1 .int) (.vreg d2 .int)),
      k = d1 ∨ k = d2 := by
  cases hp : p.allocatable <;> cases hx : x.allocatable <;> cases p <;> cases x <;>
    simp_all [unstored, MInst.operands, MInst.visitOperands, storedDefs, MInst.keptDefs,
      MInst.isTerminator, OpSpec.fixedUse, OpSpec.fixedDef, MInst.isBranch, MInst.isRet,
      st_run_throw]

set_option maxHeartbeats 4000000 in
theorem unstored_cas (t : CTy) (fl : Clif.MemFlags) (p e x : Reg) (d d1 : Nat) :
    ∀ k ∈ unstored (.atomicCasLoop t fl p e x (.vreg d .int) (.vreg d1 .int)), k = d1 := by
  cases hp : p.allocatable <;> cases he : e.allocatable <;> cases hx : x.allocatable <;>
    cases p <;> cases e <;> cases x <;>
    simp_all [unstored, MInst.operands, MInst.visitOperands, storedDefs, MInst.keptDefs,
      MInst.isTerminator, OpSpec.fixedUse, OpSpec.fixedDef, MInst.isBranch, MInst.isRet,
      st_run_throw]

/-! ## The emitted instructions -/

theorem ofV_cmpImm_inv {a b : V} {m : MInst}
    (h : MInst.ofV (.data 58 4 [.data 59 10 [], .data 93 0 [], .reg .xzr, a, b]) = some m) :
    ∃ rn imm, a = .reg rn ∧ m = .aluRRImm12 .subS .size32 .xzr rn imm := by
  have e : MInst.ofV (.data 58 4 [.data 59 10 [], .data 93 0 [], .reg .xzr, a, b]) =
      (do let rn ← a.reg?; let imm ← b.imm12?; return .aluRRImm12 .subS .size32 .xzr rn imm) := rfl
  rw [e] at h
  cases ha : a.reg? <;> cases hb : b.imm12? <;> simp [ha, hb] at h
  exact ⟨_, _, reg?_eq ha, h.symm⟩

theorem ofV_cmpRR_inv {a b : V} {m : MInst}
    (h : MInst.ofV (.data 58 2 [.data 59 10 [], .data 93 0 [], .reg .xzr, a, b]) = some m) :
    ∃ rn rm, a = .reg rn ∧ b = .reg rm ∧ m = .aluRRR .subS .size32 .xzr rn rm := by
  have e : MInst.ofV (.data 58 2 [.data 59 10 [], .data 93 0 [], .reg .xzr, a, b]) =
      (do let rn ← a.reg?; let rm ← b.reg?; return .aluRRR .subS .size32 .xzr rn rm) := rfl
  rw [e] at h
  cases ha : a.reg? <;> cases hb : b.reg? <;> simp [ha, hb] at h
  exact ⟨_, _, reg?_eq ha, reg?_eq hb, h.symm⟩

theorem ofV_jt_inv {d ts r : V} {t1 t2 : Reg} {m : MInst}
    (h : MInst.ofV (.data 58 128 [d, ts, r, .reg t1, .reg t2]) = some m) :
    ∃ dl tl rr, r = .reg rr ∧ m = .jtSequence dl tl rr t1 t2 := by
  have e : MInst.ofV (.data 58 128 [d, ts, r, .reg t1, .reg t2]) =
      (do let dl ← d.label?; let tl ← ts.labels?; let rr ← r.reg?
          return .jtSequence dl tl rr t1 t2) := rfl
  rw [e] at h
  cases hd : d.label? <;> cases ht : ts.labels? <;> cases hr : r.reg? <;> simp [hd, ht, hr] at h
  exact ⟨_, _, _, reg?_eq hr, h.symm⟩

/-! ## The helper terms of `br_table_impl`, at any fuel -/

section
variable {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
include hc

theorem cmp_imm_any {n : Nat} {a b c : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal program (sem ctx) cfg n 47 391 [a, b, c] s v s') :
    s'.1 = s.1 ∧ v = .data 47 1 [.data 58 4 [.data 59 10 [], a, .reg .xzr, b, c]] := by
  obtain ⟨s, tr⟩ := s
  obtain ⟨s', tr'⟩ := s'
  obtain ⟨rl, hrl, env, tr0, hma, he⟩ := internal_rule hc program_term_391 term_391_kind rfl
    (by rw [program_rulesOf_391]; simp [rule_inst_2774]) h
  rw [program_rulesOf_391, List.mem_singleton] at hrl
  subst hrl
  oracle_inv [rule_inst_2774, program_term_1791, program_term_1822, program_term_1972,
    program_term_356] at hma he

theorem cmp_any {n : Nat} {a b c : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal program (sem ctx) cfg n 47 390 [a, b, c] s v s') :
    s'.1 = s.1 ∧ v = .data 47 1 [.data 58 2 [.data 59 10 [], a, .reg .xzr, b, c]] := by
  obtain ⟨s, tr⟩ := s
  obtain ⟨s', tr'⟩ := s'
  obtain ⟨rl, hrl, env, tr0, hma, he⟩ := internal_rule hc program_term_390 term_390_kind rfl
    (by rw [program_rulesOf_390]; simp [rule_inst_2767]) h
  rw [program_rulesOf_390, List.mem_singleton] at hrl
  subst hrl
  oracle_inv [rule_inst_2767, program_term_1791, program_term_1820, program_term_1972,
    program_term_356] at hma he

theorem jt_sequence_any {n : Nat} {r d ts : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal program (sem ctx) cfg n 49 662 [r, d, ts] s v s') :
    s'.1 = ((s.1.fresh .int).2.fresh .int).2 ∧
      v = .data 49 0 [.data 58 128 [d, ts, r, .reg (s.1.fresh .int).1,
        .reg ((s.1.fresh .int).2.fresh .int).1]] := by
  obtain ⟨s, tr⟩ := s
  obtain ⟨s', tr'⟩ := s'
  obtain ⟨rl, hrl, env, tr0, hma, he⟩ := internal_rule hc program_term_662 term_662_kind rfl
    (by rw [program_rulesOf_662]; simp [rule_inst_5394]) h
  rw [program_rulesOf_662, List.mem_singleton] at hrl
  subst hrl
  oracle_inv [rule_inst_5394, program_term_1799, program_term_1946] at hma he

set_option maxHeartbeats 4000000 in
theorem with_flags_side_effect_any {n : Nat} {mi ci : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal program (sem ctx) cfg n 46 256 [.data 47 1 [mi], .data 49 0 [ci]] s v s') :
    s'.1 = s.1 ∧ v = .data 46 1 [mi, ci] := by
  obtain ⟨s, tr⟩ := s
  obtain ⟨s', tr'⟩ := s'
  obtain ⟨rl, hrl, env, tr0, hma, he⟩ := internal_rule hc program_term_256 term_256_kind rfl
    (by rw [program_rulesOf_256]; simp [rule_prelude_lower_1000, rule_prelude_lower_1006,
      rule_prelude_lower_1016, rule_prelude_lower_1023, rule_prelude_lower_1030,
      rule_prelude_lower_1035, rule_prelude_lower_1040, rule_prelude_lower_1045,
      rule_prelude_lower_1050]) h
  rw [program_rulesOf_256] at hrl
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hrl
  rcases hrl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  oracle_inv [rule_prelude_lower_1000, rule_prelude_lower_1006,
      rule_prelude_lower_1016, rule_prelude_lower_1023, rule_prelude_lower_1030,
      rule_prelude_lower_1035, rule_prelude_lower_1040, rule_prelude_lower_1045,
      rule_prelude_lower_1050, program_term_1795, program_term_1796, program_term_1790,
      program_term_1791, program_term_1792, program_term_1799, program_term_1800,
      program_term_1787, program_term_1788, program_term_1789] at hma he

set_option maxHeartbeats 4000000 in
theorem emit_side_effect_any {n : Nat} {i j : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal program (sem ctx) cfg n 13 242 [.data 46 1 [i, j]] s v s') :
    ∃ m1 m2, MInst.ofV i = some m1 ∧ MInst.ofV j = some m2 ∧ s'.1 = (s.1.emit m1).emit m2 ∧
      v = .op .unit := by
  obtain ⟨s, tr⟩ := s
  obtain ⟨s', tr'⟩ := s'
  obtain ⟨rl, hrl, env, tr0, hma, he⟩ := internal_rule hc program_term_242 term_242_kind rfl
    (by rw [program_rulesOf_242]; simp [rule_prelude_lower_522, rule_prelude_lower_524,
      rule_prelude_lower_527]) h
  rw [program_rulesOf_242] at hrl
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hrl
  rcases hrl with rfl | rfl | rfl <;>
  oracle_inv [rule_prelude_lower_522, rule_prelude_lower_524, rule_prelude_lower_527,
      program_term_1787, program_term_1788, program_term_1789] at hma he
  exact ⟨_, ‹_›, _, ‹_›, rfl⟩

end

/-! ## The oracles -/

section
variable {ctx : Ctx} {lo : Nat} {s0 : LState}

theorem kp_reg {s : LState} {r : Reg} (h : KP ctx lo s0 s (.reg r)) {u : Nat} {c : RegClass}
    (hr : Reg.vreg u c = r) :
    VOk ctx.valDef.size lo s.nextVreg (killedL (emittedSince s0 s)) u :=
  h.2.1 u c (by simp [V.regsK, hr])

theorem kp_noRegs {s : LState} {w : V} (hk : w.kIn = false) (hr : w.regsK = []) (hd : w.regsD = []) :
    KP ctx lo s0 s w := by
  refine ⟨hk, fun n c h => ?_, fun _ n c h => ?_⟩
  · rw [hr] at h; cases h
  · rw [hd] at h; cases h

/-- **One emitted control form after fresh vregs**: the invariant holds after it, and the first
fresh vreg (not killed) is a value of the invariant. -/
theorem fin_fresh {s s1 : LState} {m : MInst} {c : RegClass} (hIs : IsK ctx lo s0 s)
    (he : s1.emitted = s.emitted) (hv : s.nextVreg < s1.nextVreg)
    (hkill : ∀ k ∈ unstored m, s.nextVreg < k ∧ k < s1.nextVreg)
    (huse : ∀ u ∈ useVregs m, VOk ctx.valDef.size lo s.nextVreg (killedL (emittedSince s0 s)) u)
    (hnt : ∀ c ti, m ≠ .tryCall c ti) (hcall : ∀ c, m ≠ .call c) :
    IsK ctx lo s0 (s1.emit m) ∧ RsK s (s1.emit m) ∧
      ∀ w, V.reg (.vreg s.nextVreg c) = w → KP ctx lo s0 (s1.emit m) w := by
  have he' : (s1.emit m).emitted = s.emitted ++ [m].toArray := by simp [LState.emit, he]
  have hkill' : ∀ k ∈ killedL [m], s.nextVreg ≤ k ∧ k < (s1.emit m).nextVreg := by
    intro k hk
    simp only [killedL, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hk
    have := hkill k hk
    simp only [LState.emit]
    omega
  obtain ⟨hI, hR⟩ := isK_ext hIs (by simp only [LState.emit]; omega) he' hkill'
    (by simpa using huse) (by simpa using hnt) (by simpa using hcall)
  refine ⟨hI, hR, ?_⟩
  rintro w rfl
  have hsince := isK_since hIs
  have hes : emittedSince s0 (s1.emit m) = emittedSince s0 s ++ [m] :=
    emittedSince_of (by rw [he', hsince]; simp)
  obtain ⟨-, hnV, hlo, hall⟩ := hIs
  refine ⟨rfl, fun n c' hn => ?_, fun _ n c' hn => by simp [V.regsD] at hn⟩
  simp only [V.regsK, List.mem_singleton, Reg.vreg.injEq] at hn
  obtain ⟨rfl, -⟩ := hn
  refine ⟨.inr ⟨hlo, by simp only [LState.emit]; omega⟩, ?_⟩
  rw [hes, killedL_append]
  intro hk
  rcases List.mem_append.mp hk with hk | hk
  · obtain ⟨m', hm', hk'⟩ := mem_killedL.mp hk
    have := ((hall m' hm').2.1 _ hk').2
    omega
  · have := hkill _ (by simpa [killedL] using hk)
    omega

/-- The tail of `br_table_impl`: two fresh temporaries, the bound check `m1` (no kills), the
`JTSequence` on `rn` killing the temporaries. -/
theorem jt_tail {s1 s' : LState} {m1 : MInst} {dl : Label} {tl : List Label} {rn : Reg}
    (hIs : IsK ctx lo s0 s1)
    (hs : s' = ((((s1.fresh .int).2.fresh .int).2.emit m1).emit
      (.jtSequence dl tl rn (s1.fresh .int).1 ((s1.fresh .int).2.fresh .int).1)))
    (hm1 : unstored m1 = [])
    (hu1 : ∀ u ∈ useVregs m1, VOk ctx.valDef.size lo s1.nextVreg (killedL (emittedSince s0 s1)) u)
    (hrn : KP ctx lo s0 s1 (.reg rn)) (hnt1 : ∀ c ti, m1 ≠ .tryCall c ti)
    (hc1 : ∀ c, m1 ≠ .call c) :
    IsK ctx lo s0 s' ∧ RsK s1 s' := by
  subst hs
  refine isK_ext (ms := [m1, .jtSequence dl tl rn (s1.fresh .int).1 ((s1.fresh .int).2.fresh .int).1])
    hIs (by simp only [LState.emit, LState.fresh]; omega)
    (by apply Array.toList_inj.mp; simp [LState.emit, LState.fresh]) ?_ ?_
    (by simpa using hnt1) (by simpa using hc1)
  · intro k hk
    simp only [killedL, List.flatMap_cons, List.flatMap_nil, List.append_nil, hm1,
      List.nil_append] at hk
    obtain ⟨c, hc⟩ := unstored_regsK hk
    simp [defRegsK, MInst.defs, pairDefs, LState.fresh] at hc
    simp only [LState.emit, LState.fresh]
    omega
  · intro m hm u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl
    · exact hu1 u hu
    · obtain ⟨c, hc⟩ := use_regsK hu
      simp only [useRegsK, MInst.uses, pairUses, List.append_nil, List.mem_singleton] at hc
      exact kp_reg hrn hc

end

end Oracle

open Oracle

section
variable {ctx : Ctx} {lo : Nat} {s0 : LState}

set_option maxHeartbeats 1000000 in
/-- **`atomic_rmw_loop`** (term 612): three fresh int vregs, the `AtomicRMWLoop` on the argument
registers killing the last two, the first returned. -/
theorem oracle_rmw (htot : Cov.Totality) : OracleK ctx lo s0 TId.atomic_rmw_loop := by
  intro cfg hc n ty vs s tr r s' tr' hvs hIs h
  obtain ⟨v, m, env, tr0, rfl, hma, he⟩ := Cov.single_rule_run htot hc program_term_612
    term_612_kind rfl (by rfl) program_rulesOf_612 rfl h
  clear h
  oracle_inv [rule_inst_4518, program_term_1855] at hma he
  obtain ⟨t, op, fl, p, x, rfl, rfl, rfl⟩ := Cov.ofV_rmw_inv ‹MInst.ofV _ = some _›
  have hp := hvs (.reg p) (by simp)
  have hx := hvs (.reg x) (by simp)
  refine fin_fresh hIs rfl (by simp only [LState.fresh]; omega) ?_ ?_ (by simp) (by simp)
  · intro k hk
    rcases unstored_rmw t op fl p x s.nextVreg (s.nextVreg + 1) (s.nextVreg + 2) k hk with
      rfl | rfl <;> simp [LState.fresh]
  · intro u hu
    obtain ⟨c, hc⟩ := use_regsK hu
    simp only [useRegsK, MInst.uses, pairUses, List.append_nil, List.mem_cons, List.mem_nil_iff,
      or_false] at hc
    rcases hc with hc | hc
    · exact kp_reg hp hc
    · exact kp_reg hx hc

set_option maxHeartbeats 1000000 in
/-- **`atomic_cas_loop`** (term 613): two fresh int vregs, the `AtomicCASLoop` on the argument
registers killing the second, the first returned. -/
theorem oracle_cas (htot : Cov.Totality) : OracleK ctx lo s0 TId.atomic_cas_loop := by
  intro cfg hc n ty vs s tr r s' tr' hvs hIs h
  obtain ⟨v, m, env, tr0, rfl, hma, he⟩ := Cov.single_rule_run htot hc program_term_613
    term_613_kind rfl (by rfl) program_rulesOf_613 rfl h
  clear h
  oracle_inv [rule_inst_4532, program_term_1856] at hma he
  obtain ⟨t, fl, p, e, x, rfl, rfl, rfl, rfl⟩ := Cov.ofV_cas_inv ‹MInst.ofV _ = some _›
  have hp := hvs (.reg p) (by simp)
  have he := hvs (.reg e) (by simp)
  have hx := hvs (.reg x) (by simp)
  refine fin_fresh hIs rfl (by simp only [LState.fresh]; omega) ?_ ?_ (by simp) (by simp)
  · intro k hk
    rcases unstored_cas t fl p e x s.nextVreg (s.nextVreg + 1) k hk with rfl
    simp [LState.fresh]
  · intro u hu
    obtain ⟨c, hc⟩ := use_regsK hu
    simp only [useRegsK, MInst.uses, pairUses, List.append_nil, List.mem_cons, List.mem_nil_iff,
      or_false] at hc
    rcases hc with hc | hc | hc
    · exact kp_reg hp hc
    · exact kp_reg he hc
    · exact kp_reg hx hc

set_option maxHeartbeats 4000000 in
/-- **`br_table_impl`** (term 670): the bound check (`cmp_imm`, or `cmp` after `imm`) and the
`JTSequence` on two fresh temporaries (killed); returns no registers. -/
theorem oracle_brTable (htot : Cov.Totality) (himm : OracleK ctx lo s0 TId.imm) :
    OracleK ctx lo s0 TId.br_table_impl := by
  intro cfg hc n ty vs s tr r s' tr' hvs hIs h
  have hs := htot.2 ctx cfg n ty _ vs (s, tr) r (s', tr') (by rfl) h
  obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp hs
  rcases n with _ | n
  · rw [applyTerm.eq_1] at h; cases h
  obtain ⟨rl, hrl, env, tr0, hma, he⟩ := internal_rule hc program_term_670 term_670_kind rfl
    (by rw [program_rulesOf_670]; simp [rule_inst_5450, rule_inst_5454]) h
  clear h
  rw [program_rulesOf_670] at hrl
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hrl
  rcases hrl with rfl | rfl
  · oracle_inv [rule_inst_5450, program_term_325, program_term_242, program_term_256,
      program_term_391, program_term_2028, program_term_662] at hma he
    obtain ⟨hs1, rfl⟩ := cmp_imm_any hc ‹ApplyInternal _ _ _ _ 47 391 _ _ _ _›
    obtain ⟨hs2, rfl⟩ := jt_sequence_any hc ‹ApplyInternal _ _ _ _ 49 662 _ _ _ _›
    obtain ⟨hs3, rfl⟩ := with_flags_side_effect_any hc ‹ApplyInternal _ _ _ _ 46 256 _ _ _ _›
    obtain ⟨m1, m2, hm1, hm2, hs4, rfl⟩ := emit_side_effect_any hc ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨rn, imm, rfl, rfl⟩ := ofV_cmpImm_inv hm1
    obtain ⟨dl, tl, rr, hrr, rfl⟩ := ofV_jt_inv hm2
    cases hrr
    have hrn := hvs (.reg rn) (by simp)
    simp only at hs1 hs2 hs3 hs4
    rw [hs3, hs2, hs1] at hs4
    obtain ⟨hI, hR⟩ := jt_tail hIs hs4 (unstored_nil trivial) (fun u hu => by
      obtain ⟨c, hc⟩ := use_regsK hu
      simp only [useRegsK, MInst.uses, pairUses, List.append_nil, List.mem_singleton] at hc
      exact kp_reg hrn hc) hrn (by simp) (by simp)
    exact ⟨hI, hR, fun w hw => hw ▸ kp_noRegs rfl rfl rfl⟩
  · oracle_inv [rule_inst_5454, program_term_553, program_term_2235, program_term_242,
      program_term_256, program_term_390, program_term_2028, program_term_662] at hma he
    have hw7 := hvs _ List.mem_cons_self
    have h553 := ‹ApplyInternal _ _ _ _ 27 553 _ _ _ _›
    obtain ⟨hI1, hR1, hw⟩ := himm cfg hc _ _ _ s tr _ _ _ (by
      intro w hw
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact kp_noRegs rfl rfl rfl
      · exact kp_noRegs rfl rfl rfl
      · exact hw7) hIs h553
    have hw5 := hw _ rfl
    obtain ⟨hs1, rfl⟩ := cmp_any hc ‹ApplyInternal _ _ _ _ 47 390 _ _ _ _›
    obtain ⟨hs2, rfl⟩ := jt_sequence_any hc ‹ApplyInternal _ _ _ _ 49 662 _ _ _ _›
    obtain ⟨hs3, rfl⟩ := with_flags_side_effect_any hc ‹ApplyInternal _ _ _ _ 46 256 _ _ _ _›
    obtain ⟨m1, m2, hm1, hm2, hs4, rfl⟩ := emit_side_effect_any hc ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨rn, rm, rfl, rfl, rfl⟩ := ofV_cmpRR_inv hm1
    obtain ⟨dl, tl, rr, hrr, rfl⟩ := ofV_jt_inv hm2
    cases hrr
    have hrn := kp_mono hIs hR1 (hvs (.reg rn) (by simp))
    simp only at hs1 hs2 hs3 hs4
    rw [hs3, hs2, hs1] at hs4
    obtain ⟨hI, hR⟩ := jt_tail hI1 hs4 (unstored_nil trivial) (fun u hu => by
      obtain ⟨c, hc⟩ := use_regsK hu
      simp only [useRegsK, MInst.uses, pairUses, List.append_nil, List.mem_cons,
        List.mem_nil_iff, or_false] at hc
      rcases hc with hc | hc
      · exact kp_reg hrn hc
      · exact kp_reg hw5 hc) hrn (by simp) (by simp)
    exact ⟨hI, rsK_trans hR1 hR, fun w hw => hw ▸ kp_noRegs rfl rfl rfl⟩

/-- **The oracle obligations** of the three oracle terms (given `imm`'s, a term of both term
sets, for `br_table_impl`). -/
theorem oracle_all (htot : Cov.Totality) (himm : OracleK ctx lo s0 TId.imm) :
    ∀ t ∈ killOracles, OracleK ctx lo s0 t := by
  intro t ht
  simp only [killOracles, List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact oracle_rmw htot
  · exact oracle_cas htot
  · exact oracle_brTable htot himm

end

end Backend.Proof.Kill
