import FV.Backend.Proof.IselShpBase
import FV.Backend.Proof.IselShpFns
import FV.Backend.Proof.IselCovModel
import FV.Backend.Proof.IselCtlCall

/-!
# Control shapes of the ISLE lowering (V4): the control-form oracles

`ctlOracle` selects the helpers emitting a control form with fresh defs: `load_ext_name_got`
(term 571), `load_ext_name_near` (572), `atomic_rmw_loop` (612, int-vreg operands),
`atomic_cas_loop` (613, int-vreg operands), `elf_tls_get_addr` (647). Each has one rule: fresh
temporaries (`temp_writable_reg`), one `emit` of the control form, the first temporary returned.
`oracle_ctl`: at every fuel, a run of one of them keeps `ShpIs` and returns an int vreg.

The runs are inverted at an arbitrary fuel with the `*_any` forms of the inverse-evaluation
lemmas (`IselCmpInv`): each exposes the fuel as `m + 1` (fuel `0` throws).
-/

set_option maxRecDepth 20000

/-! ## Inverse evaluation at any fuel -/

namespace Isle.Interp

variable {W σ : Type} {p : Program} {sem : Sem W σ} {cfg : Config}

theorem evalExpr_var_any {n : Nat} {ty : TypeId} {x : VarId} {env : Env W} {v : W}
    {s s' : σ × Array RuleId} :
    (evalExpr p sem cfg n (.var ty x) env).run s = .ok (some v, s') ↔
      ∃ m, n = m + 1 ∧ env[x]? = some (some v) ∧ s' = s := by
  cases n with
  | zero => rw [evalExpr.eq_1]; simp
  | succ m => rw [evalExpr_var_iff]; simp

theorem evalExpr_constPrim_any {n : Nat} {ty : TypeId} {nm : String} {env : Env W} {v : W}
    {s s' : σ × Array RuleId} :
    (evalExpr p sem cfg n (.constPrim ty nm) env).run s = .ok (some v, s') ↔
      ∃ m, n = m + 1 ∧ sem.prim ty nm = some v ∧ s' = s := by
  cases n with
  | zero => rw [evalExpr.eq_1]; simp
  | succ m => rw [evalExpr_constPrim_iff]; simp

theorem evalExpr_let_any {n : Nat} {ty : TypeId} {bs : List (VarId × TypeId × Expr)}
    {body : Expr} {env : Env W} {v : W} {s s' : σ × Array RuleId} :
    (evalExpr p sem cfg n (.let ty bs body) env).run s = .ok (some v, s') ↔
      ∃ m, n = m + 1 ∧ ∃ env' s1, (evalBinds p sem cfg m bs env).run s = .ok (some env', s1) ∧
        (evalExpr p sem cfg m body env').run s1 = .ok (some v, s') := by
  cases n with
  | zero => rw [evalExpr.eq_1]; simp
  | succ m => rw [evalExpr_let_iff]; simp

theorem evalExpr_term_any {n : Nat} {ty : TypeId} {t : TermId} {args : List Expr}
    {env : Env W} {v : W} {s s' : σ × Array RuleId} :
    (evalExpr p sem cfg n (.term ty t args) env).run s = .ok (some v, s') ↔
      ∃ m, n = m + 1 ∧ ∃ vs s1, (evalArgs p sem cfg m args env).run s = .ok (some vs, s1) ∧
        (applyTerm p sem cfg m ty t vs).run s1 = .ok (some v, s') := by
  cases n with
  | zero => rw [evalExpr.eq_1]; simp
  | succ m => rw [evalExpr_term_iff]; simp

theorem evalArgs_nil_any {n : Nat} {env : Env W} {vs : List W} {s s' : σ × Array RuleId} :
    (evalArgs p sem cfg n [] env).run s = .ok (some vs, s') ↔
      ∃ m, n = m + 1 ∧ vs = [] ∧ s' = s := by
  cases n with
  | zero => rw [evalArgs.eq_1]; simp
  | succ m => rw [evalArgs_nil_iff]; simp

theorem evalArgs_cons_any {n : Nat} {e : Expr} {es : List Expr} {env : Env W} {vs : List W}
    {s s' : σ × Array RuleId} :
    (evalArgs p sem cfg n (e :: es) env).run s = .ok (some vs, s') ↔
      ∃ m, n = m + 1 ∧ ∃ v s1 ws, (evalExpr p sem cfg m e env).run s = .ok (some v, s1) ∧
        (evalArgs p sem cfg m es env).run s1 = .ok (some ws, s') ∧ vs = v :: ws := by
  cases n with
  | zero => rw [evalArgs.eq_1]; simp
  | succ m => rw [evalArgs_cons_iff]; simp

theorem evalBinds_nil_any {n : Nat} {env env' : Env W} {s s' : σ × Array RuleId} :
    (evalBinds p sem cfg n [] env).run s = .ok (some env', s') ↔
      ∃ m, n = m + 1 ∧ env' = env ∧ s' = s := by
  cases n with
  | zero => rw [evalBinds.eq_1]; simp
  | succ m => rw [evalBinds_nil_iff]; simp

theorem evalBinds_cons_any {n : Nat} {x : VarId} {ty : TypeId} {e : Expr}
    {bs : List (VarId × TypeId × Expr)} {env env' : Env W} {s s' : σ × Array RuleId} :
    (evalBinds p sem cfg n ((x, ty, e) :: bs) env).run s = .ok (some env', s') ↔
      ∃ m, n = m + 1 ∧ ∃ v s1, (evalExpr p sem cfg m e env).run s = .ok (some v, s1) ∧
        x < env.size ∧ (evalBinds p sem cfg m bs (env.set! x (some v))).run s1 = .ok (some env', s') := by
  cases n with
  | zero => rw [evalBinds.eq_1]; simp
  | succ m => rw [evalBinds_cons_iff]; simp

theorem applyTerm_any {n : Nat} {ty : TypeId} {t : TermId} {vs : List W} {v : W}
    {s s' : σ × Array RuleId} :
    (applyTerm p sem cfg n ty t vs).run s = .ok (some v, s') ↔
      ∃ m, n = m + 1 ∧ ApplySpec p sem cfg m ty t vs s v s' := by
  cases n with
  | zero => rw [applyTerm.eq_1]; simp
  | succ m => rw [applyTerm_iff]; simp

end Isle.Interp

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64

/-! ## The single rule of an oracle term -/

variable {f : Clif.Function} {ctx : Ctx} {cfg : Config}

/-- A run of a non-`partial` internal term with one rule (no if-lets) that does not throw
returns a value: the rule's argument match and right-hand side (at some fuel). -/
theorem single_rule_run (htot : Totality) (hc : cfg.checkOverlap = false) {t : TermId}
    {term : Term} {flags : TermFlags} {ex : Option Extractor} (ht : termOf program t = .ok term)
    (hk : term.kind = .decl flags (some .internal) ex) (hm : flags.isMulti = false)
    (htt : termTotal program t = true) {rl : Rule} (hrs : program.rulesOf t = [rl])
    (hil : rl.iflets = []) {n : Nat} {ty : TypeId} {vs : List V} {s : LState}
    {tr : Array RuleId} {r : Option V} {s' : LState} {tr' : Array RuleId}
    (h : (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    ∃ v m env tr0, r = some v ∧
      matchArgs program (sem ctx) s rl.args vs (Array.replicate rl.vars.length none) =
        .ok (some env) ∧
      (evalExpr program (sem ctx) cfg m rl.rhs env).run (s, tr) = .ok (some v, (s', tr0)) := by
  have hs := htot.2 ctx cfg n ty t vs (s, tr) r (s', tr') htt h
  obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp hs
  rcases n with _ | n
  · rw [applyTerm.eq_1] at h; cases h
  obtain ⟨r1, pre, post, hrs', -, m, env, s1, st, tr0, -, hmatch, he, hs'⟩ :=
    applyTerm_internal_some_first hc ht hk hm h
  rw [hrs] at hrs'
  obtain ⟨rfl, rfl⟩ : pre = [] ∧ r1 = rl := by
    rcases pre with _ | ⟨a, pre⟩
    · simp only [List.nil_append, List.cons.injEq] at hrs'
      exact ⟨rfl, hrs'.1.symm⟩
    · simp at hrs'
  obtain ⟨rfl, hma⟩ := matchRule_noIfLets hil hmatch
  simp only [Prod.mk.injEq] at hs'
  obtain ⟨rfl, -⟩ := hs'
  exact ⟨v, n, env, tr0, rfl, hma, he⟩

/-- Inverse evaluation, at any fuel, of an oracle rule's argument match and right-hand side
(`ts`: the rule and the data facts of the terms it calls). -/
syntax "oracle_inv" "[" Lean.Parser.Tactic.simpLemma,* "]" " at " (ppSpace colGt ident)+ : tactic
macro_rules
  | `(tactic| oracle_inv [$ts,*] at $hs*) => `(tactic| isel_inv_all [Isle.Interp.evalExpr_var_any,
      Isle.Interp.evalExpr_constPrim_any, Isle.Interp.evalExpr_let_any,
      Isle.Interp.evalExpr_term_any, Isle.Interp.evalArgs_nil_any, Isle.Interp.evalArgs_cons_any,
      Isle.Interp.evalBinds_nil_any, Isle.Interp.evalBinds_cons_any, Isle.Interp.applyTerm_any,
      Backend.Proof.program_term_175, Backend.Proof.program_term_235,
      Backend.Proof.program_term_201, Array.getElem?_setIfInBounds, Array.size_setIfInBounds,
      Array.size_replicate, $ts,*] at $hs*)

/-! ## The emitted control forms -/

theorem reg?_reg (r : Reg) : (V.reg r).reg? = some r := rfl

theorem ofV_got_inv {r : Reg} {w : V} {m : MInst}
    (h : MInst.ofV (.data 58 129 [.reg r, w]) = some m) : ∃ nm, m = .loadExtNameGot r nm := by
  have e : MInst.ofV (.data 58 129 [.reg r, w]) =
      (do return MInst.loadExtNameGot (← (V.reg r).reg?) (← w.extName?)) := rfl
  rw [e] at h
  cases hw : w.extName? <;> simp [hw, reg?_reg] at h
  exact ⟨_, h.symm⟩

theorem ofV_near_inv {r : Reg} {w o : V} {m : MInst}
    (h : MInst.ofV (.data 58 130 [.reg r, w, o]) = some m) :
    ∃ nm i, m = .loadExtNameNear r nm i := by
  have e : MInst.ofV (.data 58 130 [.reg r, w, o]) =
      (do return MInst.loadExtNameNear (← (V.reg r).reg?) (← w.extName?) (← o.int?)) := rfl
  rw [e] at h
  cases hw : w.extName? <;> cases ho : o.int? <;> simp [hw, ho, reg?_reg] at h
  exact ⟨_, _, h.symm⟩

theorem ofV_rmw_inv {a0 a1 a2 a3 a4 : V} {d d1 d2 : Reg} {m : MInst}
    (h : MInst.ofV (.data 58 37 [a0, a1, a2, a3, a4, .reg d, .reg d1, .reg d2]) = some m) :
    ∃ t op fl p x, a3 = .reg p ∧ a4 = .reg x ∧ m = .atomicRmwLoop t op fl p x d d1 d2 := by
  have e : MInst.ofV (.data 58 37 [a0, a1, a2, a3, a4, .reg d, .reg d1, .reg d2]) = (do
      let t ← a0.ty?; let op ← a1.atomicRmwLoopOp?; let fl ← a2.memFlags?; let p ← a3.reg?
      let x ← a4.reg?; let r5 ← (V.reg d).reg?; let r6 ← (V.reg d1).reg?
      let r7 ← (V.reg d2).reg?; return MInst.atomicRmwLoop t op fl p x r5 r6 r7) := rfl
  rw [e] at h
  cases h0 : a0.ty? <;> cases h1 : a1.atomicRmwLoopOp? <;> cases h2 : a2.memFlags? <;>
    cases h3 : a3.reg? <;> cases h4 : a4.reg? <;> simp [h0, h1, h2, h3, h4, reg?_reg] at h
  exact ⟨_, _, _, _, _, reg?_eq h3, reg?_eq h4, h.symm⟩

theorem ofV_cas_inv {a0 a1 a2 a3 a4 : V} {d d1 : Reg} {m : MInst}
    (h : MInst.ofV (.data 58 38 [a0, a1, a2, a3, a4, .reg d, .reg d1]) = some m) :
    ∃ t fl p e x, a2 = .reg p ∧ a3 = .reg e ∧ a4 = .reg x ∧ m = .atomicCasLoop t fl p e x d d1 := by
  have e : MInst.ofV (.data 58 38 [a0, a1, a2, a3, a4, .reg d, .reg d1]) = (do
      let t ← a0.ty?; let fl ← a1.memFlags?; let p ← a2.reg?; let e ← a3.reg?
      let x ← a4.reg?; let r5 ← (V.reg d).reg?; let r6 ← (V.reg d1).reg?
      return MInst.atomicCasLoop t fl p e x r5 r6) := rfl
  rw [e] at h
  cases h0 : a0.ty? <;> cases h1 : a1.memFlags? <;> cases h2 : a2.reg? <;>
    cases h3 : a3.reg? <;> cases h4 : a4.reg? <;> simp [h0, h1, h2, h3, h4, reg?_reg] at h
  exact ⟨_, _, _, _, _, reg?_eq h2, reg?_eq h3, reg?_eq h4, h.symm⟩

theorem ofV_tls_inv {w : V} {d t : Reg} {m : MInst}
    (h : MInst.ofV (.data 58 137 [w, .reg d, .reg t]) = some m) :
    ∃ nm, m = .elfTlsGetAddr nm d t := by
  have e : MInst.ofV (.data 58 137 [w, .reg d, .reg t]) =
      (do return MInst.elfTlsGetAddr (← w.extName?) (← (V.reg d).reg?) (← (V.reg t).reg?)) := rfl
  rw [e] at h
  cases hw : w.extName? <;> simp [hw, reg?_reg] at h
  exact ⟨_, h.symm⟩

/-- Emitting a control form of its shape after allocating keeps `ShpIs`; the returned int vreg
is described by `.reg 1`. -/
theorem ctl_fin {N : Nat} {s0 s s1 : LState} {m : MInst} {k : Nat} (hIs : ShpIs N s0 s)
    (he : s1.emitted = s.emitted) (hv : s.nextVreg ≤ s1.nextVreg) (hm : CtlShape N m) :
    ShpIs N s0 (s1.emit m) ∧ ∀ v, V.reg (.vreg k .int) = v → γ f ctx (.reg 1) v := by
  obtain ⟨⟨ms, hms, hok⟩, hN⟩ := hIs
  refine ⟨⟨⟨ms ++ [m], ?_, ?_⟩, ?_⟩, ?_⟩
  · simp [LState.emit, he, hms]
  · intro m' hm' _
    rcases List.mem_append.mp hm' with hm' | hm'
    · exact hok m' hm' ‹_›
    · rw [List.mem_singleton.mp hm']; exact hm
  · simp only [LState.emit]; omega
  · intro v hv'
    cases hv'
    exact ⟨_, rfl, by simp [Reg.kind]⟩

/-- The register of an argument the oracle requires to be an int vreg. -/
def IntAt (vs : List V) (k : Nat) : Prop := ∀ r, vs[k]? = some (.reg r) → ∃ n, r = .vreg n .int

theorem intAt_of {as : List AW} {vs : List V} (hvs : Holds2 f ctx as vs) {k : Nat} {a : AW}
    (ha : as[k]? = some a) (hv : a.isV = true) : IntAt vs k :=
  fun _ hr => isV_sound hv (γL_get hvs k a _ ha hr)

/-! ## The five oracles -/

section
variable (htot : Totality) (hc : cfg.checkOverlap = false) {N : Nat} {s0 : LState} {n : Nat}
  {ty : TypeId} {vs : List V} {s : LState} {tr : Array RuleId} {r : Option V} {s' : LState}
  {tr' : Array RuleId}
include htot hc

theorem got_ok (hIs : ShpIs N s0 s)
    (h : (applyTerm program (sem ctx) cfg n ty 571 vs).run (s, tr) = .ok (r, (s', tr'))) :
    ShpIs N s0 s' ∧ ∀ v, r = some v → γ f ctx (.reg 1) v := by
  obtain ⟨v, m, env, tr0, rfl, hma, he⟩ := single_rule_run htot hc program_term_571 term_571_kind
    rfl (by rfl) program_rulesOf_571 rfl h
  clear h
  oracle_inv [rule_inst_4002, program_term_1947] at hma he
  obtain ⟨nm, rfl⟩ := ofV_got_inv ‹MInst.ofV _ = some _›
  refine ctl_fin hIs ?_ ?_ (.got s.nextVreg nm hIs.2) <;> simp [LState.fresh] <;> omega

theorem near_ok (hIs : ShpIs N s0 s)
    (h : (applyTerm program (sem ctx) cfg n ty 572 vs).run (s, tr) = .ok (r, (s', tr'))) :
    ShpIs N s0 s' ∧ ∀ v, r = some v → γ f ctx (.reg 1) v := by
  obtain ⟨v, m, env, tr0, rfl, hma, he⟩ := single_rule_run htot hc program_term_572 term_572_kind
    rfl (by rfl) program_rulesOf_572 rfl h
  clear h
  oracle_inv [rule_inst_4009, program_term_1948] at hma he
  obtain ⟨nm, i, rfl⟩ := ofV_near_inv ‹MInst.ofV _ = some _›
  refine ctl_fin hIs ?_ ?_ (.near s.nextVreg nm i hIs.2) <;> simp [LState.fresh] <;> omega

theorem tls_ok (hIs : ShpIs N s0 s)
    (h : (applyTerm program (sem ctx) cfg n ty 647 vs).run (s, tr) = .ok (r, (s', tr'))) :
    ShpIs N s0 s' ∧ ∀ v, r = some v → γ f ctx (.reg 1) v := by
  obtain ⟨v, m, env, tr0, rfl, hma, he⟩ := single_rule_run htot hc program_term_647 term_647_kind
    rfl (by rfl) program_rulesOf_647 rfl h
  clear h
  oracle_inv [rule_inst_4918, program_term_1955, program_term_264, ctor_box_external_name_iff]
    at hma he
  obtain ⟨nm, rfl⟩ := ofV_tls_inv ‹MInst.ofV _ = some _›
  have hN := hIs.2
  refine ctl_fin hIs ?_ ?_
    (.tls nm s.nextVreg (s.nextVreg + 1) (by omega) hN (by omega)) <;> simp [LState.fresh] <;> omega

set_option maxHeartbeats 1000000 in
theorem rmw_ok (hIs : ShpIs N s0 s) (h1 : IntAt vs 1) (h2 : IntAt vs 2)
    (h : (applyTerm program (sem ctx) cfg n ty 612 vs).run (s, tr) = .ok (r, (s', tr'))) :
    ShpIs N s0 s' ∧ ∀ v, r = some v → γ f ctx (.reg 1) v := by
  obtain ⟨v, m, env, tr0, rfl, hma, he⟩ := single_rule_run htot hc program_term_612 term_612_kind
    rfl (by rfl) program_rulesOf_612 rfl h
  clear h
  oracle_inv [rule_inst_4518, program_term_1855] at hma he
  obtain ⟨t, op, fl, p, x, rfl, rfl, rfl⟩ := ofV_rmw_inv ‹MInst.ofV _ = some _›
  obtain ⟨p, rfl⟩ := h1 _ rfl
  obtain ⟨x, rfl⟩ := h2 _ rfl
  have hN := hIs.2
  refine ctl_fin hIs ?_ ?_ (.rmw t op fl p x s.nextVreg (s.nextVreg + 1) (s.nextVreg + 2)
    (by omega) (by omega) (by omega) hN (by omega) (by omega)) <;> simp [LState.fresh] <;> omega

theorem cas_ok (hIs : ShpIs N s0 s) (h0 : IntAt vs 0) (h1 : IntAt vs 1) (h2 : IntAt vs 2)
    (h : (applyTerm program (sem ctx) cfg n ty 613 vs).run (s, tr) = .ok (r, (s', tr'))) :
    ShpIs N s0 s' ∧ ∀ v, r = some v → γ f ctx (.reg 1) v := by
  obtain ⟨v, m, env, tr0, rfl, hma, he⟩ := single_rule_run htot hc program_term_613 term_613_kind
    rfl (by rfl) program_rulesOf_613 rfl h
  clear h
  oracle_inv [rule_inst_4532, program_term_1856] at hma he
  obtain ⟨t, fl, p, e, x, rfl, rfl, rfl, rfl⟩ := ofV_cas_inv ‹MInst.ofV _ = some _›
  obtain ⟨p, rfl⟩ := h0 _ rfl
  obtain ⟨e, rfl⟩ := h1 _ rfl
  obtain ⟨x, rfl⟩ := h2 _ rfl
  have hN := hIs.2
  refine ctl_fin hIs ?_ ?_ (.cas t fl p e x s.nextVreg (s.nextVreg + 1) (by omega) hN (by omega)) <;>
    simp [LState.fresh] <;> omega

end

set_option linter.unusedVariables false in
/-- **The control-form oracles are sound at every fuel**: a run of a helper `ctlOracle` selects,
on arguments its abstract values describe, keeps `ShpIs` and returns an int vreg. -/
theorem oracle_ctl (htot : Totality) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    {N : Nat} {s0 : LState} {cfg : Config} (hc : cfg.checkOverlap = false) {n : Nat}
    {ty : TypeId} {t : TermId} {as : List AW} {vs : List V} {s : LState} {tr : Array RuleId}
    {r : Option V} {s' : LState} {tr' : Array RuleId} (ha : ctlOracle t as = true)
    (hvs : Holds2 f ctx as vs) (hIs : ShpIs N s0 s)
    (h : (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    ShpIs N s0 s' ∧ ∀ v, r = some v → γ f ctx (.reg 1) v := by
  unfold ctlOracle at ha
  split at ha
  · rename_i ht
    simp only [Bool.or_eq_true, beq_iff_eq] at ht
    rcases ht with (rfl | rfl) | rfl
    · exact got_ok htot hc hIs h
    · exact near_ok htot hc hIs h
    · exact tls_ok htot hc hIs h
  split at ha
  · rename_i ht
    obtain rfl : t = 612 := eq_of_beq ht
    split at ha
    · simp only [Bool.and_eq_true] at ha
      exact rmw_ok htot hc hIs (intAt_of hvs (k := 1) rfl ha.1) (intAt_of hvs (k := 2) rfl ha.2) h
    · cases ha
  split at ha
  · rename_i ht
    obtain rfl : t = 613 := eq_of_beq ht
    split at ha
    · simp only [Bool.and_eq_true] at ha
      exact cas_ok htot hc hIs (intAt_of hvs (k := 0) rfl ha.1.1)
        (intAt_of hvs (k := 1) rfl ha.1.2) (intAt_of hvs (k := 2) rfl ha.2) h
    · cases ha
  cases ha

end Backend.Proof.Cov
