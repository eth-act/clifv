import FV.Backend.Proof.IselCmpTerms

/-!
# Family Ctl (terminators, branches, calls): common facts

The data `termData` gives each terminator (format and opcode variant indices), and the
inverse: a terminator whose data has a given format is of the corresponding shape.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

theorem termData_trap (c : Clif.TrapCode) :
    termData (.trap c) = .ok (.data 152 26 [.data 151 4 [], .op (.trapCode c)]) := rfl

theorem termData_ret (xs : List Clif.ValueId) :
    termData (.ret xs) = .ok (.data 152 18 [.data 151 7 [], .values xs]) := rfl

theorem termData_jump (d : Clif.BlockCall) :
    termData (.jump d) = .ok (.data 152 15 [.data 151 0 [], .blockCalls [0]]) := rfl

theorem termData_brif (c : Clif.ValueId) (t e : Clif.BlockCall) :
    termData (.brif c t e) = .ok (.data 152 5 [.data 151 1 [], .value c, .blockCalls [0, 1]]) := rfl

theorem termData_brTable (x : Clif.ValueId) (d : Clif.BlockCall) (tbl : List Clif.BlockCall) :
    termData (.brTable x d tbl) = .ok (.data 152 4 [.data 151 2 [], .value x, .op (.jumpTable 0)]) :=
  rfl

theorem seqRun_one_stop {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {i : MInst}
    {ops : Array Operand} (hops : i.operands = .ok ops) {ρ : Nat → CV} {w w' : Arm.ArmState}
    {outs : List CV} {ctl : Ctl} (hctl : ctl ≠ .next) (hs : ispec i (vuses ops ρ) w = some (outs, w', ctl))
    (hlen : outs.length = (ops.toList.filter Operand.isDef).length) :
    ∃ w'', seqRun isem [i] ρ w = some (.stop 0 i ops ρ w outs w'' ctl) ∧ SameWorld F w'' w' := by
  obtain ⟨w'', hi, hw⟩ := hR _ _ _ _ _ hs
  refine ⟨w'', ?_, hw⟩
  cases ctl with
  | next => exact absurd rfl hctl
  | _ => simp only [seqRun, hops, hi, hlen, ↓reduceIte]

variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

/-! ## Extern helpers of the family -/

theorem ctor_output_none' (st : LState) (v : V) (st' : LState) :
    externCtor ctx T.output_none [] st = .ok (v, st') ↔ v = .regsVec [] ∧ st' = st := by
  have : externCtor ctx T.output_none [] st = .ok (.regsVec [], st) := rfl
  rw [this]; simp [eq_comm]

theorem ext_value_list_slice_iff (st : LState) (vs : List Nat) (fs : List V) :
    externExtract ctx T.value_list_slice (.values vs) st = .ok fs ↔ fs = [.values vs] := by
  have : externExtract ctx T.value_list_slice (.values vs) st = .ok [.values vs] := rfl
  rw [this]; simp [eq_comm]

theorem ctor_put_in_regs_vec_iff (st : LState) (vs : List Nat) (v : V) (st' : LState) :
    externCtor ctx T.put_in_regs_vec [.values vs] st = .ok (v, st') ↔
      ∃ rs, vs.mapM ctx.valueReg? = some rs ∧ v = .regsVec (rs.map fun r => [r]) ∧ st' = st := by
  have : externCtor ctx T.put_in_regs_vec [.values vs] st = match vs.mapM ctx.valueReg? with
      | some rs => .ok (.regsVec (rs.map fun r => [r]), st)
      | none => .unmodeled "put_in_regs_vec" := rfl
  rw [this]
  cases vs.mapM ctx.valueReg? <;> simp [eq_comm]

/-- The single register of each entry (`gen_return`, `gen_call_args`, `gen_call_rets`). -/
def single? : List Reg → Option Reg
  | [r] => some r
  | _ => none

theorem ctor_gen_return_iff (st : LState) (rss : List (List Reg)) (v : V) (st' : LState) :
    externCtor ctx T.gen_return [.regsVec rss] st = .ok (v, st') ↔
      ∃ ps rs, retRegs rss.length = some ps ∧ rss.mapM single? = some rs ∧ v = .op .unit ∧
        st' = st.emit (.rets (rs.zip ps)) := by
  have : externCtor ctx T.gen_return [.regsVec rss] st =
      match retRegs rss.length, rss.mapM single? with
      | some ps, some rs => .ok (.op .unit, st.emit (.rets (rs.zip ps)))
      | _, _ => .unmodeled "gen_return: more than 8 return values or multi-register values" := by
    show (match retRegs rss.length, rss.mapM (fun | [r] => some r | _ => none) with
      | some ps, some rs => _ | _, _ => _) = _
    rfl
  rw [this]
  cases retRegs rss.length <;> cases rss.mapM single? <;> simp [eq_comm]

theorem mapM_single_map (rs : List Reg) : (rs.map fun r => [r]).mapM single? = some rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [List.mapM_cons, single?, ih]

/-- `ctl_inv [lemmas] at h₁ … hₙ`: `isel_inv` plus the family's extern lemmas at every round. -/
syntax "ctl_inv" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? " at " (ppSpace colGt ident)+ : tactic
macro_rules
  | `(tactic| ctl_inv [$ts,*] at $hs*) => `(tactic| (isel_inv [$ts,*, ctor_output_none',
      ext_value_list_slice_iff, ctor_put_in_regs_vec_iff, ctor_gen_return_iff] at $hs* <;>
      repeat (isel_inv_simp [ctor_output_none', ext_value_list_slice_iff, ctor_put_in_regs_vec_iff,
        ctor_gen_return_iff] at * <;> isel_destruct <;> subst_vars)))

/-! ## Side-effect helpers (`emit_side_effect`, `side_effect`, `udf`) -/

include hp hc in
theorem emit_side_effect_inst_ok {n : Nat} (hn : 30 ≤ n) {i : V} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 13 242 [.data 46 0 [i]] s v s') :
    ∃ m, MInst.ofV i = some m ∧ s'.1 = s.1.emit m ∧ v = .op .unit := by
  isel_split hp hc h 242
  · isel_inv [*, rule_prelude_lower_522] at hm he
    exact ⟨_, ‹_›, rfl⟩
  · isel_inv [*, rule_prelude_lower_524] at hm
  · isel_inv [*, rule_prelude_lower_527] at hm

include hp hc in
theorem side_effect_inst_ok {n : Nat} (hn : 60 ≤ n) {i : V} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 25 243 [.data 46 0 [i]] s v s') :
    ∃ m, MInst.ofV i = some m ∧ s'.1 = s.1.emit m ∧ v = .regsVec [] := by
  have k := fun n (hn : 30 ≤ n) s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  isel_split hp hc h 243
  isel_inv [*, rule_prelude_lower_535] at hm he
  simp only [ctor_output_none'] at *
  isel_destruct; subst_vars
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨m, hm, hs, -⟩ := k _ (by omega) _ _ _ h242
  exact ⟨m, hm, hs, rfl⟩

include hp hc in
theorem udf_ok {n : Nat} (hn : 30 ≤ n) {c : V} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 46 528 [c] s v s') :
    s'.1 = s.1 ∧ v = .data 46 0 [.data 58 123 [c]] := by
  isel_split hp hc h 528
  isel_inv [*, rule_inst_3569] at hm he

end Backend.Proof
