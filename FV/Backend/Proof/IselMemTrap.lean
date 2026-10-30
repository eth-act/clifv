import FV.Backend.Proof.IselExcl
import FV.Backend.Proof.IselAtomic
import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.IselCovForm
import FV.Backend.Proof.StockRootOpcode
import FV.Backend.Proof.IselCtlUnmatch
import FV.Clif.MemTrap

/-!
# The lowered code of a trapping atomic (A3, #412, slice F3)

`docs/plans/memfault.md`, "Backend layers". A memory trap of `Clif.run` that the theorems refine
is one of an `atomic_rmw` or `atomic_cas` (`Clif.memTrapInst`). Cranelift lowers both to one
LL/SC pseudo-instruction (`AtomicRMWLoop`, `AtomicCASLoop`) whose address operand is the CLIF
address value's vreg and whose flags are the CLIF instruction's: the loop's first line is the
`ldaxr` of the address, which carries the flags' trap code (`Backend.Asm`). This file proves that
shape of the lowering, independently of any semantics:

* `AtomicLowered inst ms`: `ms` is the single loop of the atomic `inst`;
* `loopTrap? i`: the trap code and the access size of a loop instruction;
* `rmwShape_*`, `casShape_ok`: every `atomic_rmw` root rule (`lower.isle:2357`–`2377`) and the
  `atomic_cas` rule (`lower.isle:2390`) emits that loop (the matching of the M4 proofs
  `atomic_rmw_*_ok`, `atomic_cas_ok`, with the shape as conclusion);
* `atomic_rules_filter`: the closure root rules of `lower` whose source opcode is `AtomicRmw` or
  `AtomicCas` are exactly those twelve (`opcode_args_match`, as the private lemma of
  `StockRootOpcodeMatch`, connects a matching
  rule's source opcode with the instruction's);
* **`atomicLowered_runTerm`**: the backend's `lower` call on an `atomic_rmw`/`atomic_cas`
  statement (`runTerm ctx "lower"`, as `lowerFunction` makes it) emits that loop.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- **The lowering of a trapping atomic**: `ms` is the single LL/SC loop of `inst`, with the
CLIF address value's vreg as address operand and the CLIF flags; the type is an `i8..i64`. -/
def AtomicLowered (inst : Clif.Inst) (ms : List MInst) : Prop :=
  (∀ op ty fl p x, inst = .atomicRmw op ty fl p x → eTy ty = true ∧
    ∃ (lop : AtomicRmwLoopOp) (d d1 d2 : Nat),
    ms = [.atomicRmwLoop (CTy.ofClif ty) lop fl (.vreg p .int) (.vreg x .int) (.vreg d .int)
      (.vreg d1 .int) (.vreg d2 .int)]) ∧
  (∀ ty fl p e x, inst = .atomicCas ty fl p e x → eTy ty = true ∧ ∃ d d1 : Nat,
    ms = [.atomicCasLoop (CTy.ofClif ty) fl (.vreg p .int) (.vreg e .int) (.vreg x .int)
      (.vreg d .int) (.vreg d1 .int)])

/-- The trap code (the flags') and the access size of an LL/SC loop instruction of an
`i8..i64` type (`AtomTy`). -/
def loopTrap? : MInst → Option (Clif.TrapCode × Nat)
  | .atomicRmwLoop ty _ fl .. | .atomicCasLoop ty fl .. =>
    if AtomTy ty then fl.trapCode.map (·, ty.bytes) else none
  | _ => none

theorem loopTrap?_mapRegs (g : Reg → Reg) (i : MInst) : loopTrap? (i.mapRegs g) = loopTrap? i := by
  cases i <;> rfl

/-- **The shape obligation of a `lower` rule**: whenever it fires on an instruction, the code it
appends is `AtomicLowered`. Stated like `MemRuleOk`'s matching premises. -/
def RuleShapeOk (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ AtomicLowered inst ms

/-- The shape proof of an `atomic_rmw` root rule: the matching of `rmw_root`. -/
syntax "rmw_shape" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rmw_shape) => `(tactic| (
    intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hmatch heval
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
    mem_inv hp [ext_valid_atomic_transaction_iff] at hmatch heval
    have hdat0 := hctx.data _ _ _ hi hic
    have hRT := hctx.resTys _ _ _ hi hic
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hdat := data_trans hdat0 ‹_›
    obtain ⟨cop, ty, fl, a, x, nm, rfl, hvs, rfl, hnm, hk, hety, hfl⟩ := inv_atomicRmw_root hdat
    cases cop <;> simp only [rmwOpName, Option.some.injEq] at hnm <;> subst hnm <;>
      (try (exact absurd hk (by decide)))
    repeat (mem_inv_simp [ext_value_array_2_iff] at * <;> isel_destruct <;> subst_vars)
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hL := ‹ApplyInternal _ _ _ _ 27 612 _ _ _ _›
    have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    obtain ⟨mi, hmi, rfl, hs3⟩ := atomic_rmw_loop_ok hp hco (by omega) hL
    obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
    have := hctx.valueReg a _ ‹ctx.valueReg? a = some _›; subst this
    have := hctx.valueReg x _ ‹ctx.valueReg? x = some _›; subst this
    simp only [‹_ = List.map CTy.ofClif [ty]›, List.map_cons, List.map_nil, List.head?_cons,
      Option.getD_some] at hmi
    obtain rfl := Option.some.inj (hmi.symm.trans rfl)
    simp only at hs' hs3 ⊢
    rw [hs3] at hs'
    subst hs'
    refine ⟨_, (frag_fresh3 _ _ ?_).emitted, ?_⟩
    · simp [vdefs, operands_rmwLoop, Operand.isDef, LState.fresh]
    · refine ⟨fun _ _ _ _ _ h => ?_, fun _ _ _ _ _ h => by cases h⟩
      cases h
      exact ⟨hety, _, _, _, _, rfl⟩))

section Shapes
variable {p : Program} (hp : Data p)

set_option maxHeartbeats 4000000 in
include hp in
theorem rmwShape_add : RuleShapeOk p rule_lower_2357 := by rmw_shape
set_option maxHeartbeats 4000000 in
include hp in
theorem rmwShape_sub : RuleShapeOk p rule_lower_2359 := by rmw_shape
set_option maxHeartbeats 4000000 in
include hp in
theorem rmwShape_and : RuleShapeOk p rule_lower_2361 := by rmw_shape
set_option maxHeartbeats 4000000 in
include hp in
theorem rmwShape_nand : RuleShapeOk p rule_lower_2363 := by rmw_shape
set_option maxHeartbeats 4000000 in
include hp in
theorem rmwShape_or : RuleShapeOk p rule_lower_2365 := by rmw_shape
set_option maxHeartbeats 4000000 in
include hp in
theorem rmwShape_xor : RuleShapeOk p rule_lower_2367 := by rmw_shape
set_option maxHeartbeats 4000000 in
include hp in
theorem rmwShape_smin : RuleShapeOk p rule_lower_2369 := by rmw_shape
set_option maxHeartbeats 4000000 in
include hp in
theorem rmwShape_smax : RuleShapeOk p rule_lower_2371 := by rmw_shape
set_option maxHeartbeats 4000000 in
include hp in
theorem rmwShape_umin : RuleShapeOk p rule_lower_2373 := by rmw_shape
set_option maxHeartbeats 4000000 in
include hp in
theorem rmwShape_umax : RuleShapeOk p rule_lower_2375 := by rmw_shape
set_option maxHeartbeats 4000000 in
include hp in
theorem rmwShape_xchg : RuleShapeOk p rule_lower_2377 := by rmw_shape

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_cas`** (`lower.isle:2390`): `AtomicCASLoop`. -/
theorem casShape_ok : RuleShapeOk p rule_lower_2390 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [ext_valid_atomic_transaction_iff, matchPat_and_single] at hmatch heval
  have hdat0 := hctx.data _ _ _ hi hic
  have hRT := hctx.resTys _ _ _ hi hic
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  obtain ⟨ty, fl, a, e, x, rfl, hvs, rfl, hety, hfl⟩ := inv_atomicCas_root hdat
  repeat (mem_inv_simp [ext_value_array_3_iff] at * <;> isel_destruct <;> subst_vars)
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hL := ‹ApplyInternal _ _ _ _ 27 613 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨mi, hmi, rfl, hs3⟩ := atomic_cas_loop_ok hp hco (by omega) hL
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
  have := hctx.valueReg a _ ‹ctx.valueReg? a = some _›; subst this
  have := hctx.valueReg e _ ‹ctx.valueReg? e = some _›; subst this
  have := hctx.valueReg x _ ‹ctx.valueReg? x = some _›; subst this
  simp only [‹_ = List.map CTy.ofClif [ty]›, List.map_cons, List.map_nil, List.head?_cons,
    Option.getD_some] at hmi
  rw [ofV_casLoop, Option.some.injEq] at hmi
  subst hmi
  simp only at hs' hs3 ⊢
  rw [hs3] at hs'
  subst hs'
  refine ⟨_, (frag_fresh2 _ _ ?_).emitted, ?_⟩
  · simp [vdefs, operands_casLoop, Operand.isDef, LState.fresh]
  · refine ⟨fun _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ h => ?_⟩
    cases h
    exact ⟨hety, _, _, rfl⟩

end Shapes

/-! ## The rules that can fire on an atomic -/

section Opcode
open Backend.Stock.Proof Backend.Proof.Driver

private theorem opcode_pattern_match {p : Program} (hp : Data p) {ctx : Ctx}
    {q : Pattern} {code : Nat} (parsed : sourceOpcodePattern p q = some code)
    {st : LState} {i : Nat} {env env' : Isle.Interp.Env V}
    (matched : matchPat p (Backend.sem ctx) st q (.inst i) env = .ok (some env')) :
    ∃ info kf opfs rest, ctx.insts[i]? = some info ∧ info.data = .data 152 kf (.data 151 code opfs :: rest) := by
  unfold sourceOpcodePattern at parsed
  split at parsed
  · rename_i type fT oT tail
    split at parsed
    · rename_i format opcode formatLookup opcodeLookup
      split at parsed
      · rename_i kf ko formatKind opcodeKind
        cases parsed
        obtain ⟨fs,extracted,args⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl matched
        rw [Backend.Proof.sem_extract] at extracted
        obtain ⟨info,source,rfl⟩ := ext_inst_data_value_inv extracted
        obtain ⟨e1,_,args2⟩ := matchArgs_cons_inv args
        obtain ⟨e2,formatMatch,_⟩ := matchArgs_cons_inv args2
        obtain ⟨fields,unFormat,fieldMatches⟩ := matchPat_enum_inv formatLookup formatKind formatMatch
        have data := sem_unData_inv unFormat
        cases fields with
        | nil => simp [matchArgs] at fieldMatches
        | cons first rest =>
          obtain ⟨e3,opMatch,_⟩ := matchArgs_cons_inv fieldMatches
          obtain ⟨opfs,unOp,_⟩ := matchPat_enum_inv opcodeLookup opcodeKind opMatch
          have opData := sem_unData_inv unOp
          exact ⟨info,kf,opfs,rest,source,by rw [data,opData]⟩
      · cases parsed
    · cases parsed
  · cases parsed

private theorem opcode_root_match {p : Program} (hp : Data p) {ctx : Ctx}
    {q : Pattern} {code : Nat} (hq : sourceRootOpcode p q = some code)
    {st : LState} {ti : Nat} {env env' : Isle.Interp.Env V}
    (h : matchPat p (Backend.sem ctx) st q (.inst ti) env = .ok (some env')) :
    ∃ info kf opfs rest, ctx.insts[ti]? = some info ∧ info.data = .data 152 kf (.data 151 code opfs :: rest) := by
  unfold sourceRootOpcode at hq
  split at hq
  · exact opcode_pattern_match hp hq (matchPat_bind_inv h).2
  · obtain ⟨e1, h1, -⟩ := matchAll_cons_inv (matchPat_and_inv h)
    exact opcode_pattern_match hp hq h1
  · obtain ⟨e1, -, h2⟩ := matchAll_cons_inv (matchPat_and_inv h)
    obtain ⟨e2, h3, -⟩ := matchAll_cons_inv h2
    obtain ⟨e3, -, h4⟩ := matchAll_cons_inv (matchPat_and_inv h3)
    obtain ⟨e4, h5, -⟩ := matchAll_cons_inv h4
    exact opcode_pattern_match hp hq h5
  · obtain ⟨e1, -, h2⟩ := matchAll_cons_inv (matchPat_and_inv h)
    obtain ⟨e2, h3, -⟩ := matchAll_cons_inv h2
    exact opcode_pattern_match hp hq h3
  · exact opcode_pattern_match hp hq h

/-- A rule whose root has the primary source opcode `code` matches only an instruction with that
opcode (the private lemma of `StockRootOpcodeMatch`, repeated here). -/
theorem opcode_args_match {p : Program} (hp : Data p) {ctx : Ctx}
    {r : Rule} {code : Nat} (parsed : sourceRuleOpcode p r = some code)
    {st : LState} {i : Nat} {env env' : Isle.Interp.Env V}
    (matched : matchArgs p (Backend.sem ctx) st r.args [.inst i] env = .ok (some env')) :
    ∃ info kf opfs rest, ctx.insts[i]? = some info ∧ info.data = .data 152 kf (.data 151 code opfs :: rest) := by
  cases args : r.args with
  | nil => simp [sourceRuleOpcode,args] at parsed
  | cons q tail =>
    simp only [sourceRuleOpcode,args,List.head?_cons,Option.bind_some] at parsed
    rw [args] at matched
    obtain ⟨e1,head,_⟩ := matchArgs_cons_inv matched
    exact opcode_root_match hp parsed head

end Opcode

/-- The source opcode of a rule is `AtomicRmw` or `AtomicCas`. -/
def atomicOpcode (k : Nat) : Bool :=
  (variantNames 151)[k]? == some "AtomicRmw" || (variantNames 151)[k]? == some "AtomicCas"

/-- **The closure root rules of `lower` on `atomic_rmw`/`atomic_cas`** (checked inventory). -/
theorem atomic_rules_filter :
    (program.rulesOf TId.lower).filter (fun r => closureRoot r &&
      (Stock.Proof.sourceRuleOpcode program r).any atomicOpcode) =
    [rule_lower_2357, rule_lower_2359, rule_lower_2361, rule_lower_2363, rule_lower_2365,
      rule_lower_2367, rule_lower_2369, rule_lower_2371, rule_lower_2373, rule_lower_2375,
      rule_lower_2377, rule_lower_2390] := by
  rw [program_rulesOf_686]
  decide +kernel

theorem opcodeV_AtomicRmw : opcodeV "AtomicRmw" = .data 151 156 [] := rfl
theorem opcodeV_AtomicCas : opcodeV "AtomicCas" = .data 151 157 [] := rfl
theorem atomicOpcode_156 : atomicOpcode 156 = true := by decide
theorem atomicOpcode_157 : atomicOpcode 157 = true := by decide

/-- The instruction data of an `atomic_rmw`/`atomic_cas` has an atomic opcode. -/
theorem instData_atomic_opcode {f : Clif.Function} {inst : Clif.Inst} {d : V}
    (hm : Clif.memTrapInst inst = true) (h : instData f inst = .ok d) {kf code : Nat}
    {opfs rest : List V} (hd : d = .data 152 kf (.data 151 code opfs :: rest)) :
    atomicOpcode code = true := by
  rcases instData_names h with ⟨rest', he⟩ | ⟨ty, imm, rfl, -⟩
  · cases inst <;> simp only [Clif.memTrapInst, Bool.false_eq_true] at hm
    all_goals
      simp only [instNames] at he
      rw [hd] at he
    · rw [opcodeV_AtomicRmw] at he
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data he.symm
      injection h3 with h4
      injection h4 with _ h5
      rw [h5]; exact atomicOpcode_156
    · rw [opcodeV_AtomicCas] at he
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data he.symm
      injection h3 with h4
      injection h4 with _ h5
      rw [h5]; exact atomicOpcode_157
  · simp [Clif.memTrapInst] at hm

/-- **The `lower` call on an atomic emits its loop** (`applyTerm` level). -/
theorem atomicLowered_of_rules {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (hE : Compile.functionE f = true) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hm : Clif.memTrapInst inst = true) {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (program.rulesOf TId.lower).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId}
    (h : (applyTerm program (sem ctx) cfg (n + 1) ty TId.lower [.inst ii]).run (st, tr) =
      .ok (some out, (st', tr'))) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ AtomicLowered inst ms := by
  change 1002 + (program.rulesOf 686).length ≤ n at hn
  obtain ⟨r, pre0, post0, hsplit, -, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some_first hco data_program.t686 term_686_kind rfl h
  have hr : r ∈ program.rulesOf TId.lower := by
    change r ∈ program.rulesOf 686; rw [hsplit]; simp
  simp only [Prod.mk.injEq] at hs
  rw [← hs.1] at heval
  cases hroot : closureRoot r
  · exact absurd hmatch (excludedUnmatchable r hr hroot f ctx hctx hE ii info inst hi hc cfg m
      (st, tr) env' s1)
  -- the rule's source opcode is the instruction's
  have hinv := List.all_eq_true.mp Stock.Proof.stock_source_opcode_inventory r hr
  simp only [hroot, Bool.not_true, Bool.false_or] at hinv
  obtain ⟨code, hcode⟩ := Option.isSome_iff_exists.mp hinv
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨env0, hargs, -⟩ := matchRule_some_inv hmatch
  obtain ⟨info', kf, opfs, rest, hfound, hshape⟩ :=
    opcode_args_match data_program hcode hargs
  rw [hi] at hfound; cases hfound
  have hat := instData_atomic_opcode hm (hctx.data _ _ _ hi hc) hshape
  have hmem : r ∈ (program.rulesOf TId.lower).filter (fun r => closureRoot r &&
      (Stock.Proof.sourceRuleOpcode program r).any atomicOpcode) :=
    List.mem_filter.2 ⟨hr, by simp [hroot, hcode, hat]⟩
  rw [atomic_rules_filter] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hm1 : 1000 ≤ m' + 1 := by omega
  have hn1 : 1000 ≤ n := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rmwShape_add data_program f ctx hctx ii info inst hi hc cfg hco _ n st tr env' s1 out st' tr2 hm1 hn1 hmatch heval
  · exact rmwShape_sub data_program f ctx hctx ii info inst hi hc cfg hco _ n st tr env' s1 out st' tr2 hm1 hn1 hmatch heval
  · exact rmwShape_and data_program f ctx hctx ii info inst hi hc cfg hco _ n st tr env' s1 out st' tr2 hm1 hn1 hmatch heval
  · exact rmwShape_nand data_program f ctx hctx ii info inst hi hc cfg hco _ n st tr env' s1 out st' tr2 hm1 hn1 hmatch heval
  · exact rmwShape_or data_program f ctx hctx ii info inst hi hc cfg hco _ n st tr env' s1 out st' tr2 hm1 hn1 hmatch heval
  · exact rmwShape_xor data_program f ctx hctx ii info inst hi hc cfg hco _ n st tr env' s1 out st' tr2 hm1 hn1 hmatch heval
  · exact rmwShape_smin data_program f ctx hctx ii info inst hi hc cfg hco _ n st tr env' s1 out st' tr2 hm1 hn1 hmatch heval
  · exact rmwShape_smax data_program f ctx hctx ii info inst hi hc cfg hco _ n st tr env' s1 out st' tr2 hm1 hn1 hmatch heval
  · exact rmwShape_umin data_program f ctx hctx ii info inst hi hc cfg hco _ n st tr env' s1 out st' tr2 hm1 hn1 hmatch heval
  · exact rmwShape_umax data_program f ctx hctx ii info inst hi hc cfg hco _ n st tr env' s1 out st' tr2 hm1 hn1 hmatch heval
  · exact rmwShape_xchg data_program f ctx hctx ii info inst hi hc cfg hco _ n st tr env' s1 out st' tr2 hm1 hn1 hmatch heval
  · exact casShape_ok data_program f ctx hctx ii info inst hi hc cfg hco _ n st tr env' s1 out st' tr2 hm1 hn1 hmatch heval

set_option maxRecDepth 20000 in
/-- **The backend's `lower` call on an `atomic_rmw`/`atomic_cas` statement emits its loop**
(`runTerm ctx "lower" [.inst ii]`, as `lowerFunction` makes it). -/
theorem atomicLowered_runTerm {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (hE : Compile.functionE f = true) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hm : Clif.memTrapInst inst = true) {st : LState} {out : V} {st' : LState} {tr : List RuleId}
    (h : runTerm ctx "lower" [.inst ii] st = .ok (some out, st', tr)) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ AtomicLowered inst ms := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower.ret T.lower.id [.inst ii]).run
      (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf TId.lower).length ≤ 1000 := by
      rw [show TId.lower = 686 from rfl, data_program.r686]; decide
    exact atomicLowered_of_rules hctx hE hi hc hm rfl (by omega) ha

end Backend.Proof
