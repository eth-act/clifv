import FV.Backend.Proof.StockConditionalParameterSelection
import FV.Backend.Proof.StockBranchHelperTargets
import FV.Backend.Proof.StockPureHelperTransport
import FV.Backend.Proof.StockExtendRequests

/-! The Stock `br_table` terminator: rule selection and emission (#140, CB-14a).

A `br_table x, default, [targets]` terminator slot holds `tableData x`. Every `lower_branch` rule
before the table rule 3277 has another root format, so first-match selection derives 3277
(`table_selected`). Its right-hand side makes four helper calls (`TableCalls`,
`table_selected_calls`):

* `side_effect` (243) of `emit_island` (669) on `targets_jt_space targets` emits
  `emit_island (4 * (8 + n))`, with `n` the number of table targets;
* `put_in_reg_zext32 x` gives the index register `ridx`;
* `br_table_impl n ridx default targets` (helper 670) checks the bound and emits the dispatch.

The helpers 669 and 243 are in a checked closure of unchanged constructors (`PureHelper`), so they
change only the code-generation state. Helper 670 reaches `opportunistic_def`; a checked scope
projects its actual Stock run onto the original helper semantics (`impl_call`). For an `i32` index
and a table of fewer than 4096 targets, the emission is exactly
`emit_island (4 * (8 + n)); subs wzr, ridx, #n; jt_sequence default targets ridx t1 t2`, with `ridx`
the register of `x` and `t1`, `t2` the next two fresh registers (`TableCalls.code`,
`table_named_code`). -/

namespace Backend.Stock.Proof.TableBranch
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- The prepared data of a `br_table x` terminator slot (`termData_brTable`). -/
def tableData (x : Nat) : V := .data 152 4 [.data 151 2 [],.value x,.op (.jumpTable 0)]

theorem termData_tableData (x : Nat) (d : Clif.BlockCall) (tbl : List Clif.BlockCall) :
    termData (.brTable x d tbl) = .ok (tableData x) := termData_brTable x d tbl

private theorem branch_ruleFmt_match {ctx : Ctx} {r : Rule} {fT : Nat}
    (format : ruleFmt r = some fT) (lo : 2447 ≤ fT) (hi : fT < 2447 + 36)
    {fuel ti : Nat} {rest : List V} {st next : State × Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel r (.inst ti :: rest)).run st =
      .ok (some env, next)) :
    ∃ info fs, ctx.insts[ti]? = some info ∧ info.data = .data 152 (fT - 2447) fs := by
  have bound : fT - 2447 < 36 := by omega
  obtain ⟨term, lookup, kind⟩ := fmtKinds_program (fT - 2447) bound
  rw [show 2447 + (fT - 2447) = fT by omega] at lookup
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨env0, args, _⟩ := matchRule_some_inv matched
    rw [stock_matchArgs] at args
    unfold ruleFmt at format
    split at format
    · rename_i q qs shape
      rw [shape] at args
      obtain ⟨env1, head, _⟩ := matchArgs_cons_inv args
      exact rootFmt_match_k data_program format lookup kind head
    · cases format

private theorem other_format {ctx : Ctx} {i fT tag : Nat} {fields : List V}
    (slot : ctx.insts[i]? = some ⟨.data 152 tag fields,[],[],none⟩) {r : Rule}
    (format : ruleFmt r = some fT) (lo : 2447 ≤ fT) (hi : fT < 2447+36) (different : fT ≠ 2447+tag)
    {fuel : Nat} {st next : State × Array RuleId} {labels : List Label} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel r [.inst i,.labels labels]).run st =
      .ok (some env,next)) : False := by
  obtain ⟨info,fs,source,shape⟩ := branch_ruleFmt_match format lo hi matched
  rw [slot] at source
  cases source
  simp only [V.data.injEq] at shape
  omega

/-- **The actual first matching rule of a `br_table` terminator is the table rule (3277).** Every
earlier `lower_branch` rule has another root format: 2542 and 2551 (format 2474), the three `brif`
rules 3251, 3257 and 3231 (2452), 2561 (2475) and 3270 (2462). -/
theorem table_selected {ctx : Ctx} {i x : Nat} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨tableData x,[],[],none⟩)
    {before next : State} {out : V} {trace : List RuleId}
    (selected : BranchSelection ctx i labels before out next trace) :
    selected.rule = rule_lower_3277 := by
  have member : selected.rule ∈ program.rulesOf T.lower_branch.id := by rw [selected.candidates]; simp
  rw [show T.lower_branch.id = 687 from rfl,data_program.r687] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with root | root | root | root | root | root | root | root
  all_goals try exact root
  all_goals
    have matched := selected.matchedRun
    rw [root] at matched
  · exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2452) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2452) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2475) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2452) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2462) rfl (by decide) (by decide) (by decide) matched)

/-! ## Helper projections -/

/-- The closure of `side_effect` (243) and `emit_island` (669). -/
private def pureIds : List Nat := [169, 235, 242, 243, 669, 1787, 1954]

section Certificate
attribute [local semireducible] Isle.Aarch64.program
private theorem pure_checked : pureIds.all (PureHelper.checkTerm program pureIds) = true := by
  decide +kernel
end Certificate

/-- An actual Stock call of a helper of `pureIds` is the original call on the code-generation
state, and it keeps every other field. -/
private theorem pure_call {ctx : Ctx} {fuel ty t : Nat} (member : t ∈ pureIds) {args : List V}
    {st next : State × Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel ty t args st out next) :
    ApplyInternal program (Backend.sem ctx) {} fuel ty t args (st.1.base,st.2) out (next.1.base,next.2) ∧
      next.1 = {st.1 with base := next.1.base} := by
  have projected := PureHelper.projects pure_checked ctx (cfg := {}) rfl (fuel+1) ty t member args st.1 st.2
  unfold ApplyInternal at run ⊢
  rw [run] at projected
  exact ⟨projected.symm,PureHelper.preserves pure_checked ctx rfl member args run⟩

/-- The actual `emit_island` builder keeps the state. -/
theorem island_builder {ctx : Ctx} {fuel : Nat} (enough : 30 ≤ fuel) {k : V}
    {st next : State × Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 46 669 [k] st out next) :
    next.1 = st.1 ∧ out = .data 46 0 [.data 58 136 [k]] := by
  obtain ⟨legacy,frame⟩ := pure_call (by decide) run
  obtain ⟨same,rfl⟩ := emit_island_ok data_program rfl enough legacy
  refine ⟨?_,rfl⟩
  rw [frame]
  simp only at same
  rw [same]

/-- The actual `side_effect` of one instruction emits it and keeps every other field. -/
theorem side_effect_emits {ctx : Ctx} {fuel : Nat} (enough : 60 ≤ fuel) {i : V}
    {st next : State × Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 25 243 [.data 46 0 [i]] st out next) :
    ∃ m,MInst.ofV i = some m ∧ next.1 = {st.1 with base := st.1.base.emit m} ∧ out = .regsVec [] := by
  obtain ⟨legacy,frame⟩ := pure_call (by decide) run
  obtain ⟨m,decoded,same,rfl⟩ := side_effect_inst_ok data_program rfl enough legacy
  refine ⟨m,decoded,?_,rfl⟩
  rw [frame]
  simp only at same
  rw [same]

/-- The closure of `br_table_impl` (670); it contains `opportunistic_def` (181). -/
private def implIds : List Nat := [164, 175, 181, 201, 235, 242, 256, 305, 318, 319, 320, 321, 352, 356,
  358, 359, 360, 390, 391, 498, 553, 554, 662, 670, 1787, 1788, 1789, 1791, 1799, 1820, 1822, 1823, 1844,
  1946, 1964, 1972, 1989, 1990, 2028, 2029, 2235]
private def ruleCalls (r : Rule) : List Nat := r.iflets.flatMap (fun il => exprCalls il.rhs) ++ exprCalls r.rhs
private def checkTerm (ids : List Nat) (id : Nat) : Bool :=
  match termOf program id with
  | .error _ => false
  | .ok term => (!(revisedCtors.contains term.id) || term.id == TId.opportunistic_def) &&
      (program.rulesOf id).all (fun r => (ruleCalls r).all (ids.contains ·))

section Certificate
attribute [local semireducible] Isle.Aarch64.program
private theorem impl_checked : implIds.all (checkTerm implIds) = true := by decide +kernel
end Certificate

private theorem delegate_project (st : State) (result : ExtResult (V × LState)) :
    projectCtor State.base (match result with
      | .ok (v,base) => .ok (v,{st with base})
      | .fail => .fail
      | .unmodeled e => .unmodeled e) = result := by
  cases result with
  | ok pair => cases pair; rfl
  | fail => rfl
  | unmodeled e => rfl

private def opportunityResult (ctx : Ctx) (st : State) (v : Nat) (rs : List Reg) : ExtResult (V × State) :=
  let block? := st.current.map (fun i => st.instBlock[i]!)
  let defBlock? := (ctx.defInst? v).map (fun i => st.instBlock[i]!)
  if st.demand[v]! == 0 || block?.isNone || block? != defBlock? then .ok (.op .unit,st)
  else .ok (.op .unit,{st with opportunistic := st.opportunistic.set! v (some ⟨block?.getD 0,rs,st.demand[v]!⟩)})

private theorem opportunity_eq (ctx : Ctx) (term : Term) (args : List V) (st : State)
    (id : term.id = TId.opportunistic_def) :
    Stock.externCtor ctx term args st = match args with
      | [.value v,.regs rs] => opportunityResult ctx st v rs
      | _ => match Backend.externCtor ctx term args st.base with
        | .ok (v,base) => .ok (v,{st with base})
        | .fail => .fail
        | .unmodeled e => .unmodeled e := by
  cases term with
  | mk tid name inputs ret kind pos =>
    change tid = 181 at id
    subst tid
    cases args with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => cases a <;> rfl
      | cons b rest =>
        cases rest with
        | cons c rest => cases a <;> cases b <;> rfl
        | nil => cases a <;> first | rfl | (cases b <;> rfl)

private theorem opportunity_project (ctx : Ctx) (term : Term) (args : List V) (st : State)
    (id : term.id = TId.opportunistic_def) :
    projectCtor State.base (Stock.externCtor ctx term args st) = Backend.externCtor ctx term args st.base := by
  rw [opportunity_eq ctx term args st id]
  split
  · rename_i v rs
    have legacy : Backend.externCtor ctx term [.value v,.regs rs] st.base = .ok (.op .unit,st.base) := by
      cases term with
      | mk tid name inputs ret kind pos =>
        change tid = 181 at id
        subst tid
        rfl
    rw [legacy]
    unfold opportunityResult
    dsimp only
    split <;> rfl
  · exact delegate_project st (Backend.externCtor ctx term args st.base)

private theorem impl_scope (ctx : Ctx) :
    ProjectionScope program (Backend.sem ctx) State.base (Stock.externCtor ctx) (fun t => t ∈ implIds) := by
  have valid : ∀ t ∈ implIds,∀ term,termOf program t = .ok term →
      (!(revisedCtors.contains term.id) || term.id == TId.opportunistic_def) = true ∧
      (program.rulesOf t).all (fun r => (ruleCalls r).all (implIds.contains ·)) = true := by
    intro t member term lookup
    have fact := List.all_eq_true.mp impl_checked t member
    simpa only [checkTerm,lookup,Bool.and_eq_true] using fact
  constructor
  · intro t term member lookup args st
    have constructors := (valid t member term lookup).1
    simp only [Bool.or_eq_true] at constructors
    rcases constructors with ordinary | opportunity
    · apply stock_ctor_unchanged
      simpa using ordinary
    · exact opportunity_project ctx term args st (beq_iff_eq.mp opportunity)
  · intro t term member lookup flags ex kind r recorded
    have calls := List.all_eq_true.mp (valid t member term lookup).2 r recorded
    have contains : ∀ u ∈ ruleCalls r,u ∈ implIds := by
      intro u inside
      have yes := List.all_eq_true.mp calls u inside
      simpa using yes
    constructor
    · intro il inside u called
      exact contains u (List.mem_append_left _ (List.mem_flatMap.mpr ⟨il,inside,called⟩))
    · intro u called
      exact contains u (List.mem_append_right _ called)

/-- An actual Stock call of `br_table_impl` is the original call on the code-generation state. -/
theorem impl_call {ctx : Ctx} {fuel : Nat} {args : List V}
    {st next : State × Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 13 670 args st out next) :
    ApplyInternal program (Backend.sem ctx) {} fuel 13 670 args (st.1.base,st.2) out (next.1.base,next.2) := by
  have projected := (evaluation_scoped_restate program (Backend.sem ctx) {} rfl State.base
    (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
    (fun t => t ∈ implIds) (impl_scope ctx) (fun _ _ _ => rfl) (fuel+1)).term
      13 670 args (by decide) st.1 st.2
  change projectResult State.base ((applyTerm program (Stock.sem ctx) {} (fuel+1) 13 670 args).run st) =
    (applyTerm program (Backend.sem ctx) {} (fuel+1) 13 670 args).run (st.1.base,st.2) at projected
  unfold ApplyInternal at run ⊢
  rw [run] at projected
  exact projected.symm

/-! ## The original dispatch helper on a small table -/

private theorem ofV_jtSequence (d : Label) (ts : List Label) (r a b : Reg) :
    MInst.ofV (.data 58 128 [.label d,.labels ts,.reg r,.reg a,.reg b]) =
      some (.jtSequence d ts r a b) := rfl

private theorem small_imm12 {k : Nat} (small : k < 4096) :
    Imm12.ofNat? (u64 (k : Int)) = some ⟨k,false⟩ := by
  rw [u64_natCast (by omega)]
  unfold Imm12.ofNat?
  have masked : mask64 k = k := by unfold mask64; omega
  simp only [masked]
  rw [ite_eq_left_iff.mpr (fun h => absurd small h)]

set_option maxHeartbeats 4000000 in
/-- **The original `br_table_impl` on a table of fewer than 4096 targets** compares the index
register with the immediate table size (rule 5450): it allocates two fresh registers and emits
`subs wzr, ridx, #n` and `jt_sequence default targets ridx t1 t2`. The register-operand rule 5454
is not reached, because rule 5450 matches. -/
theorem legacy_impl_small {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 300 ≤ fuel) {k : Nat} (small : k < 4096)
    {r : Reg} {d : Label} {ts : List Label} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (Backend.sem ctx) cfg fuel 13 670 [.int k,.reg r,.label d,.labels ts] s v s') :
    s'.1 = ((((s.1.fresh .int).2.fresh .int).2.emit (.aluRRImm12 .subS .size32 .xzr r ⟨k,false⟩)).emit
      (.jtSequence d ts r (s.1.fresh .int).1 ((s.1.fresh .int).2.fresh .int).1)) := by
  have kJ := fun n (hn : 30 ≤ n) r d ts s v s' h => jt_sequence_ok hp (ctx := ctx) hc (n := n)
    (r := r) (d := d) (ts := ts) (s := s) (v := v) (s' := s') hn h
  have kW := fun n (hn : 40 ≤ n) mi ci s v s' h => with_flags_side_effect_ok hp (ctx := ctx) hc
    (n := n) (mi := mi) (ci := ci) (s := s) (v := v) (s' := s') hn h
  have kE2 := fun n (hn : 30 ≤ n) i j s v s' h => emit_side_effect_inst2_ok hp (ctx := ctx) hc
    (n := n) (i := i) (j := j) (s := s) (v := v) (s' := s') hn h
  have kCI := fun n (hn : 30 ≤ n) a b c s v s' h => cmp_imm_ok hp (ctx := ctx) hc (n := n)
    (a := a) (b := b) (c := c) (s := s) (v := v) (s' := s') hn h
  have immediate := small_imm12 small
  have hp' := hp
  isel_split hp hc h 670
  · brif_inv [*, rule_inst_5450, ext_imm12_from_u64_iff] at hm he
    obtain ⟨himm⟩ : Nonempty (Imm12.ofNat? (u64 (k : Int)) = some _) := ⟨‹_›⟩
    rw [immediate] at himm
    cases himm
    have h391 := ‹ApplyInternal _ _ _ _ 47 391 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kCI _ (by omega) _ _ _ _ _ _ h391
    have h662 := ‹ApplyInternal _ _ _ _ 49 662 _ _ _ _›
    obtain ⟨hs2, rfl⟩ := kJ _ (by omega) _ _ _ _ _ _ h662
    have h256 := ‹ApplyInternal _ _ _ _ 46 256 _ _ _ _›
    obtain ⟨hs3, rfl⟩ := kW _ (by omega) _ _ _ _ _ h256
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨m1, m2, hs4, hm1, hm2⟩ := kE2 _ (by omega) _ _ _ _ _ h242
    rw [ofV_cmpImm32] at hm1
    rw [ofV_jtSequence] at hm2
    cases hm1; cases hm2
    simp only at hs1 hs2 hs3 hs4
    rw [hs4, hs3, hs2, hs1]
  · obtain ⟨m, s2, failed⟩ := hpre _ (List.mem_cons_self ..)
    revert failed
    isel_eval [*, rule_inst_5450, ext_imm12_from_u64]
    simp

/-! ## The calls of the table rule -/

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl

private theorem jump_table_size (ctx : Ctx) (st : State) (ls : List Label) (v : V) (st' : State) :
    Stock.externCtor ctx T.jump_table_size [.labels ls] st = .ok (v,st') ↔ v = .int ls.length ∧ st' = st := by
  have actual : Stock.externCtor ctx T.jump_table_size [.labels ls] st = .ok (.int ls.length,st) := rfl
  rw [actual]; simp [eq_comm]
private theorem targets_jt_space (ctx : Ctx) (st : State) (ls : List Label) (v : V) (st' : State) :
    Stock.externCtor ctx T.targets_jt_space [.labels ls] st = .ok (v,st') ↔
      v = .int (4 * (8 + ls.length)) ∧ st' = st := by
  have actual : Stock.externCtor ctx T.targets_jt_space [.labels ls] st =
    .ok (.int (4 * (8 + ls.length)),st) := rfl
  rw [actual]; simp [eq_comm]
private theorem u32_into_u64 (ctx : Ctx) (st : State) (a : Int) (v : V) (st' : State) :
    Stock.externCtor ctx T.u32_into_u64 [.int a] st = .ok (v,st') ↔ v = .int a ∧ st' = st := by
  have actual : Stock.externCtor ctx T.u32_into_u64 [.int a] st = .ok (.int a,st) := rfl
  rw [actual]; simp [eq_comm]

/-- The internal calls of the selected table rule (3277), derived from its actual match and
right-hand side: the labels are the default and the table, the island is emitted first, then the
index is put in a register and the dispatch helper runs on the table size. -/
structure TableCalls (ctx : Ctx) (i : Nat) (labels : List Label) (before : State) (out : V)
    (next : State) where
  source : V
  sourceData : ∃ info tableOp,ctx.insts[i]? = some info ∧
    info.data = .data 152 4 [.data 151 2 [],source,tableOp]
  default : Label
  table : List Label
  labels_eq : labels = default :: table
  island : State × Array RuleId
  islandEq : island.1 = {before with base := before.base.emit (.emitIsland (4*(8+table.length)))}
  extended : State × Array RuleId
  ridx : V
  extendFuel : Nat
  implFuel : Nat
  finalTrace : Array RuleId
  extendEnough : 60 ≤ extendFuel
  implEnough : 300 ≤ implFuel
  extendRun : ApplyInternal program (Stock.sem ctx) {} extendFuel 27 556 [source] island ridx extended
  implRun : ApplyInternal program (Stock.sem ctx) {} implFuel 13 670
    [.int table.length,ridx,.label default,.labels table] extended out (next,finalTrace)

private theorem space_cast (n : Nat) : (4 * (8 + (n : Int))) = ((4 * (8 + n) : Nat) : Int) := by
  push_cast; omega

private theorem ofV_emitIsland (k : Nat) :
    MInst.ofV (.data 58 136 [.int (k : Int)]) = some (.emitIsland k) := rfl

/-- **The selected table rule makes exactly the island, index and dispatch calls.** -/
theorem table_selected_calls {ctx : Ctx} {i : Nat} {labels : List Label}
    {before next : State} {out : V} {trace : List RuleId}
    (selected : BranchSelection ctx i labels before out next trace)
    (root : selected.rule = rule_lower_3277) :
    Nonempty (TableCalls ctx i labels before out next) := by
  have count : (program.rulesOf T.lower_branch.id).length = 8 := by
    rw [show T.lower_branch.id = 687 from rfl,data_program.r687]; rfl
  have bound := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+20 := ⟨selected.matchFuel-20,by omega⟩
  have matched := selected.matchedRun
  have rhs := selected.rhsRun
  rw [root,fuelEq] at matched
  rw [root] at rhs
  have hp := data_program
  cases hp
  isel_inv [*,rule_lower_3277,sem_ctor,sem_extract,sem_unData,ext_jump_table_targets_iff,
    jump_table_size,targets_jt_space,u32_into_u64] at matched rhs
  isel_destruct
  subst_vars
  repeat (isel_inv_simp [ext_jump_table_targets_iff,jump_table_size,targets_jt_space,u32_into_u64] at * <;>
    isel_destruct <;> subst_vars)
  obtain ⟨envEq⟩ : Nonempty (selected.env = _) := ⟨‹_›⟩
  generalize selected.env = env at *
  subst envEq
  simp only [Array.getElem?_setIfInBounds,Array.size_setIfInBounds,Array.size_replicate,
    Array.getElem?_replicate] at *
  simp only [Nat.reduceLT,Nat.reduceEqDiff,ite_true,ite_false,Option.some.injEq,reduceCtorEq] at *
  isel_destruct
  subst_vars
  simp only [jump_table_size,targets_jt_space] at *
  isel_destruct
  subst_vars
  simp only [u32_into_u64] at *
  isel_destruct
  subst_vars
  have islandCall := ‹ApplyInternal _ _ _ _ 46 669 _ _ _ _›
  obtain ⟨islandState,rfl⟩ := island_builder (by omega) islandCall
  have sideCall := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  rw [space_cast] at sideCall
  obtain ⟨mi,decoded,sideState,_⟩ := side_effect_emits (by omega) sideCall
  rw [ofV_emitIsland] at decoded
  cases decoded
  have extendCall := ‹ApplyInternal _ _ _ _ 27 556 _ _ _ _›
  have implCall := ‹ApplyInternal _ _ _ _ 13 670 _ _ _ _›
  have matchedEq := ‹selected.matched = before›
  simp only [Prod.eta] at implCall
  exact ⟨{
    source := _
    sourceData := ⟨_,_,‹ctx.insts[i]? = some _›,(‹V.data 152 4 _ = _›).symm⟩
    default := _
    table := _
    labels_eq := rfl
    island := _
    islandEq := by rw [sideState]; simp only [islandState,matchedEq]
    extended := _
    ridx := _
    extendFuel := _
    implFuel := _
    finalTrace := _
    extendEnough := by omega
    implEnough := by omega
    extendRun := extendCall
    implRun := implCall }⟩

/-- The source of the calls of a real `br_table x` slot is `x`. -/
theorem TableCalls.source_of_slot {ctx : Ctx} {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : TableCalls ctx i labels before out next) {x : Nat}
    (slot : ctx.insts[i]? = some ⟨tableData x,[],[],none⟩) : calls.source = .value x := by
  obtain ⟨info,tableOp,found,data⟩ := calls.sourceData
  rw [slot] at found
  cases found
  simp only [tableData,V.data.injEq,List.cons.injEq,true_and] at data
  exact data.1.symm

/-- **A real named `br_table` terminator derives its table calls.** The rule is derived
(`table_selected`) and the source of the calls is the index `x`. -/
theorem table_named_calls {ctx : Ctx} {i x : Nat} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨tableData x,[],[],none⟩)
    {before next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels] before = .ok (some out,next,trace)) :
    ∃ calls : TableCalls ctx i labels before out next,calls.source = .value x := by
  obtain ⟨selected⟩ := stock_named_branch_selection run
  obtain ⟨calls⟩ := table_selected_calls selected (table_selected slot selected)
  exact ⟨calls,calls.source_of_slot slot⟩

/-- The exact code of a `br_table` on the index register `r` with default `d` and table `ts`,
whose two temporaries are the fresh registers `n` and `n+1`: the island, the bound check and the
dispatch. -/
def tableCode (d : Label) (ts : List Label) (r : Reg) (n : Nat) : List MInst :=
  [.emitIsland (4*(8+ts.length)),.aluRRImm12 .subS .size32 .xzr r ⟨ts.length,false⟩,
    .jtSequence d ts r (.vreg n .int) (.vreg (n+1) .int)]

/-- The code-generation state after the code `tableCode d ts r st.nextVreg` from `st`. -/
def tableState (st : LState) (d : Label) (ts : List Label) (r : Reg) : LState :=
  ((((st.emit (.emitIsland (4*(8+ts.length)))).fresh .int).2.fresh .int).2.emit
    (.aluRRImm12 .subS .size32 .xzr r ⟨ts.length,false⟩)).emit
    (.jtSequence d ts r (.vreg st.nextVreg .int) (.vreg (st.nextVreg+1) .int))

theorem tableState_emitted (st : LState) (d : Label) (ts : List Label) (r : Reg) :
    (tableState st d ts r).emitted = st.emitted ++ (tableCode d ts r st.nextVreg).toArray := by
  simp only [tableState,tableCode,LState.emit,LState.fresh]
  apply Array.ext'
  simp

theorem tableState_nextVreg (st : LState) (d : Label) (ts : List Label) (r : Reg) :
    (tableState st d ts r).nextVreg = st.nextVreg+2 := by
  simp only [tableState,LState.emit,LState.fresh]

/-- **The emission of a `br_table` on an `i32` index with fewer than 4096 targets.** The index
passes through `put_in_reg_zext32` as the register `r` of `x` (`x` is marked demanded), and the
dispatch helper takes its immediate rule: the code is exactly `tableCode`, with the next two fresh
registers as temporaries. -/
theorem TableCalls.code {ctx : Ctx} {i : Nat} {labels : List Label} {before next : State} {out : V}
    (calls : TableCalls ctx i labels before out next) {x : Nat} (source : calls.source = .value x)
    (typeX : ctx.valueType? x = some (.int 32)) (small : calls.table.length < 4096) :
    ∃ r,ctx.valueReg? x = some r ∧ DemandAllowed ctx before x ∧
      calls.extended.1 = {before.mark x with
        base := before.base.emit (.emitIsland (4*(8+calls.table.length)))} ∧
      next.base = tableState before.base calls.default calls.table r := by
  have extendRun := calls.extendRun
  rw [source] at extendRun
  obtain ⟨t,typed,safe,rx,mapped,form⟩ := ScalarShift.stock_zext32_out data_program rfl calls.extendEnough extendRun
  rw [typeX] at typed
  cases typed
  rcases form with ⟨_,output,state⟩ | ⟨notPass,_⟩
  · have implRun := calls.implRun
    rw [output] at implRun
    have legacy := impl_call implRun
    have code := legacy_impl_small data_program rfl calls.implEnough small legacy
    rw [state,calls.islandEq] at code
    rw [calls.islandEq] at state safe
    exact ⟨rx,mapped,safe,state,code⟩
  · exact absurd (by simp) notPass

/-- **A real named `br_table` on an `i32` index with fewer than 4096 targets emits exactly
`tableCode`.** The labels are the default followed by the table, `r` is the register of `x`, `x` is
marked demanded, and the frontier grows by the two temporaries. -/
theorem table_named_code {ctx : Ctx} {i x : Nat} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨tableData x,[],[],none⟩)
    (typeX : ctx.valueType? x = some (.int 32)) (small : labels.length ≤ 4096)
    {before next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels] before = .ok (some out,next,trace)) :
    ∃ d ts r,labels = d :: ts ∧ ctx.valueReg? x = some r ∧ DemandAllowed ctx before x ∧
      next.base = tableState before.base d ts r ∧
      next.base.emitted = before.base.emitted ++ (tableCode d ts r before.base.nextVreg).toArray ∧
      next.base.nextVreg = before.base.nextVreg+2 := by
  obtain ⟨calls,source⟩ := table_named_calls slot run
  have short : calls.table.length < 4096 := by
    have equal := congrArg List.length calls.labels_eq
    simp only [List.length_cons] at equal
    omega
  obtain ⟨r,mapped,safe,_,code⟩ := calls.code source typeX short
  refine ⟨calls.default,calls.table,r,calls.labels_eq,mapped,safe,code,?_,?_⟩
  · rw [code]; exact tableState_emitted _ _ _ _
  · rw [code]; exact tableState_nextVreg _ _ _ _

end Backend.Stock.Proof.TableBranch
