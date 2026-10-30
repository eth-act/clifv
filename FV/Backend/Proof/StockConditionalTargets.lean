import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.StockBranchHelperProjection
import FV.Backend.Proof.IselCtlBrif
import FV.Backend.Proof.IselScopedProjection

namespace Backend.Stock.Proof.ConditionalTargets
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private def helperIds : List Nat := [164, 166, 169, 175, 181, 185, 201, 235, 242, 243, 251, 254, 256, 305, 318, 319, 320, 321, 327, 329, 349, 350, 351, 352, 356, 358, 359, 360, 362, 390, 391, 426, 497, 498, 501, 528, 553, 554, 661, 662, 663, 664, 665, 666, 667, 668, 670, 715, 722, 1787, 1788, 1789, 1791, 1799, 1800, 1802, 1803, 1820, 1822, 1823, 1844, 1851, 1935, 1936, 1937, 1941, 1946, 1964, 1966, 1972, 1989, 1990, 2028, 2029, 2030, 2031, 2037, 2038, 2235]
private def ruleCalls (r : Rule) : List Nat := r.iflets.flatMap (fun il => exprCalls il.rhs) ++ exprCalls r.rhs
private def checkTerm (ids : List Nat) (id : Nat) : Bool :=
  match termOf program id with
  | .error _ => false
  | .ok term => (!(revisedCtors.contains term.id) || term.id == TId.opportunistic_def) &&
      (program.rulesOf id).all (fun r => (ruleCalls r).all (ids.contains ·))

section Certificate
attribute [local semireducible] Isle.Aarch64.program
private theorem checked : helperIds.all (checkTerm helperIds) = true := by decide +kernel
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

private theorem scope (ctx : Ctx) :
    ProjectionScope program (Backend.sem ctx) State.base (Stock.externCtor ctx) (fun t => t ∈ helperIds) := by
  have valid : ∀ t ∈ helperIds,∀ term,termOf program t = .ok term →
      (!(revisedCtors.contains term.id) || term.id == TId.opportunistic_def) = true ∧
      (program.rulesOf t).all (fun r => (ruleCalls r).all (helperIds.contains ·)) = true := by
    intro t member term lookup
    have fact := List.all_eq_true.mp checked t member
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
    have contains : ∀ u ∈ ruleCalls r,u ∈ helperIds := by
      intro u inside
      have yes := List.all_eq_true.mp calls u inside
      simpa using yes
    constructor
    · intro il inside u called
      exact contains u (List.mem_append_left _ (List.mem_flatMap.mpr ⟨il,inside,called⟩))
    · intro u called
      exact contains u (List.mem_append_right _ called)

/-- A descriptor with a specified final instruction; the earlier instructions
in the descriptor and the already-emitted machine prefix are unrestricted. -/
def RawLast (last out : V) : Prop := out = .data 46 0 [last] ∨
  (∃ first,out = .data 46 1 [first,last]) ∨ (∃ first second,out = .data 46 2 [first,second,last])

private theorem flags_last {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 40 ≤ fuel) {flags ci : V}
    {st next : LState × Array RuleId} {out : V}
    (run : ApplyInternal p (Backend.sem ctx) cfg fuel 46 256 [flags,.data 49 0 [ci]] st out next) :
    RawLast ci out := by
  isel_split hp hc run 256
  all_goals
    isel_inv [*,rule_prelude_lower_1000,rule_prelude_lower_1006,rule_prelude_lower_1016,
      rule_prelude_lower_1023,rule_prelude_lower_1030,rule_prelude_lower_1035,
      rule_prelude_lower_1040,rule_prelude_lower_1045,rule_prelude_lower_1050] at hm he <;>
    isel_destruct <;> subst_vars <;> first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl ⟨_,rfl⟩)
    | exact Or.inr (Or.inr ⟨_,_,rfl⟩)

private theorem legacy_encoded {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 100 ≤ fuel) {raw : V} {a b : Label}
    {st next : LState × Array RuleId} {out : V}
    (run : ApplyInternal p (Backend.sem ctx) cfg fuel 46 722 [raw,.label a,.label b] st out next) :
    ∃ condition,RawLast (.data 58 118 [.label a,.label b,condition]) out := by
  have kZ := fun n (hn : 30 ≤ n) r sz a b s v s' h => a64_br_zero_ok hp (ctx := ctx) hc (n := n)
    (r := r) (sz := sz) (a := a) (b := b) (s := s) (v := v) (s' := s') hn h
  have kN := fun n (hn : 30 ≤ n) r sz a b s v s' h => a64_br_not_zero_ok hp (ctx := ctx) hc (n := n)
    (r := r) (sz := sz) (a := a) (b := b) (s := s) (v := v) (s' := s') hn h
  have kC := fun n (hn : 30 ≤ n) c a b s v s' h => a64_br_cond_ok hp (ctx := ctx) hc (n := n)
    (c := c) (a := a) (b := b) (s := s) (v := v) (s' := s') hn h
  have kW := fun n (hn : 40 ≤ n) flags ci s v s' h => flags_last hp (ctx := ctx) hc (fuel := n)
    (flags := flags) (ci := ci) (st := s) (out := v) (next := s') hn h
  isel_split hp hc run 722
  · brif_inv [*,rule_lower_3236] at hm he
    have call := ‹ApplyInternal _ _ _ _ 46 664 _ _ _ _›
    obtain ⟨_,rfl⟩ := kZ _ (by omega) _ _ _ _ _ _ _ call
    exact ⟨_,Or.inl rfl⟩
  · brif_inv [*,rule_lower_3238] at hm he
    have call := ‹ApplyInternal _ _ _ _ 46 665 _ _ _ _›
    obtain ⟨_,rfl⟩ := kN _ (by omega) _ _ _ _ _ _ _ call
    exact ⟨_,Or.inl rfl⟩
  · brif_inv [*,rule_lower_3240] at hm he
    have call := ‹ApplyInternal _ _ _ _ 49 663 _ _ _ _›
    obtain ⟨_,rfl⟩ := kC _ (by omega) _ _ _ _ _ _ call
    have combine := ‹ApplyInternal _ _ _ _ 46 256 _ _ _ _›
    have last := kW _ (by omega) _ _ _ _ _ combine
    exact ⟨_,last⟩
  · brif_inv [*,rule_lower_3247] at hm he
    have call := ‹ApplyInternal _ _ _ _ 46 665 _ _ _ _›
    obtain ⟨_,rfl⟩ := kN _ (by omega) _ _ _ _ _ _ _ call
    exact ⟨_,Or.inl rfl⟩

/-- Every successful actual conditional branch builder retains the original
taken/not-taken labels in its final raw instruction, for arbitrary condition
results, including combined-flag fallback forms. -/
theorem stock_conditional_descriptor_targets {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 100 ≤ fuel) {raw : V} {a b : Label}
    {st next : State × Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) cfg fuel 46 722 [raw,.label a,.label b] st out next) :
    ∃ condition,RawLast (.data 58 118 [.label a,.label b,condition]) out := by
  have projected := BranchHelpers.stock_br_cond_result_projects ctx cfg hc (fuel+1)
    [raw,.label a,.label b] st.1 st.2
  unfold ApplyInternal at run
  rw [run] at projected
  exact legacy_encoded data_program hc enough projected.symm

private theorem decode_cond {a b : Label} {condition : V} {m : MInst}
    (run : MInst.ofV (.data 58 118 [.label a,.label b,condition]) = some m) :
    m.isTerminator = true ∧ m.targets = [a,b] := by
  have normal : MInst.ofV (.data 58 118 [.label a,.label b,condition]) =
      (fun k => MInst.condBr a b k) <$> condition.condBrKind? := by
    change (condition.condBrKind? >>= fun k => some (MInst.condBr a b k)) = _
    cases condition.condBrKind? <;> rfl
  rw [normal] at run
  cases parsed : condition.condBrKind? with
  | none => simp [parsed] at run
  | some k =>
    rw [parsed] at run
    change some (MInst.condBr a b k) = some m at run
    cases run
    exact ⟨rfl,rfl⟩

private theorem emit3 {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 30 ≤ fuel) {i j k : V}
    {st next : LState × Array RuleId} {out : V}
    (run : ApplyInternal p (Backend.sem ctx) cfg fuel 13 242 [.data 46 2 [i,j,k]] st out next) :
    ∃ m1 m2 m3,next.1 = ((st.1.emit m1).emit m2).emit m3 ∧ MInst.ofV k = some m3 := by
  isel_split hp hc run 242
  · isel_inv [*,rule_prelude_lower_522] at hm
  · isel_inv [*,rule_prelude_lower_524] at hm
  · isel_inv [*,rule_prelude_lower_527] at hm he
    exact ⟨_,_,_,rfl,by assumption⟩

private theorem legacy_emit_last {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 30 ≤ fuel) {last raw : V}
    (shape : RawLast last raw) {st next : LState × Array RuleId} {out : V}
    (run : ApplyInternal p (Backend.sem ctx) cfg fuel 13 242 [raw] st out next) :
    ∃ m,MInst.ofV last = some m ∧ next.1.emitted.back? = some m := by
  rcases shape with rfl | ⟨first,rfl⟩ | ⟨first,second,rfl⟩
  · obtain ⟨m,decoded,state,_⟩ := emit_side_effect_inst_ok hp hc enough run
    exact ⟨m,decoded,by rw [state]; simp [LState.emit]⟩
  · obtain ⟨m1,m2,state,_,decoded⟩ := emit_side_effect_inst2_ok hp hc enough run
    exact ⟨m2,decoded,by rw [state]; simp [LState.emit]⟩
  · obtain ⟨m1,m2,m3,state,decoded⟩ := emit3 hp hc enough run
    exact ⟨m3,decoded,by rw [state]; simp [LState.emit]⟩

/-- Successful actual conditional construction and emission ends in a decoded
terminator with the exact original two labels. Earlier helper/emitter code may
form an unrestricted prefix; no CondShape/source-value certificate is
required to establish this structural fact. -/
theorem stock_conditional_emitted_targets {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel emitFuel : Nat}
    (enough : 100 ≤ fuel) (emitEnough : 30 ≤ emitFuel) {raw descriptor out : V} {a b : Label}
    {st middle next : State × Array RuleId}
    (construct : ApplyInternal program (Stock.sem ctx) cfg fuel 46 722 [raw,.label a,.label b] st descriptor middle)
    (emit : ApplyInternal program (Stock.sem ctx) cfg emitFuel 13 242 [descriptor] middle out next) :
    ∃ last,next.1.base.emitted.back? = some last ∧ last.isTerminator = true ∧ last.targets = [a,b] := by
  obtain ⟨condition,shape⟩ := stock_conditional_descriptor_targets hc enough construct
  have projected := (evaluation_scoped_restate program (Backend.sem ctx) cfg hc State.base
    (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
    (fun t => t ∈ helperIds) (scope ctx) (fun _ _ _ => rfl) (emitFuel+1)).term
      13 242 [descriptor] (by decide) middle.1 middle.2
  change projectResult State.base ((applyTerm program (Stock.sem ctx) cfg (emitFuel+1) 13 242 [descriptor]).run middle) =
    (applyTerm program (Backend.sem ctx) cfg (emitFuel+1) 13 242 [descriptor]).run (middle.1.base,middle.2) at projected
  unfold ApplyInternal at emit
  rw [emit] at projected
  obtain ⟨last,decoded,back⟩ := legacy_emit_last data_program hc emitEnough shape projected.symm
  obtain ⟨ends,targets⟩ := decode_cond decoded
  exact ⟨last,back,ends,targets⟩

end Backend.Stock.Proof.ConditionalTargets
