import FV.Backend.Proof.IselCtlTbz
import FV.Backend.Proof.StockConditionalTargets
import FV.Backend.Proof.IselCtlBrTable

namespace Backend.Stock.Proof.BranchHelperTargets
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 ConditionalTargets
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


private theorem project_call {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
    {fuel ty t : Nat} (member : t ∈ helperIds) {args : List V}
    {st next : State × Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) cfg fuel ty t args st out next) :
    ApplyInternal program (Backend.sem ctx) cfg fuel ty t args (st.1.base,st.2) out (next.1.base,next.2) := by
  have projected := (evaluation_scoped_restate program (Backend.sem ctx) cfg hc State.base
    (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
    (fun t => t ∈ helperIds) (scope ctx) (fun _ _ _ => rfl) (fuel+1)).term
      ty t args member st.1 st.2
  change projectResult State.base ((applyTerm program (Stock.sem ctx) cfg (fuel+1) ty t args).run st) =
    (applyTerm program (Backend.sem ctx) cfg (fuel+1) ty t args).run (st.1.base,st.2) at projected
  unfold ApplyInternal at run ⊢
  rw [run] at projected
  exact projected.symm

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


private theorem decode_bit {zero : Bool} {a b : Label} {r bit : V} {m : MInst}
    (run : MInst.ofV (.data 58 119 [.data 94 (if zero then 0 else 1) [],.label a,.label b,r,bit]) = some m) :
    m.isTerminator = true ∧ m.targets = [a,b] := by
  have normal : MInst.ofV (.data 58 119 [.data 94 (if zero then 0 else 1) [],.label a,.label b,r,bit]) =
      (do let rn ← r.reg?; let n ← bit.nat?; pure (.testBitAndBranch (if zero then .z else .nz) a b rn n)) := by
    cases zero <;> rfl
  rw [normal] at run
  cases hr : r.reg? with
  | none => simp [hr] at run
  | some rn =>
    cases hb : bit.nat? with
    | none => simp [hr,hb] at run
    | some n =>
      simp only [hr,hb,bind,Option.bind,pure,Option.some.injEq] at run
      cases run
      exact ⟨rfl,rfl⟩

/-- Both actual test-bit builders followed by actual side-effect emission end
in a terminator with the original labels, for arbitrary successful operands. -/
theorem stock_test_bit_emitted_targets {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
    (zero : Bool) {fuel emitFuel : Nat} (enough : 100 ≤ fuel) (emitEnough : 30 ≤ emitFuel)
    {r bit descriptor out : V} {a b : Label} {st middle next : State × Array RuleId}
    (construct : ApplyInternal program (Stock.sem ctx) cfg fuel 46 (if zero then 668 else 667)
      [.label a,.label b,r,bit] st descriptor middle)
    (emit : ApplyInternal program (Stock.sem ctx) cfg emitFuel 13 242 [descriptor] middle out next) :
    ∃ last,next.1.base.emitted.back? = some last ∧ last.isTerminator = true ∧ last.targets = [a,b] := by
  have legacy := project_call hc (show (if zero then 668 else 667) ∈ helperIds from by cases zero <;> decide) construct
  have descriptorEq : descriptor = .data 46 0 [.data 58 119
      [.data 94 (if zero then 0 else 1) [],.label a,.label b,r,bit]] := by
    cases zero
    · exact (tbnz_inst_ok data_program hc (n := fuel) (by omega) legacy).2
    · exact (tbz_inst_ok data_program hc (n := fuel) (by omega) legacy).2
  have emitted := project_call hc (by decide : 242 ∈ helperIds) emit
  rw [descriptorEq] at emitted
  obtain ⟨last,decoded,state,_⟩ := emit_side_effect_inst_ok data_program hc (n := emitFuel) emitEnough emitted
  simp only at state
  obtain ⟨ends,targets⟩ := decode_bit decoded
  exact ⟨last,by rw [state]; simp [LState.emit],ends,targets⟩

private theorem decode_table {d : Label} {ts : List Label} {r t1 t2 : V} {m : MInst}
    (run : MInst.ofV (.data 58 128 [.label d,.labels ts,r,t1,t2]) = some m) :
    m.isTerminator = true ∧ m.targets = d :: ts := by
  change (do let rn ← r.reg?; let a ← t1.reg?; let b ← t2.reg?; pure (MInst.jtSequence d ts rn a b)) = some m at run
  cases hr : r.reg? with
  | none => simp [hr] at run
  | some rn =>
    cases ha : t1.reg? with
    | none => simp [hr,ha] at run
    | some a =>
      cases hb : t2.reg? with
      | none => simp [hr,ha,hb] at run
      | some b =>
        simp only [hr,ha,hb,bind,Option.bind,pure,Option.some.injEq] at run
        cases run
        exact ⟨rfl,rfl⟩

private theorem legacy_table_targets {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 300 ≤ fuel) {k r : V}
    {d : Label} {ts : List Label} {st next : LState × Array RuleId} {out : V}
    (run : ApplyInternal p (Backend.sem ctx) cfg fuel 13 670 [k,r,.label d,.labels ts] st out next) :
    ∃ last,next.1.emitted.back? = some last ∧ last.isTerminator = true ∧ last.targets = d :: ts := by
  have kJ := fun n (hn : 30 ≤ n) r d ts s v s' h => jt_sequence_ok hp (ctx := ctx) hc (n := n)
    (r := r) (d := d) (ts := ts) (s := s) (v := v) (s' := s') hn h
  have kW := fun n (hn : 40 ≤ n) flags ci s v s' h => flags_last hp (ctx := ctx) hc (fuel := n)
    (flags := flags) (ci := ci) (st := s) (out := v) (next := s') hn h
  have kE := fun n (hn : 30 ≤ n) last raw s v s' shape h => legacy_emit_last hp (ctx := ctx) hc (fuel := n)
    (last := last) (raw := raw) (st := s) (out := v) (next := s') hn shape h
  isel_split hp hc run 670
  all_goals
    brif_inv [*,rule_inst_5450,rule_inst_5454] at hm he
    have jt := ‹ApplyInternal _ _ _ _ 49 662 _ _ _ _›
    obtain ⟨_,rfl⟩ := kJ _ (by omega) _ _ _ _ _ _ jt
    have combine := ‹ApplyInternal _ _ _ _ 46 256 _ _ _ _›
    have shape := kW _ (by omega) _ _ _ _ _ combine
    have emit := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨last,decoded,back⟩ := kE _ (by omega) _ _ _ _ _ shape emit
    obtain ⟨ends,targets⟩ := decode_table decoded
    exact ⟨last,back,ends,targets⟩

/-- Successful actual table dispatch ends in a decoded terminator whose targets
are exactly default followed by table labels. No index value/range certificate
is required for this structural fact. -/
theorem stock_table_impl_targets {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
    {fuel : Nat} (enough : 300 ≤ fuel) {k r : V} {d : Label} {ts : List Label}
    {st next : State × Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) cfg fuel 13 670 [k,r,.label d,.labels ts] st out next) :
    ∃ last,next.1.base.emitted.back? = some last ∧ last.isTerminator = true ∧ last.targets = d :: ts := by
  exact legacy_table_targets data_program hc enough (project_call hc (by decide : 670 ∈ helperIds) run)

end Backend.Stock.Proof.BranchHelperTargets
