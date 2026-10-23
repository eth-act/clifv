import FV.Backend.Proof.StockSinkRuleSyntax
import FV.Backend.Proof.StockSinkFrame

/-! In scalar/division-only contexts every generated sinking rule is
unmatchable. This is an internal installed-data invariant, not a new checker. -/
namespace Backend.Stock.Proof.SinkRules
open Backend.Proof Isle Isle.Interp Isle.Aarch64 Isle.Interp.RuleFrame
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

def NoLoadData (ctx : Ctx) : Prop :=
  ∀ (i : Nat) (info : IInfo), ctx.insts[i]? = some info → ∀ (fmt : Nat) (fields : List V),
    fmt = 16 ∨ fmt = 17 →
    (Backend.sem ctx).unData 152 info.data ≠ some (fmt,fields)

private def Rejects (ctx : Ctx) (st : State) (pat : Pattern) : Prop :=
  ∀ v env bound, matchPat program (Stock.sem ctx) st pat v env ≠ .ok (some bound)

private theorem rejects_args {ctx : Ctx} {st : State} {ps : List Pattern}
    {q : Pattern} (member : q ∈ ps) (reject : Rejects ctx st q)
    {vs : List V} {env bound : Isle.Interp.Env V}
    (run : matchArgs program (Stock.sem ctx) st ps vs env = .ok (some bound)) : False := by
  induction ps generalizing vs env with
  | nil => cases member
  | cons p ps ih =>
    cases vs with
    | nil => cases run
    | cons v vs =>
      obtain ⟨middle, head, tail⟩ := matchArgs_cons_inv run
      rcases List.mem_cons.mp member with same | later
      · subst p; exact reject _ _ _ head
      · exact ih later tail

private theorem rejects_bind {ctx : Ctx} {st : State} {ty k : Nat} {pat : Pattern}
    (reject : Rejects ctx st pat) : Rejects ctx st (.bind ty k pat) := by
  intro v env bound run
  obtain ⟨_, inner⟩ := matchPat_bind_inv run
  exact reject _ _ _ inner

private theorem rejects_extract {ctx : Ctx} {st : State} {ty t : Nat}
    {ps : List Pattern} {q : Pattern} {term : Term} {flags : TermFlags}
    {ctor : Option Ctor} {name : String} {infallible : Bool}
    (lookup : termOf program t = .ok term)
    (kind : term.kind = .decl flags ctor (some (.external name infallible)))
    (single : flags.isMulti = false) (member : q ∈ ps)
    (reject : Rejects ctx st q) : Rejects ctx st (.term ty t ps) := by
  intro v env bound run
  obtain ⟨_, _, args⟩ := matchPat_extract_inv lookup kind single run
  exact rejects_args member reject args

private theorem rejects_enum {ctx : Ctx} {st : State} {ty t fmt : Nat}
    {ps : List Pattern} {q : Pattern} {term : Term}
    (lookup : termOf program t = .ok term) (kind : term.kind = .enumVariant fmt)
    (member : q ∈ ps) (reject : Rejects ctx st q) : Rejects ctx st (.term ty t ps) := by
  intro v env bound run
  obtain ⟨_, _, args⟩ := matchPat_enum_inv lookup kind run
  exact rejects_args member reject args

private theorem inst_data_input {ctx : Ctx} {st : State} {v : V} {fields : List V}
    (run : (Stock.sem ctx).extract T.inst_data_value v st = .ok fields) :
    ∃ i, v = .inst i := by
  cases v with
  | inst i => exact ⟨i,rfl⟩
  | _ => simp [Stock.sem, Backend.externExtract, T.inst_data_value, Backend.tyPred] at run

private theorem rejects_load {ctx : Ctx} {st : State} {tyPat : Pattern}
    {t fmt : Nat} {ps : List Pattern} {term : Term}
    (noLoads : NoLoadData ctx) (lookup : termOf program t = .ok term)
    (kind : term.kind = .enumVariant fmt) (load : fmt = 16 ∨ fmt = 17) :
    Rejects ctx st (.term 18 209 [tyPat,.term 152 t ps]) := by
  intro v env bound run
  obtain ⟨fields, extracted, args⟩ :=
    matchPat_extract_inv data_program.t209 term_209_kind rfl run
  obtain ⟨i,rfl⟩ := inst_data_input extracted
  change (match ctx.insts[i]? with
    | some info => ExtResult.ok [V.ty (info.resTys.head?.getD .invalid),info.data]
    | none => ExtResult.unmodeled s!"inst {i}") = .ok fields at extracted
  cases found : ctx.insts[i]? with
  | none => rw [found] at extracted; cases extracted
  | some info =>
    rw [found] at extracted
    cases extracted
    obtain ⟨middle, _, args⟩ := matchArgs_cons_inv args
    obtain ⟨_, data, _⟩ := matchArgs_cons_inv args
    obtain ⟨fields, decoded, _⟩ := matchPat_enum_inv lookup kind data
    exact noLoads i info found fmt fields load decoded

private theorem rule_inst_3905_no_match {ctx : Ctx} {st : State}
    (noLoads : NoLoadData ctx) {vs : List V} {env bound : Isle.Interp.Env V}
    (run : matchArgs program (Stock.sem ctx) st rule_inst_3905.args vs env = .ok (some bound)) : False := by
  apply rejects_args (q := (.bind 18 1 (.term 18 209 [(.wildcard 14), (.term 152 2464 [(.term 151 2442 []), (.bind 15 0 (.wildcard 15)), (.wildcard 137)])]))) (by simp [rule_inst_3905]) ?_ run
  apply rejects_bind
  exact rejects_load noLoads data_program.t2464 rfl (Or.inr rfl)

private theorem rule_inst_4203_no_match {ctx : Ctx} {st : State}
    (noLoads : NoLoadData ctx) {vs : List V} {env bound : Isle.Interp.Env V}
    (run : matchArgs program (Stock.sem ctx) st rule_inst_4203.args vs env = .ok (some bound)) : False := by
  apply rejects_args (q := (.bind 18 3 (.term 18 209 [(.wildcard 14), (.term 152 2463 [(.term 151 2313 []), (.bind 15 1 (.wildcard 15)), (.wildcard 137), (.term 138 4 [(.bind 9 2 (.wildcard 9))])])]))) (by simp [rule_inst_4203]) ?_ run
  apply rejects_bind
  exact rejects_load noLoads data_program.t2463 rfl (Or.inl rfl)

private theorem rule_lower_1300_no_match {ctx : Ctx} {st : State}
    (noLoads : NoLoadData ctx) {vs : List V} {env bound : Isle.Interp.Env V}
    (run : matchArgs program (Stock.sem ctx) st rule_lower_1300.args vs env = .ok (some bound)) : False := by
  apply rejects_args (q := (.term 18 209 [(.term 14 113 [(.wildcard 14)]), (.term 152 2476 [(.term 151 2425 []), (.bind 15 4 (.term 15 1 [(.term 18 209 [(.bind 14 0 (.wildcard 14)), (.term 152 2463 [(.term 151 2313 []), (.bind 15 1 (.wildcard 15)), (.term 137 103 [(.bind 142 2 (.wildcard 142))]), (.bind 138 3 (.wildcard 138))])])]))])])) (by simp [rule_lower_1300]) ?_ run
  apply rejects_extract (q := (.term 152 2476 [(.term 151 2425 []), (.bind 15 4 (.term 15 1 [(.term 18 209 [(.bind 14 0 (.wildcard 14)), (.term 152 2463 [(.term 151 2313 []), (.bind 15 1 (.wildcard 15)), (.term 137 103 [(.bind 142 2 (.wildcard 142))]), (.bind 138 3 (.wildcard 138))])])]))])) data_program.t209 term_209_kind rfl (by simp)
  apply rejects_enum (q := (.bind 15 4 (.term 15 1 [(.term 18 209 [(.bind 14 0 (.wildcard 14)), (.term 152 2463 [(.term 151 2313 []), (.bind 15 1 (.wildcard 15)), (.term 137 103 [(.bind 142 2 (.wildcard 142))]), (.bind 138 3 (.wildcard 138))])])]))) data_program.t2476 rfl (by simp)
  apply rejects_bind
  apply rejects_extract (q := (.term 18 209 [(.bind 14 0 (.wildcard 14)), (.term 152 2463 [(.term 151 2313 []), (.bind 15 1 (.wildcard 15)), (.term 137 103 [(.bind 142 2 (.wildcard 142))]), (.bind 138 3 (.wildcard 138))])])) data_program.t1 term_1_kind rfl (by simp)
  exact rejects_load noLoads data_program.t2463 rfl (Or.inl rfl)

private theorem rule_lower_1359_no_match {ctx : Ctx} {st : State}
    (noLoads : NoLoadData ctx) {vs : List V} {env bound : Isle.Interp.Env V}
    (run : matchArgs program (Stock.sem ctx) st rule_lower_1359.args vs env = .ok (some bound)) : False := by
  apply rejects_args (q := (.term 18 209 [(.term 14 113 [(.wildcard 14)]), (.term 152 2476 [(.term 151 2426 []), (.bind 15 4 (.term 15 1 [(.term 18 209 [(.bind 14 0 (.wildcard 14)), (.term 152 2463 [(.term 151 2313 []), (.bind 15 1 (.wildcard 15)), (.term 137 103 [(.bind 142 2 (.wildcard 142))]), (.bind 138 3 (.wildcard 138))])])]))])])) (by simp [rule_lower_1359]) ?_ run
  apply rejects_extract (q := (.term 152 2476 [(.term 151 2426 []), (.bind 15 4 (.term 15 1 [(.term 18 209 [(.bind 14 0 (.wildcard 14)), (.term 152 2463 [(.term 151 2313 []), (.bind 15 1 (.wildcard 15)), (.term 137 103 [(.bind 142 2 (.wildcard 142))]), (.bind 138 3 (.wildcard 138))])])]))])) data_program.t209 term_209_kind rfl (by simp)
  apply rejects_enum (q := (.bind 15 4 (.term 15 1 [(.term 18 209 [(.bind 14 0 (.wildcard 14)), (.term 152 2463 [(.term 151 2313 []), (.bind 15 1 (.wildcard 15)), (.term 137 103 [(.bind 142 2 (.wildcard 142))]), (.bind 138 3 (.wildcard 138))])])]))) data_program.t2476 rfl (by simp)
  apply rejects_bind
  apply rejects_extract (q := (.term 18 209 [(.bind 14 0 (.wildcard 14)), (.term 152 2463 [(.term 151 2313 []), (.bind 15 1 (.wildcard 15)), (.term 137 103 [(.bind 142 2 (.wildcard 142))]), (.bind 138 3 (.wildcard 138))])])) data_program.t1 term_1_kind rfl (by simp)
  exact rejects_load noLoads data_program.t2463 rfl (Or.inl rfl)

private theorem exceptional_no_match {ctx : Ctx} (noLoads : NoLoadData ctx)
    {rule : Rule} (special : Exceptional rule) {n : Nat} {vs : List V}
    {st matched : State} {tr tr' : Array RuleId} {env : Isle.Interp.Env V}
    (run : (matchRule program (Stock.sem ctx) {} n rule vs).run (st,tr) =
      .ok (some env,matched,tr')) : False := by
  cases n with
  | zero => rw [matchRule.eq_1] at run; cases run
  | succ n =>
    obtain ⟨_, args, _⟩ := matchRule_some_inv run
    rcases special with rfl | rfl | rfl | rfl
    · exact rule_inst_3905_no_match noLoads args
    · exact rule_inst_4203_no_match noLoads args
    · exact rule_lower_1300_no_match noLoads args
    · exact rule_lower_1359_no_match noLoads args

/-- The original interpreter preserves every sunk bit in a context with no
installed load data. Internal rule calls are covered by the actual complete
generated table, rather than by a supplied successful-lowering certificate. -/
theorem no_load_frames {ctx : Ctx} (noLoads : NoLoadData ctx) :
    ∀ n, CtorFreeAt program (Stock.sem ctx) {} blocked
      (fun a b => b.sunk = a.sunk) n := by
  apply ctorFreeAt_inductive (p := program) (sem := Stock.sem ctx)
    (cfg := {}) (blocked := blocked) (R := fun a b => b.sunk = a.sunk) (fun _ => rfl)
    (fun _ _ _ first second => second.trans first)
    (special := Exceptional)
  · intro term vs st value next free run
    exact stock_ctor_noSink (by simpa [blocked] using free) run
  · rfl
  · intro t rule member
    exact rule_cases member
  · intro n frames rule special m vs env st tr matched trm out next tr' matchedRun rhsRun
    exact (exceptional_no_match noLoads special matchedRun).elim

/-- Successful actual helper evaluation cannot sink any instruction in a
load-free source context, whether or not its result is demanded. -/
theorem no_load_apply {ctx : Ctx} (noLoads : NoLoadData ctx)
    {n ty t : Nat} {vs : List V} {st next : State} {tr tr' : Array RuleId}
    {out : Option V} (notSink : termCtorFree program blocked t = true)
    (run : (applyTerm program (Stock.sem ctx) {} n ty t vs).run (st,tr) =
      .ok (out,next,tr')) : next.sunk = st.sunk :=
  (no_load_frames noLoads n).apply ty t vs st tr out next tr' notSink run

private theorem named_frame {ctx : Ctx} (noLoads : NoLoadData ctx)
    {name : String} {vs : List V} {st next : State} {out : Option V} {trace : List RuleId}
    (allowed : ∀ term, program.termByName? name = some term → termCtorFree program blocked term.id = true)
    (run : Stock.runTerm ctx name vs st = .ok (out,next,trace)) : next.sunk = st.sunk := by
  unfold Stock.runTerm at run
  cases executed : Isle.Interp.run program (Stock.sem ctx) {} name vs st with
  | error message => rw [executed] at run; cases run
  | ok result =>
    rw [executed] at run
    cases run
    unfold Isle.Interp.run at executed
    cases lookup : program.termByName? name with
    | none => simp only [lookup] at executed; cases executed
    | some term =>
      simp only [lookup] at executed
      cases call : (applyTerm program (Stock.sem ctx) {} (Config.fuel ({} : Config))
          term.ret term.id vs).run (st,#[]) with
      | error error => simp only [call, bind, Except.bind] at executed; cases executed
      | ok result =>
        obtain ⟨value,next,trace⟩ := result
        simp only [call, bind, Except.bind, pure, Except.pure] at executed
        cases executed
        exact no_load_apply noLoads (allowed term lookup) call

/-- The actual named statement/return helper retains the complete sunk table.
The term guard is derived from the generated `lower` lookup. -/
theorem no_load_lower {ctx : Ctx} (noLoads : NoLoadData ctx)
    {vs : List V} {st next : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" vs st = .ok (out,next,trace)) : next.sunk = st.sunk := by
  apply named_frame noLoads (name := "lower") ?_ run
  intro term lookup
  rw [program_termByName_lower] at lookup
  cases lookup
  rw [term_guard]
  decide +kernel

end Backend.Stock.Proof.SinkRules
