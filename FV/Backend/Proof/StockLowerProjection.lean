import FV.Backend.Proof.IselScopedProjectionInv
import FV.Backend.Proof.StockPureHelperTransport
import FV.Backend.Proof.IselPrgOfvSound
import FV.Backend.Proof.KillDriver
import FV.Backend.Proof.IselFlow

namespace Backend.Stock.Proof.LowerProjection
open Isle Isle.Interp Isle.Aarch64 Backend.Stock.Proof
set_option autoImplicit false

/-- The terms whose Stock semantics diverges from the baseline on reachable states, closed
upward: every internal term with a rule that calls one of them is listed too. -/
def disallowed : List Nat := [180,221,236,294,295,296,300,564,583,686,687]

/-- No instruction has been sunk into a later one. -/
def NoSunk (st : State) : Prop := ∀ i : Nat, st.sunk[i]! = false

private theorem foldl_mark_base (vs : List Nat) (st : State) : (vs.foldl State.mark st).base = st.base := by
  induction vs generalizing st with
  | nil => rfl
  | cons v vs ih => exact ih (st.mark v)

private theorem backend_opportunistic (ctx : Ctx) (t : Term) (h : t.id = TId.opportunistic_def)
    (a b : V) (s : LState) : Backend.externCtor ctx t [a, b] s = .ok (.op .unit, s) := by
  obtain ⟨id, name, targs, ret, kind, pos⟩ := t
  simp only at h
  subst h
  red_safe Backend.externCtor
  rfl

private theorem delegate_proj (ctx : Ctx) (t : Term) (args : List V) (s : State) :
    projectCtor State.base (match Backend.externCtor ctx t args s.base with
      | .ok (v, b) => ExtResult.ok (v, { s with base := b })
      | .fail => .fail
      | .unmodeled e => .unmodeled e) = Backend.externCtor ctx t args s.base := by
  cases Backend.externCtor ctx t args s.base <;> rfl

/-- On states without a sunk instruction, every allowed Stock constructor projects to the
baseline constructor. -/
theorem stock_ctor_agree (ctx : Ctx) (t : Term) (args : List V) (st : State)
    (hid : t.id ∉ disallowed) (hst : NoSunk st) :
    projectCtor State.base (Stock.externCtor ctx t args st) = Backend.externCtor ctx t args st.base := by
  by_cases hr : t.id ∈ revisedCtors
  · unfold Stock.externCtor
    split
    all_goals first
      | (exfalso; apply hid; simp [disallowed, *]; done)
      | skip
    case h_1 | h_2 | h_4 =>
      rename_i heq
      have hne : (t.id == TId.mark_value_used) = false := by rw [heq]; rfl
      dsimp only
      split
      · rename_i i _
        simp only [hst i, Bool.false_eq_true, ite_false, hne]
        exact delegate_proj ctx t _ (st.mark _)
      · simp only [hne, Bool.false_eq_true, ite_false]
        exact delegate_proj ctx t _ (st.mark _)
    case h_5 =>
      dsimp only
      have hany : ∀ (vs : List Nat), (vs.any fun v => Option.any (fun i => st.sunk[i]!) (ctx.defInst? v)) = false := by
        intro vs
        simp only [List.any_eq_false]
        intro v _
        cases ctx.defInst? v with
        | none => simp
        | some i => simp [hst i]
      simp only [hany, Bool.false_eq_true, ite_false]
      rw [← foldl_mark_base _ st]
      exact delegate_proj ctx t _ _
    case h_8 =>
      rename_i heq
      dsimp only
      rw [backend_opportunistic ctx t heq]
      split <;> rfl
    case h_12 => exact delegate_proj ctx t _ st
  · exact stock_ctor_unchanged ctx t args st hr
private theorem delegate_sunk (ctx : Ctx) (t : Term) (args : List V) (s : State) {v : V} {st' : State}
    (h : (match Backend.externCtor ctx t args s.base with
      | .ok (v, b) => ExtResult.ok (v, { s with base := b })
      | .fail => .fail
      | .unmodeled e => .unmodeled e) = .ok (v, st')) : st'.sunk = s.sunk := by
  cases hb : Backend.externCtor ctx t args s.base with
  | ok a =>
    rw [hb] at h
    simp only [ExtResult.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
  | fail => rw [hb] at h; cases h
  | unmodeled e => rw [hb] at h; cases h

private theorem foldl_mark_sunk (vs : List Nat) (st : State) : (vs.foldl State.mark st).sunk = st.sunk := by
  induction vs generalizing st with
  | nil => rfl
  | cons v vs ih => exact ih (st.mark v)

/-- An allowed Stock constructor never sinks an instruction. -/
theorem stock_ctor_sunk (ctx : Ctx) (t : Term) (args : List V) (st : State) {v : V} {st' : State}
    (hid : t.id ∉ disallowed) (h : Stock.externCtor ctx t args st = .ok (v, st')) : st'.sunk = st.sunk := by
  unfold Stock.externCtor at h
  split at h
  all_goals first
    | (exfalso; apply hid; simp [disallowed, *]; done)
    | skip
  all_goals dsimp only at h
  all_goals first
    | exact delegate_sunk ctx t _ st h
    | skip
  case h_1 | h_2 | h_4 =>
    split at h
    · split at h
      · cases h
      · split at h
        · simp only [ExtResult.ok.injEq, Prod.mk.injEq] at h; rw [← h.2]; rfl
        · split at h <;> first | (simp only [ExtResult.ok.injEq, Prod.mk.injEq] at h; rw [← h.2]; rfl) | cases h
    · split at h
      · simp only [ExtResult.ok.injEq, Prod.mk.injEq] at h; rw [← h.2]; rfl
      · split at h <;> first | (simp only [ExtResult.ok.injEq, Prod.mk.injEq] at h; rw [← h.2]; rfl) | cases h
  case h_5 =>
    split at h
    · cases h
    · split at h <;> first | (simp only [ExtResult.ok.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact foldl_mark_sunk _ st) | cases h
  case h_8 =>
    split at h <;> (simp only [ExtResult.ok.injEq, Prod.mk.injEq] at h; rw [← h.2])

end Backend.Stock.Proof.LowerProjection

namespace Backend.Stock.Proof.LowerProjection
open Isle Isle.Interp Isle.Aarch64 Backend.Stock.Proof Backend.Stock.Proof.PureHelper Backend.Proof Backend.Proof.Kill
set_option autoImplicit false

/-- The rules of `lower` that call a diverging term: extends and splats of a sunk load, calls,
indirect calls and returns. -/
def lowerDiverging : List Nat := [810,815,824,982,1031,1032,1033,1037]

set_option maxRecDepth 100000 in
/-- Kernel check: every rule of a term outside `disallowed` calls only terms outside it (one pass
over the rule table). -/
theorem rules_avoid : program.ruleLists.toList.zipIdx.all (fun (rs, t) => disallowed.contains t ||
    rs.all (fun r => (ruleCalls r).all (fun u => !disallowed.contains u))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Kernel check: the other rules of `lower` call only terms outside `disallowed`. -/
theorem lower_rules_avoid : (program.rulesOf 686).all (fun r => lowerDiverging.contains r.id ||
    (ruleCalls r).all (fun u => !disallowed.contains u)) = true := by
  decide +kernel

private theorem scoped_of_calls {r : Rule} (h : (ruleCalls r).all (fun u => !disallowed.contains u) = true) :
    RuleScoped (fun t => t ∉ disallowed) r := by
  have contains : ∀ u ∈ ruleCalls r, u ∉ disallowed := by
    intro u inside
    have := List.all_eq_true.mp h u inside
    simpa using this
  constructor
  · intro il inside u called
    exact contains u (List.mem_append_left _ (List.mem_flatMap.mpr ⟨il,inside,called⟩))
  · intro u called
    exact contains u (List.mem_append_right _ called)

theorem rule_scoped {t : Nat} (ht : t ∉ disallowed) {r : Rule} (hr : r ∈ program.rulesOf t) :
    RuleScoped (fun t => t ∉ disallowed) r := by
  unfold Program.rulesOf at hr
  cases hl : program.ruleLists[t]? with
  | none => rw [hl] at hr; cases hr
  | some rs =>
    rw [hl, Option.getD_some] at hr
    have hmem : (rs, t) ∈ program.ruleLists.toList.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList]
      exact hl
    have h := List.all_eq_true.mp rules_avoid (rs, t) hmem
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd (List.contains_iff_mem.mp h) ht
    · exact scoped_of_calls (List.all_eq_true.mp h r hr)

/-- The Stock embedding is the baseline embedding restated on the Stock state, with guarded
agreement of every allowed constructor. -/
theorem stock_scope (ctx : Ctx) :
    ProjectionScopeInv program (Backend.sem ctx) State.base NoSunk (Stock.externCtor ctx)
      (fun t => t ∉ disallowed) where
  agree t term ht hterm vs st hst := by
    have hid := termOf_id_eq hterm
    exact stock_ctor_agree ctx term vs st (by rw [hid]; exact ht) hst
  preserve t term ht hterm vs st v st' hst h := by
    have hid := termOf_id_eq hterm
    intro i
    rw [stock_ctor_sunk ctx term vs st (by rw [hid]; exact ht) h]
    exact hst i
  rules t term ht hterm flags ex hk vs r hr := .inl (rule_scoped ht hr)

theorem stock_sem_restate (ctx : Ctx) :
    Stock.sem ctx = (Backend.sem ctx).restate (Stock.externCtor ctx)
      (fun t v st => Backend.externExtract ctx t v st.base) := rfl

/-- Stock's `lower` run of an instruction equals the baseline run on the base state, with the
invariant kept, whenever every diverging rule of `lower` cannot match the instruction. -/
theorem stock_runTerm_lower_of_backend (ctx : Ctx) {i : Nat} {st : State} (hst : NoSunk st)
    (hfail : ∀ r ∈ program.rulesOf 686, r.id ∈ lowerDiverging →
      ArgsFail program (Backend.sem ctx) r [.inst i])
    {out : Option V} {s' : LState} {tr : List RuleId}
    (hb : Backend.runTerm ctx "lower" [.inst i] st.base = .ok (out, s', tr)) :
    ∃ st', Stock.runTerm ctx "lower" [.inst i] st = .ok (out, st', tr) ∧ st'.base = s' ∧ NoSunk st' := by
  have hrules : ∀ r ∈ program.rulesOf 686, RuleScoped (fun t => t ∉ disallowed) r ∨
      ArgsFail program (Backend.sem ctx) r [.inst i] := by
    intro r hr
    have h := List.all_eq_true.mp lower_rules_avoid r hr
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact .inr (hfail r hr (List.contains_iff_mem.mp h))
    · exact .inl (scoped_of_calls h)
  have proj := applyTerm_internal_restate_inv program (Backend.sem ctx) {} rfl State.base NoSunk
    (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base) (fun t => t ∉ disallowed)
    (stock_scope ctx) (fun _ _ _ => rfl) 999999 (ty := T.lower.ret) data_program.t686 term_686_kind hrules
  obtain ⟨agree, keep⟩ := proj st #[] hst
  have hfuel : ({} : Config).fuel = 999999 + 1 := rfl
  unfold Backend.runTerm Interp.run at hb
  have hid : T.lower.id = 686 := rfl
  rw [program_termByName_lower, hfuel] at hb
  dsimp only at hb
  rw [hid] at hb
  unfold Stock.runTerm Interp.run
  rw [program_termByName_lower, hfuel, stock_sem_restate]
  dsimp only
  rw [hid]
  cases hrun : (applyTerm program (Backend.sem ctx) {} (999999 + 1) T.lower.ret 686 [.inst i]).run
      (st.base, #[]) with
  | error e => rw [hrun] at hb; cases hb
  | ok a =>
    obtain ⟨v, s2, tr2⟩ := a
    rw [hrun] at hb
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl, rfl⟩ := hb
    rw [hrun] at agree
    cases hstock : (applyTerm program ((Backend.sem ctx).restate (Stock.externCtor ctx)
        (fun t v st => Backend.externExtract ctx t v st.base)) {} (999999 + 1) T.lower.ret 686
        [.inst i]).run (st, #[]) with
    | error e => rw [hstock] at agree; cases agree
    | ok b =>
      obtain ⟨v', st', tr'⟩ := b
      rw [hstock] at agree
      simp only [projectResult, Except.ok.injEq, Prod.mk.injEq] at agree
      obtain ⟨rfl, hbase, rfl⟩ := agree
      exact ⟨st', by simp only [bind, Except.bind, pure, Except.pure], hbase, keep _ _ _ hstock⟩
end Backend.Stock.Proof.LowerProjection
