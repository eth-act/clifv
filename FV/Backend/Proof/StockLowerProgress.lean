import FV.Backend.Proof.StockLowerArgsFail
import FV.Backend.Proof.StockPrgContext

/-!
# Progress of Stock's `lower` runs on scalar statements

On the Stock statement context of a block (`termCtx` with the terminator data and `try_call`
registers), every statement of a function in the original input scope whose opcode names rule out
loads, calls, splats and returns has a Stock `lower` run that returns its result registers, from
every scheduling state without a sunk instruction, and the run keeps that invariant. The baseline
progress analysis supplies the run (`stmtProg`), and the guarded projection transports it.
-/

namespace Backend.Stock.Proof.LowerProjection
open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Prg Isle Isle.Interp Isle.Aarch64
  Backend.Stock.Proof
set_option autoImplicit false

/-- Opcode and format names of a statement that rule out the diverging rules of `lower`. -/
structure ScalarNames (cl : Clif.Inst) : Prop where
  noLoad : (instNames cl).1 ≠ "LoadNoOffset" ∧ (instNames cl).1 ≠ "Load"
  names : ∀ n ∈ ["Call","CallIndirect","Splat","Return"], (instNames cl).2 ≠ n
  extend : (instNames cl).2 = "Uextend" ∨ (instNames cl).2 = "Sextend" →
    ∃ sg ty x, cl = .extend (ScalarCast.extendOp sg) ty x

/-- **Stock `lower` progress on statements.** -/
theorem stock_runTerm_lower_ok {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : State} (hb : Stock.buildCtx f = .ok (ctx,ranges,st0)) (hdom : dominatedB f = true)
    (hs : lowerScopeB f = true) (hw : extendsWidenB f = true) (hin : iselInB f = true)
    (scalar : ∀ cl, InstOf f cl → ScalarNames cl)
    {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V)
    (regs : List Reg × List Reg) {i : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : ({ termCtx ctx ti data with tryRegs := regs } : Ctx).insts[i]? = some info)
    (clif : info.clif = some inst) {st : State} (hst : NoSunk st) :
    ∃ rss st' tr, Stock.runTerm { termCtx ctx ti data with tryRegs := regs } "lower" [.inst i] st =
        .ok (some (.regsVec rss), st', tr) ∧
      (info.results ≠ [] → rss.length = info.results.length ∧ ∀ rs ∈ rss, rs.length = 1) ∧
      NoSunk st' := by
  have hP : PInv f { termCtx ctx ti data with tryRegs := regs } :=
    stock_pinv_termCtx (stock_pinv hb hdom hs hw hin) hph data regs
  have mapped : MappedCtxInv f { termCtx ctx ti data with tryRegs := regs } :=
    ((buildCtx_mappedInv (lowerScope_of hs) hb).termCtx hph data).withTryRegs regs
  obtain ⟨rss, s', tr, hrun, hshape⟩ := stmtProg hP i info inst st.base source clif
  have noLoad : ∀ (j : Nat) (info : IInfo) (cl : Clif.Inst),
      ({ termCtx ctx ti data with tryRegs := regs } : Ctx).insts[j]? = some info → info.clif = some cl →
      (instNames cl).1 ≠ "LoadNoOffset" ∧ (instNames cl).1 ≠ "Load" :=
    fun j info cl hj hc => (scalar cl (hP.clifOf j info cl hj hc)).noLoad
  have hcl := scalar inst (hP.clifOf i info inst source clif)
  have hfail := lower_diverging_args_fail mapped noLoad source clif hcl.names hcl.extend
  obtain ⟨st', hstock, -, hkeep⟩ := stock_runTerm_lower_of_backend _ hst hfail hrun
  exact ⟨rss, st', tr, hstock, hshape, hkeep⟩
private def progressFixture : Clif.Function := {
  name := "stock_lower_progress"
  sig := { params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0, .i64), (1, .i64)], body := [⟨[2], .binary .iadd .i64 0 1⟩], term := .ret [2] }] }

private def progressChecks : Bool :=
  dominatedB progressFixture && lowerScopeB progressFixture && extendsWidenB progressFixture &&
    Prg.iselInB progressFixture &&
  match Stock.buildCtx progressFixture with
  | .error _ => false
  | .ok (ctx, ranges, _) =>
    let ti := ranges[0]!.2 - 1
    ti != 0 && (match ctx.insts[ti]? with
      | some ⟨.op .unit, [], [], none⟩ => true
      | _ => false) &&
    match ctx.insts[0]? with
    | some info => info.clif == some (.binary .iadd .i64 0 1)
    | none => false

-- witness: native_decide (one fixed context build and its scope checks only)
private theorem progressChecks_true : progressChecks = true := by native_decide

private theorem fixture_names : ∀ cl, InstOf progressFixture cl → ScalarNames cl := by
  intro cl ⟨B, hB, s, hs, hcl⟩
  simp only [progressFixture, List.mem_cons, List.not_mem_nil, or_false] at hB
  subst hB
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  subst hcl
  refine ⟨by decide, ?_, ?_⟩
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> decide
  · intro h
    exfalso
    rcases h with h | h <;> simp [instNames, binaryOpcode] at h

/-- Non-vacuity: on a real scalar function, Stock's `lower` run of its statement succeeds from a
state without a sunk instruction, through `stock_runTerm_lower_ok`. -/
theorem stock_runTerm_lower_ok_witness :
    ∃ (ctx : Ctx) (ti : Nat) (data : V) (rss : List (List Reg)) (st st' : State) (tr : List RuleId),
      Stock.runTerm { termCtx ctx ti data with tryRegs := ([], []) } "lower" [.inst 0] st =
        .ok (some (.regsVec rss), st', tr) := by
  have h := progressChecks_true
  unfold progressChecks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hdom, hs⟩, hw⟩, hin⟩, h⟩ := h
  cases hb : Stock.buildCtx progressFixture with
  | error message => rw [hb] at h; cases h
  | ok triple =>
    obtain ⟨ctx, ranges, st0⟩ := triple
    rw [hb] at h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hne, hph'⟩, h⟩ := h
    have hph : ctx.insts[ranges[0]!.2 - 1]? = some ⟨.op .unit, [], [], none⟩ := by
      revert hph'
      split <;> intro hph'
      · assumption
      · cases hph'
    cases hi : ctx.insts[0]? with
    | none => rw [hi] at h; cases h
    | some info =>
      rw [hi] at h
      have hclif : info.clif = some (.binary .iadd .i64 0 1) := by simpa using h
      have hsource : ({ termCtx ctx (ranges[0]!.2 - 1) (.op .unit) with tryRegs := ([], []) } : Ctx).insts[0]? =
          some info := by
        show (termCtx ctx (ranges[0]!.2 - 1) (.op .unit)).insts[0]? = some info
        rw [termCtx_insts_ne (Ne.symm hne)]
        exact hi
      have hst : NoSunk { st0 with sunk := #[] } := by intro i; simp
      obtain ⟨rss, st', tr, hrun, -, -⟩ := stock_runTerm_lower_ok hb hdom hs hw hin fixture_names hph
        (.op .unit) ([], []) hsource hclif hst
      exact ⟨ctx, _, _, rss, _, st', tr, hrun⟩

end Backend.Stock.Proof.LowerProjection
