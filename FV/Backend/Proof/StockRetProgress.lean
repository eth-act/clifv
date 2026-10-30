import FV.Backend.Proof.StockLowerArgsFail
import FV.Backend.Proof.StockPrgContext
import FV.Backend.Proof.StockReturnRootCalls

/-!
# Progress of Stock's `lower` run on a `return`

The return rule 1037 calls Stock's own `gen_return`, so the guarded projection does not transport
the whole `lower` run of a `return` slot. It transports the rule selection only: every rule of
`lower` either has `if-let`s in scope or cannot match the return data (the diverging rules other
than 1037 by their primary opcode). The baseline progress analysis gives a successful baseline run
on the Stock terminator context (`stock_ret_backend`), so the baseline selection succeeds; its rule
is the return rule (`lower_term_nomatch`, the trap rule by its format), and Stock's selection
agrees. Stock's return helper then runs to completion (`stock_lower_return_call`).
-/

namespace Backend.Stock.Proof.LowerProjection
open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 Backend.Stock.Proof
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The `return` data of a block's terminator, with the ABI's `sret` pointer. -/
abbrev retData (f : Clif.Function) (xs : List Nat) : V :=
  instDataV "MultiAry" [opcodeV "Return", .values (xs ++ sretRet f)]

theorem retData_eq (f : Clif.Function) (xs : List Nat) :
    retData f xs = .data 152 18 [.data 151 7 [], .values (xs ++ sretRet f)] := rfl

section Backend
open Backend.Proof.Prg

/-- **The baseline `lower` run of a `return` on the Stock terminator context returns.** -/
theorem stock_ret_backend {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st : State}
    (hb : Stock.buildCtx f = .ok (ctx,ranges,st)) (hdom : dominatedB f = true)
    (hs : lowerScopeB f = true) (hw : extendsWidenB f = true) (hin : iselInB f = true)
    (hdrv : driverInB f = true) {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {B : Clif.Block} (hB : B ∈ f.blocks) {xs : List Nat} (hret : B.term = .ret xs)
    (regs : List Reg × List Reg) (s : LState) :
    ∃ w s' tr, Backend.runTerm { termCtx ctx ti (retData f xs) with tryRegs := regs } "lower"
      [.inst ti] s = .ok (some w, s', tr) := by
  obtain ⟨original, st0, hold, -, view⟩ := buildCtx_source hb
  have hP := stock_pinv_termCtx (stock_pinv hb hdom hs hw hin) hph (retData f xs) regs
  have hself : ({ termCtx ctx ti (retData f xs) with tryRegs := regs } : Ctx).insts[ti]? =
      some ⟨retData f xs, [], [], none⟩ := termCtx_insts_self hph _
  have hA : ∀ x ∈ xs ++ sretRet f,
      γ f { termCtx ctx ti (retData f xs) with tryRegs := regs } aV (.value x) := by
    intro x hx
    refine γ_aV hP.ctxInv ?_
    have typed := termArgs_typed hold hdom hB (x := x) (by rw [hret]; simpa [abiTerm, Driver.termArgs] using hx)
    show ((ctx.valTy[x]?).join).isSome
    rw [view.valTy]
    exact typed
  have hTI := termIsel_of hin hB
  rw [hret] at hTI
  have hv : xs.length = f.sig.returns.length := by simpa [termIselB] using hTI
  have h8 : f.sig.returns.length ≤ 8 := by
    simp only [driverInB, Bool.and_eq_true, decide_eq_true_eq] at hdrv; exact hdrv.1.2
  have hm := ret_len hv h8
  have hq : (TId.lower, [termInst VIdx.InstructionData.MultiAry [opc VIdx.Opcode.Return,
      .vals (List.replicate (xs ++ sretRet f).length aV)]]) ∈ termRoots := by
    dsimp only [termRoots]; iterate 3 apply List.mem_append_left
    exact List.mem_map.2 ⟨_, List.mem_range.2 (by omega), rfl⟩
  have hinst : ∀ k fs, γ f { termCtx ctx ti (retData f xs) with tryRegs := regs } (idat k fs)
      (retData f xs) → γ f { termCtx ctx ti (retData f xs) with tryRegs := regs } (termInst k fs)
        (.inst ti) :=
    fun k fs h => γ_inst hself (γ_ty_mem (by simp)) h (by simp)
  have hγ : γL f { termCtx ctx ti (retData f xs) with tryRegs := regs }
      [termInst VIdx.InstructionData.MultiAry [opc VIdx.Opcode.Return,
        .vals (List.replicate (xs ++ sretRet f).length aV)]] [.inst ti] :=
    γL_cons' (hinst _ _ (γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl))
      (γL_cons' (γ_vals (γL_rep hA)) γL_nil')))) γL_nil'
  obtain ⟨e, he, hos, hfu⟩ := termRoot_entry hq
  obtain ⟨w, s', tr, hrun, -⟩ := root_run (model_of hP) (handOk hP rfl prgTab) prgTab_ok
    program_termByName_lower he hos hfu hγ s
  exact ⟨w, s', tr, hrun⟩

end Backend

set_option maxRecDepth 100000 in
/-- Every diverging rule of `lower` other than one without `if-let`s has a primary opcode other
than `Return`. -/
theorem lower_ret_scope : (program.rulesOf 686).all (fun r => !lowerDiverging.contains r.id ||
    r.iflets.isEmpty || (match sourceRuleOpcode program r with
      | some c => c != 7
      | none => false)) = true := by
  rw [data_program.r686]
  decide +kernel

/-- Rule selection of `lower` on a `return` slot is in the guarded scope. -/
theorem ret_rules_scoped (ctx : Ctx) {ti : Nat} {ys : List Nat}
    (slot : ctx.insts[ti]? = some ⟨.data 152 18 [.data 151 7 [], .values ys], [], [], none⟩) :
    ∀ r ∈ program.rulesOf 686, IfLetsScoped (fun t => t ∉ disallowed) r.iflets ∨
      ArgsFail program (Backend.sem ctx) r [.inst ti] := by
  intro r hr
  have h := List.all_eq_true.mp lower_rules_avoid r hr
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · have k := List.all_eq_true.mp lower_ret_scope r hr
    simp only [h, Bool.not_true, Bool.false_or, Bool.or_eq_true, List.isEmpty_iff] at k
    rcases k with k | k
    · refine .inl ?_
      rw [k]
      intro il hil
      cases hil
    · cases hc : sourceRuleOpcode program r with
      | none => rw [hc] at k; cases k
      | some c =>
        rw [hc] at k
        have ne : c ≠ 7 := by simpa using k
        exact .inr (argsFail_of_opcode hc slot rfl (Ne.symm ne))
  · exact .inl (scoped_of_calls h).1

private theorem trap_nomatch_ret {ctx : Ctx} {ti : Nat} {ys : List Nat}
    (slot : ctx.insts[ti]? = some ⟨.data 152 18 [.data 151 7 [], .values ys], [], [], none⟩)
    {fuel : Nat} {s s' : LState × Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Backend.sem ctx) {} fuel rule_lower_2237 [.inst ti]).run s =
      .ok (some env, s')) : False := by
  obtain ⟨term, lookup, kind⟩ := fmtKinds_program (2473 - 2447) (by decide)
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨env0, args, -⟩ := matchRule_some_inv matched
    have format : ruleFmt rule_lower_2237 = some 2473 := rfl
    unfold ruleFmt at format
    split at format
    · rename_i q qs shape
      rw [shape] at args
      obtain ⟨env1, head, -⟩ := matchArgs_cons_inv args
      obtain ⟨info, fs, source, data⟩ := rootFmt_match_k data_program format lookup kind head
      rw [slot] at source
      cases source
      cases data
    · cases format

/-- The baseline selection on a `return` slot that succeeds selects the return rule. -/
private theorem ret_selected {ctx : Ctx} {ti : Nat} {ys : List Nat}
    (slot : ctx.insts[ti]? = some ⟨.data 152 18 [.data 151 7 [], .values ys], [], [], none⟩)
    {n : Nat} {s s' : LState × Array RuleId} {r : Rule} {env : Isle.Interp.Env V}
    (selected : (selectRule program (Backend.sem ctx) {} n T.lower (program.rulesOf 686) [.inst ti]).run s =
      .ok (some (r, env), s')) : r = rule_lower_2574 := by
  obtain ⟨member, m, -, matched⟩ := selectRule_some rfl selected
  cases root : termRootRule r with
  | false =>
    exact False.elim (lower_term_nomatch (t := .ret ys) rfl (termData_ret ys) slot member root _ _ _ _
      matched)
  | true =>
    simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at root
    rcases root with trap | ret
    · have eq := eq_of_mem_of_id lower_ids_nodup member mem_lower_2237 (by rw [trap]; rfl)
      subst eq
      exact False.elim (trap_nomatch_ret slot matched)
    · exact eq_of_mem_of_id lower_ids_nodup member mem_lower_2574 (by rw [ret]; rfl)

/-- The return rule's right-hand side runs Stock's return helper. -/
private theorem ret_rhs (ctx : Ctx) {ys : List Nat} {st : State} {rs ps : List Reg}
    (safe : ∀ x ∈ ys, DemandAllowed ctx st x) (mapped : ys.mapM ctx.valueReg? = some rs)
    (pins : returnPins ctx.func rs.length = some ps) :
    (evalExpr program (Stock.sem ctx) {} 999999 rule_lower_2574.rhs (returnRootEnv ys)).run (st, #[]) =
      .ok (some (.regsVec []), { ys.foldl State.mark st with
        base := (ys.foldl State.mark st).base.emit (.rets (rs.zip ps)) },
        #[].push rule_prelude_lower_1493.id) := by
  have call : (applyTerm program (Stock.sem ctx) {} 999998 25 294 [.values ys]).run (st, #[]) =
      .ok (some (.regsVec []), { ys.foldl State.mark st with
        base := (ys.foldl State.mark st).base.emit (.rets (rs.zip ps)) },
        #[].push rule_prelude_lower_1493.id) :=
    stock_lower_return_call data_program ctx (cfg := {}) rfl ys rs ps st #[] 999938 safe mapped pins
  have get0 : (returnRootEnv ys)[0]? = some (some (.values ys)) := rfl
  rw [show rule_lower_2574.rhs = .term 25 294 [.var 19 0] from rfl]
  isel_eval [call, get0]

/-- **Stock `lower` progress on a `return`.** From a state without a sunk instruction, Stock's
`lower` run of a `return` slot with mapped, pinned requests returns no registers and emits the
return. -/
theorem stock_runTerm_ret_ok (ctx : Ctx) {ti : Nat} {ys : List Nat}
    (slot : ctx.insts[ti]? = some ⟨.data 152 18 [.data 151 7 [], .values ys], [], [], none⟩)
    {st : State} (hst : NoSunk st)
    (hb : ∃ w s' tr, Backend.runTerm ctx "lower" [.inst ti] st.base = .ok (some w, s', tr))
    {rs ps : List Reg} (mapped : ys.mapM ctx.valueReg? = some rs)
    (pins : returnPins ctx.func rs.length = some ps) :
    ∃ tr, Stock.runTerm ctx "lower" [.inst ti] st = .ok (some (.regsVec []),
      { ys.foldl State.mark st with
        base := (ys.foldl State.mark st).base.emit (.rets (rs.zip ps)) }, tr) := by
  obtain ⟨w, s', tr, hb⟩ := hb
  have hfuel : ({} : Config).fuel = 999999 + 1 := rfl
  have hid : T.lower.id = 686 := rfl
  unfold Backend.runTerm Interp.run at hb
  rw [program_termByName_lower, hfuel] at hb
  dsimp only at hb
  rw [hid] at hb
  cases hrunB : (applyTerm program (Backend.sem ctx) {} (999999 + 1) T.lower.ret 686 [.inst ti]).run
      (st.base, #[]) with
  | error e => rw [hrunB] at hb; cases hb
  | ok a =>
  obtain ⟨v, s2, tr2⟩ := a
  rw [hrunB] at hb
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, -, -⟩ := hb
  rw [applyTerm_internal_run data_program.t686 term_686_kind rfl] at hrunB
  cases hselB : (selectRule program (Backend.sem ctx) {} 999999 T.lower (program.rulesOf 686)
      [.inst ti]).run (st.base, #[]) with
  | error e => rw [hselB] at hrunB; cases hrunB
  | ok q =>
  obtain ⟨sel, s1⟩ := q
  cases sel with
  | none =>
    rw [hselB] at hrunB
    simp only [M.except_ok_bind] at hrunB
    revert hrunB
    split <;> simp [pure, StateT.pure, StateT.run, throw, throwThe, MonadExceptOf.throw,
      StateT.lift, Except.pure]
  | some pair =>
  obtain ⟨r, env⟩ := pair
  have chosen := ret_selected slot hselB
  subst chosen
  -- Stock's selection agrees with the baseline's.
  have proj := selectRule_restate_inv program (Backend.sem ctx) {} rfl State.base NoSunk
    (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
    (fun t => t ∉ disallowed) (stock_scope ctx) (fun _ _ _ => rfl) 999999 T.lower
    (ret_rules_scoped ctx slot)
  obtain ⟨agree, -⟩ := proj st #[] hst
  rw [hselB] at agree
  cases hselS : (selectRule program ((Backend.sem ctx).restate (Stock.externCtor ctx)
      (fun t v st => Backend.externExtract ctx t v st.base)) {} 999999 T.lower (program.rulesOf 686)
      [.inst ti]).run (st, #[]) with
  | error e => rw [hselS] at agree; cases agree
  | ok b =>
  obtain ⟨selS, st1, tr1⟩ := b
  rw [hselS] at agree
  simp only [projectResult, Except.ok.injEq, Prod.mk.injEq] at agree
  obtain ⟨rfl, -, -⟩ := agree
  -- The return rule matched from the start state, so the selection keeps it.
  obtain ⟨-, m, enough, matchedS⟩ := selectRule_some rfl hselS
  have count : (program.rulesOf 686).length = 517 := by rw [data_program.r686]; rfl
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [← stock_sem_restate, stock_return_root_match data_program ctx slot st #[] k] at matchedS
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at matchedS
  obtain ⟨rfl, rfl, rfl⟩ := matchedS
  -- Stock's return helper.
  have safe : ∀ x ∈ ys, DemandAllowed ctx st x := fun x _ i _ => hst i
  have rhs := ret_rhs ctx safe mapped pins
  rw [stock_sem_restate] at rhs
  have hrunS : (applyTerm program ((Backend.sem ctx).restate (Stock.externCtor ctx)
      (fun t v st => Backend.externExtract ctx t v st.base)) {} (999999 + 1) T.lower.ret 686
      [.inst ti]).run (st, #[]) = .ok (some (.regsVec []), { ys.foldl State.mark st with
        base := (ys.foldl State.mark st).base.emit (.rets (rs.zip ps)) },
        (#[].push rule_prelude_lower_1493.id).push rule_lower_2574.id) := by
    rw [applyTerm_internal_run data_program.t686 term_686_kind rfl, hselS]
    simp only [M.except_ok_bind, M.run_bind, rhs]
    rfl
  refine ⟨((#[].push rule_prelude_lower_1493.id).push rule_lower_2574.id).toList, ?_⟩
  unfold Stock.runTerm Interp.run
  rw [program_termByName_lower, hfuel]
  dsimp only
  rw [hid, stock_sem_restate, hrunS]
  rfl

end Backend.Stock.Proof.LowerProjection
