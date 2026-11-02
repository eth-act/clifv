import FV.Backend.Proof.KillHypT
import FV.Backend.Proof.KillDriver
import FV.Backend.Proof.IselFlowT
import FV.Backend.Proof.IselExclTF

set_option Elab.async false

/-!
# Killed vregs of the ISLE lowering over the typed scope: `killRunsHypT`

The killed-vreg analysis (`KillDriver.lean`) is a uniform invariant of the ISLE interpreter over
**every** root rule of `lower` and `lower_branch` of the exported program (`killRootS`,
`killRootB`; no closure restriction), so it holds over float-capable contexts unchanged. The
context invariant was used for two rule exclusions only, which hold over `CtxInvT`:

* `nop`'s rule 587 matches only an instruction without results (`nop_match_resultsT`, by
  `pinned_namesT`);
* the I128 rules 636/637 never match a statement (`stmt_killT` takes this as a premise; on the
  typed scope it is `lower_nonroot_nomatchT`).

A `try_call`'s exact defs over the typed scope: `KillTryDefsT.lean` (`tryDefsExactT`).

Nothing here depends on which float roots are proven: a new root rule needs no new proof.
-/

namespace Backend.Proof.Kill

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Cov Backend.Proof.Spill
  Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

/-! ## Statements -/

set_option maxRecDepth 100000 in
/-- `nop`'s rule 587 matches only an instruction without results (over `CtxInvT`). -/
theorem nop_match_resultsT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {rl : Rule} (hrl : rl ∈ program.rulesOf TId.lower) (h587 : rl.id = 587) {m : Nat}
    {s0 s1 : LState × Array RuleId} {env : Isle.Interp.Env V}
    (hm : (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 = .ok (some env, s1)) :
    info.results = [] := by
  have hop := List.all_eq_true.mp lower_ops rl hrl
  simp only [h587, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hop
  have hn := pinned_namesT hctx hi hc hop.1 kind_nullAry kind_nop (by decide) hm
  rw [variantNames_Nop] at hn
  have hnop := Driver.instNames_nop (Option.some.inj hn).symm
  subst hnop
  obtain ⟨tys, hty, -, hlen⟩ := hctx.resTys ii info .nop hi hc
  simp [Clif.Inst.resultTypes] at hty
  subst hty
  exact List.eq_nil_of_length_eq_zero hlen

/-- **A statement's `lower` run** over a float-capable context, given that the I128 rules
636/637 do not match it. -/
theorem stmt_killT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (htr : ctx.tryRegs = ([], [])) (hvr : ValRegK ctx) (hd : DataK ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hX : ∀ rl ∈ program.rulesOf TId.lower, (rl.id = 636 ∨ rl.id = 637) →
      ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1))
    {s : LState} {out : Option V} {s' : LState} {tr : List RuleId} (hN : ctx.valDef.size ≤ s.nextVreg)
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) :
    RunKill ctx.valDef.size s.nextVreg s s' ∧
      (info.results ≠ [] → OutKill ctx.valDef.size s.nextVreg s s' out) := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      ((∀ u ∈ ruleTerms rl, u ∈ killTabS) ∧ ∀ q ∈ ruleTys rl, killCall q.1 q.2) ∨
        (rl ∈ program.rulesOf TId.lower ∧ rl.id = 587) ∨
        ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠
          .ok (some env, s1) := by
    intro rl hrl
    by_cases h587 : rl.id = 587
    · exact .inr (.inl ⟨hrl, h587⟩)
    by_cases h636 : rl.id = 636 ∨ rl.id = 637
    · exact .inr (.inr (hX rl hrl h636))
    · exact .inl (killRootS rl hrl h587 (fun h => h636 (.inl h)) (fun h => h636 (.inr h)))
  obtain ⟨hIs, -, hv⟩ := uRoot (sModel ctx s.nextVreg s hvr hd htr) rfl (fun _ _ => info.results = [])
    (fun rl => rl ∈ program.rulesOf TId.lower ∧ rl.id = 587) data_program.t686 term_686_kind rfl
    hrules
    (fun rl _ ⟨hrl, h587⟩ k m s1 tr1 env s2 tr2 r s3 tr3 _ _ _ _ hIs hm he => by
      obtain ⟨hs, -⟩ := Cov.matchRule_noIfLets (iflets_587 hrl h587) hm
      cases hs
      obtain ⟨rfl, -⟩ := nop_rhs Cov.totality hrl h587 _ rfl _ _ _ _ _ _ _ he
      exact ⟨hIs, rsK_refl _, fun _ _ => nop_match_resultsT hctx hi hc hrl h587 hm⟩)
    (fun v hv => by simp only [List.mem_singleton] at hv; subst hv; exact kp_inst ii)
    (isK_start hN (Nat.le_refl _)) happ
  refine ⟨runKill_of hIs, fun hres => outKill_of fun v hv' => ?_⟩
  rcases hv v hv' with hp | hq
  · exact hp
  · exact absurd hq hres

/-- **`KillRunsHyp` over the float scope.** -/
theorem killRunsHypTF : KillRunsHypTF := by
  intro f ctx ranges st0 _ hs _ hb
  have hctx : CtxInvT f ctx := ctxInvT_ofF hs hb
  have hsc : InstScopeTF ctx := (ctxSpec_of hb).instScopeTF hs.subsetTF
  have hx : CallsE f ctx := callsE_of_externs hs.externsE ctx
  have htr := (ctxFacts_of hb).tryRegs
  have hvr := valRegK_of_build hb
  have hd := dataK_of_build hb
  exact ⟨fun ii info inst s out s' tr hi hc hN h =>
      stmt_killT hctx htr hvr hd hi hc
        (fun rl hrl hid => lower_nonroot_nomatchTF_calls hctx hsc hx hi hc hrl
          (by rcases hid with h | h <;> rw [h] <;> decide) {}) hN h,
    fun ti t data targets s out s' tr _ hph hty hdat hN h =>
      term_kill htr hvr hd hph hty hdat hN h,
    fun ti t et data sig items lo trs st1 targets out s' tr _ _ _ _ hdat he hlo htr h =>
      try_kill hvr hd hdat he hlo htr h⟩

/-- **`KillRunsHyp` over the typed scope.** -/
theorem killRunsHypT : KillRunsHypT := killRunsHypTF.toT

end Backend.Proof.Kill
