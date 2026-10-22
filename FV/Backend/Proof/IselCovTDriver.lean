import FV.Backend.Proof.IselCovTModel
import FV.Backend.Proof.IselCovTTab
import FV.Backend.Proof.IselCovTCall
import FV.Backend.Proof.IselCovDriver

/-!
# Form coverage over float-capable contexts (typed V3): the driver's calls

The typed abstract interpretation (`soundAt` with `covModelT`, the table `covTabT` and its root
checks) applied to the driver's ISLE calls over a float-capable context (`CtxInvT`) whose
statements belong to the instruction families (`FamCover`):

* `stmt_covT`: a statement's `lower` emits covered instructions only, and with results its result
  registers are vregs, of the class of every result (`famOut`: the family's result classes, one
  class per family, `famTab_uniform`), or int vregs of a `call`/`call_indirect` (rules
  1031-1033, by hand: `out_callT`);
* `termCall_covT`: a terminator's `lower` (`return`/`trap`, input `c0`) or `lower_branch` (input
  the terminator's family, `termFam`);
* `tryCall_covT`: a `try_call`'s `lower_branch`.

`root_hand_varT` is `SoundAt.root` with a per-rule output and hand-checked result properties.
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (Clean CovSince LogicImmComplete IntOut CallInst kind_cases kind_int kind_float)
open Backend.Proof.Driver (covSince_refl lower_len)

set_option maxRecDepth 20000

section Root

variable {f : Clif.Function} {ctx : Ctx} {p : Program} {aext : TermId → AT → List AT}
  {actor : TermId → List AT → AT}
  {apre : TermId → List AT → Bool} {aOracle : TermId → List AT → Option AT}
  {md : CovModel aext actor apre aOracle p f ctx} {cfg : Config} {tab : Tab}

/-- **A root term whose rules pass `aRule` with a per-rule output `outOf rl`, or never match**:
the state invariant holds after the run, and the result is described by `out` (rules with
`outOf rl = out`) or has `P` (rules `Hand`, checked by hand). -/
theorem root_hand_varT (hc : cfg.checkOverlap = false) (sa : ∀ n, SoundAt md cfg tab n)
    {vs : List V} {Hand : Rule → Prop} {P : V → Prop} {outOf : Rule → AT}
    (hhand : ∀ rl, Hand rl → ∀ (m n : Nat) (s : LState) (tr : Array RuleId) (env : Isle.Interp.Env V)
      (s1 : LState × Array RuleId) (v : V) (s2 : LState) (tr2 : Array RuleId),
      1000 ≤ m → 1000 ≤ n →
      (matchRule p (sem ctx) cfg m rl vs).run (s, tr) = .ok (some env, s1) →
      (evalExpr p (sem ctx) cfg n rl.rhs env).run s1 = .ok (some v, (s2, tr2)) → P v)
    {ty : TypeId} {t : TermId} {term : Term} {flags : TermFlags} {ex : Option Extractor}
    {ins : List AT} {out : AT} {s : LState} {tr : Array RuleId} {r : Option V} {s' : LState}
    {tr' : Array RuleId} (ht : termOf p t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    (hrules : ∀ rl ∈ p.rulesOf t, (aRule p tab aext actor apre aOracle ins (outOf rl) rl = true ∧
      (outOf rl = out ∨ Hand rl)) ∨
      (∀ m s0 env s1, (matchRule p (sem ctx) cfg m rl vs).run s0 ≠ .ok (some env, s1)))
    (hins : Holds2 f ctx ins vs) (hIs : md.Is s) {n : Nat} (hn : 1002 + (p.rulesOf t).length ≤ n)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    md.Is s' ∧ ∀ v, r = some v → γ f ctx out v ∨ P v := by
  cases hm : flags.isMulti with
  | true =>
    rw [applyTerm.eq_2] at h
    obtain ⟨term', s1, h1, h2⟩ := bind_ok h
    obtain ⟨_, ht', he⟩ := liftM_ok h1
    rw [ht] at ht'; cases ht'; cases he
    rw [hk] at h2
    simp only [hm, ↓reduceIte] at h2
    exact (throw_ok h2).elim
  | false =>
  rw [applyTerm_internal_run ht hk hm] at h
  obtain ⟨⟨sel, ⟨s1, tr1⟩⟩, h1, h2⟩ := except_bind_eq_ok h
  cases sel with
  | none =>
    have := selectRule_none h1
    cases this
    simp only at h2
    split at h2
    · cases pure_ok h2; exact ⟨hIs, fun v hv => by cases hv⟩
    · exact (throw_ok h2).elim
  | some re =>
    obtain ⟨rl, env⟩ := re
    obtain ⟨hrl, m, hmn, hmatch⟩ := selectRule_some_lt hc h1
    simp only at h2
    obtain ⟨ev, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
    have hst : s' = s2 := by
      cases ev with
      | some w =>
        obtain ⟨u, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
        cases pure_ok h6
        cases pure_ok h5
        rfl
      | none => cases pure_ok h4; rfl
    have hres : ∀ v, r = some v → ev = some v := by
      intro v hv
      subst hv
      cases ev with
      | some w =>
        obtain ⟨u, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
        cases pure_ok h6
        rfl
      | none => cases pure_ok h4
    subst hst
    rcases hrules rl hrl with ⟨hok, hout⟩ | hno
    · obtain ⟨envs, hae, hall⟩ := aRule_inv hok
      obtain ⟨hIs1, aenv, haenv, he1⟩ := (sa m).mrule _ _ _ _ _ _ _ _ _ hae hins hIs hmatch
      obtain ⟨a, ha, hle⟩ := hall aenv haenv
      have he := (sa n).expr _ _ _ _ _ _ _ _ _ ha he1 hIs1 h3
      refine ⟨he.1, fun v hv => ?_⟩
      have hev := hres v hv
      subst hev
      rcases hout with ho | hhd
      · exact .inl (ho ▸ le_sound a (outOf rl) hle v (he.2 v rfl))
      · obtain ⟨-, m', hm', hmatch'⟩ := selectRule_some hc h1
        exact .inr (hhand rl hhd m' n s tr env _ v s2 tr2 (by omega) (by omega) hmatch' h3)
    · exact absurd hmatch (hno m _ _ _)

end Root

/-! ## Result classes -/

/-- Every family's result types are of one class. -/
theorem famTab_uniform : ∀ F ∈ famTab, ∀ t ∈ F.all, ∀ u ∈ F.all, t.valClass = u.valClass := by
  decide +kernel

theorem foldl_or_split {α : Type} (g : α → Nat) (k : Nat) : ∀ (l : List α) (m0 : Nat),
    l.foldl (fun m t => m ||| g t) m0 &&& k ≠ 0 → m0 &&& k ≠ 0 ∨ ∃ t ∈ l, g t &&& k ≠ 0
  | [], _, h => .inl h
  | a :: l, m0, h => by
    rw [List.foldl_cons] at h
    rcases foldl_or_split g k l _ h with h | ⟨t, ht, hg⟩
    · by_cases h1 : m0 &&& k = 0
      · right
        refine ⟨a, List.mem_cons_self, fun h2 => h ?_⟩
        apply Nat.eq_of_testBit_eq; intro i
        have e1 := congrArg (·.testBit i) h1
        have e2 := congrArg (·.testBit i) h2
        simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at e1 e2 ⊢
        cases hm : m0.testBit i <;> cases hg : (g a).testBit i <;> cases hk : k.testBit i <;>
          simp_all
      · exact .inl h1
    · exact .inr ⟨t, List.mem_cons_of_mem _ ht, hg⟩

/-- A register of a kind of `vcls ts` is a vreg of the class of a type of `ts`. -/
theorem vcls_kind {r : Reg} {ts : List CTy} (h : r.kind &&& vcls ts ≠ 0) :
    ∃ n c, r = .vreg n c ∧ ∃ t ∈ ts, t.valClass = c := by
  rw [Nat.and_comm] at h
  unfold vcls at h
  rcases foldl_or_split (fun t : CTy => match t.valClass with | .int => 1 | .float => 2) _ ts 0 h with
    h | ⟨t, ht, hg⟩
  · simp at h
  · rcases kind_cases r with hk | hk | hk | hk <;> rw [hk] at hg
    · obtain ⟨n, rfl⟩ := kind_int hk
      refine ⟨n, .int, rfl, t, ht, ?_⟩
      revert hg; cases t.valClass <;> decide
    · obtain ⟨n, rfl⟩ := kind_float hk
      refine ⟨n, .float, rfl, t, ht, ?_⟩
      revert hg; cases t.valClass <;> decide
    · exfalso; revert hg; cases t.valClass <;> decide
    · exfalso; revert hg; cases t.valClass <;> decide

/-- The class of a value of one of the types `ts`. -/
theorem valIn_class {ctx : Ctx} {x : Nat} {ts : List CTy} (h : ValIn ctx x ts) :
    ∃ t ∈ ts, valClassOf ctx x = t.valClass := by
  cases hty : ctx.valueType? x with
  | none =>
    obtain ⟨t, ht, hc⟩ := h.2 hty
    exact ⟨t, ht, by simp [valClassOf, hty, CTy.valClass, hc]⟩
  | some t => exact ⟨t, h.1 t hty, by simp [valClassOf, hty]⟩

theorem famTab_lt {i : Nat} {F : Fam} (h : famTab[i]? = some F) : i < famTab.length :=
  (List.getElem?_eq_some_iff.mp h).1

/-! ## The driver's ISLE calls -/

/-- The statement's family as the abstract input of `lower`. -/
theorem holds_famT {f : Clif.Function} {ctx : Ctx} {ii : Nat} {info : IInfo} {i : Nat} {F : Fam}
    (hi : ctx.insts[ii]? = some info) (hF : famTab[i]? = some F) (hok : FamOk ctx F info) :
    Holds2 f ctx [.inst [i]] [.inst ii] :=
  ⟨⟨ii, info, rfl, hi, i, List.mem_singleton_self _, F, hF, hok⟩, trivial⟩

set_option maxRecDepth 100000 in
/-- **A statement's lowering is covered** (typed): everything it emits is covered, and with
results its result registers are vregs of the class of every result, or int vregs of a call. -/
theorem stmt_covT (hLI : LogicImmComplete) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hx : f.externs.all (Compile.sigE ·.2.sig) = true) (hcl : Clean ctx) (hfam : FamCover ctx)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst) {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) :
    CovSince s s' ∧ ∀ rss, out = some (.regsVec rss) → info.results ≠ [] →
      ∀ rs ∈ rss, ∀ r ∈ rs, ∃ n c, r = .vreg n c ∧
        ((CallInst inst ∧ c = .int) ∨ ∀ x ∈ info.results, valClassOf ctx x = c) := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  obtain ⟨i, F, hF, hok⟩ := hfam ii info inst hi hc
  have hins := holds_famT (f := f) hi hF hok
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      (aRule program covTabT aext actor apre aOracle [.inst [i]] (stmtOut rl i) rl = true ∧
        (stmtOut rl i = famOut i ∨
          (rl ∈ program.rulesOf TId.lower ∧ (rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033)))) ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1)) := by
    intro rl hrl
    have hf := List.all_eq_true.mp (List.all_eq_true.mp covStmtT_ok rl hrl) i
      (List.mem_range.mpr (famTab_lt hF))
    refine .inl ⟨hf, ?_⟩
    by_cases hid : rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033
    · exact .inr ⟨hrl, hid⟩
    · left
      unfold stmtOut
      rw [if_neg]
      simpa only [Bool.or_eq_true, beq_iff_eq] using hid
  have hv := root_hand_varT (md := covModelT hLI hctx hcl hfam s) rfl
    (fun n => soundAt (md := covModelT hLI hctx hcl hfam s) (cfg := {}) (tab := covTabT)
      rfl covTabT_ok n)
    (Hand := fun rl => rl ∈ program.rulesOf TId.lower ∧ (rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033))
    (P := fun v => IntOut v ∧ CallInst inst)
    (fun rl ⟨hrl, hid⟩ _ _ _ _ _ _ _ _ _ hm hn hmatch heval =>
      Cov.out_callT hctx hx hi hc hrl hid rfl hm hn hmatch heval)
    data_program.t686 term_686_kind hrules hins (covSince_refl s) (n := 999999) lower_len happ
  refine ⟨hv.1, ?_⟩
  intro rss hout hres
  subst hout
  rcases hv.2 _ rfl with hγ | ⟨hI, hcall⟩
  · intro rs hrs r hr
    have hk := hγ.1 r (Driver.mem_regsVec hrs hr)
    have hall : F.all ≠ [] := by
      intro hnil
      obtain ⟨x, hx'⟩ := List.exists_mem_of_ne_nil _ hres
      have := hok.2.2.1 x hx'
      rw [hnil] at this
      cases hty : ctx.valueType? x with
      | none => obtain ⟨_, h1, _⟩ := this.2 hty; cases h1
      | some t => exact absurd (this.1 t hty) (by simp)
    have hfo : famOut i = .flat (vcls F.all) true := by
      unfold famOut
      rw [List.getD_eq_getElem?_getD, hF]
      simp [hall]
    rw [hfo] at hk
    obtain ⟨n, c, rfl, t, ht, htc⟩ := vcls_kind hk
    refine ⟨n, c, rfl, .inr fun x hx' => ?_⟩
    obtain ⟨u, hu, hxu⟩ := valIn_class (hok.2.2.1 x hx')
    rw [hxu, ← htc]
    exact famTab_uniform F (List.mem_of_getElem? hF) u hu t ht
  · intro rs hrs r hr
    obtain ⟨n, rfl⟩ := hI rss rfl rs hrs r hr
    exact ⟨n, .int, rfl, .inl ⟨hcall, rfl⟩⟩

set_option maxRecDepth 100000 in
/-- `lower_branch` on a terminator of a family: everything emitted is covered. -/
theorem branch_covT (hLI : LogicImmComplete) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hcl : Clean ctx) (hfam : FamCover ctx) {ti : Nat} {tinfo : IInfo} {i : Nat} {F : Fam}
    (hti : ctx.insts[ti]? = some tinfo) (hF : famTab[i]? = some F) (hok : FamOk ctx F tinfo)
    {targets : List Label} {s : LState} {out : Option V} {s' : LState}
    {tr : List Isle.RuleId} (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    CovSince s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  have sa := soundAt (md := covModelT hLI hctx hcl hfam s) (cfg := {}) (tab := covTabT)
    rfl covTabT_ok 1000000
  have hins : Holds2 f ctx [.inst [i], AT.c0] [.inst ti, .labels targets] :=
    ⟨⟨ti, tinfo, rfl, hti, i, List.mem_singleton_self _, F, hF, hok⟩,
      ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩, trivial⟩
  exact (sa.root T.lower_branch.ret T.lower_branch.id T.lower_branch _ _ [.inst [i], AT.c0] AT.top _ s #[]
    out s' tr' data_program.t687 term_687_kind
    (fun rl hrl => .inl (List.all_eq_true.mp (List.all_eq_true.mp covBranchT_ok rl hrl) i
      (List.mem_range.mpr (famTab_lt hF)))) hins (covSince_refl s) happ).1

end Backend.Proof.CovT
