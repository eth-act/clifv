import FV.Backend.Proof.IselSzTSound
import FV.Backend.Proof.IselSzTExt
import FV.Backend.Proof.IselSzTTab
import FV.Backend.Proof.IselSzCallT
import FV.Backend.Proof.IselSzBrTableG
import FV.Backend.Proof.IselSzDriver
import FV.Backend.Proof.IselCovTDriver
import FV.Backend.Proof.IselCovTFamCover
import FV.Backend.Proof.LogicImmComplete

/-!
# The size of the ISLE lowering's output over float-capable contexts (typed V6c): the driver's
calls, `IselSzT`

The typed cost analysis (`IselSzTSound`) instantiated with the typed coverage model `covModelT`
(value table `covTabT`), the extern costs `actorW`/`actorT` (`IselSzTExt`) and the cost tables
`szCTabT`/`tgCTabT` (`IselSzTTab`), on the instruction families (`FamCover`, `termFam_of`), with
the hand-checked rules over typed contexts (`IselSzCallT`; `br_table` by `IselSzBrTableG`, its
sub-runs from the typed analyses), bounds the driver's three ISLE calls:

* a statement's `lower` (`stmt_szT`): the call rules (1031–1033) by hand, every other rule on
  the statement's family by the table;
* a terminator's `lower`/`lower_branch` (`termCall_szT`): `return`/`trap` on `c0`; a branch on
  its family, the `br_table` rule (1140) by hand on a `br_table` and never matching another
  terminator, the `try_call` rules never matching a branch;
* a `try_call`'s `lower_branch` (`tryCall_szT`): the `try_call` rules (1034–1036) by hand.

`IselSzT f` is `IselSz f` with the terminators taken from `f`'s blocks (`termFam_of` gives a
family to a terminator of `f` only). **`iselSzT`: `IselSzT f` on the typed scope** (`LowerScopeT`,
`Dominated`, class-checked float `store`s and `select`s, as `formsCovered_completeT`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Cov

/-! ## The contract over `f`'s terminators -/

/-- Every non-`try_call` terminator of `f`'s run (with at most a label per successor) emits at
most `termSzB` and `termTgB`. -/
def TermSzT (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ B ∈ f.blocks, ∀ ti data targets s out s' tr, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → B.term.isTry = false →
    termData (abiTerm f B.term) = .ok data → targets.length ≤ (dests B.term).length →
    termCallF ctx ti data B.term targets s = .ok (out, s', tr) →
    wtA s'.emitted ≤ wtA s.emitted + termSzB B.term ∧ tgA s'.emitted ≤ tgA s.emitted + termTgB B.term

/-- Every `try_call` terminator of `f`'s run emits at most `termSzB` and `termTgB`. -/
def TrySzT (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ B ∈ f.blocks, ∀ ti et data sig items lo st1 trs targets s out s' tr, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → IsTryWith B.term et →
    tryCallData f B.term = .ok data →
    exnTableOpnd f et = .ok (sig, items) → tryRegsOf sig lo = some (trs, st1) →
    tryCallF ctx ti data trs targets s = .ok (out, s', tr) →
    wtA s'.emitted ≤ wtA s.emitted + termSzB B.term ∧ tgA s'.emitted ≤ tgA s.emitted + termTgB B.term

/-- **The ISLE runs of the driver on `f` are bounded**, for `f`'s own terminators (`IselSz` with
`TermSzT`/`TrySzT`). -/
def IselSzT (f : Clif.Function) : Prop :=
  ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) → StmtSz ctx ∧ TermSzT f ctx ∧ TrySzT f ctx

/-- `IselSz` gives `IselSzT`. -/
theorem IselSz.toT {f : Clif.Function} (h : IselSz f) : IselSzT f := fun ctx ranges st0 hb =>
  let ⟨hS, hT, hY⟩ := h ctx ranges st0 hb
  ⟨hS, fun _ _ ti data targets s out s' tr hti hph hty hd hl hc => hT ti _ data targets s out s' tr
      hti hph hty hd hl hc,
    fun _ _ ti et data sig items lo st1 trs targets s out s' tr hti hph het hd he htr hc =>
      hY ti _ et data sig items lo st1 trs targets s out s' tr hti hph het hd he htr hc⟩

end Backend.Proof.Driver

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (Clean CovSince LogicImmComplete HandW SubRun BrIdx emW wtA tgA szInstW
  logicImmComplete
  handW_callT handW_tryT handW_brTable_wtG handW_brTable_tgG clean_termCtx
  clean_tryCtx)

set_option maxRecDepth 20000

variable {f : Clif.Function} {ctx : Ctx}

/-! ## Tools -/

theorem cRuleLe_monoT {p : Program} {tab : Tab} {aw : TermId → List AT → Option Nat} {ctab : CTab}
    {aext : TermId → AT → List AT} {actor : TermId → List AT → AT} {apre : TermId → List AT → Bool}
    {aOracle : TermId → List AT → Option AT} {ins : List AT} {c c' : Nat} {r : Rule}
    (h : cRuleLe p tab aw ctab aext actor apre aOracle ins c r = true) (hc : c ≤ c') :
    cRuleLe p tab aw ctab aext actor apre aOracle ins c' r = true := by
  unfold cRuleLe at h ⊢
  cases hr : cRule p tab aw ctab aext actor apre aOracle ins r with
  | none => rw [hr] at h; cases h
  | some c0 =>
    rw [hr] at h
    exact decide_eq_true (Nat.le_trans (of_decide_eq_true h) hc)

/-- The typed value soundness at every fuel, the coverage model at `s0`. -/
theorem cov_saT (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) (s0 : LState)
    {cfg : Config} (hc : cfg.checkOverlap = false) :
    ∀ n, SoundAt (covModelT logicImmComplete hctx hcl hfam s0) cfg covTabT n :=
  soundAt (md := covModelT logicImmComplete hctx hcl hfam s0) (cfg := cfg) (tab := covTabT) hc covTabT_ok

/-! ## `br_table`'s sub-runs -/

/-- The index of a `br_table` of a family is a value of an integer type. -/
theorem brIdx_fam {F : Fam} (hF : F ∈ famTab) {a x b : V}
    (h : γP ctx noInst F.data (.data 152 4 [a, x, b])) : ∃ idx, x = .value idx ∧ ValIn ctx idx eCTys := by
  simp only [famTab, List.mem_cons, List.not_mem_nil, or_false] at hF
  repeat' obtain rfl | hF := hF
  all_goals
    obtain ⟨vs, he, hl⟩ := h
    simp only [V.data.injEq] at he
    obtain ⟨-, hk, rfl⟩ := he
  all_goals first
    | exact absurd hk (by decide)
    | exact hl.2.1

/-- A value of an integer type is described by `.val [t]` for one of them. -/
theorem valIn_single {x : Nat} (h : ValIn ctx x eCTys) : ∃ t ∈ eCTys, ValIn ctx x [t] := by
  cases hty : ctx.valueType? x with
  | some t =>
    refine ⟨t, h.1 t hty, ?_⟩
    unfold ValIn
    refine ⟨fun u hu => ?_, fun hn => by rw [hty] at hn; cases hn⟩
    rw [hty] at hu; cases hu; exact List.mem_singleton_self _
  | none =>
    refine ⟨.int 64, by simp [eCTys], ?_⟩
    unfold ValIn
    exact ⟨fun u hu => (by rw [hty] at hu; cases hu), fun _ => ⟨.int 64, List.mem_singleton_self _, rfl⟩⟩

/-- `aApply` of an internal term does not depend on the result type. -/
theorem aApply_internal_eqSzT {t : TermId} {term : Term} {flags : TermFlags} {ex : Option Extractor}
    (ht : termOf program t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    (ty : TypeId) (as : List AT) : aApply program covTabT actor apre aOracle ty t as =
      if as.any AT.isBot then some .bot else
        match aOracle t as with
        | some a => some a
        | none => tabGet covTabT t as := by
  unfold aApply; rw [ht]; simp only [hk]; rfl

/-- An `Option AT` that is `some (.reg 1)`, as a test. -/
def isReg1 : Option AT → Bool
  | some (.reg 1) => true
  | _ => false

theorem eq_of_isReg1 : ∀ {o : Option AT}, isReg1 o = true → o = some (.reg 1)
  | some (.reg 1), _ => rfl

/-- The tables on a sub-run of `br_table` (term `t` on `as`): its weight at most `cw`, no
branch targets, an int vreg result. -/
def subOk (t : TermId) (as : List AT) (cw : Nat) : Bool :=
  (match cApply program covTabT actorW szCTabT apre aOracle 0 t as with
    | some c => decide (c ≤ cw)
    | none => false) &&
  (match cApply program covTabT actorT tgCTabT apre aOracle 0 t as with
    | some c => c == 0
    | none => false) &&
  isReg1 (if as.any AT.isBot then some .bot else
    match aOracle t as with
    | some a => some a
    | none => tabGet covTabT t as)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `put_in_reg_zext32` on a value of an integer type. -/
theorem subOk_556 : eCTys.all (fun t => subOk 556 [.val [t]] 107) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `imm $I64 (ImmExtend.Zero) n`. -/
theorem subOk_553 : subOk 553 [.ty [.int 64], .data 122 1 [], .c0] 428 = true := by decide +kernel

/-- `cApply` does not depend on the result type. -/
theorem cApply_tyT (aw : TermId → List AT → Option Nat) (ctab : CTab) (ty : TypeId) (t : TermId)
    (as : List AT) :
    cApply program covTabT aw ctab apre aOracle ty t as = cApply program covTabT aw ctab apre aOracle 0 t as :=
  rfl

/-- The parts of `subOk`. -/
theorem subOk_parts {t : TermId} {term : Term} {flags : TermFlags} {ex : Option Extractor}
    (ht : termOf program t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    {as : List AT} {cw : Nat} (h : subOk t as cw = true) :
    (∀ ty, ∃ c, cApply program covTabT actorW szCTabT apre aOracle ty t as = some c ∧ c ≤ cw) ∧
    (∀ ty, ∃ c, cApply program covTabT actorT tgCTabT apre aOracle ty t as = some c ∧ c ≤ 0) ∧
    (∀ ty, aApply program covTabT actor apre aOracle ty t as = some (.reg 1)) := by
  unfold subOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun ty => ?_, fun ty => ?_, fun ty => by rw [aApply_internal_eqSzT ht hk]; exact eq_of_isReg1 h3⟩
  · rw [cApply_tyT]
    revert h1
    cases cApply program covTabT actorW szCTabT apre aOracle 0 t as with
    | none => intro h1; cases h1
    | some c => intro h1; exact ⟨c, rfl, of_decide_eq_true h1⟩
  · rw [cApply_tyT]
    revert h2
    cases cApply program covTabT actorT tgCTabT apre aOracle 0 t as with
    | none => intro h2; cases h2
    | some c => intro h2; exact ⟨c, rfl, by simp only [beq_iff_eq] at h2; omega⟩

/-- A run of a term the cost table and the value table bound: the measure grows by at most the
cost, a result is an int vreg. -/
theorem subRun_of (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx)
    {aw : TermId → List AT → Option Nat} {ctab : CTab} {w : MInst → Nat}
    (hext : ExtW f ctx apre aw (emW w)) (hor : OracleW program f ctx aOracle (emW w))
    (hct : chkCost program covTabT aw ctab aext actor apre aOracle = true)
    {t : TermId} {as : List AT} {vs : List V} {c : Nat} (hvs : Holds2 f ctx as vs)
    (hca : ∀ ty, ∃ c', cApply program covTabT aw ctab apre aOracle ty t as = some c' ∧ c' ≤ c)
    (haa : ∀ ty, aApply program covTabT actor apre aOracle ty t as = some (.reg 1)) :
    SubRun program ctx t vs w c := by
  intro cfg hc n ty s tr r s' tr' h
  obtain ⟨c', hc', hle⟩ := hca ty
  have hW := (costAt (md := covModelT logicImmComplete hctx hcl hfam s) hc
    (cov_saT hctx hcl hfam s hc) hext hor hct n).apply ty t as c' vs s tr r s' tr' hc' hvs
    (covSince_refl s) h
  refine ⟨by omega, fun v hv => ?_⟩
  have := ((cov_saT hctx hcl hfam s hc n).apply ty t as _ vs s tr r s' tr' (haa ty) hvs
    (covSince_refl s) h).2 v hv
  obtain ⟨r, rfl, hk⟩ := this
  obtain ⟨d, rfl⟩ := isV_sound (a := .reg 1) rfl (f := f) (ctx := ctx) ⟨r, rfl, hk⟩
  exact ⟨d, rfl⟩

/-- The arguments of `imm $I64 (ImmExtend.Zero) n`. -/
theorem holds2_imm64T (k : Int) :
    Holds2 f ctx [.ty [.int 64], .data 122 1 [], .c0] [.ty (.int 64), .data 122 1 [], .int k] :=
  ⟨⟨_, List.mem_singleton_self _, rfl⟩, ⟨[], rfl, trivial⟩,
    ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩, trivial⟩

/-- `wtA`/`tgA` are `emW` of the weight / the targets. -/
theorem extW_wtE : ExtW f ctx apre actorW (emW szInstW) := extW_wt
theorem extW_tgE : ExtW f ctx apre actorT (emW fun m => m.targets.length) := extW_tg
theorem oracleW_wtE : OracleW program f ctx aOracle (emW szInstW) := oracleW_wt
theorem oracleW_tgE : OracleW program f ctx aOracle (emW fun m => m.targets.length) := oracleW_tg

/-- **`br_table`'s sub-runs** in a context where the data at `ti` is of a family. -/
theorem brSubs (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) {ti : Nat}
    {data : V} (hti : ctx.insts[ti]? = some ⟨data, [], [], none⟩) {i : Nat} {F : Fam}
    (hF : famTab[i]? = some F) (hok : FamOk ctx F ⟨data, [], [], none⟩) :
    (∀ x, BrIdx ctx ti x → SubRun program ctx 556 [x] szInstW 107) ∧
    (∀ k : Int, SubRun program ctx 553 [.ty (.int 64), .data 122 1 [], .int k] szInstW 428) ∧
    (∀ x, BrIdx ctx ti x → SubRun program ctx 556 [x] (fun m => m.targets.length) 0) ∧
    (∀ k : Int, SubRun program ctx 553 [.ty (.int 64), .data 122 1 [], .int k]
      (fun m => m.targets.length) 0) := by
  have hidx : ∀ x, BrIdx ctx ti x → ∃ t ∈ eCTys, Holds2 f ctx [.val [t]] [x] := by
    intro x ⟨info, a, b, hi, hd⟩
    rw [hti] at hi
    cases hi
    have hg := hok.2.2.2
    simp only at hd
    rw [← hd] at hg
    obtain ⟨idx, rfl, hv⟩ := brIdx_fam (List.mem_of_getElem? hF) hg
    obtain ⟨t, ht, hv'⟩ := valIn_single hv
    exact ⟨t, ht, ⟨idx, rfl, hv'⟩, trivial⟩
  have p553 := subOk_parts program_term_553 term_553_kind subOk_553
  refine ⟨fun x hx => ?_, fun k => ?_, fun x hx => ?_, fun k => ?_⟩
  · obtain ⟨t, ht, hvs⟩ := hidx x hx
    have p556 := subOk_parts program_term_556 term_556_kind (List.all_eq_true.mp subOk_556 t ht)
    exact subRun_of hctx hcl hfam extW_wtE oracleW_wtE szCTabT_ok hvs p556.1 p556.2.2
  · exact subRun_of hctx hcl hfam extW_wtE oracleW_wtE szCTabT_ok (holds2_imm64T k) p553.1 p553.2.2
  · obtain ⟨t, ht, hvs⟩ := hidx x hx
    have p556 := subOk_parts program_term_556 term_556_kind (List.all_eq_true.mp subOk_556 t ht)
    exact subRun_of hctx hcl hfam extW_tgE oracleW_tgE tgCTabT_ok hvs p556.2.1 p556.2.2
  · exact subRun_of hctx hcl hfam extW_tgE oracleW_tgE tgCTabT_ok (holds2_imm64T k) p553.2.1 p553.2.2

/-! ## The driver's calls -/

set_option maxRecDepth 100000 in
/-- **A statement's lowering emits at most `stmtSzB` and `tgStmtK` targets** (typed). -/
theorem stmt_szT (hctx : CtxT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) :
    wtA s'.emitted ≤ wtA s.emitted + stmtSzB inst ∧ tgA s'.emitted ≤ tgA s.emitted + tgStmtK := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  obtain ⟨i, F, hF, hok⟩ := hfam ii info inst hi hc
  have hins := holds_famT (f := f) hi hF hok
  have hiF : i ∈ List.range famTab.length := List.mem_range.mpr (famTab_lt hF)
  have hK : szStmtK ≤ stmtSzB inst := by
    unfold stmtSzB szStmtK szCallB; split <;> omega
  have hrulesW : ∀ rl ∈ program.rulesOf T.lower.id,
      cRuleLe program covTabT actorW szCTabT aext actor apre aOracle [.inst [i]] (stmtSzB inst) rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1)) ∨
      (rl ∈ program.rulesOf TId.lower ∧ (rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033)) := by
    intro rl hrl
    have hf := List.all_eq_true.mp szStmtT_ok rl hrl
    unfold szStmtOkT at hf
    simp only [Bool.or_eq_true, beq_iff_eq] at hf
    rcases hf with ((h1 | h2) | h3) | hall
    · exact .inr (.inr ⟨hrl, .inl h1⟩)
    · exact .inr (.inr ⟨hrl, .inr (.inl h2)⟩)
    · exact .inr (.inr ⟨hrl, .inr (.inr h3)⟩)
    · exact .inl (cRuleLe_monoT (List.all_eq_true.mp hall i hiF) hK)
  have hrulesT : ∀ rl ∈ program.rulesOf T.lower.id,
      cRuleLe program covTabT actorT tgCTabT aext actor apre aOracle [.inst [i]] tgStmtK rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1)) :=
    fun rl hrl => .inl (List.all_eq_true.mp (List.all_eq_true.mp tgStmtT_ok rl hrl) i hiF)
  refine ⟨?_, ?_⟩
  · exact cost_root_hand (md := covModelT logicImmComplete hctx.inv hcl hfam s) rfl
      (cov_saT hctx.inv hcl hfam s rfl) extW_wt oracleW_wt szCTabT_ok
      (Hand := fun rl => rl ∈ program.rulesOf TId.lower ∧ (rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033))
      (fun rl ⟨hrl, hid⟩ => handW_callT hctx hi hc hrl hid)
      data_program.t686 term_686_kind hrulesW hins (covSince_refl s) (n := 999999) lower_len happ
  · exact cost_root (md := covModelT logicImmComplete hctx.inv hcl hfam s) rfl
      (cov_saT hctx.inv hcl hfam s rfl) extW_tg oracleW_tg tgCTabT_ok data_program.t686
      term_686_kind hrulesT hins (covSince_refl s) happ

set_option maxRecDepth 100000 in
/-- `lower_branch` on a terminator of a family (typed): the rules other than the `try_call`
(1034–1036) and `br_table` (1140) ones by the table, those by the given hand facts or never
matching. -/
theorem branch_szT (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) {ti : Nat}
    {tinfo : IInfo} {i : Nat} {F : Fam} (hti : ctx.insts[ti]? = some tinfo)
    (hF : famTab[i]? = some F) (hok : FamOk ctx F tinfo) {targets : List Label}
    {cW cT : Nat} (hcW : szTermK ≤ cW) (hcT : tgTermK ≤ cT)
    {Try : Rule → Prop} {Br : Rule → Prop}
    (htry : ∀ rl ∈ program.rulesOf TId.lower_branch, (rl.id = 1034 ∨ rl.id = 1035 ∨ rl.id = 1036) →
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ti, .labels targets]).run s0 ≠
        .ok (some env, s1)) ∨ Try rl)
    (hbr : ∀ rl ∈ program.rulesOf TId.lower_branch, rl.id = 1140 →
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ti, .labels targets]).run s0 ≠
        .ok (some env, s1)) ∨ Br rl)
    (hTryW : ∀ rl, Try rl → HandW program ctx [.inst ti, .labels targets] rl (fun s => wtA s.emitted) cW)
    (hBrW : ∀ rl, Br rl → HandW program ctx [.inst ti, .labels targets] rl (fun s => wtA s.emitted) cW)
    (hBrT : ∀ rl, Br rl → HandW program ctx [.inst ti, .labels targets] rl (fun s => tgA s.emitted) cT)
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    wtA s'.emitted ≤ wtA s.emitted + cW ∧ tgA s'.emitted ≤ tgA s.emitted + cT := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  have hins : Holds2 f ctx [.inst [i], AT.c0] [.inst ti, .labels targets] :=
    ⟨⟨ti, tinfo, rfl, hti, i, List.mem_singleton_self _, F, hF, hok⟩,
      ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩, trivial⟩
  have hiF : i ∈ List.range famTab.length := List.mem_range.mpr (famTab_lt hF)
  have hrulesW : ∀ rl ∈ program.rulesOf T.lower_branch.id,
      cRuleLe program covTabT actorW szCTabT aext actor apre aOracle [.inst [i], .c0] cW rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ti, .labels targets]).run s0 ≠
        .ok (some env, s1)) ∨ (Try rl ∨ Br rl) := by
    intro rl hrl
    have hf := List.all_eq_true.mp szBranchT_ok rl hrl
    unfold szBranchOkT at hf
    simp only [Bool.or_eq_true, beq_iff_eq] at hf
    rcases hf with (((h1 | h2) | h3) | h4) | hall
    · rcases htry rl hrl (.inl h1) with hn | hT
      · exact .inr (.inl hn)
      · exact .inr (.inr (.inl hT))
    · rcases htry rl hrl (.inr (.inl h2)) with hn | hT
      · exact .inr (.inl hn)
      · exact .inr (.inr (.inl hT))
    · rcases htry rl hrl (.inr (.inr h3)) with hn | hT
      · exact .inr (.inl hn)
      · exact .inr (.inr (.inl hT))
    · rcases hbr rl hrl h4 with hn | hB
      · exact .inr (.inl hn)
      · exact .inr (.inr (.inr hB))
    · exact .inl (cRuleLe_monoT (List.all_eq_true.mp hall i hiF) hcW)
  have hrulesT : ∀ rl ∈ program.rulesOf T.lower_branch.id,
      cRuleLe program covTabT actorT tgCTabT aext actor apre aOracle [.inst [i], .c0] cT rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ti, .labels targets]).run s0 ≠
        .ok (some env, s1)) ∨ Br rl := by
    intro rl hrl
    have hf := List.all_eq_true.mp tgBranchT_ok rl hrl
    unfold tgBranchOkT at hf
    simp only [Bool.or_eq_true, beq_iff_eq] at hf
    rcases hf with h4 | hall
    · rcases hbr rl hrl h4 with hn | hB
      · exact .inr (.inl hn)
      · exact .inr (.inr hB)
    · exact .inl (cRuleLe_monoT (List.all_eq_true.mp hall i hiF) hcT)
  refine ⟨?_, ?_⟩
  · exact cost_root_hand (md := covModelT logicImmComplete hctx hcl hfam s) rfl
      (cov_saT hctx hcl hfam s rfl) extW_wt oracleW_wt szCTabT_ok (Hand := fun rl => Try rl ∨ Br rl)
      (fun rl hrl => by
        rcases hrl with hT | hB
        · exact hTryW rl hT
        · exact hBrW rl hB)
      data_program.t687 term_687_kind hrulesW hins (covSince_refl s) (n := 999999) lower_branch_len happ
  · exact cost_root_hand (md := covModelT logicImmComplete hctx hcl hfam s) rfl
      (cov_saT hctx hcl hfam s rfl) extW_tg oracleW_tg tgCTabT_ok (Hand := Br) hBrT
      data_program.t687 term_687_kind hrulesT hins (covSince_refl s) (n := 999999) lower_branch_len happ

/-- The `try_call` rules (1034–1036) never match a branch (typed). -/
theorem try_rules_unmatchT {c : Ctx} (hctx' : CtxT f c) {ti : Nat} {t : Clif.Terminator} {data : V}
    {targets : List Label} (hrt : retOrTrap (abiTerm f t) = false) (hd : termData (abiTerm f t) = .ok data)
    (hslot : c.insts[ti]? = some ⟨data, [], [], none⟩) :
    ∀ rl ∈ program.rulesOf TId.lower_branch, (rl.id = 1034 ∨ rl.id = 1035 ∨ rl.id = 1036) →
      (∀ m s0 env s1, (matchRule program (sem c) {} m rl [.inst ti, .labels targets]).run s0 ≠
        .ok (some env, s1)) ∨ False := by
  intro rl hrl hid
  have hb := List.all_eq_true.mp branch_hand_ids rl hrl
  have hcr : closureRoot rl = false := by
    cases hcr : closureRoot rl with
    | false => rfl
    | true =>
      rw [hcr] at hb
      rcases hid with h | h | h <;> rw [h] at hb <;> exact absurd hb (by decide)
  exact .inl fun m s0 env s1 =>
    branchExcludedUnmatchableT_program rl hrl hcr f _ hctx' ti _ data targets hrt hd hslot {} m s0 env s1

/-- `return`/`trap` on `c0` at a terminator slot. -/
theorem holds_c0_inst (ti : Nat) : Holds2 f ctx [AT.c0] [.inst ti] :=
  ⟨⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩, trivial⟩

set_option maxRecDepth 100000 in
/-- A `return`/`trap`'s `lower` (typed): at most `szTermK` and `tgTermK`. -/
theorem retTrap_szT {c : Ctx} (hctx' : CtxInvT f c) (hcl' : Clean c) (hfam' : FamCover c) {ti : Nat}
    {t : Clif.Terminator} {data : V} (hrt : retOrTrap (abiTerm f t) = true)
    (hd : termData (abiTerm f t) = .ok data) (hslot : c.insts[ti]? = some ⟨data, [], [], none⟩)
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm c "lower" [.inst ti] s = .ok (out, s', tr)) :
    wtA s'.emitted ≤ wtA s.emitted + szTermK ∧ tgA s'.emitted ≤ tgA s.emitted + tgTermK := by
  obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hrulesW : ∀ rl ∈ program.rulesOf T.lower.id,
      cRuleLe program covTabT actorW szCTabT aext actor apre aOracle [AT.c0] szTermK rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem c) {} m rl [.inst ti]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    cases hroot : termRootRule rl with
    | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
    | true =>
      have hf := List.all_eq_true.mp szTermT_ok rl hrl
      simp only [termRootRule] at hroot
      simp only [hroot, Bool.not_true, Bool.false_or] at hf
      exact .inl hf
  have hrulesT : ∀ rl ∈ program.rulesOf T.lower.id,
      cRuleLe program covTabT actorT tgCTabT aext actor apre aOracle [AT.c0] tgTermK rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem c) {} m rl [.inst ti]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    cases hroot : termRootRule rl with
    | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
    | true =>
      have hf := List.all_eq_true.mp tgTermT_ok rl hrl
      simp only [termRootRule] at hroot
      simp only [hroot, Bool.not_true, Bool.false_or] at hf
      exact .inl hf
  exact ⟨cost_root (md := covModelT logicImmComplete hctx' hcl' hfam' s) rfl
      (cov_saT hctx' hcl' hfam' s rfl) extW_wt oracleW_wt szCTabT_ok data_program.t686 term_686_kind
      hrulesW (holds_c0_inst ti) (covSince_refl s) happ,
    cost_root (md := covModelT logicImmComplete hctx' hcl' hfam' s) rfl
      (cov_saT hctx' hcl' hfam' s rfl) extW_tg oracleW_tg tgCTabT_ok data_program.t686 term_686_kind
      hrulesT (holds_c0_inst ti) (covSince_refl s) happ⟩

/-- **A terminator's lowering** (typed, a terminator of a family, a label per successor): at most
`termSzB` and `termTgB`. -/
theorem termCall_szT (hctx : CtxT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator}
    (hty : t.isTry = false) {data : V} (hd : termData (abiTerm f t) = .ok data)
    (htf : ∃ (i : Nat) (F : Fam), famTab[i]? = some F ∧ FamOk ctx F ⟨data, [], [], none⟩)
    {targets : List Label} (hlen : targets.length ≤ (dests t).length) {s : LState}
    {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) :
    wtA s'.emitted ≤ wtA s.emitted + termSzB t ∧ tgA s'.emitted ≤ tgA s.emitted + termTgB t := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have hctxT' := ctxT_termCtx hctx hph data
  have hctx' := hctxT'.inv
  have hcl' := clean_termCtx hcl hd ti
  have hfam' := famCover_termCtx hfam hph data
  have hslot := termCtx_self hti data
  obtain ⟨i, F, hF, hok⟩ := htf
  have hok' : FamOk (termCtx ctx ti data) F ⟨data, [], [], none⟩ :=
    famOk_valTy (ctx := ctx) (ctx' := termCtx ctx ti data) rfl hok
  unfold termCallF at h
  cases t with
  | ret vs => exact retTrap_szT hctx' hcl' hfam' rfl hd hslot h
  | trap c => exact retTrap_szT hctx' hcl' hfam' rfl hd hslot h
  | jump bc =>
    have hnb : ∀ fs, data ≠ .data 152 4 fs := by
      intro fs he
      rw [show abiTerm f (.jump bc) = .jump bc from rfl, termData_jump] at hd
      cases hd; cases he
    exact branch_szT hctx' hcl' hfam' hslot hF hok' (Nat.le_refl _) (Nat.le_refl _)
      (Try := fun _ => False) (Br := fun _ => False)
      (try_rules_unmatchT hctxT' rfl hd hslot)
      (fun _ hrl hid => .inl fun m s0 env s1 => br1140_unmatch hslot hnb hrl hid {} m s0 env s1)
      (fun _ h => h.elim) (fun _ h => h.elim) (fun _ h => h.elim) h
  | brif c a b =>
    have hnb : ∀ fs, data ≠ .data 152 4 fs := by
      intro fs he
      rw [show abiTerm f (.brif c a b) = .brif c a b from rfl, termData_brif] at hd
      cases hd; cases he
    exact branch_szT hctx' hcl' hfam' hslot hF hok' (Nat.le_refl _) (Nat.le_refl _)
      (Try := fun _ => False) (Br := fun _ => False)
      (try_rules_unmatchT hctxT' rfl hd hslot)
      (fun _ hrl hid => .inl fun m s0 env s1 => br1140_unmatch hslot hnb hrl hid {} m s0 env s1)
      (fun _ h => h.elim) (fun _ h => h.elim) (fun _ h => h.elim) h
  | brTable x d tb =>
    have hl : targets.length ≤ 1 + tb.length := by
      simp only [dests, List.length_cons] at hlen; omega
    have hW : szTermK ≤ termSzB (.brTable x d tb) := by
      show 600 ≤ 1500 + 2 * (1 + tb.length); omega
    have hT : tgTermK ≤ termTgB (.brTable x d tb) := by
      show 2 ≤ 2 + tb.length; omega
    obtain ⟨h556W, h553W, h556T, h553T⟩ := brSubs hctx' hcl' hfam' hslot hF hok'
    exact branch_szT hctx' hcl' hfam' hslot hF hok' hW hT (Try := fun _ => False)
      (Br := fun rl => rl ∈ program.rulesOf TId.lower_branch ∧ rl.id = 1140)
      (try_rules_unmatchT hctxT' rfl hd hslot)
      (fun rl hrl hid => .inr ⟨hrl, hid⟩) (fun _ h => h.elim)
      (fun rl ⟨hrl, hid⟩ => handW_mono (handW_brTable_wtG h556W h553W hrl hid)
        (by show 1500 + 2 * targets.length ≤ 1500 + 2 * (1 + tb.length); omega))
      (fun rl ⟨hrl, hid⟩ => handW_mono (handW_brTable_tgG h556T h553T hrl hid)
        (by show targets.length ≤ 2 + tb.length; omega)) h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [Clif.Terminator.isTry] at hty
  | tryCallIndirect callee args et => simp [Clif.Terminator.isTry] at hty

/-- **A `try_call`'s lowering** (typed, a terminator of a family): at most `termSzB` (its call)
and `termTgB`. -/
theorem tryCall_szT (hctx : CtxT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator} {et : Clif.ExnTable}
    (het : IsTryWith t et) {data : V} (hd : tryCallData f t = .ok data)
    (htf : ∃ (i : Nat) (F : Fam), famTab[i]? = some F ∧ FamOk ctx F ⟨data, [], [], none⟩)
    {sig : Clif.Signature} {items : List (Option Nat)} (he : exnTableOpnd f et = .ok (sig, items))
    {lo st1 : LState} {trs : List Reg × List Reg} (htr : tryRegsOf sig lo = some (trs, st1))
    {targets : List Label} {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : tryCallF ctx ti data trs targets s = .ok (out, s', tr)) :
    wtA s'.emitted ≤ wtA s.emitted + termSzB t ∧ tgA s'.emitted ≤ tgA s.emitted + termTgB t := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have h' := ctxInvT_termCtx hctx.inv hph data
  have hctx' : CtxInvT f (tryCtx ctx ti data trs) := { h' with }
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hK : szTermK ≤ termSzB t := by unfold termSzB szCallB szTermK szBrK; split <;> omega
  have hKT : tgTermK ≤ termTgB t := by
    rcases het with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [termTgB]
  obtain ⟨i, F, hF, hok⟩ := htf
  exact branch_szT hctx' (clean_tryCtx hcl hd ti trs)
    (famCover_eq (ctx := termCtx ctx ti data) (ctx' := tryCtx ctx ti data trs) rfl rfl
      (famCover_termCtx hfam hph data)) hi hF
    (famOk_valTy (ctx := ctx) (ctx' := tryCtx ctx ti data trs) rfl hok) hK hKT
    (Try := fun rl => rl ∈ program.rulesOf TId.lower_branch ∧ (rl.id = 1034 ∨ rl.id = 1035 ∨ rl.id = 1036))
    (Br := fun _ => False)
    (fun rl hrl hid => .inr ⟨hrl, hid⟩)
    (fun _ hrl hid => .inl fun m s0 env s1 =>
      br1140_unmatch hi (tryCallData_ne_brTable hd) hrl hid {} m s0 env s1)
    (fun rl ⟨hrl, hid⟩ => handW_tryT hctx hph het hd he htr hrl hid)
    (fun _ h => h.elim) (fun _ h => h.elim) h

end Backend.Proof.CovT

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## `IselSzT` -/

/-- **The ISLE runs of the driver are bounded on the typed scope**: for `f` in `Dominated` and
`LowerScopeT` with class-checked float `store`s and `select`s (`formsCovered_completeT`'s
premises), every statement's run and every run of one of `f`'s terminators. -/
theorem iselSzT {f : Clif.Function} (hdom : dominatedB f = true) (hs : LowerScopeT f)
    (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true) : IselSzT f := by
  intro ctx ranges st0 hb
  have hctx : CtxT f ctx :=
    ⟨ctxInvT_of hs hb, ((ctxSpec_of hb).instScopeT hs.subsetT).toTF,
      callsE_of_externs (functionET_externs hs.subsetT) ctx⟩
  have hcl : Cov.Clean ctx := Cov.clean_of_build hb
  have hfam := CovT.famCover_of hs hdom hst hsel hb
  exact ⟨fun ii info inst s out s' tr hi hc h => CovT.stmt_szT hctx hcl hfam hi hc h,
    fun B hB ti data targets s out s' tr _ hph hty hd hlen h =>
      CovT.termCall_szT hctx hcl hfam hph hty hd (CovT.termFam_of hs hdom hb hB (.inl hd)) hlen h,
    fun B hB ti et data sig items lo st1 trs targets s out s' tr _ hph het hd he htr h =>
      CovT.tryCall_szT hctx hcl hfam hph het hd (CovT.termFam_of hs hdom hb hB (.inr hd)) he htr h⟩

end Backend.Proof.Driver
