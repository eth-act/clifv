import FV.Backend.Proof.IselSzSound
import FV.Backend.Proof.IselSzExt
import FV.Backend.Proof.IselSzTab
import FV.Backend.Proof.IselSzCall
import FV.Backend.Proof.IselSzBrTable
import FV.Backend.Proof.IselShpDriver
import FV.Backend.Proof.IselCovDriver

/-!
# The size of the ISLE lowering's output (V6c): the driver's calls, `IselSz`

The cost analysis (`IselSzSound`) instantiated with V3's coverage model `covModel` (value table
`covTab`), the extern costs `actorW`/`actorT` (`IselSzExt`) and the cost tables `szCTab`/`tgCTab`
(`IselSzTab`), with the hand-checked rules (`IselSzCall`, `IselSzBrTable`), bounds the driver's
three ISLE calls:

* a statement's `lower` (`stmt_sz`): the call rules (1031–1033) by hand, the other closure roots
  by the table (a non-root never matches);
* a terminator's `lower`/`lower_branch` (`termCall_sz`): the `br_table` rule (1140) by hand on a
  `br_table` (with a label per successor), never matching another terminator (its root format is
  `BranchTable`, `br1140_unmatch`); the `try_call` rules never match a branch;
* a `try_call`'s `lower_branch` (`tryCall_sz`): the `try_call` rules (1034–1036) by hand.

**`iselSz`: `IselSz f` for every in-scope `f`.**
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Cov Backend.Proof.Spill Isle Isle.Interp
  Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

/-! ## Tools -/

theorem cRuleLe_mono {p : Program} {tab : Cov.Tab} {aw : TermId → List AW → Option Nat} {ctab : CTab}
    {aext : TermId → AW → List AW} {actor : TermId → List AW → AW} {apre : TermId → List AW → Bool}
    {aOracle : TermId → List AW → Option AW} {ins : List AW} {c c' : Nat} {r : Rule}
    (h : cRuleLe p tab aw ctab aext actor apre aOracle ins c r = true) (hc : c ≤ c') :
    cRuleLe p tab aw ctab aext actor apre aOracle ins c' r = true := by
  unfold cRuleLe at h ⊢
  cases hr : cRule p tab aw ctab aext actor apre aOracle ins r with
  | none => rw [hr] at h; cases h
  | some c0 =>
    rw [hr] at h
    exact decide_eq_true (Nat.le_trans (of_decide_eq_true h) hc)

theorem handW_mono {p : Program} {vs : List V} {rl : Rule} {W : LState → Nat} {c c' : Nat}
    (h : HandW p ctx vs rl W c) (hc : c ≤ c') : HandW p ctx vs rl W c' :=
  fun cfg hco m n s tr env s1 r s2 tr2 hm hn h1 h2 =>
    Nat.le_trans (h cfg hco m n s tr env s1 r s2 tr2 hm hn h1 h2) (Nat.add_le_add_left hc _)

/-- V3's value soundness at every fuel, the coverage model at `s0`. -/
theorem cov_sa (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) (s0 : LState) {cfg : Config}
    (hc : cfg.checkOverlap = false) : ∀ n, SoundAt (covModel logicImmComplete hctx hcl s0) cfg covTab n :=
  soundAt (hctx := hctx) (md := covModel logicImmComplete hctx hcl s0) (cfg := cfg) (tab := covTab)
    hc covTab_ok

/-- A sub-run of an internal term the cost table bounds at `as` (`SubW`), from `costAt`. -/
theorem subW_of_cost (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) {aw : TermId → List AW → Option Nat}
    {ctab : CTab} {W : LState → Nat} (hext : ExtW f ctx apre aw W) (hor : OracleW program f ctx aOracle W)
    (hct : chkCost program covTab aw ctab aext actor apre aOracle = true) {t : TermId} {as : List AW}
    {c : Nat} (hca : ∀ ty, cApply program covTab aw ctab apre aOracle ty t as = some c) :
    SubW program f ctx t as W c := by
  intro cfg hc n ty vs s tr r s' tr' hvs h
  exact (costAt (md := covModel logicImmComplete hctx hcl s) hc (cov_sa hctx hcl s hc) hext
    (fun cfg' hc' => hor cfg' hc') hct n).apply ty t as c vs s tr r s' tr' (hca ty) hvs
    (covSince_refl s) h

/-- `cApply` does not depend on the result type. -/
theorem cApply_ty (aw : TermId → List AW → Option Nat) (ctab : CTab) (ty : TypeId) (t : TermId)
    (as : List AW) :
    cApply program covTab aw ctab apre aOracle ty t as = cApply program covTab aw ctab apre aOracle 0 t as :=
  rfl

theorem cApply_556_wt0 : cApply program covTab actorW szCTab apre aOracle 0 556 [.c0] = some 107 := by
  native_decide

theorem cApply_553_wt0 :
    cApply program covTab actorW szCTab apre aOracle 0 553 [.ty [.int 64], .data 122 1 [], .c0] =
      some 428 := by native_decide

theorem cApply_556_tg0 : cApply program covTab actorT tgCTab apre aOracle 0 556 [.c0] = some 0 := by
  native_decide

theorem cApply_553_tg0 :
    cApply program covTab actorT tgCTab apre aOracle 0 553 [.ty [.int 64], .data 122 1 [], .c0] =
      some 0 := by native_decide

/-! ## `br_table`'s rule on other terminators -/

theorem rule1140_fmt : ruleFmt rule_lower_3277 = some 2451 := by decide

/-- **Rule 1140 (`br_table`) never matches an instruction whose data is not a `BranchTable`.** -/
theorem br1140_unmatch {ti : Nat} {data : V} (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    (hfmt : ∀ fs, data ≠ .data 152 4 fs) {rl : Rule} (hrl : rl ∈ program.rulesOf TId.lower_branch)
    (hid : rl.id = 1140) {targets : List Label} :
    ∀ (cfg : Config) m s0 env s1,
      (matchRule program (sem ctx) cfg m rl [.inst ti, .labels targets]).run s0 ≠ .ok (some env, s1) := by
  intro cfg m s0 env s1 h
  have hmem : rule_lower_3277 ∈ program.rulesOf TId.lower_branch := by
    rw [show TId.lower_branch = 687 from rfl, program_rulesOf_687]; simp
  obtain rfl := eq_of_mem_of_id lower_branch_ids_nodup hrl hmem hid
  obtain ⟨info, fs, hinfo, hdat⟩ := ruleFmt_match (vs := [.labels targets]) data_program
    fmtKinds_program rule1140_fmt (by omega) (by omega) h
  rw [hi] at hinfo
  cases hinfo
  exact hfmt fs hdat

/-- A `try_call`'s data is not a `BranchTable`. -/
theorem tryCallData_ne_brTable {t : Clif.Terminator} {data : V} (hd : tryCallData f t = .ok data) :
    ∀ fs, data ≠ .data 152 4 fs := by
  intro fs he
  cases t with
  | tryCall fn args et =>
    obtain ⟨sig, items, ext, he', hx, hs⟩ := tryCallData_spec hd
    rw [tryCallData_eq he' hx hs] at hd
    cases hd
    cases he
  | tryCallIndirect callee args et =>
    obtain ⟨sig, items, he'⟩ := tryCallIndData_spec hd
    rw [tryCallIndData_eq he'] at hd
    cases hd
    cases he
  | _ => simp [tryCallData, throw, throwThe, MonadExceptOf.throw] at hd

/-! ## The driver's calls -/

set_option maxRecDepth 100000 in
/-- **A statement's lowering emits at most `stmtSzB` and `tgStmtK` targets.** -/
theorem stmt_sz (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst) {s : LState}
    {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) :
    wtA s'.emitted ≤ wtA s.emitted + stmtSzB inst ∧ tgA s'.emitted ≤ tgA s.emitted + tgStmtK := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hK : szStmtK ≤ stmtSzB inst := by
    unfold stmtSzB szStmtK szCallB; split <;> omega
  have hrulesW : ∀ rl ∈ program.rulesOf T.lower.id,
      cRuleLe program covTab actorW szCTab aext actor apre aOracle [.xv .inst] (stmtSzB inst) rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1)) ∨
      (rl ∈ program.rulesOf TId.lower ∧ (rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033)) := by
    intro rl hrl
    have hf := List.all_eq_true.mp szStmt_ok rl hrl
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hf
    rcases hf with (((hcr | h1) | h2) | h3) | hle
    · exact .inr (.inl (lower_nonroot_nomatch hctx hi hc hrl hcr))
    · exact .inr (.inr ⟨hrl, .inl h1⟩)
    · exact .inr (.inr ⟨hrl, .inr (.inl h2)⟩)
    · exact .inr (.inr ⟨hrl, .inr (.inr h3)⟩)
    · exact .inl (cRuleLe_mono hle hK)
  have hrulesT : ∀ rl ∈ program.rulesOf T.lower.id,
      cRuleLe program covTab actorT tgCTab aext actor apre aOracle [.xv .inst] tgStmtK rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1)) := by
    intro rl hrl
    have hf := List.all_eq_true.mp tgStmt_ok rl hrl
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hf
    rcases hf with hcr | hle
    · exact .inr (lower_nonroot_nomatch hctx hi hc hrl hcr)
    · exact .inl hle
  refine ⟨?_, ?_⟩
  · exact cost_root_hand (md := covModel logicImmComplete hctx hcl s) rfl (cov_sa hctx hcl s rfl)
      extW_wt oracleW_wt szCTab_ok
      (Hand := fun rl => rl ∈ program.rulesOf TId.lower ∧ (rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033))
      (fun rl ⟨hrl, hid⟩ => handW_call hctx hi hc hrl hid)
      data_program.t686 term_686_kind hrulesW (holds_inst hctx hi hc) (covSince_refl s) (n := 999999)
      lower_len happ
  · exact cost_root (md := covModel logicImmComplete hctx hcl s) rfl (cov_sa hctx hcl s rfl)
      extW_tg oracleW_tg tgCTab_ok data_program.t686 term_686_kind hrulesT (holds_inst hctx hi hc)
      (covSince_refl s) happ

set_option maxRecDepth 100000 in
/-- `lower_branch` in a context with `CtxInv`/`Clean`, at an instruction whose data is `data`:
the rules other than the `try_call` (1034–1036) and `br_table` (1140) ones by the table, those
by the given hand facts or never matching. -/
theorem branch_sz (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) {ti : Nat} {targets : List Label}
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
  have hins : Holds2 f ctx [AW.c0, AW.c0] [.inst ti, .labels targets] :=
    ⟨γ_c0_inst ti, γ_c0_labels targets, trivial⟩
  have hrulesW : ∀ rl ∈ program.rulesOf T.lower_branch.id,
      cRuleLe program covTab actorW szCTab aext actor apre aOracle [.c0, .c0] cW rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ti, .labels targets]).run s0 ≠
        .ok (some env, s1)) ∨ (Try rl ∨ Br rl) := by
    intro rl hrl
    have hf := List.all_eq_true.mp szBranch_ok rl hrl
    simp only [Bool.or_eq_true, beq_iff_eq] at hf
    rcases hf with (((h1 | h2) | h3) | h4) | hle
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
    · exact .inl (cRuleLe_mono hle hcW)
  have hrulesT : ∀ rl ∈ program.rulesOf T.lower_branch.id,
      cRuleLe program covTab actorT tgCTab aext actor apre aOracle [.c0, .c0] cT rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ti, .labels targets]).run s0 ≠
        .ok (some env, s1)) ∨ Br rl := by
    intro rl hrl
    have hf := List.all_eq_true.mp tgBranch_ok rl hrl
    simp only [Bool.or_eq_true, beq_iff_eq] at hf
    rcases hf with h4 | hle
    · rcases hbr rl hrl h4 with hn | hB
      · exact .inr (.inl hn)
      · exact .inr (.inr hB)
    · exact .inl (cRuleLe_mono hle hcT)
  refine ⟨?_, ?_⟩
  · exact cost_root_hand (md := covModel logicImmComplete hctx hcl s) rfl (cov_sa hctx hcl s rfl)
      extW_wt oracleW_wt szCTab_ok (Hand := fun rl => Try rl ∨ Br rl)
      (fun rl hrl => by
        rcases hrl with hT | hB
        · exact hTryW rl hT
        · exact hBrW rl hB)
      data_program.t687 term_687_kind hrulesW hins (covSince_refl s) (n := 999999) lower_branch_len happ
  · exact cost_root_hand (md := covModel logicImmComplete hctx hcl s) rfl (cov_sa hctx hcl s rfl)
      extW_tg oracleW_tg tgCTab_ok (Hand := Br) hBrT
      data_program.t687 term_687_kind hrulesT hins (covSince_refl s) (n := 999999) lower_branch_len happ

/-- The `try_call` rules (1034–1036) never match a branch. -/
theorem try_rules_unmatch {c : Ctx} (hctx' : CtxInv f c) {ti : Nat} {t : Clif.Terminator} {data : V}
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
    branchExcludedUnmatchable rl hrl hcr f _ hctx' ti _ data targets hrt hd hslot {} m s0 env s1

set_option maxRecDepth 100000 in
/-- A `jump`/`brif`'s `lower_branch`: at most `szTermK` and `tgTermK`. -/
theorem jumpBrif_sz {c : Ctx} (hctx' : CtxInv f c) (hcl' : Cov.Clean c) {ti : Nat} {t : Clif.Terminator}
    {data : V} {targets : List Label} (hrt : retOrTrap (abiTerm f t) = false)
    (hd : termData (abiTerm f t) = .ok data) (hslot : c.insts[ti]? = some ⟨data, [], [], none⟩)
    (hnb : ∀ fs, data ≠ .data 152 4 fs) {s : LState} {out : Option V} {s' : LState}
    {tr : List Isle.RuleId}
    (h : runTerm c "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    wtA s'.emitted ≤ wtA s.emitted + szTermK ∧ tgA s'.emitted ≤ tgA s.emitted + tgTermK :=
  branch_sz hctx' hcl' (Nat.le_refl _) (Nat.le_refl _) (Try := fun _ => False) (Br := fun _ => False)
    (try_rules_unmatch hctx' hrt hd hslot)
    (fun _ hrl hid => .inl fun m s0 env s1 => br1140_unmatch hslot hnb hrl hid {} m s0 env s1)
    (fun _ h => h.elim) (fun _ h => h.elim) (fun _ h => h.elim) h

set_option maxRecDepth 100000 in
/-- A `br_table`'s `lower_branch` (a label per successor): at most `termSzB` and `termTgB`. -/
theorem brTable_sz {c : Ctx} (hctx' : CtxInv f c) (hcl' : Cov.Clean c) {ti : Nat} {x : Clif.ValueId}
    {d : Clif.BlockCall} {tbl : List Clif.BlockCall} {data : V} {targets : List Label}
    (hrt : retOrTrap (abiTerm f (.brTable x d tbl)) = false)
    (hd : termData (abiTerm f (.brTable x d tbl)) = .ok data)
    (hslot : c.insts[ti]? = some ⟨data, [], [], none⟩) (hl : targets.length ≤ 1 + tbl.length)
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm c "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    wtA s'.emitted ≤ wtA s.emitted + termSzB (.brTable x d tbl) ∧
      tgA s'.emitted ≤ tgA s.emitted + termTgB (.brTable x d tbl) := by
  have hsub := brSub hctx' hcl' 0
  have hW : szTermK ≤ termSzB (.brTable x d tbl) := by
    show 600 ≤ 1500 + 2 * (1 + tbl.length); omega
  have hT : tgTermK ≤ termTgB (.brTable x d tbl) := by
    show 2 ≤ 2 + tbl.length; omega
  exact branch_sz hctx' hcl' hW hT (Try := fun _ => False)
    (Br := fun rl => rl ∈ program.rulesOf TId.lower_branch ∧ rl.id = 1140)
    (try_rules_unmatch hctx' hrt hd hslot)
    (fun rl hrl hid => .inr ⟨hrl, hid⟩) (fun _ h => h.elim)
    (fun rl ⟨hrl, hid⟩ => handW_mono (handW_brTable_wt hsub
      (subW_of_cost hctx' hcl' extW_wt oracleW_wt szCTab_ok fun ty => (cApply_ty _ _ ty _ _).trans cApply_556_wt0)
      (subW_of_cost hctx' hcl' extW_wt oracleW_wt szCTab_ok fun ty => (cApply_ty _ _ ty _ _).trans cApply_553_wt0)
      hrl hid) (by show 1500 + 2 * targets.length ≤ 1500 + 2 * (1 + tbl.length); omega))
    (fun rl ⟨hrl, hid⟩ => handW_mono (handW_brTable_tg hsub
      (subW_of_cost hctx' hcl' extW_tg oracleW_tg tgCTab_ok fun ty => (cApply_ty _ _ ty _ _).trans cApply_556_tg0)
      (subW_of_cost hctx' hcl' extW_tg oracleW_tg tgCTab_ok fun ty => (cApply_ty _ _ ty _ _).trans cApply_553_tg0)
      hrl hid) (by show targets.length ≤ 2 + tbl.length; omega)) h

set_option maxRecDepth 100000 in
/-- A `return`/`trap`'s `lower`: at most `szTermK` and `tgTermK`. -/
theorem retTrap_sz {c : Ctx} (hctx' : CtxInv f c) (hcl' : Cov.Clean c) {ti : Nat} {t : Clif.Terminator}
    {data : V} (hrt : retOrTrap (abiTerm f t) = true) (hd : termData (abiTerm f t) = .ok data)
    (hslot : c.insts[ti]? = some ⟨data, [], [], none⟩) {s : LState} {out : Option V} {s' : LState}
    {tr : List Isle.RuleId} (h : runTerm c "lower" [.inst ti] s = .ok (out, s', tr)) :
    wtA s'.emitted ≤ wtA s.emitted + szTermK ∧ tgA s'.emitted ≤ tgA s.emitted + tgTermK := by
  obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hrulesW : ∀ rl ∈ program.rulesOf T.lower.id,
      cRuleLe program covTab actorW szCTab aext actor apre aOracle [AW.c0] szTermK rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem c) {} m rl [.inst ti]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    cases hroot : termRootRule rl with
    | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
    | true =>
      have hf := List.all_eq_true.mp szTerm_ok rl hrl
      simp only [termRootRule] at hroot
      simp only [hroot, Bool.not_true, Bool.false_or] at hf
      exact .inl hf
  have hrulesT : ∀ rl ∈ program.rulesOf T.lower.id,
      cRuleLe program covTab actorT tgCTab aext actor apre aOracle [AW.c0] tgTermK rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem c) {} m rl [.inst ti]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    cases hroot : termRootRule rl with
    | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
    | true =>
      have hf := List.all_eq_true.mp tgTerm_ok rl hrl
      simp only [termRootRule] at hroot
      simp only [hroot, Bool.not_true, Bool.false_or] at hf
      exact .inl hf
  exact ⟨cost_root (md := covModel logicImmComplete hctx' hcl' s) rfl (cov_sa hctx' hcl' s rfl)
      extW_wt oracleW_wt szCTab_ok data_program.t686 term_686_kind hrulesW ⟨γ_c0_inst ti, trivial⟩
      (covSince_refl s) happ,
    cost_root (md := covModel logicImmComplete hctx' hcl' s) rfl (cov_sa hctx' hcl' s rfl)
      extW_tg oracleW_tg tgCTab_ok data_program.t686 term_686_kind hrulesT ⟨γ_c0_inst ti, trivial⟩
      (covSince_refl s) happ⟩

/-- **A terminator's lowering** (with a label per successor): at most `termSzB` and `termTgB`. -/
theorem termCall_sz (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator} (hty : t.isTry = false)
    {data : V} (hd : termData (abiTerm f t) = .ok data) {targets : List Label}
    (hlen : targets.length ≤ (dests t).length) {s : LState}
    {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) :
    wtA s'.emitted ≤ wtA s.emitted + termSzB t ∧ tgA s'.emitted ≤ tgA s.emitted + termTgB t := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have hctx' := ctxInv_termCtx hctx hph data
  have hcl' := clean_termCtx hcl hd ti
  have hslot := termCtx_self hti data
  unfold termCallF at h
  cases t with
  | ret vs => exact retTrap_sz hctx' hcl' rfl hd hslot h
  | trap c => exact retTrap_sz hctx' hcl' rfl hd hslot h
  | jump bc =>
    have hnb : ∀ fs, data ≠ .data 152 4 fs := by
      intro fs he
      rw [show abiTerm f (.jump bc) = .jump bc from rfl, termData_jump] at hd
      cases hd; cases he
    exact jumpBrif_sz hctx' hcl' rfl hd hslot hnb h
  | brif c a b =>
    have hnb : ∀ fs, data ≠ .data 152 4 fs := by
      intro fs he
      rw [show abiTerm f (.brif c a b) = .brif c a b from rfl, termData_brif] at hd
      cases hd; cases he
    exact jumpBrif_sz hctx' hcl' rfl hd hslot hnb h
  | brTable x d tb =>
    have hl : targets.length ≤ 1 + tb.length := by
      simp only [dests, List.length_cons] at hlen; omega
    exact brTable_sz hctx' hcl' rfl hd hslot hl h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [Clif.Terminator.isTry] at hty
  | tryCallIndirect callee args et => simp [Clif.Terminator.isTry] at hty

/-- **A `try_call`'s lowering**: at most `termSzB` (its call) and `termTgB`. -/
theorem tryCall_sz (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator} {et : Clif.ExnTable}
    (het : IsTryWith t et) {data : V} (hd : tryCallData f t = .ok data) {sig : Clif.Signature}
    {items : List (Option Nat)} (he : exnTableOpnd f et = .ok (sig, items)) {lo st1 : LState}
    {trs : List Reg × List Reg} (htr : tryRegsOf sig lo = some (trs, st1)) {targets : List Label}
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : tryCallF ctx ti data trs targets s = .ok (out, s', tr)) :
    wtA s'.emitted ≤ wtA s.emitted + termSzB t ∧ tgA s'.emitted ≤ tgA s.emitted + termTgB t := by
  have h' := ctxInv_termCtx hctx hph data
  have hctx' : CtxInv f (tryCtx ctx ti data trs) := { h' with }
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hK : szTermK ≤ termSzB t := by unfold termSzB szCallB szTermK szBrK; split <;> omega
  have hKT : tgTermK ≤ termTgB t := by
    rcases het with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [termTgB]
  exact branch_sz hctx' (clean_tryCtx hcl hd ti trs) hK hKT
    (Try := fun rl => rl ∈ program.rulesOf TId.lower_branch ∧ (rl.id = 1034 ∨ rl.id = 1035 ∨ rl.id = 1036))
    (Br := fun _ => False)
    (fun rl hrl hid => .inr ⟨hrl, hid⟩)
    (fun _ hrl hid => .inl fun m s0 env s1 =>
      br1140_unmatch hi (tryCallData_ne_brTable hd) hrl hid {} m s0 env s1)
    (fun rl ⟨hrl, hid⟩ => handW_try hctx hph het hd he htr hrl hid)
    (fun _ h => h.elim) (fun _ h => h.elim) h

/-! ## `IselSz` -/

/-- **The ISLE runs of the driver are bounded** for every in-scope function. -/
theorem iselSz (hs : LowerScope f) : IselSz f := by
  intro ctx ranges st0 hb
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  have hcl : Cov.Clean ctx := clean_of_build hb
  exact ⟨fun ii info inst s out s' tr hi hc h => stmt_sz hctx hcl hi hc h,
    fun ti t data targets s out s' tr _ hph hty hd hlen h => termCall_sz hctx hcl hph hty hd hlen h,
    fun ti t et data sig items lo st1 trs targets s out s' tr _ hph het hd he htr h =>
      tryCall_sz hctx hcl hph het hd he htr h⟩

end Backend.Proof.Driver
