import FV.Backend.Proof.IselSzDriver
import FV.Backend.Proof.IselSzDefsT
import FV.Backend.Proof.IselSzExtT
import FV.Backend.Proof.IselSzSoundT
import FV.Backend.Proof.IselCovModelT
import FV.Backend.Proof.IselCovSoundT
import FV.Backend.Proof.IselExclT
import FV.Backend.Proof.IselCtlUnmatchTI
import FV.Backend.Proof.LowerLoopCtxT
import FV.Compile.SubsetT

/-!
# The size of the ISLE lowering's output over float-capable contexts: the driver's calls

The typed counterpart of `IselSzDriver`: `stmt_szT`, `termCall_szT`, `tryCall_szT` over a
float-capable context (`CtxInvT`, the scope `Compile.instET` with the opcode split
`opsT`/`floatOps`), on the typed tables (`covTabT`/`szCTabT`/`tgCTabT`) and the typed exclusion
`lower_nonroot_nomatchT`; **`iselSzT`: `IselSz f` for every function of the typed scope**
(`LowerScopeT`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Cov Backend.Proof.Spill Isle Isle.Interp
  Isle.Aarch64


open Backend.Proof.Cov Backend.Compile

/-! ## The typed context of a terminator -/

/-- `InstScopeT` of the terminator context. -/
theorem instScopeT_termCtx {f : Clif.Function} {ctx : Ctx} (h : InstScopeT ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V) :
    InstScopeT (termCtx ctx ti data) := by
  intro ii info inst hi hc
  by_cases e : ii = ti
  · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
  · rw [termCtx_insts_ne e] at hi; exact h ii info inst hi hc

/-- `InstSplit` of the terminator context. -/
theorem instSplit_termCtx {S : Clif.Inst → Bool} {f : Clif.Function} {ctx : Ctx}
    {iOps fOps : List Nat} (h : InstSplit S f ctx iOps fOps) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V) :
    InstSplit S f (termCtx ctx ti data) iOps fOps := by
  intro j info c hi hc hd
  by_cases e : j = ti
  · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
  · rw [termCtx_insts_ne e] at hi; exact h hi hc hd

variable {f : Clif.Function} {ctx : Ctx}
/-- A sub-run of an internal term the cost table bounds at `as` (`SubW`), from `costAt`. -/
theorem subW_of_costT (hctx : CtxInvT f ctx) (hsp : InstSplit Compile.instET f ctx opsT floatOps)
    (hsc : InstScopeT ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true) (hcl : Cov.Clean ctx) {aw : TermId → List AW → Option Nat}
    {ctab : CTab} {W : LState → Nat} (hext : ExtW f ctx apre aw W) (hor : OracleW program f ctx aOracle W)
    (hct : chkCost program covTabT aw ctab aext actor apre aOracle = true) {t : TermId} {as : List AW}
    {c : Nat} (hca : ∀ ty, cApply program covTabT aw ctab apre aOracle ty t as = some c) :
    SubW program f ctx t as W c := by
  intro cfg hc n ty vs s tr r s' tr' hvs h
  exact (costAt (md := covModelT logicImmComplete hctx hsp hsc hx hcl s) hc (cov_sa hctx hsp hsc hx hcl s hc) hext
    (fun cfg' hc' => hor cfg' hc') hct n).apply ty t as c vs s tr r s' tr' (hca ty) hvs
    (covSince_refl s) h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem cApply_556_wt0T : cApply program covTabT actorW szCTabT apre aOracle 0 556 [.c0] = some 107 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem cApply_553_wt0T :
    cApply program covTabT actorW szCTabT apre aOracle 0 553 [.ty [.int 64], .data 122 1 [], .c0] =
      some 428 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem cApply_556_tg0T : cApply program covTabT actorT tgCTabT apre aOracle 0 556 [.c0] = some 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem cApply_553_tg0T :
    cApply program covTabT actorT tgCTabT apre aOracle 0 553 [.ty [.int 64], .data 122 1 [], .c0] =
      some 0 := by decide +kernel
/-! ## The driver's calls -/

set_option maxRecDepth 100000 in
/-- **A statement's lowering emits at most `stmtSzB` and `tgStmtK` targets.** -/
theorem stmt_szT (hctx : CtxInvT f ctx) (hsp : InstSplit Compile.instET f ctx opsT floatOps)
    (hsc : InstScopeT ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true) (hcl : Cov.Clean ctx) {ii : Nat} {info : IInfo}
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
      cRuleLe program covTabT actorW szCTabT aext actor apre aOracle [.xv .inst] (stmtSzB inst) rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1)) ∨
      (rl ∈ program.rulesOf TId.lower ∧ (rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033)) := by
    intro rl hrl
    have hf := List.all_eq_true.mp szStmt_okT rl hrl
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hf
    rcases hf with (((hcr | h1) | h2) | h3) | hle
    · exact .inr (.inl (lower_nonroot_nomatchT hctx hsc hx hi hc hrl hcr {}))
    · exact .inr (.inr ⟨hrl, .inl h1⟩)
    · exact .inr (.inr ⟨hrl, .inr (.inl h2)⟩)
    · exact .inr (.inr ⟨hrl, .inr (.inr h3)⟩)
    · exact .inl (cRuleLe_mono hle hK)
  have hrulesT : ∀ rl ∈ program.rulesOf T.lower.id,
      cRuleLe program covTabT actorT tgCTabT aext actor apre aOracle [.xv .inst] tgStmtK rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1)) := by
    intro rl hrl
    have hf := List.all_eq_true.mp tgStmt_okT rl hrl
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hf
    rcases hf with hcr | hle
    · exact .inr (lower_nonroot_nomatchT hctx hsc hx hi hc hrl hcr {})
    · exact .inl hle
  refine ⟨?_, ?_⟩
  · exact cost_root_handT (md := covModelT logicImmComplete hctx hsp hsc hx hcl s) rfl (cov_sa hctx hsp hsc hx hcl s rfl)
      extWT_wt oracleWT_wt szCTab_ok
      (Hand := fun rl => rl ∈ program.rulesOf TId.lower ∧ (rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033))
      (fun rl ⟨hrl, hid⟩ => handW_callT hctx hi hc hrl hid)
      data_program.t686 term_686_kind hrulesW (holds_instT hctx hi hc) (covSince_refl s) (n := 999999)
      lower_len happ
  · exact cost_rootT (md := covModelT logicImmComplete hctx hsp hsc hx hcl s) rfl (cov_sa hctx hsp hsc hx hcl s rfl)
      extWT_tg oracleWT_tg tgCTab_ok data_program.t686 term_686_kind hrulesT (holds_instT hctx hi hc)
      (covSince_refl s) happ

set_option maxRecDepth 100000 in
/-- `lower_branch` in a context with `CtxInv`/`Clean`, at an instruction whose data is `data`:
the rules other than the `try_call` (1034–1036) and `br_table` (1140) ones by the table, those
by the given hand facts or never matching. -/
theorem branch_szT (hctx : CtxInvT f ctx) (hsp : InstSplit Compile.instET f ctx opsT floatOps)
    (hsc : InstScopeT ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true) (hcl : Cov.Clean ctx) {ti : Nat} {targets : List Label}
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
  have hins : Holds2T Compile.instET opsT floatOps f ctx [AW.c0, AW.c0] [.inst ti, .labels targets] :=
    ⟨γT_c0_inst ti, γT_c0_labels targets, trivial⟩
  have hrulesW : ∀ rl ∈ program.rulesOf T.lower_branch.id,
      cRuleLe program covTabT actorW szCTabT aext actor apre aOracle [.c0, .c0] cW rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ti, .labels targets]).run s0 ≠
        .ok (some env, s1)) ∨ (Try rl ∨ Br rl) := by
    intro rl hrl
    have hf := List.all_eq_true.mp szBranch_okT rl hrl
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
      cRuleLe program covTabT actorT tgCTabT aext actor apre aOracle [.c0, .c0] cT rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ti, .labels targets]).run s0 ≠
        .ok (some env, s1)) ∨ Br rl := by
    intro rl hrl
    have hf := List.all_eq_true.mp tgBranch_okT rl hrl
    simp only [Bool.or_eq_true, beq_iff_eq] at hf
    rcases hf with h4 | hle
    · rcases hbr rl hrl h4 with hn | hB
      · exact .inr (.inl hn)
      · exact .inr (.inr hB)
    · exact .inl (cRuleLe_mono hle hcT)
  refine ⟨?_, ?_⟩
  · exact cost_root_handT (md := covModelT logicImmComplete hctx hsp hsc hx hcl s) rfl (cov_sa hctx hsp hsc hx hcl s rfl)
      extWT_wt oracleWT_wt szCTab_ok (Hand := fun rl => Try rl ∨ Br rl)
      (fun rl hrl => by
        rcases hrl with hT | hB
        · exact hTryW rl hT
        · exact hBrW rl hB)
      data_program.t687 term_687_kind hrulesW hins (covSince_refl s) (n := 999999) lower_branch_len happ
  · exact cost_root_handT (md := covModelT logicImmComplete hctx hsp hsc hx hcl s) rfl (cov_sa hctx hsp hsc hx hcl s rfl)
      extWT_tg oracleWT_tg tgCTab_ok (Hand := Br) hBrT
      data_program.t687 term_687_kind hrulesT hins (covSince_refl s) (n := 999999) lower_branch_len happ

/-- The `try_call` rules (1034–1036) never match a branch. -/
theorem try_rules_unmatchT {c : Ctx} (hctx' : CtxInv f c) {ti : Nat} {t : Clif.Terminator} {data : V}
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
theorem jumpBrif_szT {c : Ctx} (hctx' : CtxInv f c) (hcl' : Cov.Clean c) {ti : Nat} {t : Clif.Terminator}
    {data : V} {targets : List Label} (hrt : retOrTrap (abiTerm f t) = false)
    (hd : termData (abiTerm f t) = .ok data) (hslot : c.insts[ti]? = some ⟨data, [], [], none⟩)
    (hnb : ∀ fs, data ≠ .data 152 4 fs) {s : LState} {out : Option V} {s' : LState}
    {tr : List Isle.RuleId}
    (h : runTerm c "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    wtA s'.emitted ≤ wtA s.emitted + szTermK ∧ tgA s'.emitted ≤ tgA s.emitted + tgTermK :=
  branch_szT hctx' hcl' (Nat.le_refl _) (Nat.le_refl _) (Try := fun _ => False) (Br := fun _ => False)
    (try_rules_unmatchT hctx' hrt hd hslot)
    (fun _ hrl hid => .inl fun m s0 env s1 => br1140_unmatch hslot hnb hrl hid {} m s0 env s1)
    (fun _ h => h.elim) (fun _ h => h.elim) (fun _ h => h.elim) h

set_option maxRecDepth 100000 in
/-- A `br_table`'s `lower_branch` (a label per successor): at most `termSzB` and `termTgB`. -/
theorem brTable_szT {c : Ctx} (hctx' : CtxInv f c) (hcl' : Cov.Clean c) {ti : Nat} {x : Clif.ValueId}
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
  exact branch_szT hctx' hcl' hW hT (Try := fun _ => False)
    (Br := fun rl => rl ∈ program.rulesOf TId.lower_branch ∧ rl.id = 1140)
    (try_rules_unmatchT hctx' hrt hd hslot)
    (fun rl hrl hid => .inr ⟨hrl, hid⟩) (fun _ h => h.elim)
    (fun rl ⟨hrl, hid⟩ => handW_mono (handW_brTable_wt hsub
      (subW_of_costT hctx' hcl' extWT_wt oracleWT_wt szCTab_ok fun ty => (cApply_ty _ _ ty _ _).trans cApply_556_wt0T)
      (subW_of_costT hctx' hcl' extWT_wt oracleWT_wt szCTab_ok fun ty => (cApply_ty _ _ ty _ _).trans cApply_553_wt0T)
      hrl hid) (by show 1500 + 2 * targets.length ≤ 1500 + 2 * (1 + tbl.length); omega))
    (fun rl ⟨hrl, hid⟩ => handW_mono (handW_brTable_tg hsub
      (subW_of_costT hctx' hcl' extWT_tg oracleWT_tg tgCTab_ok fun ty => (cApply_ty _ _ ty _ _).trans cApply_556_tg0T)
      (subW_of_costT hctx' hcl' extWT_tg oracleWT_tg tgCTab_ok fun ty => (cApply_ty _ _ ty _ _).trans cApply_553_tg0T)
      hrl hid) (by show targets.length ≤ 2 + tbl.length; omega)) h

set_option maxRecDepth 100000 in
/-- A `return`/`trap`'s `lower`: at most `szTermK` and `tgTermK`. -/
theorem retTrap_szT {c : Ctx} (hctx' : CtxInv f c) (hcl' : Cov.Clean c) {ti : Nat} {t : Clif.Terminator}
    {data : V} (hrt : retOrTrap (abiTerm f t) = true) (hd : termData (abiTerm f t) = .ok data)
    (hslot : c.insts[ti]? = some ⟨data, [], [], none⟩) {s : LState} {out : Option V} {s' : LState}
    {tr : List Isle.RuleId} (h : runTerm c "lower" [.inst ti] s = .ok (out, s', tr)) :
    wtA s'.emitted ≤ wtA s.emitted + szTermK ∧ tgA s'.emitted ≤ tgA s.emitted + tgTermK := by
  obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hrulesW : ∀ rl ∈ program.rulesOf T.lower.id,
      cRuleLe program covTabT actorW szCTabT aext actor apre aOracle [AW.c0] szTermK rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem c) {} m rl [.inst ti]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    cases hroot : termRootRule rl with
    | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
    | true =>
      have hf := List.all_eq_true.mp szTerm_okT rl hrl
      simp only [termRootRule] at hroot
      simp only [hroot, Bool.not_true, Bool.false_or] at hf
      exact .inl hf
  have hrulesT : ∀ rl ∈ program.rulesOf T.lower.id,
      cRuleLe program covTabT actorT tgCTabT aext actor apre aOracle [AW.c0] tgTermK rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem c) {} m rl [.inst ti]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    cases hroot : termRootRule rl with
    | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
    | true =>
      have hf := List.all_eq_true.mp tgTerm_okT rl hrl
      simp only [termRootRule] at hroot
      simp only [hroot, Bool.not_true, Bool.false_or] at hf
      exact .inl hf
  exact ⟨cost_rootT (md := covModelT logicImmComplete hctx' hsp' hsc' hx hcl' s) rfl (cov_sa hctx' hsp' hsc' hx hcl' s rfl)
      extWT_wt oracleWT_wt szCTab_ok data_program.t686 term_686_kind hrulesW ⟨γT_c0_inst ti, trivial⟩
      (covSince_refl s) happ,
    cost_rootT (md := covModelT logicImmComplete hctx' hsp' hsc' hx hcl' s) rfl (cov_sa hctx' hsp' hsc' hx hcl' s rfl)
      extWT_tg oracleWT_tg tgCTab_ok data_program.t686 term_686_kind hrulesT ⟨γT_c0_inst ti, trivial⟩
      (covSince_refl s) happ⟩

/-- **A terminator's lowering** (with a label per successor): at most `termSzB` and `termTgB`. -/
theorem termCall_szT (hctx : CtxInvT f ctx) (hsp : InstSplit Compile.instET f ctx opsT floatOps)
    (hsc : InstScopeT ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true) (hcl : Cov.Clean ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator} (hty : t.isTry = false)
    {data : V} (hd : termData (abiTerm f t) = .ok data) {targets : List Label}
    (hlen : targets.length ≤ (dests t).length) {s : LState}
    {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) :
    wtA s'.emitted ≤ wtA s.emitted + termSzB t ∧ tgA s'.emitted ≤ tgA s.emitted + termTgB t := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have hctx' := ctxInvT_termCtx hctx hph data
  have hcl' := clean_termCtx hcl hd ti
  have hslot := termCtx_self hti data
  unfold termCallF at h
  cases t with
  | ret vs => exact retTrap_szT hctx' hcl' rfl hd hslot h
  | trap c => exact retTrap_szT hctx' hcl' rfl hd hslot h
  | jump bc =>
    have hnb : ∀ fs, data ≠ .data 152 4 fs := by
      intro fs he
      rw [show abiTerm f (.jump bc) = .jump bc from rfl, termData_jump] at hd
      cases hd; cases he
    exact jumpBrif_szT hctx' hcl' rfl hd hslot hnb h
  | brif c a b =>
    have hnb : ∀ fs, data ≠ .data 152 4 fs := by
      intro fs he
      rw [show abiTerm f (.brif c a b) = .brif c a b from rfl, termData_brif] at hd
      cases hd; cases he
    exact jumpBrif_szT hctx' hcl' rfl hd hslot hnb h
  | brTable x d tb =>
    have hl : targets.length ≤ 1 + tb.length := by
      simp only [dests, List.length_cons] at hlen; omega
    exact brTable_szT hctx' hcl' rfl hd hslot hl h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [Clif.Terminator.isTry] at hty
  | tryCallIndirect callee args et => simp [Clif.Terminator.isTry] at hty

/-- **A `try_call`'s lowering**: at most `termSzB` (its call) and `termTgB`. -/
theorem tryCall_szT (hctx : CtxInvT f ctx) (hsp : InstSplit Compile.instET f ctx opsT floatOps)
    (hsc : InstScopeT ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true) (hcl : Cov.Clean ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator} {et : Clif.ExnTable}
    (het : IsTryWith t et) {data : V} (hd : tryCallData f t = .ok data) {sig : Clif.Signature}
    {items : List (Option Nat)} (he : exnTableOpnd f et = .ok (sig, items)) {lo st1 : LState}
    {trs : List Reg × List Reg} (htr : tryRegsOf sig lo = some (trs, st1)) {targets : List Label}
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : tryCallF ctx ti data trs targets s = .ok (out, s', tr)) :
    wtA s'.emitted ≤ wtA s.emitted + termSzB t ∧ tgA s'.emitted ≤ tgA s.emitted + termTgB t := by
  have h' := ctxInvT_termCtx hctx hph data
  have hctx' : CtxInv f (tryCtx ctx ti data trs) := { h'.toCtxInv with }
  have hctx'T : CtxInvT f (tryCtx ctx ti data trs) := h'
  have hsc' : InstScopeT (tryCtx ctx ti data trs) := instScopeT_termCtx hsc hph data
  have hsp' : InstSplit Compile.instET f (tryCtx ctx ti data trs) opsT floatOps :=
    instSplit_termCtx hsp hph data
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hK : szTermK ≤ termSzB t := by unfold termSzB szCallB szTermK szBrK; split <;> omega
  have hKT : tgTermK ≤ termTgB t := by
    rcases het with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [termTgB]
  exact branch_szT hctx'T hsp' hsc' hx (clean_tryCtx hcl hd ti trs) hK hKT
    (Try := fun rl => rl ∈ program.rulesOf TId.lower_branch ∧ (rl.id = 1034 ∨ rl.id = 1035 ∨ rl.id = 1036))
    (Br := fun _ => False)
    (fun rl hrl hid => .inr ⟨hrl, hid⟩)
    (fun _ hrl hid => .inl fun m s0 env s1 =>
      br1140_unmatch hi (tryCallData_ne_brTable hd) hrl hid {} m s0 env s1)
    (fun rl ⟨hrl, hid⟩ => handW_tryT hctx hph het hd he htr hrl hid)
    (fun _ h => h.elim) (fun _ h => h.elim) h

/-! ## `IselSzT` -/

/-- **The ISLE runs of the driver are bounded** for every in-scope function. -/
theorem iselSzT (hs : LowerScopeT f) : IselSz f := by
  intro ctx ranges st0 hb
  have hctx : CtxInvT f ctx := ctxInvT_of hs hb
  have hcl : Cov.Clean ctx := clean_of_build hb
  have hsc : InstScopeT ctx := (ctxSpec_of hb).instScopeT hs.subsetT
  have hx : f.externs.all (Compile.sigE ·.2.sig) = true := functionET_externs hs.subsetT
  have hsp : InstSplit Compile.instET f ctx opsT floatOps := inst_split hctx hsc hx
  exact ⟨fun ii info inst s out s' tr hi hc h => stmt_szT hctx hsp hsc hx hcl hi hc h,
    fun ti t data targets s out s' tr _ hph hty hd hlen h =>
      termCall_szT hctx hsp hsc hx hcl hph hty hd hlen h,
    fun ti t et data sig items lo st1 trs targets s out s' tr _ hph het hd he htr h =>
      tryCall_szT hctx hsp hsc hx hcl hph het hd he htr h⟩

end Backend.Proof.Driver
