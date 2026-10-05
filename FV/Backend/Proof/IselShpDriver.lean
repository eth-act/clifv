import FV.Backend.Proof.IselShpRoot
import FV.Backend.Proof.IselShpTab
import FV.Backend.Proof.IselShpTotal
import FV.Backend.Proof.IselShpCtor
import FV.Backend.Proof.IselShpOracle
import FV.Backend.Proof.IselShpCall
import FV.Backend.Proof.IselShpTry
import FV.Backend.Proof.IselShpBrTable
import FV.Backend.Proof.IselCovDriver
import FV.Backend.Proof.LowerLoopRun

/-!
# Control shapes of the ISLE lowering (V4): the driver's calls, `IselCtlHyp`

The control-shape model `shpModel` (V3's abstract interpreter with `apreS`/`aOracleS`, state
invariant `ShpIs N s0`), its soundness on the table `shpTab`, and the driver's three ISLE calls:
a statement's `lower` (`stmt_shp`), a terminator's `lower`/`lower_branch` (`termCall_shp`), a
`try_call`'s `lower_branch` (`tryCall_shp`). The root rules the interpreter does not check are
the hand-checked ones (`handOk_call`, `handOk_try`, `handOk_brTable`); `try_call` rules never
match a non-`try` terminator (`branchExcludedUnmatchable`). **`iselCtlHyp : IselCtlHyp`.**
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Cov Backend.Proof.Spill Isle Isle.Interp
  Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

/-! ## The model -/

/-- The oracles are sound: `operand_size` (state unchanged) and the control helpers. -/
theorem oracleS_sound (hctx : CtxInv f ctx) (N : Nat) (s0 : LState) (cfg : Config)
    (hc : cfg.checkOverlap = false) (n : Nat) (ty : TypeId) (t : TermId) (as : List AW) (vs : List V)
    (a : AW) (s : LState) (tr : Array RuleId) (r : Option V) (s' : LState) (tr' : Array RuleId)
    (ha : aOracleS t as = some a) (hvs : Holds2 f ctx as vs) (hIs : ShpIs N s0 s)
    (h : (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    ShpIs N s0 s' ∧ ∀ v, r = some v → γ f ctx a v := by
  unfold aOracleS at ha
  cases hos : aOracle t as with
  | some a' =>
    rw [hos] at ha
    cases ha
    have hγ := (oracle_sound s cfg hc n ty t as vs a s tr r s' tr' hos hvs (covSince_refl s) h).2
    have ht : t = 305 := by
      unfold aOracle at hos
      split at hos
      · exact eq_of_beq ‹_›
      · cases hos
    subst ht
    have hs := (os_run hc h).1
    simp only at hs
    subst hs
    exact ⟨hIs, hγ⟩
  | none =>
    rw [hos] at ha
    simp only at ha
    split at ha
    · cases ha
      exact oracle_ctl totality hctx hc ‹_› hvs hIs h
    · cases ha

/-- **The control-shape model** of the driver's semantics: state invariant `ShpIs N s0`. -/
def shpModel (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) (N : Nat) (s0 : LState) :
    CovModel actor apreS aOracleS program f ctx where
  Is := ShpIs N s0
  ext := fun a term v st fs hv h => ext_sound hctx hcl a term v st fs hv h
  ctor := fun as vs term v st st' hvs hIs hpre h =>
    ctorS_sound hctx N s0 as vs term v st st' hvs hIs hpre h
  oracle := oracleS_sound hctx N s0

theorem shp_sound (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) (N : Nat) (s0 : LState) {cfg : Config}
    (hc : cfg.checkOverlap = false) : ∀ n, SoundAt (shpModel hctx hcl N s0) cfg shpTab n :=
  soundAt (hctx := hctx) (md := shpModel hctx hcl N s0) (cfg := cfg) (tab := shpTab) hc shpTab_ok

/-- **`SubOk` from the table.** -/
theorem subOk_of_tab (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) (N : Nat) {t : TermId} {as : List AW}
    {out : AW} (h : ∀ ty, Cov.aApply program shpTab actor apreS aOracleS ty t as = some out) :
    SubOk f ctx N t as out := by
  intro cfg hc n ty vs s0 s tr r s' tr' hvs hIs hrun
  exact (shp_sound hctx hcl N s0 hc n).apply ty t as out vs s tr r s' tr' (h ty) hvs hIs hrun

/-- `aApply` of an internal term does not depend on the result type. -/
theorem aApply_internal_eq {t : TermId} {term : Term} {flags : TermFlags} {ex : Option Extractor}
    (ht : termOf program t = .ok term) (hk : term.kind = .decl flags (some .internal) ex) (ty : TypeId)
    (as : List AW) : Cov.aApply program shpTab actor apreS aOracleS ty t as =
      if as.any AW.isBot then some .bot else
        match aOracleS t as with
        | some a => some a
        | none => tabGet shpTab t as := by
  unfold Cov.aApply; rw [ht]; simp only [hk]; rfl

/-- An `Option AW` that is `some (.reg 1)`, as a test. -/
def isReg1 : Option AW → Bool
  | some (.reg 1) => true
  | _ => false

theorem eq_of_isReg1 : ∀ {o : Option AW}, isReg1 o = true → o = some (.reg 1)
  | some (.reg 1), _ => rfl

theorem tab_556 : isReg1 (if [AW.c0].any AW.isBot then some .bot else
    match aOracleS 556 [AW.c0] with
    | some a => some a
    | none => tabGet shpTab 556 [AW.c0]) = true := by native_decide

theorem tab_553 : isReg1 (if [AW.ty [.int 64], .data 122 1 [], .c0].any AW.isBot then some .bot else
    match aOracleS 553 [AW.ty [.int 64], .data 122 1 [], .c0] with
    | some a => some a
    | none => tabGet shpTab 553 [AW.ty [.int 64], .data 122 1 [], .c0]) = true := by native_decide

/-- The table's sub-runs of `br_table` (`put_in_reg_zext32`, `imm`). -/
theorem brSub (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) (N : Nat) : BrSub f ctx N :=
  ⟨hcl, subOk_of_tab hctx hcl N fun ty => by
      rw [aApply_internal_eq program_term_556 term_556_kind]; exact eq_of_isReg1 tab_556,
    subOk_of_tab hctx hcl N fun ty => by
      rw [aApply_internal_eq program_term_553 term_553_kind]; exact eq_of_isReg1 tab_553⟩

theorem shpIs_refl {N : Nat} {s : LState} (h : N ≤ s.nextVreg) : ShpIs N s s :=
  ⟨⟨[], by simp, by simp⟩, h⟩

/-- A hand-checked rule, at the model of `s0`. -/
theorem hand_model {ctx : Ctx} {N : Nat} {vs : List V} {rl : Rule} (h : HandOk ctx N vs rl)
    (s0 : LState) : ∀ (m n : Nat) (s : LState) (tr : Array RuleId) (env : Isle.Interp.Env V)
      (s1 : LState × Array RuleId) (r : Option V) (s2 : LState) (tr2 : Array RuleId),
      1000 ≤ m → 1000 ≤ n → ShpIs N s0 s →
      (matchRule program (sem ctx) {} m rl vs).run (s, tr) = .ok (some env, s1) →
      (evalExpr program (sem ctx) {} n rl.rhs env).run s1 = .ok (r, (s2, tr2)) → ShpIs N s0 s2 :=
  fun m n s tr env s1 r s2 tr2 hm hn hIs h1 h2 => h {} rfl m n s0 s tr env s1 r s2 tr2 hm hn hIs h1 h2

/-! ## Rule-data facts -/

theorem lower_len : 1002 + (program.rulesOf T.lower.id).length ≤ 999999 := by native_decide

theorem lower_branch_len : 1002 + (program.rulesOf T.lower_branch.id).length ≤ 999999 := by
  native_decide

theorem lower_hand_ids : (program.rulesOf TId.lower).all (fun r => !shpHandIds.contains r.id ||
    r.id == 1031 || r.id == 1032 || r.id == 1033) = true := by native_decide

theorem branch_hand_ids : (program.rulesOf TId.lower_branch).all (fun r => !shpHandIds.contains r.id ||
    ((r.id == 1034 || r.id == 1035 || r.id == 1036) && !closureRoot r) || r.id == 1140) = true := by
  native_decide

/-! ## The driver's calls -/

set_option maxRecDepth 100000 in
/-- **A statement's lowering emits control forms of their shapes.** -/
theorem stmt_shp (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) (ha : AbiSigsOk f) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hmem : ∃ B ∈ f.blocks, ∃ st ∈ B.body, st.inst = inst) {s : LState} {out : Option V}
    {s' : LState} {tr : List Isle.RuleId} (hN : ctx.valDef.size ≤ s.nextVreg)
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) : CtlSince ctx.valDef.size s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      aRule program shpTab aext actor apreS aOracleS [.xv .inst] AW.top rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1)) ∨
      (rl ∈ program.rulesOf TId.lower ∧ (rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033)) := by
    intro rl hrl
    have hf := List.all_eq_true.mp shpStmt_ok rl hrl
    have hid := List.all_eq_true.mp lower_hand_ids rl hrl
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hf
    rcases hf with (hcr | hh) | ha
    · exact .inr (.inl (lower_nonroot_nomatch hctx hi hc hrl hcr))
    · simp only [hh, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hid
      exact .inr (.inr ⟨hrl, or_assoc.mp hid⟩)
    · exact .inl ha
  exact (root_hand (md := shpModel hctx hcl ctx.valDef.size s) rfl (shp_sound hctx hcl _ s rfl)
    (Hand := fun rl => rl ∈ program.rulesOf TId.lower ∧ (rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033))
    (fun rl ⟨hrl, hid⟩ => hand_model (handOk_call totality hctx ha hi hc hmem hrl hid _) s)
    data_program.t686 term_686_kind hrules (holds_inst hctx hi hc) (shpIs_refl hN) (n := 999999)
    lower_len happ).1

set_option maxRecDepth 100000 in
/-- `lower_branch` with the `br_table` rule checked by hand and the `try_call` rules excluded
(`Excl`) or checked by hand (`Try`). -/
theorem branch_shp (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) (N : Nat) {ti : Nat} {targets : List Label}
    {Try : Rule → Prop}
    (htry : ∀ rl ∈ program.rulesOf TId.lower_branch, (rl.id = 1034 ∨ rl.id = 1035 ∨ rl.id = 1036) →
      closureRoot rl = false →
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ti, .labels targets]).run s0 ≠
        .ok (some env, s1)) ∨ Try rl)
    (hTry : ∀ rl, Try rl → HandOk ctx N [.inst ti, .labels targets] rl)
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId} (hN : N ≤ s.nextVreg)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    CtlSince N s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  have hrules : ∀ rl ∈ program.rulesOf T.lower_branch.id,
      aRule program shpTab aext actor apreS aOracleS [AW.c0, AW.c0] AW.top rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ti, .labels targets]).run s0 ≠
        .ok (some env, s1)) ∨ (Try rl ∨ (rl ∈ program.rulesOf TId.lower_branch ∧ rl.id = 1140)) := by
    intro rl hrl
    have hf := List.all_eq_true.mp shpBranch_ok rl hrl
    have hid := List.all_eq_true.mp branch_hand_ids rl hrl
    simp only [Bool.or_eq_true] at hf
    rcases hf with hh | ha
    · simp only [hh, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        Bool.not_eq_true'] at hid
      rcases hid with ⟨hid, hcr⟩ | hid
      · rcases htry rl hrl (or_assoc.mp hid) hcr with hno | hT
        · exact .inr (.inl hno)
        · exact .inr (.inr (.inl hT))
      · exact .inr (.inr (.inr ⟨hrl, hid⟩))
    · exact .inl ha
  exact (root_hand (md := shpModel hctx hcl N s) rfl (shp_sound hctx hcl _ s rfl)
    (Hand := fun rl => Try rl ∨ (rl ∈ program.rulesOf TId.lower_branch ∧ rl.id = 1140))
    (fun rl hrl => by
      rcases hrl with hT | ⟨hrl, hid⟩
      · exact hand_model (hTry rl hT) s
      · exact hand_model (handOk_brTable totality hctx (brSub hctx hcl) hrl hid N) s)
    data_program.t687 term_687_kind hrules ⟨γ_c0_inst ti, γ_c0_labels targets, trivial⟩
    (shpIs_refl hN) (n := 999999) lower_branch_len happ).1

set_option maxRecDepth 100000 in
/-- **A terminator's lowering emits control forms of their shapes.** -/
theorem termCall_shp (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator} (hty : t.isTry = false)
    {data : V} (hd : termData (abiTerm f t) = .ok data) {targets : List Label} {s : LState}
    {out : Option V} {s' : LState} {tr : List Isle.RuleId} (hN : ctx.valDef.size ≤ s.nextVreg)
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) : CtlSince ctx.valDef.size s s' := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have hctx' := ctxInv_termCtx hctx hph data
  have hcl' := clean_termCtx hcl hd ti
  have hslot := termCtx_self hti data
  unfold termCallF at h
  have hbranch : retOrTrap (abiTerm f t) = false →
      runTerm (termCtx ctx ti data) "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr) →
      CtlSince ctx.valDef.size s s' := fun hrt h =>
    branch_shp hctx' hcl' _ (Try := fun _ => False)
      (fun rl hrl _ hcr => .inl fun m s0 env s1 =>
        branchExcludedUnmatchable rl hrl hcr f _ hctx' ti _ data targets hrt hd hslot {} m s0 env s1)
      (fun _ h => h.elim) hN h
  have hlower : retOrTrap (abiTerm f t) = true →
      runTerm (termCtx ctx ti data) "lower" [.inst ti] s = .ok (out, s', tr) →
      CtlSince ctx.valDef.size s s' := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower] at ht
    cases ht
    have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
        aRule program shpTab aext actor apreS aOracleS [AW.c0] AW.top rl = true ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl [.inst ti]).run s0 ≠
            .ok (some env, s1) := by
      intro rl hrl
      cases hroot : termRootRule rl with
      | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
      | true =>
        have hf := List.all_eq_true.mp shpTerm_ok rl hrl
        simp only [termRootRule] at hroot
        simp only [hroot, Bool.not_true, Bool.false_or] at hf
        exact .inl hf
    exact ((shp_sound hctx' hcl' ctx.valDef.size s rfl 1000000).root T.lower.ret T.lower.id T.lower _ _
      [AW.c0] AW.top [.inst ti] s #[] out s' tr' data_program.t686 term_686_kind hrules
      ⟨γ_c0_inst ti, trivial⟩ (shpIs_refl hN) happ).1.1
  cases t with
  | ret vs => exact hlower rfl h
  | trap c => exact hlower rfl h
  | jump bc => exact hbranch rfl h
  | brif c a b => exact hbranch rfl h
  | brTable x d tb => exact hbranch rfl h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [Clif.Terminator.isTry] at hty
  | tryCallIndirect callee args et => simp [Clif.Terminator.isTry] at hty

/-- The signature of a `try_call_indirect` terminator of `f` passes `sigAbiOk`. -/
theorem tryInd_sig (ha : AbiSigsOk f) {t : Clif.Terminator} {et : Clif.ExnTable}
    {sig : Clif.Signature} {items : List (Option Nat)} (hB : ∃ B ∈ f.blocks, B.term = t)
    (he : exnTableOpnd f et = .ok (sig, items)) :
    ∀ callee args, t = .tryCallIndirect callee args et → sigAbiOk sig = true := by
  intro callee args rfl
  obtain ⟨B, hB, hBt⟩ := hB
  have hl : f.sigDecls.lookup et.sig = some sig := by
    unfold exnTableOpnd at he
    cases hs : f.sigDecls.lookup et.sig with
    | none => simp [hs] at he
    | some sig' =>
      simp only [hs] at he
      split at he
      · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at he
      · simp only [bind, Except.bind, pure, Except.pure] at he
        split at he
        · cases he
        · simp only [Except.ok.injEq, Prod.mk.injEq] at he
          rw [he.1]
  have hmem : sig ∈ indSigs f := by
    simp only [indSigs, List.mem_flatMap, List.mem_append]
    exact ⟨B, hB, .inr (by rw [hBt]; simp [hl])⟩
  exact (ha.2 sig hmem).2

/-- **A `try_call`'s lowering emits control forms of their shapes.** -/
theorem tryCall_shp (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx) (ha : AbiSigsOk f) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator} {et : Clif.ExnTable}
    (het : IsTryWith t et) (hB : ∃ B ∈ f.blocks, B.term = t) {data : V}
    (hd : tryCallData f t = .ok data) {sig : Clif.Signature} {items : List (Option Nat)}
    (he : exnTableOpnd f et = .ok (sig, items)) {lo st1 : LState} {trs : List Reg × List Reg}
    (hlo : ctx.valDef.size ≤ lo.nextVreg) (htr : tryRegsOf sig lo = some (trs, st1))
    {targets : List Label} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (out, s', tr)) :
    CtlSince ctx.valDef.size { st1 with emitted := #[] } s' := by
  have h' := ctxInv_termCtx hctx hph data
  have hctx' : CtxInv f (tryCtx ctx ti data trs) := { h' with }
  have hst := (tryRegsOf_mono htr).1
  exact branch_shp hctx' (clean_tryCtx hcl hd ti trs) _
    (Try := fun rl => rl ∈ program.rulesOf TId.lower_branch ∧ (rl.id = 1034 ∨ rl.id = 1035 ∨ rl.id = 1036))
    (fun rl hrl hid _ => .inr ⟨hrl, hid⟩)
    (fun rl ⟨hrl, hid⟩ => handOk_try totality hctx ha hph het hd he (tryInd_sig ha hB he) _ hlo htr
      hrl hid)
    (by show ctx.valDef.size ≤ st1.nextVreg; omega) h

/-! ## The ISLE inversion -/

/-- **`IselCtlHyp`**: every ISLE run of the driver emits only control forms of the shapes
`CtlShape`, with defs above every value's vreg. -/
theorem iselCtlHyp : IselCtlHyp := by
  intro f ctx ranges st0 _ hs ha hb
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  have hcl : Cov.Clean ctx := clean_of_build hb
  refine ⟨fun ii info inst s out s' tr hi hc hN h => ?_,
    fun ti t data targets s out s' tr _ hph hty hd hN h => termCall_shp hctx hcl hph hty hd hN h,
    fun ti t et data sig items lo trs st1 targets out s' tr _ hph het hB hd he hlo htr h =>
      tryCall_shp hctx hcl ha hph het hB hd he hlo htr h⟩
  have hmem : ∃ B ∈ f.blocks, ∃ st ∈ B.body, st.inst = inst := by
    rcases (ctxSpec_of hb).insts info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) with
      rfl | ⟨B, hB, st, hst, rfl⟩
    · cases hc
    · exact ⟨B, hB, st, hst, Option.some.inj hc⟩
  exact stmt_shp hctx hcl ha hi hc hmem hN h

end Backend.Proof.Driver
