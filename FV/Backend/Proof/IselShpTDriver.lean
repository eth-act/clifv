import FV.Backend.Proof.IselShpTModel
import FV.Backend.Proof.IselShpTTab
import FV.Backend.Proof.IselShpTCall
import FV.Backend.Proof.IselShpTTry
import FV.Backend.Proof.IselShpTBrTable
import FV.Backend.Proof.IselShpDriver
import FV.Backend.Proof.IselCovTDriver
import FV.Backend.Proof.IselCovTFamCover
import FV.Backend.Proof.LowerShapeOkT

/-!
# Control shapes of the typed ISLE lowering: the driver's calls, `IselCtlHypT`

`IselShpDriver` over typed contexts: the typed control-shape model `shpModelT` is sound on the
table `shpTabT` (`IselShpTTab`), and the driver's three ISLE calls emit only control forms of
the typed shapes: a statement's `lower` on its instruction family (`stmt_shpT`), a terminator's
`lower`/`lower_branch` on its family (`termCall_shpT`), a `try_call`'s `lower_branch`
(`tryCall_shpT`). The root rules the interpreter does not check are the hand-checked ones
(`handOkT_call`, `handOkT_try`, `handOkT_brTable`); `try_call` rules never match a non-`try`
terminator (`branchExcludedUnmatchableT_program`). **`iselCtlHypT : IselCtlHypT`.**
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (Clean LogicImmComplete Totality totality shpHandIds clean_termCtx
  clean_tryCtx logicImmComplete)
open Backend.Proof.Driver

variable {f : Clif.Function} {ctx : Ctx}

/-! ## Root terms with hand-checked rules (typed domain) -/

section
variable {p : Program} {aext : TermId → AT → List AT} {actor : TermId → List AT → AT}
  {apre : TermId → List AT → Bool} {aOracle : TermId → List AT → Option AT}
  {md : CovModel aext actor apre aOracle p f ctx} {cfg : Config} {tab : Tab}

/-- **A root term whose rules pass `aRule`, never match, or are checked by hand** keeps the
invariant (`Cov.root_hand` over `AT`). -/
theorem root_handT (hc : cfg.checkOverlap = false) (sa : ∀ n, SoundAt md cfg tab n)
    {vs : List V} {Hand : Rule → Prop}
    (hhand : ∀ rl, Hand rl → ∀ (m n : Nat) (s : LState) (tr : Array RuleId) (env : Isle.Interp.Env V)
      (s1 : LState × Array RuleId) (r : Option V) (s2 : LState) (tr2 : Array RuleId),
      1000 ≤ m → 1000 ≤ n → md.Is s →
      (matchRule p (sem ctx) cfg m rl vs).run (s, tr) = .ok (some env, s1) →
      (evalExpr p (sem ctx) cfg n rl.rhs env).run s1 = .ok (r, (s2, tr2)) → md.Is s2)
    {ty : TypeId} {t : TermId} {term : Term} {flags : TermFlags} {ex : Option Extractor}
    {ins : List AT} {out : AT} {s : LState} {tr : Array RuleId} {r : Option V} {s' : LState}
    {tr' : Array RuleId} (ht : termOf p t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    (hrules : ∀ rl ∈ p.rulesOf t, aRule p tab aext actor apre aOracle ins out rl = true ∨
      (∀ m s0 env s1, (matchRule p (sem ctx) cfg m rl vs).run s0 ≠ .ok (some env, s1)) ∨ Hand rl)
    (hins : Holds2 f ctx ins vs) (hIs : md.Is s) {n : Nat} (hn : 1002 + (p.rulesOf t).length ≤ n)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty t vs).run (s, tr) = .ok (r, (s', tr'))) : md.Is s' := by
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
    · cases pure_ok h2; exact hIs
    · exact (throw_ok h2).elim
  | some re =>
    obtain ⟨rl, env⟩ := re
    obtain ⟨hrl, m, hmn, hmatch⟩ := selectRule_some_lt hc h1
    simp only at h2
    obtain ⟨ev, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
    have hfin : md.Is s2 → md.Is s' := by
      intro hIs2
      cases ev with
      | some v =>
        obtain ⟨u, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
        have hf := fire_ok h5
        cases pure_ok h6
        simp only at hf
        subst hf
        exact hIs2
      | none => cases pure_ok h4; exact hIs2
    rcases hrules rl hrl with hok | hno | hhd
    · obtain ⟨envs, hae, hall⟩ := aRule_inv hok
      obtain ⟨hIs1, aenv, haenv, he1⟩ := (sa m).mrule _ _ _ _ _ _ _ _ _ hae hins hIs hmatch
      obtain ⟨a, ha, -⟩ := hall aenv haenv
      exact hfin ((sa n).expr _ _ _ _ _ _ _ _ _ ha he1 hIs1 h3).1
    · exact absurd hmatch (hno m _ _ _)
    · obtain ⟨-, m', hm', hmatch'⟩ := selectRule_some hc h1
      exact hfin (hhand rl hhd m' n s tr env _ ev s2 tr2 (by omega) (by omega) hIs hmatch' h3)

end

/-! ## The model on the table -/

theorem shp_soundT (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) (N : Nat)
    (s0 : LState) {cfg : Config} (hc : cfg.checkOverlap = false) :
    ∀ n, SoundAt (shpModelT logicImmComplete hctx hcl hfam N s0) cfg shpTabT n :=
  soundAt (md := shpModelT logicImmComplete hctx hcl hfam N s0) (cfg := cfg) (tab := shpTabT) hc
    shpTabT_ok

/-- **`SubOkT` from the table.** -/
theorem subOkT_of_tab (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) (N : Nat)
    {t : TermId} {as : List AT} {out : AT}
    (h : ∀ ty, aApply program shpTabT actor apreST aOracleST ty t as = some out) :
    SubOkT f ctx N t as out := by
  intro cfg hc n ty vs s0 s tr r s' tr' hvs hIs hrun
  exact (shp_soundT hctx hcl hfam N s0 hc n).apply ty t as out vs s tr r s' tr' (h ty) hvs hIs hrun

/-- `aApply` of an internal term does not depend on the result type. -/
theorem aApply_internal_eqT {t : TermId} {term : Term} {flags : TermFlags} {ex : Option Extractor}
    (ht : termOf program t = .ok term) (hk : term.kind = .decl flags (some .internal) ex) (ty : TypeId)
    (as : List AT) : aApply program shpTabT actor apreST aOracleST ty t as =
      if as.any AT.isBot then some .bot else
        match aOracleST t as with
        | some a => some a
        | none => tabGet shpTabT t as := by
  unfold aApply; rw [termOfT_eq, ht]; simp only [hk]; rfl

/-- An `Option AT` that is `some (.reg 1)`, as a test. -/
def isReg1T : Option AT → Bool
  | some (.reg 1) => true
  | _ => false

theorem eq_of_isReg1T : ∀ {o : Option AT}, isReg1T o = true → o = some (.reg 1)
  | some (.reg 1), _ => rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem tabT_556_8 : isReg1T (if [AT.val [.int 8]].any AT.isBot then some .bot else
    match aOracleST 556 [AT.val [.int 8]] with
    | some a => some a
    | none => tabGet shpTabT 556 [AT.val [.int 8]]) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem tabT_556_16 : isReg1T (if [AT.val [.int 16]].any AT.isBot then some .bot else
    match aOracleST 556 [AT.val [.int 16]] with
    | some a => some a
    | none => tabGet shpTabT 556 [AT.val [.int 16]]) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem tabT_556_32 : isReg1T (if [AT.val [.int 32]].any AT.isBot then some .bot else
    match aOracleST 556 [AT.val [.int 32]] with
    | some a => some a
    | none => tabGet shpTabT 556 [AT.val [.int 32]]) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem tabT_556_64 : isReg1T (if [AT.val [.int 64]].any AT.isBot then some .bot else
    match aOracleST 556 [AT.val [.int 64]] with
    | some a => some a
    | none => tabGet shpTabT 556 [AT.val [.int 64]]) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem tabT_553 : isReg1T (if [AT.ty [.int 64], .data 122 1 [], .c0].any AT.isBot then some .bot else
    match aOracleST 553 [AT.ty [.int 64], .data 122 1 [], .c0] with
    | some a => some a
    | none => tabGet shpTabT 553 [AT.ty [.int 64], .data 122 1 [], .c0]) = true := by decide +kernel

/-- The table's sub-runs of `br_table` (`put_in_reg_zext32`, `imm`). -/
theorem brSubT (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) (N : Nat) :
    BrSubT f ctx N :=
  ⟨hcl, fun w hw => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact subOkT_of_tab hctx hcl hfam N fun ty => by
          rw [aApply_internal_eqT program_term_556 term_556_kind]; exact eq_of_isReg1T tabT_556_8
      · exact subOkT_of_tab hctx hcl hfam N fun ty => by
          rw [aApply_internal_eqT program_term_556 term_556_kind]; exact eq_of_isReg1T tabT_556_16
      · exact subOkT_of_tab hctx hcl hfam N fun ty => by
          rw [aApply_internal_eqT program_term_556 term_556_kind]; exact eq_of_isReg1T tabT_556_32
      · exact subOkT_of_tab hctx hcl hfam N fun ty => by
          rw [aApply_internal_eqT program_term_556 term_556_kind]; exact eq_of_isReg1T tabT_556_64,
    subOkT_of_tab hctx hcl hfam N fun ty => by
      rw [aApply_internal_eqT program_term_553 term_553_kind]; exact eq_of_isReg1T tabT_553⟩

/-- A hand-checked rule, at the model of `s0`. -/
theorem hand_modelT {ctx : Ctx} {N : Nat} {vs : List V} {rl : Rule} (h : HandOkT ctx N vs rl)
    (s0 : LState) : ∀ (m n : Nat) (s : LState) (tr : Array RuleId) (env : Isle.Interp.Env V)
      (s1 : LState × Array RuleId) (r : Option V) (s2 : LState) (tr2 : Array RuleId),
      1000 ≤ m → 1000 ≤ n → ShpIsT N s0 s →
      (matchRule program (sem ctx) {} m rl vs).run (s, tr) = .ok (some env, s1) →
      (evalExpr program (sem ctx) {} n rl.rhs env).run s1 = .ok (r, (s2, tr2)) → ShpIsT N s0 s2 :=
  fun m n s tr env s1 r s2 tr2 hm hn hIs h1 h2 => h {} rfl m n s0 s tr env s1 r s2 tr2 hm hn hIs h1 h2

/-! ## The driver's calls -/

set_option maxRecDepth 100000 in
/-- **A statement's lowering emits control forms of their typed shapes.** Integer externs (`hx`):
since #609 `CtxT` only records the integer `call` callees (`CtxT.calls`). -/
theorem stmt_shpT (hctx : CtxT f ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true)
    (hcl : Clean ctx) (hfam : FamCover ctx) (ha : AbiSigsOk f)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst) (hmem : ∃ B ∈ f.blocks, ∃ st ∈ B.body, st.inst = inst)
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (hN : ctx.valDef.size ≤ s.nextVreg)
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) : CtlSinceT ctx.valDef.size s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  obtain ⟨i, F, hF, hok⟩ := hfam ii info inst hi hc
  have hins := holds_famT (f := f) hi hF hok
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      aRule program shpTabT aext actor apreST aOracleST [.inst [i]] AT.top rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1)) ∨
      (rl ∈ program.rulesOf TId.lower ∧ (rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033)) := by
    intro rl hrl
    have hs := List.all_eq_true.mp shpStmtT_ok rl hrl
    unfold shpStmtOkT at hs
    have hid := List.all_eq_true.mp lower_hand_ids rl hrl
    simp only [Bool.or_eq_true] at hs
    rcases hs with hh | hs
    · simp only [hh, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hid
      exact .inr (.inr ⟨hrl, or_assoc.mp hid⟩)
    · exact .inl (List.all_eq_true.mp hs i (List.mem_range.mpr (famTab_lt hF)))
  exact (root_handT (md := shpModelT logicImmComplete hctx.inv hcl hfam ctx.valDef.size s) rfl
    (shp_soundT hctx.inv hcl hfam _ s rfl)
    (Hand := fun rl => rl ∈ program.rulesOf TId.lower ∧ (rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033))
    (fun rl ⟨hrl, hid⟩ => hand_modelT (handOkT_call totality hctx ha
      (fun fn e he => (sigE_int (List.all_eq_true.mp hx (fn, e) (lookup_some_mem he))).1)
      hi hc hmem hrl hid _) s)
    data_program.t686 term_686_kind hrules hins (ShpIsT.refl hN) (n := 999999)
    lower_len happ).1

set_option maxRecDepth 100000 in
/-- `lower_branch` on a terminator of a family, with the `br_table` rule checked by hand and
the `try_call` rules excluded or checked by hand (`Try`). -/
theorem branch_shpT (hctx : CtxT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) (N : Nat)
    {ti : Nat} {tinfo : IInfo} {i : Nat} {F : Fam}
    (hti : ctx.insts[ti]? = some tinfo) (hF : famTab[i]? = some F) (hok : FamOk ctx F tinfo)
    {targets : List Label} {Try : Rule → Prop}
    (htry : ∀ rl ∈ program.rulesOf TId.lower_branch, (rl.id = 1034 ∨ rl.id = 1035 ∨ rl.id = 1036) →
      closureRoot rl = false →
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ti, .labels targets]).run s0 ≠
        .ok (some env, s1)) ∨ Try rl)
    (hTry : ∀ rl, Try rl → HandOkT ctx N [.inst ti, .labels targets] rl)
    (hval : ∀ (x c : V) (info : IInfo), ctx.insts[ti]? = some info →
      V.data 152 4 [V.data 151 2 [], x, c] = info.data →
      ∃ w, w ∈ [8, 16, 32, 64] ∧ γ f ctx (.val [.int w]) x)
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId} (hN : N ≤ s.nextVreg)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    CtlSinceT N s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  have hins : Holds2 f ctx [.inst [i], AT.c0] [.inst ti, .labels targets] :=
    ⟨⟨ti, tinfo, rfl, hti, i, List.mem_singleton_self _, F, hF, hok⟩,
      ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩, trivial⟩
  have hrules : ∀ rl ∈ program.rulesOf T.lower_branch.id,
      aRule program shpTabT aext actor apreST aOracleST [.inst [i], AT.c0] AT.top rl = true ∨
      (∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ti, .labels targets]).run s0 ≠
        .ok (some env, s1)) ∨ (Try rl ∨ (rl ∈ program.rulesOf TId.lower_branch ∧ rl.id = 1140)) := by
    intro rl hrl
    have hb := List.all_eq_true.mp shpBranchT_ok rl hrl
    unfold shpBranchOkT at hb
    have hid := List.all_eq_true.mp branch_hand_ids rl hrl
    simp only [Bool.or_eq_true] at hb
    rcases hb with hh | hb
    · simp only [hh, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        Bool.not_eq_true'] at hid
      rcases hid with ⟨hid, hcr⟩ | hid
      · rcases htry rl hrl (or_assoc.mp hid) hcr with hno | hT
        · exact .inr (.inl hno)
        · exact .inr (.inr (.inl hT))
      · exact .inr (.inr (.inr ⟨hrl, hid⟩))
    · exact .inl (List.all_eq_true.mp hb i (List.mem_range.mpr (famTab_lt hF)))
  exact (root_handT (md := shpModelT logicImmComplete hctx.inv hcl hfam N s) rfl
    (shp_soundT hctx.inv hcl hfam _ s rfl)
    (Hand := fun rl => Try rl ∨ (rl ∈ program.rulesOf TId.lower_branch ∧ rl.id = 1140))
    (fun rl hrl => by
      rcases hrl with hT | ⟨hrl, hid⟩
      · exact hand_modelT (hTry rl hT) s
      · exact hand_modelT (handOkT_brTable totality (brSubT hctx.inv hcl hfam) hval hrl hid N) s)
    data_program.t687 term_687_kind hrules hins (ShpIsT.refl hN) (n := 999999)
    lower_branch_len happ).1

set_option maxRecDepth 100000 in
/-- **A terminator's lowering emits control forms of their typed shapes.** -/
theorem termCall_shpT (hctx : CtxT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator}
    (hty : t.isTry = false) (hip : TermIntPos ctx t) {data : V} (hd : termData (abiTerm f t) = .ok data)
    (htf : ∃ (i : Nat) (F : Fam), famTab[i]? = some F ∧ FamOk ctx F ⟨data, [], [], none⟩)
    {targets : List Label} {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (hN : ctx.valDef.size ≤ s.nextVreg)
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) : CtlSinceT ctx.valDef.size s s' := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have hctx' := ctxT_termCtx hctx hph data
  have hcl' := clean_termCtx hcl hd ti
  have hfam' := famCover_termCtx hfam hph data
  have hslot := termCtx_self hti data
  unfold termCallF at h
  obtain ⟨i, F, hF, hok⟩ := htf
  have hok' : FamOk (termCtx ctx ti data) F ⟨data, [], [], none⟩ :=
    famOk_valTy (ctx := ctx) (ctx' := termCtx ctx ti data) rfl hok
  have hval : ∀ (x c : V) (info : IInfo), (termCtx ctx ti data).insts[ti]? = some info →
      V.data 152 4 [V.data 151 2 [], x, c] = info.data →
      ∃ w, w ∈ [8, 16, 32, 64] ∧ γ f (termCtx ctx ti data) (.val [.int w]) x := by
    intro x c info hi he
    rw [hslot] at hi
    cases hi
    cases t with
    | brTable x' d tb =>
      rw [show abiTerm f (.brTable x' d tb) = .brTable x' d tb from rfl, termData_brTable] at hd
      cases hd
      cases he
      have hx : IntPos ctx x' := hip x' (by simp [Compile.termIntOperands])
      cases hvt : ctx.valueType? x' with
      | none =>
        refine ⟨8, by simp, x', rfl, ⟨fun t ht => ?_, fun _ => ⟨.int 8, by simp, rfl⟩⟩⟩
        have ht' : ctx.valueType? x' = some t := ht
        rw [hvt] at ht'
        cases ht'
      | some t =>
        have hm := hx t hvt
        simp only [eCTys, List.mem_cons, List.mem_nil_iff, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl <;>
          exact ⟨_, by simp, x', rfl, valIn_type hvt (List.mem_singleton_self _)⟩
    | jump bc =>
      rw [show abiTerm f (.jump bc) = .jump bc from rfl, termData_jump] at hd; cases hd; cases he
    | brif c' a b =>
      rw [show abiTerm f (.brif c' a b) = .brif c' a b from rfl, termData_brif] at hd
      cases hd; cases he
    | ret vs =>
      rw [show abiTerm f (.ret vs) = .ret (vs ++ sretRet f) from rfl, termData_ret] at hd
      cases hd; cases he
    | trap c' =>
      rw [show abiTerm f (.trap c') = .trap c' from rfl, termData_trap] at hd; cases hd; cases he
    | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
    | tryCall fn args et => simp [Clif.Terminator.isTry] at hty
    | tryCallIndirect callee args et => simp [Clif.Terminator.isTry] at hty
  have hbranch : retOrTrap (abiTerm f t) = false →
      runTerm (termCtx ctx ti data) "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr) →
      CtlSinceT ctx.valDef.size s s' := fun hrt h =>
    branch_shpT hctx' hcl' hfam' _ hslot hF hok' (Try := fun _ => False)
      (fun rl hrl _ hcr => .inl fun m s0 env s1 =>
        branchExcludedUnmatchableT_program rl hrl hcr f _ hctx' ti _ data targets hrt hd hslot {} m
          s0 env s1)
      (fun _ h => h.elim) hval hN h
  have hlower : retOrTrap (abiTerm f t) = true →
      runTerm (termCtx ctx ti data) "lower" [.inst ti] s = .ok (out, s', tr) →
      CtlSinceT ctx.valDef.size s s' := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower] at ht
    cases ht
    have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
        aRule program shpTabT aext actor apreST aOracleST [AT.c0] AT.top rl = true ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl [.inst ti]).run s0 ≠
            .ok (some env, s1) := by
      intro rl hrl
      cases hroot : termRootRule rl with
      | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
      | true =>
        have hf := List.all_eq_true.mp shpTermT_ok rl hrl
        simp only [termRootRule] at hroot
        simp only [hroot, Bool.not_true, Bool.false_or] at hf
        exact .inl hf
    exact ((shp_soundT hctx'.inv hcl' hfam' ctx.valDef.size s rfl 1000000).root T.lower.ret
      T.lower.id T.lower _ _ [AT.c0] AT.top [.inst ti] s #[] out s' tr' data_program.t686
      term_686_kind (fun rl hrl => (hrules rl hrl).imp_right id)
      ⟨⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩, trivial⟩ (ShpIsT.refl hN) happ).1.1
  cases t with
  | ret vs => exact hlower rfl h
  | trap c => exact hlower rfl h
  | jump bc => exact hbranch rfl h
  | brif c a b => exact hbranch rfl h
  | brTable x d tb => exact hbranch rfl h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [Clif.Terminator.isTry] at hty
  | tryCallIndirect callee args et => simp [Clif.Terminator.isTry] at hty

/-- A `try_call`'s data is not a `BranchTable`. -/
theorem tryCallData_ne_brTableT {t : Clif.Terminator} {data : V} (hd : tryCallData f t = .ok data) :
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

/-- **A `try_call`'s lowering emits control forms of their typed shapes.** -/
theorem tryCall_shpT (hctx : CtxT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) (ha : AbiSigsOk f)
    {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator}
    {et : Clif.ExnTable} (het : IsTryWith t et) (hB : ∃ B ∈ f.blocks, B.term = t) {data : V}
    (hd : tryCallData f t = .ok data)
    (htf : ∃ (i : Nat) (F : Fam), famTab[i]? = some F ∧ FamOk ctx F ⟨data, [], [], none⟩)
    {sig : Clif.Signature} {items : List (Option Nat)}
    (he : exnTableOpnd f et = .ok (sig, items)) (hip : TermIntPos ctx t)
    {lo st1 : LState} {trs : List Reg × List Reg}
    (hlo : ctx.valDef.size ≤ lo.nextVreg) (htr : tryRegsOf sig lo = some (trs, st1))
    {targets : List Label} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (out, s', tr)) :
    CtlSinceT ctx.valDef.size { st1 with emitted := #[] } s' := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have h' := ctxT_termCtx hctx hph data
  have hctx' : CtxT f (tryCtx ctx ti data trs) := ⟨{ h'.inv with }, h'.scope, h'.calls⟩
  have hst := (tryRegsOf_mono htr).1
  obtain ⟨i, F, hF, hok⟩ := htf
  exact branch_shpT hctx' (clean_tryCtx hcl hd ti trs)
    (famCover_eq (ctx := termCtx ctx ti data) (ctx' := tryCtx ctx ti data trs) rfl rfl
      (famCover_termCtx hfam hph data)) _ (termCtx_self hti data) hF
    (famOk_valTy (ctx := ctx) (ctx' := tryCtx ctx ti data trs) rfl hok)
    (Try := fun rl => rl ∈ program.rulesOf TId.lower_branch ∧ (rl.id = 1034 ∨ rl.id = 1035 ∨ rl.id = 1036))
    (fun rl hrl hid _ => .inr ⟨hrl, hid⟩)
    (fun rl ⟨hrl, hid⟩ => handOkT_try totality hctx ha hph het hd he hip (tryInd_sig ha hB he) _ hlo htr
      hrl hid)
    (fun x c info hi he' => by
      have hsl : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ := termCtx_self hti data
      rw [hsl] at hi
      cases hi
      exact absurd he'.symm (tryCallData_ne_brTableT hd _))
    (by show ctx.valDef.size ≤ st1.nextVreg; omega) h

/-! ## The typed ISLE inversion -/

/-- **`IselCtlHypT`**: on the typed scope, every ISLE run of the driver emits only control
forms of the typed shapes `CtlShapeT`, with defs above every value's vreg. -/
theorem iselCtlHypT : IselCtlHypT := by
  intro f ctx ranges st0 hdom hs hst hsel ha hb
  have hx := externsE_of hs.subsetT
  have hctx : CtxT f ctx :=
    ⟨ctxInvT_of hs hb, (buildCtx_typed hs hb).2.2.toTF, callsE_of_externs hx ctx⟩
  have hcl : Clean ctx := Cov.clean_of_build hb
  have hfam := famCover_of hs hdom hst hsel hb
  refine ⟨fun ii info inst s out s' tr hi hc hN h => ?_,
    fun ti t data targets s out s' tr _ hph hty hB hd hN h => ?_,
    fun ti t et data sig items lo trs st1 targets out s' tr _ hph het hB hd he hlo htr h => ?_⟩
  · have hmem : ∃ B ∈ f.blocks, ∃ st ∈ B.body, st.inst = inst := by
      rcases (ctxSpec_of hb).insts info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) with
        rfl | ⟨B, hB, st, hst, rfl⟩
      · cases hc
      · exact ⟨B, hB, st, hst, Option.some.inj hc⟩
    exact stmt_shpT hctx hx hcl hfam ha hi hc hmem hN h
  · obtain ⟨B, hBm, rfl⟩ := hB
    exact termCall_shpT hctx hcl hfam hph hty (termIntPos_of hs hb hBm) hd
      (termFam_of hs hdom hb hBm (.inl hd)) hN h
  · obtain ⟨B, hBm, hBt⟩ := hB
    subst hBt
    exact tryCall_shpT hctx hcl hfam ha hph het ⟨B, hBm, rfl⟩ hd
      (termFam_of hs hdom hb hBm (.inr hd)) he (termIntPos_of hs hb hBm) hlo htr h

end Backend.Proof.CovT
