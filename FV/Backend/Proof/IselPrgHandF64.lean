import FV.Backend.Proof.IselPrgTabF64
import FV.Backend.Proof.IselPrgHandT
import FV.Backend.Proof.IselPrgExtSoundT
import FV.Backend.Proof.IselPrgCtorSoundT
import FV.Backend.Proof.IselPrgSound
import FV.Backend.Proof.IselPrgMono
import FV.Backend.Proof.IselFloatConst

/-!
# Progress of the ISLE lowering over the typed scope: the `f64const` rule

`handOkT`: the hand-checked rules of the typed scope (`handRulesT`) return: V7's two
(`handRules_okT`) and the `lower` rule of `f64const` (`lower.isle:68`, rule 585, `hand_585T`), on
every table whose `lower` entries cannot describe a slot without CLIF instruction holding
`f64const` data (`f64Safe`).

Rule 585 is `(lower (f64const _ (u64_from_ieee64 n))) → (output_reg (constant_f64 n))`. The matched
instruction is an `f64const` of `f` (`f64Safe`: a slot without CLIF instruction has no result
type), so its bits `n` are `Compile.f64PoolFree` (`PInvT.instET`). Below `2^32`, `constant_f64 n` is
the `f64Tab` entry on `aU32`; from `2^32` on, `constant_f64`'s rules are followed by hand
(`constant_f64_hi`): `0` and `u32_from_u64` do not match, the `fmov` immediate (rule 3) or the
zero low half (rule 1, `mov x; fmov d`) does, and their calls are `f64Tab`'s entries
(`f64_run`). The literal-pool rule is never reached.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx} {cfg : Config}

/-! ## The model and the `f64const` sub-table -/

/-- **The model of the extern helpers over the typed scope** under the context invariant. -/
theorem model_ofT (hP : PInvT f ctx) : Model f ctx aextT actorT aidata :=
  ⟨fun term a outs must v st h hv => aextT_sound hP term a outs must v st h hv,
   fun term as a must vs st h hv => actorT_sound hP term as a must vs st h hv,
   fun v hv => aidata_soundT hP v hv⟩

/-- No hand-checked rules: nothing to check. -/
theorem handOk_none (tab : PTab) : HandOk f ctx program cfg tab (fun _ => none) := by
  intro _ _ _ _ _ _ hh
  cases hh

/-- An `f64Tab` root: its entry surely returns a value `out` describes, within fuel `fu`. -/
def f64RootOk (t : TermId) (as : List PA) (out : PA) (fu : Nat) : Bool :=
  match tabFind f64Tab t as with
  | some e => e.osome && PA.le e.out out && decide (e.fu ≤ fu)
  | none => false

/-- A run of an `f64Tab` root returns a value its output describes. -/
theorem f64_run (hP : PInvT f ctx) (hc : cfg.checkOverlap = false) {t : TermId} {as : List PA}
    {out : PA} {fu : Nat} (hok : f64RootOk t as out fu = true) {args : List V}
    (hargs : γL f ctx as args) {n : Nat} (hn : fu ≤ n) (ty : TypeId) (st : LState)
    (tr : Array RuleId) :
    ∃ w st' tr', (applyTerm program (sem ctx) cfg n ty t args).run (st, tr) =
      .ok (some w, (st', tr')) ∧ γ f ctx out w := by
  unfold f64RootOk at hok
  split at hok
  · rename_i e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hos, hle⟩, hfu⟩ := hok
    obtain ⟨hmem, het, hleL⟩ := tabFind_sound he
    obtain ⟨v, st', tr', hrun, hsome, hout⟩ := progress (model_ofT hP) (handOk_none f64Tab) hc
      f64Tab_ok n e hmem (by omega) ty args st tr (leL_sound _ _ hleL _ hargs)
    obtain ⟨w, rfl⟩ := Option.isSome_iff_exists.mp (hsome hos)
    rw [het] at hrun
    exact ⟨w, st', tr', hrun, le_sound _ _ hle w (hout w rfl)⟩
  · cases hok

/-- The `f64Tab` roots the hand proof calls: `constant_f64` below `2^32`, `output_reg`,
`fpu_move_fp_imm` and `mov_to_fpu` at 64 bits, `imm` of an `i64` from `2^32` on. -/
theorem f64Roots_ok :
    (f64RootOk 587 [aU32] .reg 1000 && f64RootOk 172 [.reg] (.regsVec (some 1)) 1000 &&
      f64RootOk 411 [.op .fpModImm none, .data 95 3 []] .reg 1000 &&
      f64RootOk 553 [.ty [.int 64], .data 122 1 [], f64Hi] .reg 1000 &&
      f64RootOk 409 [.reg, .data 95 3 []] .reg 1000) = true := by
  decide +kernel

theorem f64Root_587 : f64RootOk 587 [aU32] .reg 1000 = true := by
  have h := f64Roots_ok; simp only [Bool.and_eq_true] at h; exact h.1.1.1.1
theorem f64Root_172 : f64RootOk 172 [.reg] (.regsVec (some 1)) 1000 = true := by
  have h := f64Roots_ok; simp only [Bool.and_eq_true] at h; exact h.1.1.1.2
theorem f64Root_411 : f64RootOk 411 [.op .fpModImm none, .data 95 3 []] .reg 1000 = true := by
  have h := f64Roots_ok; simp only [Bool.and_eq_true] at h; exact h.1.1.2
theorem f64Root_553 : f64RootOk 553 [.ty [.int 64], .data 122 1 [], f64Hi] .reg 1000 = true := by
  have h := f64Roots_ok; simp only [Bool.and_eq_true] at h; exact h.1.2
theorem f64Root_409 : f64RootOk 409 [.reg, .data 95 3 []] .reg 1000 = true := by
  have h := f64Roots_ok; simp only [Bool.and_eq_true] at h; exact h.2

theorem γ_data_nil (t : TypeId) (k : Nat) : γ f ctx (.data t k []) (.data t k []) :=
  ⟨[], rfl, trivial⟩

/-! ## `constant_f64` from `2^32` on -/

section Hi
variable (hP : PInvT f ctx) (hc : cfg.checkOverlap = false)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
include hP hc in
/-- **`constant_f64` of a pattern of at least `2^32`** without the literal pool (an `fmov`
immediate or zero low 32 bits) returns a register. -/
theorem constant_f64_hi {c : Int} (hlo : 2 ^ 32 ≤ c) (hhi : c < 2 ^ 64)
    (hpf : (fpModImm? (u64 c) .size64).isSome = true ∨ u64 c % 2 ^ 32 = 0) (k : Nat)
    (st : LState) (tr : Array RuleId) :
    ∃ w s', (applyTerm program (sem ctx) cfg (k + 2000) 27 587 [.int c]).run (st, tr) =
      .ok (some w, s') ∧ γ f ctx .reg w := by
  have hp := data_program
  have h4264 : (matchRule program (sem ctx) cfg (k + 1997) rule_inst_4264 [.int c]).run (st, tr) =
      .ok (none, (st, tr)) := by
    have hc0 : (V.int c == V.int 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, V.int.injEq]; omega
    isel_eval [rule_inst_4264, sem_eq, hc0]
  have hx2 : externExtract ctx T.u32_from_u64 (.int c) st = .fail := by
    show (if 0 ≤ c ∧ c < 2 ^ 32 then _ else _) = _
    simp only [show ¬(0 ≤ c ∧ c < 2 ^ 32) by omega, ↓reduceIte]
  have h4271 : (matchRule program (sem ctx) cfg (k + 1995) rule_inst_4271 [.int c]).run (st, tr) =
      .ok (none, (st, tr)) := by
    isel_eval [rule_inst_4271, hx2, hp.t1541]
  cases hm : fpModImm? (u64 c) .size64 with
  | some mm =>
    -- rule 3: `fmov d, #imm`
    have hctor : externCtor ctx T.asimd_fp_mod_imm_from_u64 [.int c, .data 95 3 []] st =
        .ok (.op (.fpModImm mm), st) := by
      show (match (fpModImm? (u64 c) .size64).map (V.op ∘ Opnd.fpModImm) with
        | some v => ExtResult.ok (v, st) | none => ExtResult.fail) = _
      rw [hm]; rfl
    obtain ⟨env, h4268, henv⟩ : ∃ env, (matchRule program (sem ctx) cfg (k + 1996) rule_inst_4268
        [.int c]).run (st, tr) = .ok (some env, (st, tr)) ∧
        env[1]? = some (some (.op (.fpModImm mm))) := by
      isel_eval [rule_inst_4268, hctor, hp.t679, hp.t2035, Except.ok.injEq, Prod.mk.injEq,
        Option.some.injEq, exists_eq_left', true_and, and_true]
    have hargs : (evalArgs program (sem ctx) cfg (k + 1998) [.var 71 1, .term 95 2035 []] env).run
        (st, tr) = .ok (some [.op (.fpModImm mm), .data 95 3 []], (st, tr)) := by
      isel_eval [henv, hp.t2035]
    obtain ⟨w, st', tr', h411, hγ⟩ := f64_run hP hc f64Root_411
      (args := [.op (.fpModImm mm), .data 95 3 []]) ⟨⟨_, rfl, mm, rfl⟩, γ_data_nil 95 3, trivial⟩
      (n := k + 1998) (by omega) 27 st tr
    have hrhs : (evalExpr program (sem ctx) cfg (k + 1999) rule_inst_4268.rhs env).run (st, tr) =
        .ok (some w, (st', tr')) := evalExpr_term_iff.mpr ⟨_, _, hargs, h411⟩
    refine ⟨w, (st', tr'.push rule_inst_4268.id), ?_, hγ⟩
    rw [show k + 2000 = (k + 1999) + 1 from rfl, applyTerm_internal_run hp.t587 term_587_kind rfl,
      program_rulesOf_587, selectRule_cons_ok hc (tryRule_ok h4264)]
    simp only []
    rw [selectRule_cons_ok hc (tryRule_ok h4268)]
    simp only [M.except_ok_bind, M.run_bind, hrhs, run_fire, run_pure']
  | none =>
    -- rule 1: zero low 32 bits, `mov x; fmov d, x`
    have hlow : u64 c % 2 ^ 32 = 0 := by
      rcases hpf with h | h
      · rw [hm] at h; cases h
      · exact h
    have hctor : externCtor ctx T.asimd_fp_mod_imm_from_u64 [.int c, .data 95 3 []] st = .fail := by
      show (match (fpModImm? (u64 c) .size64).map (V.op ∘ Opnd.fpModImm) with
        | some v => ExtResult.ok (v, st) | none => ExtResult.fail) = _
      rw [hm]; rfl
    have h4268 : (matchRule program (sem ctx) cfg (k + 1996) rule_inst_4268 [.int c]).run (st, tr) =
        .ok (none, (st, tr)) := by
      isel_eval [rule_inst_4268, hctor, hp.t679, hp.t2035]
    have hx1 : externExtract ctx T.u64_low32_bits_unset (.int c) st = .ok [.int c] := by
      show (if u64 c % 2 ^ 32 = 0 then _ else _) = _
      simp only [hlow, ↓reduceIte]
    obtain ⟨env, h4273, henv⟩ : ∃ env, (matchRule program (sem ctx) cfg (k + 1994) rule_inst_4273
        [.int c]).run (st, tr) = .ok (some env, (st, tr)) ∧ env[0]? = some (some (.int c)) := by
      isel_eval [rule_inst_4273, hx1, hp.t588, Except.ok.injEq, Prod.mk.injEq,
        Option.some.injEq, exists_eq_left', true_and, and_true]
    have hargs553 : (evalArgs program (sem ctx) cfg (k + 1996)
        [.constPrim 14 "I64", .term 122 2235 [], .var 4 0] env).run (st, tr) =
        .ok (some [.ty (.int 64), .data 122 1 [], .int c], (st, tr)) := by
      have hI : CTy.ofName? "I64" = some (.int 64) := rfl
      isel_eval [henv, hI, hp.t2235]
    obtain ⟨w1, st1, tr1, h553, hγ1⟩ := f64_run hP hc f64Root_553
      (args := [.ty (.int 64), .data 122 1 [], .int c])
      ⟨⟨_, List.mem_singleton_self _, rfl⟩, γ_data_nil 122 1,
        ⟨c, rfl, fun l hl => by cases hl; omega, fun h hh => by cases hh; omega⟩, trivial⟩
      (n := k + 1996) (by omega) 27 st tr
    have h553e : (evalExpr program (sem ctx) cfg (k + 1997)
        (.term 27 553 [.constPrim 14 "I64", .term 122 2235 [], .var 4 0]) env).run (st, tr) =
        .ok (some w1, (st1, tr1)) := evalExpr_term_iff.mpr ⟨_, _, hargs553, h553⟩
    have hrest : (evalArgs program (sem ctx) cfg (k + 1997) [.term 95 2035 []] env).run (st1, tr1) =
        .ok (some [.data 95 3 []], (st1, tr1)) := by
      isel_eval [hp.t2035]
    have hargs409 : (evalArgs program (sem ctx) cfg (k + 1998)
        [.term 27 553 [.constPrim 14 "I64", .term 122 2235 [], .var 4 0], .term 95 2035 []] env).run
        (st, tr) = .ok (some [w1, .data 95 3 []], (st1, tr1)) :=
      evalArgs_cons_iff.mpr ⟨w1, (st1, tr1), _, h553e, hrest, rfl⟩
    obtain ⟨w, st', tr', h409, hγ⟩ := f64_run hP hc f64Root_409 (args := [w1, .data 95 3 []])
      ⟨hγ1, γ_data_nil 95 3, trivial⟩ (n := k + 1998) (by omega) 27 st1 tr1
    have hrhs : (evalExpr program (sem ctx) cfg (k + 1999) rule_inst_4273.rhs env).run (st, tr) =
        .ok (some w, (st', tr')) := evalExpr_term_iff.mpr ⟨_, _, hargs409, h409⟩
    refine ⟨w, (st', tr'.push rule_inst_4273.id), ?_, hγ⟩
    rw [show k + 2000 = (k + 1999) + 1 from rfl, applyTerm_internal_run hp.t587 term_587_kind rfl,
      program_rulesOf_587, selectRule_cons_ok hc (tryRule_ok h4264)]
    simp only []
    rw [selectRule_cons_ok hc (tryRule_ok h4268)]
    simp only []
    rw [selectRule_cons_ok hc (tryRule_ok h4271)]
    simp only []
    rw [selectRule_cons_ok hc (tryRule_ok h4273)]
    simp only [M.except_ok_bind, M.run_bind, hrhs, run_fire, run_pure']

end Hi

/-! ## Rule 585 -/

/-- An abstract type may describe the invalid type (of a slot without CLIF instruction). -/
def mayInvalid : PA → Bool
  | .ty ts => ts.contains .invalid
  | .bot => false
  | _ => true

/-- An abstract value may describe `f64const` data (variant 34, `UnaryIeee64`, of
`InstructionData`). -/
def mayF64c : PA → Bool
  | .data t k _ => t == tyInstData && k == 34
  | .bot => false
  | _ => true

/-- A table entry rule 585 cannot meet on a slot without CLIF instruction: not `lower`'s, or one
instruction whose type is never invalid or whose data is never `f64const`'s. -/
def f64Safe (e : PEnt) : Bool :=
  e.t != TId.lower || (match e.ins with
    | [.inst t d] => !mayInvalid t || !mayF64c d
    | _ => false)

theorem f64Safe_inv {e : PEnt} (h : f64Safe e = true) (ht : e.t = TId.lower) :
    ∃ t d, e.ins = [.inst t d] ∧ (mayInvalid t = false ∨ mayF64c d = false) := by
  unfold f64Safe at h
  rw [ht] at h
  simp only [bne_self_eq_false, Bool.false_or] at h
  split at h
  · rename_i t d heq
    refine ⟨t, d, heq, ?_⟩
    simpa only [Bool.or_eq_true, Bool.not_eq_true'] using h
  · cases h

theorem ty_ne_invalid {t : PA} {x : CTy} (h : γ f ctx t (.ty x)) (hm : mayInvalid t = false) :
    x ≠ .invalid := by
  cases t <;> simp only [mayInvalid, Bool.true_eq_false] at hm
  case bot => simp [γ] at h
  case ty ts =>
    simp only [γ] at h
    obtain ⟨t', ht', heq⟩ := h
    cases heq
    rintro rfl
    simp only [List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at hm
    exact hm _ ht' rfl

theorem f64c_of_γ {d : PA} {ws : List V} (h : γ f ctx d (.data tyInstData 34 ws)) :
    mayF64c d = true := by
  cases d <;> simp only [mayF64c]
  case bot => simp [γ] at h
  case data t k fs =>
    simp only [γ] at h
    obtain ⟨ws', heq, -⟩ := h
    simp only [V.data.injEq] at heq
    obtain ⟨rfl, rfl, -⟩ := heq
    rfl

/-- The rule lists from term `t` on: only `lower`'s (term 686) has rule 585. -/
def ids585Ok : Nat → List (List Rule) → Bool
  | _, [] => true
  | t, rs :: rss => (t == TId.lower || rs.all (·.id != 585)) && ids585Ok (t + 1) rss

set_option maxRecDepth 100000 in
theorem ids585_program : ids585Ok 0 program.ruleLists.toList = true := by decide +kernel

private theorem ids585Ok_get : ∀ {k : Nat} {L : List (List Rule)}, ids585Ok k L = true →
    ∀ (i : Nat) (rs : List Rule), L[i]? = some rs → ∀ r ∈ rs, r.id = 585 → k + i = TId.lower
  | _, [], _, i, rs, hi, _, _, _ => by simp at hi
  | k, rs0 :: L, h, i, rs, hi, r, hr, hid => by
    simp only [ids585Ok, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      rcases h.1 with h1 | h1
      · simpa using h1
      · have := List.all_eq_true.mp h1 r hr
        simp [hid] at this
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have := ids585Ok_get h.2 i rs hi r hr hid
      omega

/-- Rule 585 belongs to `lower` only. -/
theorem id585_term {t : TermId} {r : Rule} (hr : r ∈ program.rulesOf t) (hid : r.id = 585) :
    t = TId.lower := by
  unfold Program.rulesOf at hr
  cases ht : program.ruleLists[t]? with
  | none => rw [ht] at hr; cases hr
  | some rs =>
    rw [ht] at hr
    have h := ids585Ok_get ids585_program t rs (by rw [← Array.getElem?_toList] at ht; exact ht)
      r hr hid
    simpa using h

set_option maxRecDepth 100000 in
theorem lower_rule_585 :
    (program.rulesOf TId.lower).filter (fun r => r.id == 585) = [rule_lower_68] := by
  rw [show TId.lower = 686 from rfl, program_rulesOf_686]; decide +kernel

private theorem matchRule_mono_le585 {m m' : Nat} (hm : m ≤ m') {r : Rule} {vs : List V}
    {s : LState × Array RuleId} {res : Option (Isle.Interp.Env V) × (LState × Array RuleId)}
    (h : (matchRule program (sem ctx) cfg m r vs).run s = .ok res) :
    (matchRule program (sem ctx) cfg m' r vs).run s = .ok res := by
  induction hm with
  | refl => exact h
  | step _ ih => exact (monoAt _).mrule _ _ _ _ ih

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`f64const`** (`lower.isle:68`, rule 585) over the typed scope: from a successful match on
an instruction an `f64Safe` entry describes, the right-hand side returns one single register from
fuel `f64Fuel`. -/
theorem hand_585T (hP : PInvT f ctx) (hc : cfg.checkOverlap = false) {t d : PA}
    (hsafe : mayInvalid t = false ∨ mayF64c d = false) {args : List V}
    (hargs : γL f ctx [.inst t d] args) {m : Nat} {s s' : LState × Array RuleId}
    {env : Isle.Interp.Env V}
    (h : (matchRule program (sem ctx) cfg m rule_lower_68 args).run s = .ok (some env, s'))
    (n : Nat) (hn : f64Fuel ≤ n) :
    ∃ v s'', (evalExpr program (sem ctx) cfg n rule_lower_68.rhs env).run s' = .ok (some v, s'') ∧
      γ f ctx (.regsVec (some 1)) v := by
  have hp := data_program
  have hctx := hP.ctxInv
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3000 := ⟨n - 3000, by simp only [f64Fuel] at hn; omega⟩
  rcases args with _ | ⟨v, _ | ⟨v2, vs⟩⟩ <;> simp only [γL, and_false] at hargs
  obtain ⟨⟨j, info, rfl, hi, hty, hdat, -⟩, -⟩ := hargs
  have h' := matchRule_mono_le585 (m' := (m + 20) + 1) (by omega) h
  clear h
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx (r := rule_lower_68) rfl hp.t2481
    term_2481_kind hp.t2344 term_2344_kind (m := m + 20) h'
  rw [hi] at hi'
  cases hi'
  rw [hd] at hdat
  have hf := f64c_of_γ hdat
  have hti := ty_ne_invalid hty (by rw [hf] at hsafe; simpa using hsafe)
  cases hcl : info.clif with
  | none =>
    exact absurd (by rw [hP.noClifRes j info hi hcl]; rfl) hti
  | some cl =>
  have hdd := hctx.data j info cl hi hcl
  rw [hd] at hdd
  obtain ⟨imm, rfl, rfl⟩ := instData_f64const_inv hdd
  have hpf := hP.instET _ (hP.clifOf j info _ hi hcl)
  have hpf2 : imm.toNat = 0 ∨ (fpModImm? imm.toNat .size64).isSome = true ∨ imm.toNat < 2 ^ 32 ∨
      imm.toNat % 2 ^ 32 = 0 := by
    simp only [Compile.instET, Compile.tyE, Compile.f64PoolFree, Bool.or_eq_true,
      Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpf
    simp only [reduceCtorEq, false_or, true_and, or_assoc] at hpf
    rcases hpf with h | h
    · exact absurd h.1 (by decide)
    · exact h
  clear hpf
  have henv : env[0]? = some (some (.int (imm.toNat : Int))) := by
    isel_inv' hp [] at h'
    obtain ⟨rfl, rfl⟩ := fconst_data_eq hi hd ‹ctx.insts[j]? = some _› ‹V.data 152 34 _ = _›
    have hfs := (ext_u64_from_ieee64_iff ctx _ _ _).mp ‹externExtract ctx T.u64_from_ieee64 _ _ = _›
    simp only [List.cons.injEq, and_true] at hfs
    subst hfs
    simp
  clear h'
  have hlt := imm.isLt
  have hu : u64 (imm.toNat : Int) = imm.toNat := by unfold u64; omega
  obtain ⟨st1, tr1⟩ := s'
  obtain ⟨w587, s2, h587, hγ587⟩ : ∃ w s2, (applyTerm program (sem ctx) cfg (k + 2997) 27 587
      [.int (imm.toNat : Int)]).run (st1, tr1) = .ok (some w, s2) ∧ γ f ctx .reg w := by
    by_cases hsmall : imm.toNat < 2 ^ 32
    · obtain ⟨w, st', tr', hr, hγ⟩ := f64_run hP hc f64Root_587 (args := [.int (imm.toNat : Int)])
        ⟨⟨_, rfl, fun l hl => by cases hl; omega, fun h hh => by cases hh; omega⟩, trivial⟩
        (n := k + 2997) (by omega) 27 st1 tr1
      exact ⟨w, _, hr, hγ⟩
    · have hpf' : (fpModImm? (u64 (imm.toNat : Int)) .size64).isSome = true ∨
          u64 (imm.toNat : Int) % 2 ^ 32 = 0 := by
        rw [hu]
        rcases hpf2 with h0 | h1 | h2 | h3
        · omega
        · exact .inl h1
        · omega
        · exact .inr h3
      have h64 : imm.toNat < 2 ^ 64 := by simpa using hlt
      have := constant_f64_hi hP hc (c := (imm.toNat : Int)) (by omega) (by omega) hpf' (k + 997)
        st1 tr1
      rwa [show k + 997 + 2000 = k + 2997 by omega] at this
  obtain ⟨st2, tr2⟩ := s2
  obtain ⟨w, st3, tr3, h172, hγ⟩ := f64_run hP hc f64Root_172 (args := [w587]) ⟨hγ587, trivial⟩
    (n := k + 2999) (by omega) 25 st2 tr2
  refine ⟨w, (st3, tr3), ?_, hγ⟩
  show (evalExpr program (sem ctx) cfg (k + 3000) (.term 25 172 [.term 27 587 [.var 4 0]]) _).run _ = _
  refine evalExpr_term_iff.mpr ⟨[w587], (st2, tr2), ?_, h172⟩
  refine evalArgs_cons_iff.mpr ⟨w587, (st2, tr2), [], ?_, evalArgs_nil_iff.mpr ⟨rfl, rfl⟩, rfl⟩
  refine evalExpr_term_iff.mpr ⟨[.int (imm.toNat : Int)], (st1, tr1), ?_, h587⟩
  refine evalArgs_cons_iff.mpr ⟨_, (st1, tr1), [], evalExpr_var_iff.mpr ⟨?_, rfl⟩,
    evalArgs_nil_iff.mpr ⟨rfl, rfl⟩, rfl⟩
  exact henv

/-- **The hand-checked rules of the typed scope return** (`HandOk` for `handRulesT`): V7's two
(`handRules_okT`) and rule 585 (`hand_585T`), on a table whose entries are `f64Safe`. -/
theorem handOkT (hP : PInvT f ctx) (hc : cfg.checkOverlap = false) (tab : PTab)
    (htab : tab.all f64Safe = true) : HandOk f ctx program cfg tab handRulesT := by
  intro e he r hr c a hh args hargs m s env s' hmatch n hn
  simp only [handRulesT] at hh
  split at hh
  · rename_i hid
    simp only [Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    have hid' : r.id = 585 := by simpa using hid
    have ht := id585_term hr hid'
    have hm : r ∈ (program.rulesOf TId.lower).filter (fun r => r.id == 585) :=
      List.mem_filter.mpr ⟨ht ▸ hr, by simp [hid']⟩
    rw [lower_rule_585] at hm
    obtain rfl := List.mem_singleton.mp hm
    obtain ⟨t, d, hins, hsafe⟩ := f64Safe_inv (List.all_eq_true.mp htab e he) ht
    rw [hins] at hargs
    exact hand_585T hP hc hsafe hargs hmatch n hn
  · exact handRules_okT hP hc hr hh hmatch n hn

end Backend.Proof.Prg
