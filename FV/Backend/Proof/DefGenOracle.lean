import FV.Backend.Proof.DefGenSound
import FV.Backend.Proof.IselEmitLast
import FV.Backend.Proof.KillTab

/-!
# Definedness of the ISLE runs: the oracle terms

`dOracle` is the `oracle` field of `DModel program ctx c s0`: a run of `emit_side_effect` (rules
522/524/527) or `side_effect` (rule 535, `emit_side_effect` then `output_none`) on a side effect
`.data SideEffectNoResult k ws` emits the instructions `ws` in order (`oracle_esr_run`,
`oracle_se_run`: inverted at any fuel, `Cov.totality` excluding a `none` result) and returns no
registers. `aOracle` requires the argument to fit `PT … SideEffectNoResult`, so each emitted
instruction reads defined vregs or fresh defs of the earlier ones (`oracle_fields`), which keeps
`IsD` (`oracle_isD_emit`); its environment update is `emitSeq`'s (`emitSeq_sound`).
-/

set_option maxRecDepth 20000

namespace Backend.Proof.DefGen

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Spill Backend.Proof.Kill
  Backend.Proof.DefRun Isle Isle.Aarch64 Isle.Interp

/-- A successful match of one pattern: a single value. -/
theorem oracle_matchArgs_one {ctx : Ctx} {st : LState} {q : Pattern} {vs : List V}
    {env env' : Isle.Interp.Env V}
    (h : matchArgs program (sem ctx) st [q] vs env = .ok (some env')) :
    ∃ v, vs = [v] ∧ matchPat program (sem ctx) st q v env = .ok (some env') := by
  rcases vs with _ | ⟨v, _ | ⟨w, ws⟩⟩
  · simp [matchArgs] at h
  · refine ⟨v, rfl, ?_⟩
    simp only [matchArgs] at h
    cases hm : matchPat program (sem ctx) st q v env with
    | error e => rw [hm] at h; cases h
    | ok o =>
      rw [hm] at h
      cases o with
      | none => cases h
      | some e1 => simp at h; subst h; rfl
  · simp only [matchArgs] at h
    cases hm : matchPat program (sem ctx) st q v env with
    | error e => rw [hm] at h; cases h
    | ok o =>
      rw [hm] at h
      cases o with
      | none => cases h
      | some e1 => simp at h

theorem ctor_output_none_eq (ctx : Ctx) (st : LState) :
    externCtor ctx T.output_none [] st = .ok (.regsVec [], st) := rfl

section Run
variable {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
include hc

set_option maxHeartbeats 4000000 in
/-- **A run of `emit_side_effect`** (any fuel): its argument is a side effect whose fields build
instructions, emitted in order; the result is `unit`. -/
theorem oracle_esr_run {n : Nat} {ty : TypeId} {vs : List V} {s : LState} {tr : Array RuleId}
    {r : Option V} {s' : LState} {tr' : Array RuleId}
    (h : (applyTerm program (sem ctx) cfg n ty TId.emit_side_effect vs).run (s, tr) =
      .ok (r, (s', tr'))) :
    r = some (.op .unit) ∧ ∃ k ws ms, vs = [.data TyId.«SideEffectNoResult» k ws] ∧
      flagShape TyId.«SideEffectNoResult» k = some (List.replicate ws.length .i) ∧
      ws.mapM MInst.ofV = some ms ∧ s'.emitted = s.emitted ++ ms.toArray ∧
      s'.nextVreg = s.nextVreg := by
  have hs := Cov.totality.2 ctx cfg n ty 242 vs (s, tr) r (s', tr') rfl h
  obtain ⟨w, rfl⟩ := Option.isSome_iff_exists.mp hs
  rcases n with _ | n
  · rw [applyTerm.eq_1] at h; cases h
  obtain ⟨rl, hrl, env, tr0, hma, he⟩ := internal_rule hc program_term_242 term_242_kind rfl
    (by rw [program_rulesOf_242]; simp [rule_prelude_lower_522, rule_prelude_lower_524,
      rule_prelude_lower_527]) h
  clear h hs
  rw [program_rulesOf_242] at hrl
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hrl
  rcases hrl with rfl | rfl | rfl <;>
  · obtain ⟨v, rfl, hp⟩ := oracle_matchArgs_one hma
    oracle_inv [rule_prelude_lower_522, rule_prelude_lower_524, rule_prelude_lower_527,
      program_term_1787, program_term_1788, program_term_1789] at hp he
    all_goals refine ⟨_, _, ⟨rfl, rfl⟩, rfl, ?_⟩
    all_goals simp [*, LState.emit, ← Array.toList_inj]

theorem oracle_esr_ai {n : Nat} {ty : TypeId} {vs : List V} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal program (sem ctx) cfg n ty TId.emit_side_effect vs s v s') :
    ∃ k ws ms, vs = [.data TyId.«SideEffectNoResult» k ws] ∧
      flagShape TyId.«SideEffectNoResult» k = some (List.replicate ws.length .i) ∧
      ws.mapM MInst.ofV = some ms ∧ s'.1.emitted = s.1.emitted ++ ms.toArray ∧
      s'.1.nextVreg = s.1.nextVreg := by
  obtain ⟨s, tr⟩ := s
  obtain ⟨s', tr'⟩ := s'
  exact (oracle_esr_run hc h).2

set_option maxHeartbeats 4000000 in
/-- **A run of `side_effect`** (any fuel): `emit_side_effect`'s emission; the result is the
empty output. -/
theorem oracle_se_run {n : Nat} {ty : TypeId} {vs : List V} {s : LState} {tr : Array RuleId}
    {r : Option V} {s' : LState} {tr' : Array RuleId}
    (h : (applyTerm program (sem ctx) cfg n ty TId.side_effect vs).run (s, tr) =
      .ok (r, (s', tr'))) :
    r = some (.regsVec []) ∧ ∃ k ws ms, vs = [.data TyId.«SideEffectNoResult» k ws] ∧
      flagShape TyId.«SideEffectNoResult» k = some (List.replicate ws.length .i) ∧
      ws.mapM MInst.ofV = some ms ∧ s'.emitted = s.emitted ++ ms.toArray ∧
      s'.nextVreg = s.nextVreg := by
  obtain ⟨v, m, env, tr0, rfl, hma, he⟩ := Cov.single_rule_run Cov.totality hc program_term_243
    term_243_kind rfl rfl program_rulesOf_243 rfl h
  clear h
  obtain ⟨w, rfl, hp⟩ := oracle_matchArgs_one hma
  oracle_inv [rule_prelude_lower_535, program_term_169, term_169_kind, program_term_242,
    term_242_kind, ctor_output_none_eq] at hp he
  obtain ⟨k, ws, ms, h1, h2, h3, h4, h5⟩ :=
    oracle_esr_ai hc ‹ApplyInternal _ _ _ _ _ 242 _ _ _ _›
  refine ⟨k, ws, by simpa using h1, h2, ms, h3, h4, h5⟩

end Run

/-! ## Lists -/

theorem oracle_mapM_take {α β : Type} {f : α → Option β} :
    ∀ {ws : List α} {ms : List β}, ws.mapM f = some ms → ∀ j, (ws.take j).mapM f = some (ms.take j)
  | [], ms, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    intro j
    simp
  | w :: ws, ms, h => by
    cases hw : f w with
    | none => simp [hw] at h
    | some b =>
      cases hws : ws.mapM f with
      | none => simp [hw, hws] at h
      | some bs =>
        simp only [List.mapM_cons, hw, hws, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at h
        subst h
        intro j
        cases j with
        | zero => simp
        | succ j => simp [List.mapM_cons, hw, oracle_mapM_take hws j]

theorem oracle_mapM_get {α β : Type} {f : α → Option β} :
    ∀ {ws : List α} {ms : List β}, ws.mapM f = some ms → ∀ (j : Nat) m, ms[j]? = some m →
      ∃ w, ws[j]? = some w ∧ f w = some m
  | [], ms, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    intro j m hm
    simp at hm
  | w :: ws, ms, h => by
    cases hw : f w with
    | none => simp [hw] at h
    | some b =>
      cases hws : ws.mapM f with
      | none => simp [hw, hws] at h
      | some bs =>
        simp only [List.mapM_cons, hw, hws, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at h
        subst h
        intro j m hm
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hm ⊢
          subst hm
          exact ⟨w, rfl, hw⟩
        | succ j =>
          simp only [List.getElem?_cons_succ] at hm ⊢
          exact oracle_mapM_get hws j m hm

/-- The instruction fields before position `j` of a side effect (all fields instructions). -/
theorem oracle_earlier_rep : ∀ (ws : List V) (j : Nat),
    earlier ws (List.replicate ws.length .i) j = ws.take j
  | [], j => by simp [earlier]
  | w :: ws, 0 => by rw [earlier_zero, List.take_zero]
  | w :: ws, j + 1 => by
    rw [List.length_cons, List.replicate_succ, earlier_succ, oracle_earlier_rep ws j]
    simp

/-! ## The state invariant through the emission -/

section Sem
variable {ctx : Ctx} {c : SC} {s0 : LState}

theorem oracle_DD_append {D : Nat → Prop} {ms0 ms : List MInst} :
    ∀ n, DD c (DD c D ms0) ms n → DD c D (ms0 ++ ms) n := by
  intro n h
  rcases h with (h | ⟨h1, m, hm, h2⟩) | ⟨h1, m, hm, h2⟩
  · exact .inl h
  · exact .inr ⟨h1, m, List.mem_append_left _ hm, h2⟩
  · exact .inr ⟨h1, m, List.mem_append_right _ hm, h2⟩

/-- Emitting instructions `ms` whose uses are defined (or fresh defs of the earlier ones) keeps
the state invariant; the defined set grows by `ms`'s fresh defs. -/
theorem oracle_isD_emit {s s' : LState} {ms : List MInst} (hI : IsD ctx c s0 s)
    (he : s'.emitted = s.emitted ++ ms.toArray) (hv : s'.nextVreg = s.nextVreg)
    (hu : ∀ (j : Nat) m, ms[j]? = some m → ∀ u ∈ useVregs m,
      DD c (Dn ctx c s0 s) (ms.take j) u) :
    IsD ctx c s0 s' ∧ RsD s s' ∧ ∀ n, DD c (Dn ctx c s0 s) ms n → Dn ctx c s0 s' n := by
  obtain ⟨⟨ms0, e0, h0⟩, hlo⟩ := hI
  have hD : Dn ctx c s0 s = DD c (D0 ctx c) ms0 := by unfold Dn; rw [emittedSince_of' e0]
  have e1 : s'.emitted = s0.emitted ++ (ms0 ++ ms).toArray := by rw [he, e0]; simp
  refine ⟨⟨⟨ms0 ++ ms, e1, fun k m hk u hu' => ?_⟩, by rw [hv]; exact hlo⟩,
    ⟨by rw [hv]; exact Nat.le_refl _, ms, he⟩, fun n hn => ?_⟩
  · by_cases hlt : k < ms0.length
    · rw [List.getElem?_append_left hlt] at hk
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact h0 k m hk u hu'
    · have hle : ms0.length ≤ k := Nat.le_of_not_lt hlt
      rw [List.getElem?_append_right hle] at hk
      have h1 := hu _ m hk u hu'
      rw [hD] at h1
      have ht : (ms0 ++ ms).take k = ms0 ++ ms.take (k - ms0.length) := by
        rw [List.take_append, List.take_of_length_le hle]
      rw [ht]
      exact oracle_DD_append u h1
  · unfold Dn
    rw [emittedSince_of' e1]
    rw [hD] at hn
    exact oracle_DD_append n hn

/-- The instructions of a side effect described by `PT … SideEffectNoResult` read defined vregs
or fresh defs of the earlier ones. -/
theorem oracle_fields {D : Nat → Prop} {k : Nat} {ws : List V}
    (hsh : flagShape TyId.«SideEffectNoResult» k = some (List.replicate ws.length .i))
    (hPT : PT c true D TyId.«SideEffectNoResult» (.data TyId.«SideEffectNoResult» k ws)) :
    ∀ (j : Nat) w, ws[j]? = some w → ∀ msj, (ws.take j).mapM MInst.ofV = some msj →
      MIok (DD c D msj) w := by
  intro j w hw msj hmsj
  rw [PT_flag (flagShape_mem hsh)] at hPT
  rcases hPT with hcl | ⟨k', fs, sh, heq, hsh', -, hseq⟩
  · exact MIok_mono (le_DD msj) (Cl_MIok ((Cl_data_iff.mp hcl) w (List.mem_of_getElem? hw)))
  · simp only [V.data.injEq, true_and] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [hsh] at hsh'
    cases hsh'
    have hj : j < ws.length := (List.getElem?_eq_some_iff.mp hw).1
    refine (hseq j w hw).2.1 ?_ msj ?_
    · simp [hj]
    · rw [oracle_earlier_rep]; exact hmsj

end Sem

/-! ## The transfer -/

/-- The cases of the oracle transfer. -/
theorem aOracle_inv {e e' : AEnv} {as : List A} {a : A} (h : aOracle e as = some (a, e')) :
    a = .cl false false ∧ fitsTy e F (as.headD .top) TyId.«SideEffectNoResult» true = true ∧
      (e' = e ∨ ∃ τ k fs sh, res e F (as.headD .top) = .data τ k fs ∧ flagShape τ k = some sh ∧
        emitSeq e F fs sh = some e') := by
  unfold aOracle at h
  by_cases hf : fitsTy e F (as.headD .top) TyId.«SideEffectNoResult» true = true
  · simp only [hf, ↓reduceIte] at h
    generalize hq : res e F (as.headD .top) = q at h
    cases q
    case data τ k fs =>
      cases hsh : flagShape τ k with
      | none =>
        simp only [hsh, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hf, .inl rfl⟩
      | some sh =>
        cases hes : emitSeq e F fs sh with
        | none => simp [hsh, hes] at h
        | some e1 =>
          simp only [hsh, hes, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, hf, .inr ⟨τ, k, fs, sh, rfl, hsh, hes⟩⟩
    all_goals
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hf, .inl rfl⟩
  · simp only [hf, ↓reduceIte, reduceCtorEq] at h

/-! ## The oracle obligation -/

/-- **The `oracle` field of `DModel program ctx c s0`.** -/
theorem dOracle {ctx : Ctx} {c : SC} {s0 : LState} :
    ∀ t ∈ oracles, ∀ (cfg : Config), cfg.checkOverlap = false →
    ∀ (n : Nat) (ty : TypeId) (as : List A) (e e' : AEnv) (a : A) (env : Isle.Interp.Env V)
      (vs : List V) (s : LState) (tr : Array RuleId) (r : Option V) (s' : LState)
      (tr' : Array RuleId),
    aOracle e as = some (a, e') → γL c as (Dn ctx c s0 s) env vs →
    EnvOK c (Dn ctx c s0 s) env e → IsD ctx c s0 s →
    (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    IsD ctx c s0 s' ∧ RsD s s' ∧ EnvOK c (Dn ctx c s0 s') env e' ∧
      ∀ v, r = some v → γ c a (Dn ctx c s0 s') env v := by
  intro t ht cfg hc n ty as e e' a env vs s tr r s' tr' ha hvs he hI h
  obtain ⟨hr, k, ws, ms, rfl, hsh, hms, hem, hnv⟩ :
      (∀ v, r = some v → regsU v = [] ∧ v.valsIn = [] ∧ v.instsIn = []) ∧
      ∃ k ws ms, vs = [.data TyId.«SideEffectNoResult» k ws] ∧
        flagShape TyId.«SideEffectNoResult» k = some (List.replicate ws.length .i) ∧
        ws.mapM MInst.ofV = some ms ∧ s'.emitted = s.emitted ++ ms.toArray ∧
        s'.nextVreg = s.nextVreg := by
    simp only [oracles, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl
    · obtain ⟨rfl, hx⟩ := oracle_esr_run hc h
      refine ⟨fun v hv => ?_, hx⟩
      cases hv
      exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨rfl, hx⟩ := oracle_se_run hc h
      refine ⟨fun v hv => ?_, hx⟩
      cases hv
      exact ⟨rfl, rfl, rfl⟩
  rcases as with _ | ⟨a0, _ | ⟨a1, as⟩⟩
  · exact absurd hvs (by simp [γL])
  case cons.nil =>
    have hγ0 : γ c a0 (Dn ctx c s0 s) env (.data TyId.«SideEffectNoResult» k ws) := hvs.1
    obtain ⟨rfl, hfit, hE'⟩ := aOracle_inv ha
    simp only [List.headD_cons] at hfit hE'
    have hPT := fitsTy_sound he F a0 _ true hγ0 hfit
    obtain ⟨hI', hR, hDn⟩ := oracle_isD_emit hI hem hnv fun j m hm u hu => by
      obtain ⟨w, hw, hwm⟩ := oracle_mapM_get hms j m hm
      exact (oracle_fields hsh hPT j w hw (ms.take j) (oracle_mapM_take hms j) m hwm).1 u hu
    have hres : ∀ v, r = some v → γ c (.cl false false) (Dn ctx c s0 s') env v := fun v hv =>
      let ⟨h1, h2, h3⟩ := hr v hv
      Cl_noAtoms h1 h2 h3
    rcases hE' with rfl | ⟨τ, k', fs, sh, hq, hsh', hes⟩
    · exact ⟨hI', hR, he.mono (Dn_mono hI hR), hres⟩
    have hγr := res_sound he F a0 hγ0
    rw [hq] at hγr
    obtain ⟨ws', hweq, hL⟩ := hγr
    simp only [V.data.injEq] at hweq
    obtain ⟨rfl, rfl, rfl⟩ := hweq
    rw [hsh] at hsh'
    cases hsh'
    have hE := (emitSeq_sound fs _ he hL hes).2 ms (by
      rw [List.length_replicate, oracle_earlier_rep, List.take_length]; exact hms)
    exact ⟨hI', hR, hE.mono hDn, hres⟩
  · exact absurd hvs (by simp [γL])

end Backend.Proof.DefGen
