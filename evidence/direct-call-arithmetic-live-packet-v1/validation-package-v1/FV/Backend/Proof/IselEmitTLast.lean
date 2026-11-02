import FV.Backend.Proof.IselEmitTFns
import FV.Backend.Proof.IselEmitLast
import FV.Backend.Proof.IselCovTSound

/-!
# Emission conditions of the typed ISLE lowering (S11): runs ending in a branch

`IselEmitLast` over the typed domain. For a model of the typed emission analysis
(`CovModel aextET actorET apreET aOracle`, invariant `EmSince s0`) and the emission check `emChk`
sound for `MInst.ofV` (hypothesis `hchk`):

* `esr_last`: an `emit_side_effect` run on a side effect `senrLast` accepts emits its
  instructions, each `emitOk`, only the last with targets (`Cov.esr_inst*`, context-free);
* `aLast_sound`: a run of an expression `aLast` accepts ends with `EmLast s0`;
* `root_last`: a root internal term whose rules pass `aRule`, `aRuleLast`, or never match.
-/

set_option maxRecDepth 20000

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (esr_inst esr_inst2 esr_inst3 emSince_emLast emSince_emLast_trans
  emLast_of_list apply_internal_last internalOne)

/-! ## The `emit_side_effect` tail -/

section Tail
variable {f : Clif.Function} {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
  (hchk : ∀ nb a v m, emChk nb a = true → γ f ctx a v → MInst.ofV v = some m →
    m.emitOk = true ∧ (nb = true → m.targets = []))
include hc hchk

/-- A side effect `senr1` checks: its `emit_side_effect` run emits its instructions, each
`emitOk`, all but the last without targets. -/
theorem esr1_last {a : AT} {v : V} (ha : senr1 a = true) (hv : γ f ctx a v) {n : Nat} {ty : TypeId}
    {s : LState} {tr : Array RuleId} {r : Option V} {s' : LState} {tr' : Array RuleId}
    (h : (applyTerm program (sem ctx) cfg n ty TId.emit_side_effect [v]).run (s, tr) =
      .ok (r, (s', tr'))) : Driver.EmLast s s' := by
  unfold senr1 at ha
  split at ha
  · rename_i t k i
    simp only [Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨⟨rfl, rfl⟩, hi⟩ := ha
    obtain ⟨vs, rfl, hl⟩ := hv
    match vs, hl with
    | [vi], ⟨hvi, _⟩ =>
      obtain ⟨m, hm, rfl⟩ := esr_inst hc h
      have hok := hchk _ _ _ _ hi hvi hm
      exact emLast_of_list [m] (by simp [LState.emit])
        (by simpa using hok.1) (by simp)
  · rename_i t k i j
    simp only [Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨⟨⟨rfl, rfl⟩, hi⟩, hj⟩ := ha
    obtain ⟨vs, rfl, hl⟩ := hv
    match vs, hl with
    | [vi, vj], ⟨hvi, hvj, _⟩ =>
      obtain ⟨m1, m2, hm1, hm2, rfl⟩ := esr_inst2 hc h
      have hok1 := hchk _ _ _ _ hi hvi hm1
      have hok2 := hchk _ _ _ _ hj hvj hm2
      exact emLast_of_list [m1, m2]
        (by simp only [LState.emit, Array.push_eq_append, Array.append_assoc] <;> rfl)
        (by simp [hok1.1, hok2.1]) (by simp [hok1.2 rfl])
  · rename_i t k i j l
    simp only [Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨⟨⟨⟨rfl, rfl⟩, hi⟩, hj⟩, hl'⟩ := ha
    obtain ⟨vs, rfl, hl⟩ := hv
    match vs, hl with
    | [vi, vj, vl], ⟨hvi, hvj, hvl, _⟩ =>
      obtain ⟨m1, m2, m3, hm1, hm2, hm3, rfl⟩ := esr_inst3 hc h
      have hok1 := hchk _ _ _ _ hi hvi hm1
      have hok2 := hchk _ _ _ _ hj hvj hm2
      have hok3 := hchk _ _ _ _ hl' hvl hm3
      exact emLast_of_list [m1, m2, m3]
        (by simp only [LState.emit, Array.push_eq_append, Array.append_assoc] <;> rfl)
        (by simp [hok1.1, hok2.1, hok3.1]) (by simp [hok1.2 rfl, hok2.2 rfl])
  · cases ha

/-- `senrLast`: every alternative checks. -/
theorem esr_last {a : AT} {v : V} (ha : senrLast a = true) (hv : γ f ctx a v) {n : Nat}
    {ty : TypeId} {s : LState} {tr : Array RuleId} {r : Option V} {s' : LState}
    {tr' : Array RuleId}
    (h : (applyTerm program (sem ctx) cfg n ty TId.emit_side_effect [v]).run (s, tr) =
      .ok (r, (s', tr'))) : Driver.EmLast s s' := by
  cases a with
  | alts as =>
    obtain ⟨x, hx, hxv⟩ := γAny_iff.mp hv
    exact esr1_last hc hchk (List.all_eq_true.mp ha x hx) hxv h
  | _ => exact esr1_last hc hchk (by unfold senrLast at ha; exact ha) hv h

end Tail

/-! ## Soundness of `aLast` -/

section Sound
variable {f : Clif.Function} {ctx : Ctx} {s0 : LState}
  (md : CovModel aextET actorET apreET aOracle program f ctx)
  (hmd : ∀ s, md.Is s ↔ Driver.EmSince s0 s) {cfg : Config} (hc : cfg.checkOverlap = false)
  {tab : Tab} (htab : chkTab program tab aextET actorET apreET aOracle = true)
  (hchk : ∀ nb a v m, emChk nb a = true → γ f ctx a v → MInst.ofV v = some m →
    m.emitOk = true ∧ (nb = true → m.targets = []))
include hmd hc htab hchk

/-- **Soundness of `aLast`**: a run of an expression `aLast` accepts, from a state with
`EmSince s0`, ends in a state with `EmLast s0`. -/
theorem aLast_sound : ∀ (k : Nat) (e : Isle.Expr) (aenv : List AT) (env : Isle.Interp.Env V)
    (n : Nat) (s : LState) (tr : Array RuleId) (r : Option V) (s' : LState) (tr' : Array RuleId),
    aLast program tab aextET actorET apreET aOracle k e aenv = true → EnvOK f ctx aenv env →
    Driver.EmSince s0 s →
    (evalExpr program (sem ctx) cfg n e env).run (s, tr) = .ok (r, (s', tr')) →
    Driver.EmLast s0 s' := by
  have sa := soundAt md cfg tab hc htab
  intro k
  induction k with
  | zero => intro e aenv env n s tr r s' tr' ha; simp [aLast] at ha
  | succ k ih =>
  intro e aenv env n s tr r s' tr' ha he hs h
  rcases n with _ | n
  · rw [evalExpr.eq_1] at h; exact (throw_ok h).elim
  cases e with
  | term ty t args =>
    rw [evalExpr.eq_7] at h
    obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
    simp only [aLast] at ha
    split at ha
    · rename_i hte
      obtain rfl : t = TId.emit_side_effect := eq_of_beq hte
      split at ha
      · rename_i e
        split at ha
        · rename_i a hae
          obtain ⟨hIs1, hv1⟩ := (sa n).args [e] aenv [a] env s tr o s1 tr1
            (by simp [aArgs, hae]) he ((hmd s).2 hs) h1
          have hs1 := (hmd s1).1 hIs1
          cases o with
          | none => cases pure_ok h2; exact emSince_emLast hs1
          | some vs =>
            match vs, hv1 vs rfl with
            | [v], ⟨hv, _⟩ => exact emSince_emLast_trans hs1 (esr_last hc hchk ha hv h2)
        · cases ha
      · cases ha
    · simp only [Bool.and_eq_true] at ha
      obtain ⟨⟨hio, -⟩, ha⟩ := ha
      rw [rulesOfT_eq] at ha
      split at ha
      · rename_i as hargs
        obtain ⟨hIs1, hv1⟩ := (sa n).args args aenv as env s tr o s1 tr1 hargs he ((hmd s).2 hs) h1
        have hs1 := (hmd s1).1 hIs1
        cases o with
        | none => cases pure_ok h2; exact emSince_emLast hs1
        | some vs =>
          unfold internalOne at hio
          split at hio
          · rename_i term htm
            split at hio
            · rename_i flags ex hk
              refine apply_internal_last hc htm hk hs1 ?_ h2
              intro rl hrl m env' s2 tr2 k' o' s3 tr3 hmatch hrhs
              have hr := List.all_eq_true.mp ha rl hrl
              split at hr
              · rename_i envs hae
                obtain ⟨hIs2, aenv', haenv, he'⟩ :=
                  (sa m).mrule _ _ _ _ _ _ _ _ _ hae (hv1 vs rfl) hIs1 hmatch
                exact ih rl.rhs aenv' env' k' s2 tr2 o' s3 tr3 (List.all_eq_true.mp hr aenv' haenv)
                  he' ((hmd s2).1 hIs2) hrhs
              · cases hr
            · cases hio
          · cases hio
      · cases ha
  | «let» ty bs body =>
    rw [evalExpr.eq_6] at h
    simp only [aLast] at ha
    split at ha
    · rename_i aenv' hb
      obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      obtain ⟨hIs1, he1⟩ := (sa n).binds _ _ _ _ _ _ _ _ _ hb he ((hmd s).2 hs) h1
      cases o with
      | none => cases pure_ok h2; exact emSince_emLast ((hmd _).1 hIs1)
      | some env' =>
        exact ih body aenv' env' n s1 tr1 r s' tr' ha (he1 env' rfl) ((hmd s1).1 hIs1) h2
    · cases ha
  | _ => simp [aLast] at ha

/-- **A root term whose rules pass `aRule`, end in a branch (`aRuleLast`), or never match**: a
run from a state with `EmSince s0` ends in a state with `EmLast s0`. -/
theorem root_last {vs : List V} {K : Nat} {ty : TypeId} {t : TermId} {term : Term}
    {flags : TermFlags} {ex : Option Extractor} {ins : List AT} {s : LState} {tr : Array RuleId}
    {r : Option V} {s' : LState} {tr' : Array RuleId} (ht : termOf program t = .ok term)
    (hk : term.kind = .decl flags (some .internal) ex)
    (hrules : ∀ rl ∈ program.rulesOf t,
      aRule program tab aextET actorET apreET aOracle ins AT.top rl = true ∨
      aRuleLast program tab aextET actorET apreET aOracle K ins rl = true ∨
      (∀ m st env s1, (matchRule program (sem ctx) cfg m rl vs).run st ≠ .ok (some env, s1)))
    (hins : Holds2 f ctx ins vs) (hs : Driver.EmSince s0 s) {n : Nat}
    (h : (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    Driver.EmLast s0 s' := by
  have sa := soundAt md cfg tab hc htab
  refine apply_internal_last hc ht hk hs ?_ h
  intro rl hrl m env s1 tr1 k o s2 tr2 hmatch hrhs
  rcases hrules rl hrl with hok | hlast | hno
  · obtain ⟨envs, hae, hall⟩ := aRule_inv hok
    obtain ⟨hIs1, aenv, haenv, he1⟩ :=
      (sa m).mrule _ _ _ _ _ _ _ _ _ hae hins ((hmd s).2 hs) hmatch
    obtain ⟨a, ha, -⟩ := hall aenv haenv
    exact emSince_emLast ((hmd s2).1 ((sa k).expr _ _ _ _ _ _ _ _ _ ha he1 hIs1 hrhs).1)
  · unfold aRuleLast at hlast
    split at hlast
    · rename_i envs hae
      obtain ⟨hIs1, aenv, haenv, he1⟩ :=
        (sa m).mrule _ _ _ _ _ _ _ _ _ hae hins ((hmd s).2 hs) hmatch
      exact aLast_sound md hmd hc htab hchk K rl.rhs aenv env k s1 tr1 o s2 tr2
        (List.all_eq_true.mp hlast aenv haenv) he1 ((hmd s1).1 hIs1) hrhs
    · cases hlast
  · exact absurd hmatch (hno m _ _ _)

end Sound

end Backend.Proof.CovT
