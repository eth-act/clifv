module

public import FV.Backend.Proof.IselSzTDefs

@[expose] public section

/-!
# The size of the ISLE lowering's output over float-capable contexts (typed V6c): chunked rule
checks

A rule with many abstract environments is too large for one kernel `decide` of `cRuleLe`
(LEARNINGS.md, "Split one leaf further"). `cRuleLe_of_chunks` assembles `cRuleLe ins c r` from
checks of chunks of its pattern environments (`ifOk`: the if-lets' cost at most `a`) and of its
environments after the if-lets (`envOk`: the right-hand side's cost at most `b`), with
`a + b ≤ c`; `IselSzTGen` emits these checks for the rule/family pairs it lists as heavy.
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

section
variable (p : Program) (tab : Tab) (aw : TermId → List AT → Option Nat) (ctab : CTab)
  (aext : TermId → AT → List AT) (actor : TermId → List AT → AT) (apre : TermId → List AT → Bool)
  (aOracle : TermId → List AT → Option AT)

/-- The if-lets of `r` on pattern environment `e` cost at most `a`. -/
def ifOk (r : Rule) (a : Nat) (e : List AT) : Bool :=
  match cIfLets p tab aw ctab aext actor apre aOracle r.iflets e with
  | some d => decide (d ≤ a)
  | none => false

/-- The right-hand side of `r` on environment `env` costs at most `b`. -/
def envOk (r : Rule) (b : Nat) (env : List AT) : Bool :=
  match cExpr p tab aw ctab actor apre aOracle r.rhs env with
  | some d => decide (d ≤ b)
  | none => false

end

/-- A list checked chunk by chunk. -/
theorem all_of_chunks {α : Type} (g : α → Bool) (L : List α) (k n : Nat)
    (hn : L.length ≤ n * k) (h : ∀ c < n, ((L.drop (c * k)).take k).all g = true) :
    L.all g = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, Nat.mul_zero] at hn; omega
    · exact h0
  have hc : j / k < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
  have hjk := Nat.div_add_mod' j k
  have hm := Nat.mod_lt j hk
  have hl : j % k < ((L.drop (j / k * k)).take k).length := by
    simp only [List.length_take, List.length_drop]; omega
  have := List.all_eq_true.1 (h _ hc) _ (List.getElem_mem hl)
  simp only [List.getElem_take, List.getElem_drop] at this
  simp only [hjk] at this
  exact this

/-- `mapM` of a function bounded by `b` everywhere: some list whose maximum is at most `b`. -/
theorem mapM_le {α : Type} {g : α → Option Nat} {b : Nat} :
    ∀ (L : List α), (∀ x ∈ L, ∃ d, g x = some d ∧ d ≤ b) →
      ∃ ds, L.mapM g = some ds ∧ ∀ y ∈ ds, y ≤ b
  | [], _ => ⟨[], rfl, fun _ h => by cases h⟩
  | x :: L, h => by
    obtain ⟨d, hg, hd⟩ := h x (List.mem_cons_self ..)
    obtain ⟨ds, hds, hle⟩ := mapM_le L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨d :: ds, by simp [List.mapM_cons, hg, hds], fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hd
    · exact hle y hy

/-- The maximum of a list bounded by `b` is at most `b`. -/
theorem foldl_max_le {b : Nat} : ∀ (l : List Nat) (m : Nat), m ≤ b → (∀ y ∈ l, y ≤ b) →
    l.foldl max m ≤ b
  | [], _, hm, _ => hm
  | y :: l, m, hm, hy => foldl_max_le l _ (Nat.max_le.mpr ⟨hm, hy y (List.mem_cons_self ..)⟩)
      (fun z hz => hy z (List.mem_cons_of_mem _ hz))

/-- **`cRuleLe` from chunk-wise checks**: the pattern environments' if-lets (`ifOk`, chunks of
`kA`, `nA` of them) cost at most `a`, the environments' right-hand sides (`envOk`, chunks of
`kB`, `nB` of them) at most `b`, and `a + b ≤ c`. -/
theorem cRuleLe_of_chunks {p : Program} {tab : Tab} {aw : TermId → List AT → Option Nat}
    {ctab : CTab} {aext : TermId → AT → List AT} {actor : TermId → List AT → AT}
    {apre : TermId → List AT → Bool} {aOracle : TermId → List AT → Option AT}
    {ins : List AT} {c : Nat} {r : Rule} (a b kA nA kB nB : Nat) (hab : a + b ≤ c)
    (hnA : (aPatArgs p aext ins r.args (List.replicate r.vars.length .top)).length ≤ nA * kA)
    (hA : ∀ i < nA, (((aPatArgs p aext ins r.args (List.replicate r.vars.length .top)).drop
      (i * kA)).take kA).all (ifOk p tab aw ctab aext actor apre aOracle r a) = true)
    (hs : (aRuleEnvs p tab aext actor apre aOracle ins r).isSome = true)
    (hnB : ((aRuleEnvs p tab aext actor apre aOracle ins r).getD []).length ≤ nB * kB)
    (hB : ∀ i < nB, ((((aRuleEnvs p tab aext actor apre aOracle ins r).getD []).drop
      (i * kB)).take kB).all (envOk p tab aw ctab actor apre aOracle r b) = true) :
    cRuleLe p tab aw ctab aext actor apre aOracle ins c r = true := by
  have hA' := all_of_chunks _ _ kA nA hnA hA
  obtain ⟨cs, hcs, hcsle⟩ := mapM_le (g := cIfLets p tab aw ctab aext actor apre aOracle r.iflets)
    (b := a) _ fun x hx => by
      have := List.all_eq_true.mp hA' x hx
      unfold ifOk at this
      split at this
      · rename_i d hd; exact ⟨d, hd, of_decide_eq_true this⟩
      · cases this
  cases he : aRuleEnvs p tab aext actor apre aOracle ins r with
  | none => rw [he] at hs; cases hs
  | some envs =>
    rw [he] at hnB hB
    have hB' := all_of_chunks _ envs kB nB hnB hB
    obtain ⟨ds, hds, hdsle⟩ := mapM_le (g := cExpr p tab aw ctab actor apre aOracle r.rhs)
      (b := b) envs fun x hx => by
        have := List.all_eq_true.mp hB' x hx
        unfold envOk at this
        split at this
        · rename_i d hd; exact ⟨d, hd, of_decide_eq_true this⟩
        · cases this
    have h1 := foldl_max_le cs 0 (Nat.zero_le _) hcsle
    have h2 := foldl_max_le ds 0 (Nat.zero_le _) hdsle
    unfold cRuleLe cRule
    rw [hcs, he]
    simp only [hds]
    exact decide_eq_true (by omega)

end Backend.Proof.CovT
