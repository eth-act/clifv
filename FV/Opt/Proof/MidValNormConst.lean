import FV.Opt.Proof.MidValTerm
import FV.Opt.Proof.MidValFloat

/-!
# Constant evaluation is a sound normaliser (#1119 stage 2, family 1)

`Opt.MidVal.evalConst` replaces a pure, non-partial node with operands whose operands are all
constant terms (`constOf`) by the constant `Clif.evalInst` gives it in a frame holding those
constants (`constFrame`). It rests on no rewrite rule: only on the semantics.

* `evalInst_isPure_frame`: a pure node with operands reads neither the frame's function nor its
  slots (the frame `evalConst` uses has neither);
* `mapM_lookup`: the constants `evalConst` collected are the operands' (`List.lookup`);
* `tmVal_of_constOf`: a constant term has its constant as value;
* **`normSound_evalConst : NormSound evalConst`**.
-/

namespace Opt.MidVal

open Clif

/-- A pure node with operands (every `isPure` node but `iconst`, `stack_addr` and
`symbol_value`) reads neither the frame's function nor its slots. -/
theorem evalInst_isPure_frame {fr fr' : Frame} {mem : Mem} {i : Inst} (hp : isPure i = true)
    (hops : operands i ≠ []) (hr : ∀ x ∈ operands i, fr'.regs x = fr.regs x) :
    evalInst fr' mem i = evalInst fr mem i := by
  have h : evalInst fr' mem i = evalInst { fr' with func := fr.func, slots := fr.slots } mem i := by
    cases i <;> simp only [isPure, Bool.false_eq_true] at hp <;>
      first | rfl | simp [operands] at hops
  rw [h]
  exact evalInst_congr rfl rfl rfl hr

/-- What a successful `mapM` collected: each element's image, found by `List.lookup`. -/
theorem mapM_lookup {g : Nat → Option Val} :
    ∀ {l : List Nat} {vs : List Val}, l.mapM g = some vs →
      ∀ x ∈ l, ∃ c, g x = some c ∧ (l.zip vs).lookup x = some c
  | [], _, _, x, hx => by cases hx
  | a :: l, vs, h, x, hx => by
    cases ha : g a with
    | none => simp [List.mapM_cons, ha] at h
    | some b =>
      cases hl : l.mapM g with
      | none => simp [List.mapM_cons, ha, hl] at h
      | some bs =>
        simp only [List.mapM_cons, ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        by_cases hxa : x = a
        · subst hxa
          exact ⟨b, ha, by simp [List.lookup]⟩
        · have hx' : x ∈ l := by simpa [hxa] using hx
          obtain ⟨c, hc, hlk⟩ := mapM_lookup hl x hx'
          refine ⟨c, hc, ?_⟩
          have : (x == a) = false := by simpa using hxa
          simp [List.lookup, this, hlk]

/-- A constant term (`constOf`) has its constant as value. -/
theorem tmVal_of_constOf {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {o : Nat}
    {v : Val} (h : constOf tms o = some v) : tmVal f tms fr mem o = some v := by
  unfold constOf at h
  split at h
  · rename_i ty imm hx
    cases h
    rw [tmVal_node hx (by simp [operands])]
    rfl
  · cases h

/-- **Constant evaluation is sound**: the constant `evalConst` gives a node is the node's value
on its operands' values, in every frame and memory. -/
theorem normSound_evalConst : NormSound evalConst := by
  intro tms i x hx f fr mem t ht
  simp only [evalConst] at hx
  split at hx
  · cases hx
  rename_i hc
  have hne : operands i ≠ [] := by
    intro h
    simp [h] at hc
  have hp : isPure i = true := by
    cases h : isPure i <;> simp [h] at hc ⊢
  have hpart : partialK i = false := by
    cases h : partialK i <;> simp [h] at hc ⊢
  split at hx
  · cases hx
  rename_i vals hvals
  split at hx
  · rename_i v m hev
    cases hx
    rw [tmVal_node ht (by simp [operands])]
    have hl : evalNode (tmFrame f tms fr mem) mem (.iconst v.ty v.bits) = some v := rfl
    rw [hl, evalNode_pureK_mem (m := Mem.empty) (by simp [pureK, hp]) hpart]
    have hr : ∀ y ∈ operands i, (tmFrame f tms fr mem).regs y = (constFrame (operands i) vals).regs y := by
      intro y hy
      obtain ⟨c, hc, hlk⟩ := mapM_lookup hvals y hy
      exact (tmVal_of_constOf hc).trans hlk.symm
    simp only [evalNode, evalInst_isPure_frame hp hne hr, hev]
  · cases hx

end Opt.MidVal
