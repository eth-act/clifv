import FV.Compile.SubsetT

/-!
# `try_call` return and payload arguments go to integer parameters (S11e5 Stage C, slice 6)

`Compile.tryArgClassOk f`: every `ret i`/`exn i` argument of a `try_call`/`try_call_indirect`
successor goes to a parameter of integer type (the CLIF verifier types it as the callee's `i`-th
return, an integer by `instData`'s `sigIntB`, or as an exception payload, `i64`). The lowering
passes these arguments in the integer vregs of `tryRegsOf`; `edgeClassOk` checks only the `val`
arguments. `tryArgClassOk_sound` states it as a proposition; `tryArgClassOk_of_functionE`: every
function of subset E passes it.
-/

namespace Compile

open Clif

/-- **`try_call` return/payload arguments go to integer parameters** (decided). -/
def tryArgClassOk (f : Function) : Bool :=
  f.blocks.all fun b => match b.term with
    | .tryCall _ _ et | .tryCallIndirect _ _ et => et.dests.all fun td =>
      match f.block? td.block with
      | some tb => (td.args.zip tb.params).all fun
        | (.val _, _) => true
        | (_, p) => !p.2.isFloat
      | none => true
    | _ => true

/-- **Soundness of `tryArgClassOk`.** -/
theorem tryArgClassOk_sound {f : Function} (h : tryArgClassOk f = true) :
    ∀ b ∈ f.blocks, ∀ et : ExnTable,
      ((∃ fn args, b.term = .tryCall fn args et) ∨ (∃ c args, b.term = .tryCallIndirect c args et)) →
      ∀ td ∈ et.dests, ∀ tb, f.block? td.block = some tb →
      ∀ (a : TryArg) (p : ValueId × Ty), (a, p) ∈ td.args.zip tb.params → (∀ v, a ≠ .val v) →
        p.2.isFloat = false := by
  intro b hb et het td htd tb htb a p hap hv
  have hb' := List.all_eq_true.mp h b hb
  have hd : ∀ et' : ExnTable, et' = et → (et'.dests.all fun td =>
      match f.block? td.block with
      | some tb => (td.args.zip tb.params).all fun
        | (.val _, _) => true
        | (_, p) => !p.2.isFloat
      | none => true) = true → p.2.isFloat = false := by
    intro et' he h2
    subst he
    have h3 := List.all_eq_true.mp h2 td htd
    rw [htb] at h3
    have h4 := List.all_eq_true.mp h3 _ hap
    cases a with
    | val v => exact absurd rfl (hv v)
    | ret i => simpa using h4
    | exn i => simpa using h4
  rcases het with ⟨fn, args, he⟩ | ⟨c, args, he⟩ <;> rw [he] at hb' <;> exact hd et rfl hb'

/-- **Subset E passes `tryArgClassOk`** (its block parameters are integers). -/
theorem tryArgClassOk_of_functionE {f : Function} (hE : functionE f = true) :
    tryArgClassOk f = true := by
  simp only [functionE, Bool.and_eq_true, List.all_eq_true] at hE
  obtain ⟨-, hb⟩ := hE
  have hblk : ∀ {bid tb}, f.block? bid = some tb → ∀ p ∈ tb.params, p.2.isFloat = false :=
    fun htb p hp => isFloat_of_tyE ((hb _ (List.mem_of_find?_eq_some htb)).1.1 p hp)
  have hdests : ∀ et : ExnTable, (et.dests.all fun td =>
      match f.block? td.block with
      | some tb => (td.args.zip tb.params).all fun
        | (.val _, _) => true
        | (_, p) => !p.2.isFloat
      | none => true) = true := by
    intro et
    refine List.all_eq_true.mpr fun td _ => ?_
    split
    · rename_i tb htb
      refine List.all_eq_true.mpr fun ap hm => ?_
      split
      · rfl
      · rename_i _ q _
        have := hblk htb _ (List.of_mem_zip hm).2
        revert this; cases q.2 <;> decide
    · rfl
  refine List.all_eq_true.mpr fun b _ => ?_
  split
  · exact hdests _
  · exact hdests _
  · rfl

end Compile
