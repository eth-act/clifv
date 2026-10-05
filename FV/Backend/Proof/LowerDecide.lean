import FV.Backend.Proof.LowerLoop
import FV.Backend.Proof.LowerFix
import Std.Data.HashSet.Lemmas

/-!
# Completeness of `lowerCheck`: the input conditions, decided

`dominatedB f` decides `Dominated f` (`dominated_of`) and `lowerScopeB f` decides
`LowerScope f` (`lowerScope_of`), both on the CLIF input alone (they run `buildCtx` and the
input-only availability `availIn`, never the lowering). `lean-e2e-check` reports how many
corpus and runtest functions satisfy them.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- `List.Nodup` of a list of numbers, with a hash set. -/
def nodupB (l : List Nat) : Bool :=
  (l.foldl (fun (acc : Option (Std.HashSet Nat)) x => acc.bind fun s =>
    if s.contains x then none else some (s.insert x)) (some {})).isSome

/-- A lowering record with only a block start (what `Avail.of` reads). -/
def startOnly (start : Nat) : BLow :=
  { start, sl := [], data := default, targets := [], tst := default, tst' := default, tl := none }

/-- `Dominated f`, decided (`dominated_of`). -/
def dominatedB (f : Clif.Function) : Bool :=
  nodupB (valueDefs f) &&
  match buildCtx f with
  | .error _ => true
  | .ok (ctx, _, _) =>
    let In := availIn f ctx
    (List.range f.blocks.length).all fun bi => match f.blocks[bi]? with
      | none => true
      | some B =>
        let a := Avail.of B (startOnly (blockStart f bi)) In bi
        let ds := Std.HashSet.ofList (defsOf f bi)
        let ps := Std.HashSet.ofList (parsOf f bi)
        (List.range B.body.length).all (fun j => match B.body[j]? with
          | some stm => (instArgs stm.inst).all (a.mem ctx j)
          | none => true) &&
        (termArgs (abiTerm f B.term)).all (a.mem ctx B.body.length) &&
        (In.getD bi []).all fun x => ds.contains x || (defArgs ctx x).all fun y => !ps.contains y

/-- `LowerScope f`, decided (`lowerScope_of`). -/
def lowerScopeB (f : Clif.Function) : Bool :=
  Compile.functionE f && !f.blocks.isEmpty &&
  f.blocks.all (fun B => (succIds B.term).all fun b => blockIdx? f b != some 0) &&
  (match buildCtx f with
    | .error _ => true
    | .ok (ctx, _, _) => brIdxOk f ctx &&
      ctx.insts.toList.all fun info => match info.clif with
        | some inst => match memAddr? inst with
          | some x => decide (ctx.valueType? x = some (.int 64))
          | none => true
        | none => true) &&
  f.blocks.all (fun B => match B.term with
    | .tryCall _ _ et | .tryCallIndirect _ _ et => match f.sigDecls.lookup et.sig with
      | some sig => et.normal.args.all fun
        | .ret i => decide (i < sig.returns.length)
        | _ => true
      | none => true
    | _ => true) &&
  f.blocks.all (fun B => B.body.all fun st => match st.inst with
    | .call fn _ => match f.extern? fn with
      | some e => stackLayoutOk e.sig
      | none => true
    | _ => true) &&
  f.blocks.all fun B => match B.term with
    | .tryCall fn _ _ => match f.extern? fn with
      | some e => stackLayoutOk e.sig
      | none => true
    | _ => true

/-! ## Soundness -/

/-- One step of `nodupB`'s fold. -/
def nodupStep (acc : Option (Std.HashSet Nat)) (x : Nat) : Option (Std.HashSet Nat) :=
  acc.bind fun s => if s.contains x then none else some (s.insert x)

theorem nodupStep_none : ∀ l : List Nat, l.foldl nodupStep none = none
  | [] => rfl
  | _ :: l => nodupStep_none l

theorem nodupB_fold : ∀ (l : List Nat) (s : Std.HashSet Nat),
    (l.foldl nodupStep (some s)).isSome = true → l.Nodup ∧ ∀ x ∈ l, s.contains x = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h => by simp at h⟩
  | x :: l, s, h => by
    simp only [List.foldl_cons, nodupStep, Option.bind_some] at h
    by_cases hx : s.contains x = true
    · simp only [hx, ite_true, nodupStep_none] at h
      cases h
    · simp only [hx, Bool.false_eq_true, ite_false] at h
      obtain ⟨hn, hc⟩ := nodupB_fold l (s.insert x) h
      have hc' : ∀ y ∈ l, x ≠ y ∧ s.contains y = false := fun y hy => by
        have := hc y hy
        rw [Std.HashSet.contains_insert] at this
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at this
        exact this
      refine ⟨List.nodup_cons.mpr ⟨fun hm => (hc' x hm).1 rfl, hn⟩, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · simpa using hx
      · exact (hc' y hy).2

theorem nodupB_sound {l : List Nat} (h : nodupB l = true) : l.Nodup :=
  (nodupB_fold l {} h).1

theorem all_range' {n : Nat} {p : Nat → Bool} (h : (List.range n).all p = true) {i : Nat}
    (hi : i < n) : p i = true :=
  List.all_eq_true.mp h i (List.mem_range.mpr hi)

/-- `dominatedB` decides `Dominated`. -/
theorem dominated_of {f : Clif.Function} (h : dominatedB f = true) : Dominated f := by
  simp only [dominatedB, Bool.and_eq_true] at h
  obtain ⟨hn, h⟩ := h
  have hssa := nodupB_sound hn
  refine ⟨hssa, fun ctx ranges st0 hb bi B hB => ?_, fun ctx ranges st0 hb tl x hx hxd y hy => ?_⟩
  · rw [hb] at h
    have hcf := ctxFacts_of hb
    have hbi : bi < f.blocks.length := lt_of_getElem? hB
    have := all_range' h hbi
    simp only [hB, Bool.and_eq_true, List.all_eq_true] at this
    obtain ⟨⟨hs, ht⟩, -⟩ := this
    have hD : DefsAt ctx B (startOnly (blockStart f bi)).start := fun k stm hk r hr =>
      (hcf.defs hssa r _).mpr ⟨bi, B, k, stm, hB, hk, hr, rfl⟩
    refine ⟨fun j stm hj y hy => ?_, fun y hy => ?_⟩
    · have := hs j (List.mem_range.mpr (lt_of_getElem? hj))
      simp only [hj] at this
      exact (mem_avail hB hD).mpr (List.all_eq_true.mp this y hy)
    · exact (mem_avail hB hD).mpr (ht y hy)
  · rw [hb] at h
    simp only at h
    have hlen : (inFix f ctx id).size = f.blocks.length := inFix_size
    have htl : tl < f.blocks.length := by
      rw [← hlen]
      refine Classical.byContradiction fun hc => ?_
      simp [availIn, Array.getD, hc] at hx
    obtain ⟨B, hB⟩ : ∃ B, f.blocks[tl]? = some B := ⟨_, List.getElem?_eq_getElem htl⟩
    have := all_range' h htl
    simp only [hB, Bool.and_eq_true, List.all_eq_true] at this
    have h3 := this.2 x hx
    simp only [Bool.or_eq_true, Std.HashSet.contains_ofList, List.contains_iff_mem,
      List.all_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq] at h3
    rcases h3 with h3 | h3
    · exact absurd h3 hxd
    · exact h3 y hy

/-- `lowerScopeB` decides `LowerScope`. -/
theorem lowerScope_of {f : Clif.Function} (h : lowerScopeB f = true) : LowerScope f := by
  simp only [lowerScopeB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨hE, hne⟩, hent⟩, hctx⟩, htry⟩, hcall⟩, htc⟩ := h
  refine ⟨hE, hne, hent, fun ctx ranges st0 hb => ?_, fun B hB et het sig hsig i hi => ?_,
    ⟨fun B hB st hst fn args e hi he => ?_, fun B hB fn args et e ht he => ?_⟩⟩
  · rw [hb] at hctx
    simp only [Bool.and_eq_true, List.all_eq_true] at hctx
    refine ⟨hctx.1, fun ii info inst x hi hc hm => ?_⟩
    have := hctx.2 info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    simp only [hc, hm, decide_eq_true_eq] at this
    exact this
  · have := htry B hB
    rcases het with ⟨fn, args, ht⟩ | ⟨c, args, ht⟩ <;>
    · simp only [ht, hsig, List.all_eq_true] at this
      have := this _ hi
      simpa using this
  · have := hcall B hB st hst
    simp only [hi, he] at this
    exact this
  · have := htc B hB
    simp only [ht, he] at this
    exact this

end Backend.Proof.Driver
