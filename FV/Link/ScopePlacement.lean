import FV.Link.Compile
import FV.Link.ExeInput
import FV.Link.LayoutFacts

/-! # The input conditions do not read the placement (#1108)

`inScopePar`/`inScopeInPar` (`InScopeP`/`InScopeIn`) read the input's program and, of the CLIF
image's symbols, only which names have one (`mayB`, `addrSlotsInB`: `isSome`/`isNone`;
`progScopeB_isSome`). A placement `S.withSizes sz` with one size per function keeps the program
and the names of the link map (the placed functions' names, then the outside part's), so every
such placement has the same input conditions (`inScopePar_withSizes`,
`inScopeInPar_withSizes`).

`lean-link` decides them once on a placement with zero sizes before trying the Stock routes
(each `attempt` places the program with its lowering, the whole pipeline, and then fails on the
same conditions; ruint: 19 placements of 232,604 functions on the link that leaves out the
functions failing them). No statement changes.
-/

namespace E2E.LinkCheck

section
variable {S T : String → Option Nat}

theorem mayB_isSome (h : ∀ n, (S n).isSome = (T n).isSome) (g : Clif.Function) (n : String) :
    mayB S g n = mayB T g n := by
  simp only [mayB, h]

theorem indToB_isSome (h : ∀ n, (S n).isSome = (T n).isSome) (g k : Clif.Function) :
    indToB S g k = indToB T g k := by
  simp only [indToB, mayB_isSome h]

theorem indB_isSome (h : ∀ n, (S n).isSome = (T n).isSome) (P : Clif.Program)
    (g : Clif.Function) : indB P S g = indB P T g := by
  simp only [indB, mayB_isSome h]

theorem indSiteB_isSome (h : ∀ n, (S n).isSome = (T n).isSome) (P : Clif.Program)
    (g : Clif.Function) (s : Clif.Signature) (args : List Nat) :
    indSiteB P S g s args = indSiteB P T g s args := by
  simp only [indSiteB, indToB_isSome h]

theorem callScopeB_isSome (h : ∀ n, (S n).isSome = (T n).isSome) (P : Clif.Program)
    (g : Clif.Function) : callScopeB P S g = callScopeB P T g := by
  simp only [callScopeB, indSiteB_isSome h]

theorem addrSlotsInB_isSome (h : ∀ n, (S n).isSome = (T n).isSome) (P : Clif.Program) :
    addrSlotsInB P S = addrSlotsInB P T := by
  have h' : ∀ n, (S n).isNone = (T n).isNone := by
    intro n
    have := h n
    cases hs : S n <;> cases ht : T n <;> simp_all
  simp only [addrSlotsInB, h']

theorem addrSlotsInputB_isSome (h : ∀ n, (S n).isSome = (T n).isSome) (P : Clif.Program) :
    addrSlotsInputB P S = addrSlotsInputB P T := by
  have h' : ∀ n, (S n).isNone = (T n).isNone := by
    intro n
    have := h n
    cases hs : S n <;> cases ht : T n <;> simp_all
  simp only [addrSlotsInputB, h']

/-- **The program-level input conditions read only which names have a symbol.** -/
theorem progScopeB_isSome (h : ∀ n, (S n).isSome = (T n).isSome) (P : Clif.Program) :
    progScopeB P S = progScopeB P T := by
  simp only [progScopeB, indB_isSome h, callScopeB_isSome h, addrSlotsInB_isSome h]

theorem progScopeInB_isSome (h : ∀ n, (S n).isSome = (T n).isSome) (P : Clif.Program) :
    progScopeInB P S = progScopeInB P T := by
  simp only [progScopeInB, indB_isSome h, callScopeB_isSome h, addrSlotsInputB_isSome h]

end

end E2E.LinkCheck

namespace Link

open E2E E2E.LinkCheck

theorem lookup_isSome_keys (l : List (String × Nat)) (n : String) :
    (l.lookup n).isSome = decide (n ∈ l.map (·.1)) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : n = k
    · subst hk
      simp
    · have hk' : (n == k) = false := by simpa using hk
      simp [List.lookup_cons, hk', hk, ih]

theorem filterMap_keys (l : List String) (f : String → Option Nat) :
    (l.filterMap fun n => (f n).map (n, ·)).map (·.1) = l.filter fun n => (f n).isSome := by
  induction l with
  | nil => rfl
  | cons n l ih =>
    cases hf : f n <;> simp [List.filterMap_cons, List.filter_cons, hf, ih]

/-- The names of the link map of a placement with one size per function. -/
theorem withSizes_addrs_keys (S : LinkSpec) (sz : List Nat) (hs : sz.length = S.funcs.length) :
    (S.withSizes sz).addrs.map (·.1) = S.funcs.map (·.func.name) ++ S.outside.map (·.1) := by
  simp only [LinkSpec.addrs, LinkSpec.progAddrs, LinkSpec.withSizes, List.map_append]
  congr 1
  rw [List.map_fst_zip]
  simp [offsA_length, hs]

/-- **Every placement with one size per function has the same input conditions.** -/
theorem input0_syms_isSome (S : LinkSpec) (a b : List Nat) (ha : a.length = S.funcs.length)
    (hb : b.length = S.funcs.length) (n : String) :
    ((S.withSizes a).input0.syms.lookup n).isSome =
      ((S.withSizes b).input0.syms.lookup n).isSome := by
  have hk : ∀ m, ((S.withSizes a).addrs.lookup m).isSome = ((S.withSizes b).addrs.lookup m).isSome := by
    intro m
    rw [lookup_isSome_keys, lookup_isSome_keys, withSizes_addrs_keys S a ha,
      withSizes_addrs_keys S b hb]
  simp only [LinkSpec.input0, lookup_isSome_keys, filterMap_keys, hk]
  rfl

theorem inScopePar_withSizes (S : LinkSpec) (a b : List Nat) (ha : a.length = S.funcs.length)
    (hb : b.length = S.funcs.length) :
    inScopePar (S.withSizes a).input0 = inScopePar (S.withSizes b).input0 := by
  rw [inScopePar_eq, inScopePar_eq]
  unfold InScopeP
  rw [progScopeB_isSome (fun n => input0_syms_isSome S a b ha hb n)]
  rfl

theorem inScopeInPar_withSizes (S : LinkSpec) (a b : List Nat) (ha : a.length = S.funcs.length)
    (hb : b.length = S.funcs.length) :
    inScopeInPar (S.withSizes a).input0 = inScopeInPar (S.withSizes b).input0 := by
  rw [inScopeInPar_eq, inScopeInPar_eq]
  unfold InScopeIn
  rw [progScopeInB_isSome (fun n => input0_syms_isSome S a b ha hb n)]
  rfl

end Link
