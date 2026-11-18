import FV.E2E.CodeMap
import FV.E2E.LinkIdx

/-! # The code map check in linear time (#1108)

`codeMapB` (`FV/E2E/CodeMap.lean`) compares every pair of functions of the table
(`T.all fun e => T.all fun e' => …`), looks each function's link-map address up in the link map
(`List.lookup`) and, where that is not its load address, scans the table for the functions
declaring it (`noBlrB`): quadratic, about 5·10¹⁰ pairs on ruint's 232,604 functions (#1108).

`codeMapFastB` decides the same (`codeMapFastB_eq`, `@[csimp] codeMapB_eq_fast`):
* the link-map addresses through a hash map of the link map (`assocMap_get`);
* `noBlrB`, only where an address is not the load address, through the table grouped by the
  names the functions declare (`groupMulti`, `noBlrFastB_eq`) and a hash map of the CLIF image's
  symbols;
* the pairs: when every function's code ends at or before the next function's base in the
  table's order (`rangesChainB`; a placement lays them out so), any two entries of the table are
  one entry or have disjoint code ranges (`rangesChainB_pairs`), so the scan over pairs holds;
  otherwise the scan over pairs as before.

No statement changes.
-/

namespace E2E.LinkCheck

open Backend

/-- The names a function of the table declares (`groupMulti`'s keys for `noBlrFastB`). -/
def declKeys (e : Clif.Function × Art) : List String := e.1.externs.map (·.2.name)

/-- `noBlrB` with the CLIF image's symbols in `Sm` and the table's functions declaring `n` in
`G` (`noBlrFastB_eq`). -/
def noBlrFastB (Sm : Std.HashMap String Nat)
    (G : Std.HashMap String (List (Clif.Function × Art))) (n : String) : Bool :=
  (Sm[n]?).isNone && (G.getD n []).all fun e =>
    !(e.1.externs.any fun x => x.2.name == n) || blrGotB e.2.vcp n

theorem noBlrFastB_eq (I : LinkInput) (T : List (Clif.Function × Art)) (n : String) :
    noBlrFastB (assocMap I.syms) (groupMulti declKeys T) n = noBlrB I T n := by
  unfold noBlrFastB noBlrB
  rw [assocMap_get]
  congr 1
  symm
  apply all_sub_eq
  · intro x hx hp
    rw [mem_groupMulti]
    refine ⟨hx, ?_⟩
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.any_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨y, hy, hn⟩, -⟩ := hp
    simp only [declKeys, List.mem_map]
    exact ⟨y, hy, hn⟩
  · intro x hx
    exact ((mem_groupMulti _ _ _ _).1 hx).1

/-- Every function's code ends at or before the next function's base, in the table's order. -/
def rangesChainB : List (Clif.Function × Art) → Bool
  | e :: e' :: T => decide (e.2.base.toNat + 4 * e.2.fb.words.size ≤ e'.2.base.toNat) &&
      rangesChainB (e' :: T)
  | _ => true

theorem rangesChainB_head : ∀ (e : Clif.Function × Art) (T : List (Clif.Function × Art)),
    rangesChainB (e :: T) = true →
      ∀ e' ∈ T, e.2.base.toNat + 4 * e.2.fb.words.size ≤ e'.2.base.toNat
  | _, [], _, _, he' => by simp at he'
  | e, x :: T, h, e', he' => by
    simp only [rangesChainB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.1 he' with rfl | hm
    · exact h1
    · have := rangesChainB_head x T h2 e' hm
      omega

theorem rangesChainB_tail (e : Clif.Function × Art) (T : List (Clif.Function × Art))
    (h : rangesChainB (e :: T) = true) : rangesChainB T = true := by
  cases T with
  | nil => rfl
  | cons y T =>
    simp only [rangesChainB, Bool.and_eq_true] at h
    exact h.2

/-- **Consecutive ranges are pairwise disjoint**: two entries of a table whose code ranges follow
each other are one entry or have disjoint code ranges. -/
theorem rangesChainB_pairs : ∀ (T : List (Clif.Function × Art)), rangesChainB T = true →
    ∀ e ∈ T, ∀ e' ∈ T, e = e' ∨ e.2.base.toNat + 4 * e.2.fb.words.size ≤ e'.2.base.toNat ∨
      e'.2.base.toNat + 4 * e'.2.fb.words.size ≤ e.2.base.toNat
  | [], _, _, he, _, _ => by simp at he
  | x :: T, h, e, he, e', he' => by
    have hx := rangesChainB_head x T h
    have hT := rangesChainB_tail x T h
    rcases List.mem_cons.1 he with rfl | hm <;> rcases List.mem_cons.1 he' with rfl | hm'
    · exact .inl rfl
    · exact .inr (.inl (hx _ hm'))
    · exact .inr (.inr (hx _ hm))
    · exact rangesChainB_pairs T hT e hm e' hm'

/-- `codeMapB`'s scan over pairs (its second conjunct, for every function). -/
def codePairsB (T : List (Clif.Function × Art)) : Bool :=
  T.all fun e => T.all fun e' => e.1.name == e'.1.name ||
    decide (e.2.base.toNat + 4 * e.2.fb.words.size ≤ e'.2.base.toNat ∨
      e'.2.base.toNat + 4 * e'.2.fb.words.size ≤ e.2.base.toNat) ||
    (e.2.base == e'.2.base && linesAlikeB (progT T) e.2.fa.lines.toList e'.2.fa.lines.toList)

theorem chain_codePairsB (T : List (Clif.Function × Art)) :
    (rangesChainB T || codePairsB T) = codePairsB T := by
  cases h : rangesChainB T
  · rfl
  · rw [Bool.true_or, eq_comm]
    unfold codePairsB
    rw [List.all_eq_true]
    intro e he
    rw [List.all_eq_true]
    intro e' he'
    rcases rangesChainB_pairs T h e he e' he' with rfl | hd | hd
    · simp
    · simp [hd]
    · simp [hd]

/-- `codeMapB`'s first conjunct for `e`, its link-map address through the hash map `A`. -/
def addrIsBaseB (A : Std.HashMap String Nat) (e : Clif.Function × Art) : Bool :=
  BitVec.ofNat 64 ((A[e.1.name]?).getD 0) + BitVec.ofInt 64 0 == e.2.base

theorem all_or_all {α : Type} (l : List α) (p q : α → Bool) :
    (l.all p || l.all fun x => p x || q x) = l.all fun x => p x || q x := by
  cases h : l.all p
  · rfl
  · rw [Bool.true_or, eq_comm, List.all_eq_true]
    rw [List.all_eq_true] at h
    intro x hx
    simp [h x hx]

theorem all_and_eq {α : Type} (l : List α) (p q : α → Bool) :
    (l.all fun x => p x && q x) = (l.all p && l.all q) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.all_cons, ih]
    cases p x <;> cases q x <;> simp

/-- **`codeMapB` in linear time** on a table whose code ranges follow each other and whose
link-map addresses are the load addresses (`codeMapFastB_eq`). -/
def codeMapFastB (I : LinkInput) (T : List (Clif.Function × Art)) : Bool :=
  let A := assocMap I.addrs
  (T.all (addrIsBaseB A) ||
    (let Sm := assocMap I.syms
     let G := groupMulti declKeys T
     T.all fun e => addrIsBaseB A e || noBlrFastB Sm G e.1.name)) &&
  (rangesChainB T || codePairsB T)

theorem codeMapFastB_eq (I : LinkInput) (T : List (Clif.Function × Art)) :
    codeMapFastB I T = codeMapB I T := by
  have hA : ∀ e : Clif.Function × Art,
      addrIsBaseB (assocMap I.addrs) e = (I.symAddr e.1.name 0 == e.2.base) := by
    intro e
    simp only [addrIsBaseB, LinkInput.symAddr, LinkInput.addrOf, assocMap_get]
  have hA' : addrIsBaseB (assocMap I.addrs) = fun e : Clif.Function × Art =>
      (I.symAddr e.1.name 0 == e.2.base) := funext hA
  unfold codeMapFastB
  dsimp only
  rw [all_or_all, chain_codePairsB, codeMapB, all_and_eq, codePairsB]
  simp only [hA, hA', noBlrFastB_eq]

@[csimp] theorem codeMapB_eq_fast : @codeMapB = @codeMapFastB := by
  funext I T
  exact (codeMapFastB_eq I T).symm

end E2E.LinkCheck
