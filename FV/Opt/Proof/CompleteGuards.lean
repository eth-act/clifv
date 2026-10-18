import FV.Opt.Proof.CompleteRecheck
import FV.Opt.OptimizeX

/-!
# The final guards of the mid-end (M1)

`Opt.optimizeReport` returns its input unless `keepsBackendSubset f0 g` holds of the pipeline's
output `g`, and `Opt.optimizeExe` returns its input unless `keepsShapeB f0 g` holds. This module
gives the stage-by-stage facts showing when these guards accept.

* `Opt.KeepsB f g`: the transitive relation behind `keepsBackendSubset` (same header, subset E
  kept, no new callee, no new indirect call); `Opt.keepsBackendSubset_of_keepsB`.
* `Opt.ShapeK f g`: the transitive relation behind `keepsShapeB` (no new `try_call` callee or
  indirect-call signature; a `return_call` / indirect call of the entry block is kept; blocks are
  kept nonempty); `Opt.keepsShapeB_of_shapeK` under the input condition `Opt.shapeSafeB f0`
  (every `return_call`, and every indirect call, if any, has one in the entry block: those are the
  only ones no branch folding can make unreachable).
* `Opt.Derived N f g` / `Opt.HeadKeep f g`: `g` is made of `f`'s statements and terminators
  (renamed, deleted, moved; branches rewritten into branches) plus new statements satisfying `N`;
  the entry block keeps its terminator kind and its indirect calls. Every stage establishes them:
  `removeUnreachable`, DCE, GVN, LICM (under the facts of its invariant) and simplify (under the
  facts of `Opt.SimpGuard`).

`keepsShapeB` can genuinely reject: `Opt.CompleteGuardsWitness` folds the branch to the only
block with a `return_call`.
-/

namespace Opt

open Clif

/-! ## Instruction and terminator classes -/

def isCallInd : Inst → Bool
  | .callIndirect .. => true
  | _ => false

def callee? : Inst → Option FnRef
  | .call fn _ => some fn
  | _ => none

def indSig? : Inst → Option Nat
  | .callIndirect sig _ _ => some sig
  | _ => none

def tryCallee? : Terminator → Option FnRef
  | .tryCall fn _ _ => some fn
  | _ => none

def tryIndSig? : Terminator → Option Nat
  | .tryCallIndirect _ _ et => some et.sig
  | _ => none

def retCallT : Terminator → Bool
  | .returnCall .. => true
  | _ => false

theorem instE_mapOperands (σ : ValueId → ValueId) (i : Inst) :
    Compile.instE (mapOperands σ i) = Compile.instE i := by cases i <;> rfl

theorem isPure_mapOperands' (σ : ValueId → ValueId) (i : Inst) :
    isPure (mapOperands σ i) = isPure i := by cases i <;> rfl

theorem isCallInd_mapOperands (σ : ValueId → ValueId) (i : Inst) :
    isCallInd (mapOperands σ i) = isCallInd i := by cases i <;> rfl

theorem notCall_mapOperands (σ : ValueId → ValueId) (i : Inst) :
    notCall (mapOperands σ i) = notCall i := by cases i <;> rfl

theorem callee?_mapOperands (σ : ValueId → ValueId) (i : Inst) :
    callee? (mapOperands σ i) = callee? i := by cases i <;> rfl

theorem indSig?_mapOperands (σ : ValueId → ValueId) (i : Inst) :
    indSig? (mapOperands σ i) = indSig? i := by cases i <;> rfl

theorem termE_mapTerm (σ : ValueId → ValueId) (t : Terminator) :
    Compile.termE (mapTerm σ t) = Compile.termE t := by cases t <;> rfl

theorem isTry_mapTerm (σ : ValueId → ValueId) (t : Terminator) :
    (mapTerm σ t).isTry = t.isTry := by cases t <;> rfl

theorem tryCallee?_mapTerm (σ : ValueId → ValueId) (t : Terminator) :
    tryCallee? (mapTerm σ t) = tryCallee? t := by cases t <;> rfl

theorem tryIndSig?_mapTerm (σ : ValueId → ValueId) (t : Terminator) :
    tryIndSig? (mapTerm σ t) = tryIndSig? t := by cases t <;> rfl

theorem retCallT_mapTerm (σ : ValueId → ValueId) (t : Terminator) :
    retCallT (mapTerm σ t) = retCallT t := by cases t <;> rfl

theorem callee?_of_notCall {i : Inst} (h : notCall i = true) : callee? i = none := by
  cases i <;> first | rfl | cases h

theorem indSig?_of_isCallInd {i : Inst} (h : isCallInd i = false) : indSig? i = none := by
  cases i <;> first | rfl | cases h

theorem isCallInd_of_isPure {i : Inst} (h : isPure i = true) : isCallInd i = false := by
  cases i <;> first | rfl | cases h

theorem termE_of_isBranch {t : Terminator} (h : isBranch t = true) : Compile.termE t = true := by
  cases t <;> first | rfl | cases h

theorem isTry_of_isBranch {t : Terminator} (h : isBranch t = true) : t.isTry = false := by
  cases t <;> first | rfl | cases h

theorem tryCallee?_of_isBranch {t : Terminator} (h : isBranch t = true) : tryCallee? t = none := by
  cases t <;> first | rfl | cases h

theorem tryIndSig?_of_isBranch {t : Terminator} (h : isBranch t = true) : tryIndSig? t = none := by
  cases t <;> first | rfl | cases h

theorem retCallT_of_isBranch {t : Terminator} (h : isBranch t = true) : retCallT t = false := by
  cases t <;> first | rfl | cases h

/-- What `allowedIn` guarantees about subset E. -/
theorem allowedIn_instE {f : Function} {n : Inst} (h : allowedIn f n = true)
    (hE : Compile.functionE f = true) : Compile.instE n = true := by
  simp only [allowedIn, hE, ite_true, Bool.and_eq_true] at h
  exact h.2

theorem skelAllowedIn_instE {f : Function} {n : Inst} (h : skelAllowedIn f n = true)
    (hE : Compile.functionE f = true) : Compile.instE n = true := by
  simpa only [skelAllowedIn, hE, ite_true] using h

/-! ## The guard functions, restated -/

theorem mem_callees {g : Function} {fn : FnRef} :
    fn ∈ callees g ↔ ∃ b ∈ g.blocks, ∃ s ∈ b.body, callee? s.inst = some fn := by
  simp only [callees, List.mem_flatMap, List.mem_filterMap]
  constructor <;> rintro ⟨b, hb, s, hs, h⟩ <;> refine ⟨b, hb, s, hs, ?_⟩ <;>
    revert h <;> generalize s.inst = i <;> cases i <;> exact id

theorem hasCallIndirect_iff {g : Function} :
    hasCallIndirect g = true ↔
      ∃ b ∈ g.blocks, (∃ s ∈ b.body, isCallInd s.inst = true) ∨ b.term.isTry = true := by
  simp only [hasCallIndirect, List.any_eq_true, Bool.or_eq_true]
  constructor <;> rintro ⟨b, hb, ⟨s, hs, h⟩ | h⟩
  all_goals first
    | exact ⟨b, hb, .inr h⟩
    | (refine ⟨b, hb, .inl ⟨s, hs, ?_⟩⟩; revert h; generalize s.inst = i; cases i <;> exact id)

theorem mem_tryCallees {g : Function} {fn : FnRef} :
    fn ∈ tryCallees g ↔ ∃ b ∈ g.blocks, tryCallee? b.term = some fn := by
  simp only [tryCallees, List.mem_filterMap]
  constructor <;> rintro ⟨b, hb, h⟩ <;> refine ⟨b, hb, ?_⟩ <;> revert h <;>
    generalize b.term = t <;> cases t <;> exact id

theorem mem_indSigIds {g : Function} {x : Nat} :
    x ∈ indSigIds g ↔ ∃ b ∈ g.blocks,
      (∃ s ∈ b.body, indSig? s.inst = some x) ∨ tryIndSig? b.term = some x := by
  simp only [indSigIds, List.mem_flatMap, List.mem_append, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, ⟨s, hs, h⟩ | h⟩
    · refine ⟨b, hb, .inl ⟨s, hs, ?_⟩⟩
      revert h; generalize s.inst = i; cases i <;> exact id
    · refine ⟨b, hb, .inr ?_⟩
      revert h; generalize b.term = t; cases t <;> simp [tryIndSig?, eq_comm]
  · rintro ⟨b, hb, ⟨s, hs, h⟩ | h⟩
    · refine ⟨b, hb, .inl ⟨s, hs, ?_⟩⟩
      revert h; generalize s.inst = i; cases i <;> exact id
    · refine ⟨b, hb, .inr ?_⟩
      revert h; generalize b.term = t; cases t <;> simp [tryIndSig?, eq_comm]

theorem retCallFreeB_eq_false {g : Function} {b : Block} (hb : b ∈ g.blocks)
    (h : retCallT b.term = true) : retCallFreeB g = false := by
  cases hr : retCallFreeB g with
  | false => rfl
  | true =>
    simp only [retCallFreeB, List.all_eq_true] at hr
    have := hr b hb
    revert h this; generalize b.term = t; cases t <;> simp [retCallT]

/-- The entry block's terminator is a `return_call`. -/
def entryRetCallB (f : Function) : Bool := f.blocks.head?.any fun b => retCallT b.term

/-- The entry block has an indirect call (`call_indirect`, `try_call_indirect`). -/
def entryIndCallB (f : Function) : Bool :=
  f.blocks.head?.any fun b => b.body.any (fun s => isCallInd s.inst) || (tryIndSig? b.term).isSome

/-- **The input condition of the shape guard**: if `f` has a `return_call`, its entry block ends
with one, and if it has an indirect call, its entry block has one (the entry block is the only
block no branch folding can make unreachable). -/
def shapeSafeB (f : Function) : Bool :=
  (retCallFreeB f || entryRetCallB f) && (indCallFreeB f || entryIndCallB f)

theorem indCallFreeB_eq_false {g : Function} {b : Block} (hb : b ∈ g.blocks)
    (h : (b.body.any (fun s => isCallInd s.inst) || (tryIndSig? b.term).isSome) = true) :
    indCallFreeB g = false := by
  cases hr : indCallFreeB g with
  | false => rfl
  | true =>
    simp only [indCallFreeB, List.all_eq_true, Bool.and_eq_true] at hr
    obtain ⟨h1, h2⟩ := hr b hb
    simp only [Bool.or_eq_true, List.any_eq_true] at h
    rcases h with ⟨s, hs, hi⟩ | ht
    · have := h1 s hs
      revert hi this; generalize s.inst = i; cases i <;> simp [isCallInd]
    · revert ht h2; generalize b.term = t; cases t <;> simp [tryIndSig?]

/-! ## `KeepsB`: the backend-subset guard -/

/-- The header of a function (`sameHeader`) is unchanged. -/
structure SameHdr (f g : Function) : Prop where
  name : g.name = f.name
  sig : g.sig = f.sig
  slots : g.slots = f.slots
  globals : g.globals = f.globals
  externs : g.externs = f.externs

theorem SameHdr.refl (f : Function) : SameHdr f f := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem SameHdr.trans {f g k : Function} (h1 : SameHdr f g) (h2 : SameHdr g k) : SameHdr f k :=
  ⟨h2.name.trans h1.name, h2.sig.trans h1.sig, h2.slots.trans h1.slots,
    h2.globals.trans h1.globals, h2.externs.trans h1.externs⟩

/-- What `keepsBackendSubset f g` checks, as a transitive relation. -/
structure KeepsB (f g : Function) : Prop where
  hdr : SameHdr f g
  subsetE : Compile.functionE f = true → Compile.functionE g = true
  callees : ∀ fn ∈ callees g, fn ∈ callees f
  ind : hasCallIndirect g = true → hasCallIndirect f = true

theorem KeepsB.refl (f : Function) : KeepsB f f :=
  ⟨SameHdr.refl f, id, fun _ h => h, id⟩

theorem KeepsB.trans {f g k : Function} (h1 : KeepsB f g) (h2 : KeepsB g k) : KeepsB f k :=
  ⟨h1.hdr.trans h2.hdr, fun h => h2.subsetE (h1.subsetE h), fun fn h => h1.callees fn (h2.callees fn h),
    fun h => h1.ind (h2.ind h)⟩

/-- **The backend-subset guard accepts** a function related by `KeepsB`. -/
theorem keepsBackendSubset_of_keepsB {f g : Function} (h : KeepsB f g) :
    keepsBackendSubset f g = true := by
  simp only [keepsBackendSubset, sameHeader, h.hdr.name, h.hdr.sig, h.hdr.slots, h.hdr.globals,
    h.hdr.externs, beq_self_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.all_eq_true, List.contains_iff_mem, true_and]
  refine ⟨⟨?_, fun fn hfn => h.callees fn hfn⟩, ?_⟩
  · cases hf : Compile.functionE f
    · exact .inl rfl
    · exact .inr (h.subsetE hf)
  · cases hg : hasCallIndirect g
    · exact .inl rfl
    · exact .inr (h.ind hg)

/-! ## Derived functions -/

/-- `g` is made of `f`'s blocks (parameters kept; terminators renamed, or branches rewritten into
branches) and statements (renamed, deleted, moved), plus new statements satisfying `N`. -/
structure Derived (N : Inst → Prop) (f g : Function) : Prop where
  hdr : SameHdr f g
  blk : ∀ b' ∈ g.blocks, ∃ b ∈ f.blocks, b'.params = b.params ∧
    ((∃ σ, b'.term = mapTerm σ b.term) ∨ (isBranch b.term = true ∧ isBranch b'.term = true))
  st : ∀ b' ∈ g.blocks, ∀ s ∈ b'.body,
    (∃ b ∈ f.blocks, ∃ s0 ∈ b.body, ∃ σ, s.inst = mapOperands σ s0.inst) ∨ N s.inst

/-- The entry block keeps its terminator (unless it is a rewritten branch) and its indirect
calls. -/
structure HeadKeep (f g : Function) : Prop where
  head : ∀ b, f.blocks.head? = some b → ∃ b', g.blocks.head? = some b' ∧
    ((∃ σ, b'.term = mapTerm σ b.term) ∨ isBranch b.term = true) ∧
    ∀ s0 ∈ b.body, isCallInd s0.inst = true → ∃ s ∈ b'.body, ∃ σ, s.inst = mapOperands σ s0.inst

/-- **A derived function keeps `KeepsB`**, when the new statements are in subset E (if the
original input is), and are not calls. -/
theorem Derived.keepsB {N : Inst → Prop} {f0 f g : Function} (h : KeepsB f0 f) (hd : Derived N f g)
    (hN : ∀ i, N i → (Compile.functionE f0 = true → Compile.instE i = true) ∧ notCall i = true ∧
      isCallInd i = false) : KeepsB f0 g where
  hdr := h.hdr.trans hd.hdr
  subsetE hE := by
    have hf := h.subsetE hE
    simp only [Compile.functionE, Bool.and_eq_true, List.all_eq_true] at hf ⊢
    obtain ⟨⟨⟨hs, hg⟩, hx⟩, hb⟩ := hf
    refine ⟨⟨⟨by rw [hd.hdr.sig]; exact hs, by rw [hd.hdr.globals]; exact hg⟩,
      by rw [hd.hdr.externs]; exact hx⟩, fun b' hb' => ?_⟩
    obtain ⟨b, hbf, hp, ht⟩ := hd.blk b' hb'
    obtain ⟨⟨hbp, hbb⟩, hbt⟩ := hb b hbf
    refine ⟨⟨by rw [hp]; exact hbp, fun s hs => ?_⟩, ?_⟩
    · rcases hd.st b' hb' s hs with ⟨b0, hb0, s0, hs0, σ, he⟩ | hn
      · rw [he, instE_mapOperands]; exact (hb b0 hb0).1.2 s0 hs0
      · exact (hN _ hn).1 hE
    · rcases ht with ⟨σ, he⟩ | ⟨-, hbr⟩
      · rw [he, termE_mapTerm]; exact hbt
      · exact termE_of_isBranch hbr
  callees fn hfn := by
    obtain ⟨b', hb', s, hs, hc⟩ := mem_callees.1 hfn
    rcases hd.st b' hb' s hs with ⟨b0, hb0, s0, hs0, σ, he⟩ | hn
    · rw [he, callee?_mapOperands] at hc
      exact h.callees fn (mem_callees.2 ⟨b0, hb0, s0, hs0, hc⟩)
    · rw [callee?_of_notCall (hN _ hn).2.1] at hc; cases hc
  ind hi := by
    apply h.ind
    obtain ⟨b', hb', ⟨s, hs, hc⟩ | ht⟩ := hasCallIndirect_iff.1 hi
    · rcases hd.st b' hb' s hs with ⟨b0, hb0, s0, hs0, σ, he⟩ | hn
      · rw [he, isCallInd_mapOperands] at hc
        exact hasCallIndirect_iff.2 ⟨b0, hb0, .inl ⟨s0, hs0, hc⟩⟩
      · rw [(hN _ hn).2.2] at hc; cases hc
    · obtain ⟨b, hbf, -, hbt⟩ := hd.blk b' hb'
      rcases hbt with ⟨σ, he⟩ | ⟨-, hbr⟩
      · rw [he, isTry_mapTerm] at ht
        exact hasCallIndirect_iff.2 ⟨b, hbf, .inr ht⟩
      · rw [isTry_of_isBranch hbr] at ht; cases ht

/-! ## `ShapeK`: the shape guard -/

/-- What `keepsShapeB f g` needs, as a transitive relation (module doc). -/
structure ShapeK (f g : Function) : Prop where
  tryC : ∀ fn ∈ tryCallees g, fn ∈ tryCallees f
  indS : ∀ x ∈ indSigIds g, x ∈ indSigIds f
  ret : entryRetCallB f = true → entryRetCallB g = true
  indE : entryIndCallB f = true → entryIndCallB g = true
  ne : f.blocks = [] → g.blocks = []

theorem ShapeK.refl (f : Function) : ShapeK f f :=
  ⟨fun _ h => h, fun _ h => h, id, id, id⟩

theorem ShapeK.trans {f g k : Function} (h1 : ShapeK f g) (h2 : ShapeK g k) : ShapeK f k :=
  ⟨fun fn h => h1.tryC fn (h2.tryC fn h), fun x h => h1.indS x (h2.indS x h),
    fun h => h2.ret (h1.ret h), fun h => h2.indE (h1.indE h), fun h => h2.ne (h1.ne h)⟩

theorem head_mem {l : List Block} {b : Block} (h : l.head? = some b) : b ∈ l := by
  cases l with
  | nil => cases h
  | cons a l => simp only [List.head?_cons, Option.some.injEq] at h; subst h; exact List.mem_cons_self ..

/-- **The shape guard accepts** a function related by `ShapeK` to an input with `shapeSafeB`. -/
theorem keepsShapeB_of_shapeK {f g : Function} (hs : shapeSafeB f = true) (h : ShapeK f g) :
    keepsShapeB f g = true := by
  simp only [shapeSafeB, Bool.and_eq_true, Bool.or_eq_true] at hs
  obtain ⟨hr, hi⟩ := hs
  simp only [keepsShapeB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.contains_iff_mem, List.isEmpty_eq_false_iff, List.isEmpty_iff]
  refine ⟨⟨⟨⟨fun fn hfn => h.tryC fn hfn, fun x hx => h.indS x hx⟩, ?_⟩, ?_⟩, ?_⟩
  · rcases hr with hr | hr
    · exact .inl hr
    · right
      have hg := h.ret hr
      simp only [entryRetCallB, Option.any_eq_true] at hg
      obtain ⟨b, hb, ht⟩ := hg
      exact retCallFreeB_eq_false (head_mem hb) ht
  · rcases hi with hi | hi
    · exact .inl hi
    · right
      have hg := h.indE hi
      simp only [entryIndCallB, Option.any_eq_true] at hg
      obtain ⟨b, hb, ht⟩ := hg
      exact indCallFreeB_eq_false (head_mem hb) ht
  · by_cases hf : f.blocks = []
    · exact .inr (h.ne hf)
    · exact .inl hf

/-- **A derived function keeps `ShapeK`**, when the new statements are not indirect calls. -/
theorem Derived.shapeK {N : Inst → Prop} {f g : Function} (hd : Derived N f g) (hh : HeadKeep f g)
    (hN : ∀ i, N i → isCallInd i = false) : ShapeK f g where
  tryC fn hfn := by
    obtain ⟨b', hb', ht⟩ := mem_tryCallees.1 hfn
    obtain ⟨b, hbf, -, hbt⟩ := hd.blk b' hb'
    rcases hbt with ⟨σ, he⟩ | ⟨-, hbr⟩
    · rw [he, tryCallee?_mapTerm] at ht
      exact mem_tryCallees.2 ⟨b, hbf, ht⟩
    · rw [tryCallee?_of_isBranch hbr] at ht; cases ht
  indS x hx := by
    obtain ⟨b', hb', ⟨s, hs, hc⟩ | ht⟩ := mem_indSigIds.1 hx
    · rcases hd.st b' hb' s hs with ⟨b0, hb0, s0, hs0, σ, he⟩ | hn
      · rw [he, indSig?_mapOperands] at hc
        exact mem_indSigIds.2 ⟨b0, hb0, .inl ⟨s0, hs0, hc⟩⟩
      · rw [indSig?_of_isCallInd (hN _ hn)] at hc; cases hc
    · obtain ⟨b, hbf, -, hbt⟩ := hd.blk b' hb'
      rcases hbt with ⟨σ, he⟩ | ⟨-, hbr⟩
      · rw [he, tryIndSig?_mapTerm] at ht
        exact mem_indSigIds.2 ⟨b, hbf, .inr ht⟩
      · rw [tryIndSig?_of_isBranch hbr] at ht; cases ht
  ret hr := by
    simp only [entryRetCallB, Option.any_eq_true] at hr ⊢
    obtain ⟨b, hb, ht⟩ := hr
    obtain ⟨b', hb', hbt, -⟩ := hh.head b hb
    refine ⟨b', hb', ?_⟩
    rcases hbt with ⟨σ, he⟩ | hbr
    · rw [he, retCallT_mapTerm]; exact ht
    · rw [retCallT_of_isBranch hbr] at ht; cases ht
  indE hi := by
    simp only [entryIndCallB, Option.any_eq_true] at hi ⊢
    obtain ⟨b, hb, ht⟩ := hi
    obtain ⟨b', hb', hbt, hcall⟩ := hh.head b hb
    refine ⟨b', hb', ?_⟩
    simp only [Bool.or_eq_true, List.any_eq_true] at ht ⊢
    rcases ht with ⟨s0, hs0, hc⟩ | ht
    · obtain ⟨s, hs, σ, he⟩ := hcall s0 hs0 hc
      exact .inl ⟨s, hs, by rw [he, isCallInd_mapOperands]; exact hc⟩
    · rcases hbt with ⟨σ, he⟩ | hbr
      · exact .inr (by rw [he, tryIndSig?_mapTerm]; exact ht)
      · rw [tryIndSig?_of_isBranch hbr] at ht; cases ht
  ne hf := by
    cases hg : g.blocks with
    | nil => rfl
    | cons b' l =>
      obtain ⟨b, hb, -⟩ := hd.blk b' (by rw [hg]; exact List.mem_cons_self ..)
      rw [hf] at hb; cases hb

/-! ## The stages -/

theorem Derived.refl (N : Inst → Prop) (f : Function) : Derived N f f where
  hdr := SameHdr.refl f
  blk b hb := ⟨b, hb, rfl, .inl ⟨id, (mapTerm_id _).symm⟩⟩
  st b hb s hs := .inl ⟨b, hb, s, hs, id, (mapOperands_id _).symm⟩

theorem HeadKeep.refl (f : Function) : HeadKeep f f where
  head b hb := ⟨b, hb, .inl ⟨id, (mapTerm_id _).symm⟩, fun s hs _ =>
    ⟨s, hs, id, (mapOperands_id _).symm⟩⟩

/-- A function whose blocks are blocks of `f`. -/
theorem derived_sub (N : Inst → Prop) {f g : Function} (hh : SameHdr f g)
    (hsub : ∀ b ∈ g.blocks, b ∈ f.blocks) : Derived N f g where
  hdr := hh
  blk b hb := ⟨b, hsub b hb, rfl, .inl ⟨id, (mapTerm_id _).symm⟩⟩
  st b hb s hs := .inl ⟨b, hsub b hb, s, hs, id, (mapOperands_id _).symm⟩

theorem headKeep_of_head {f g : Function} (hh : g.blocks.head? = f.blocks.head?) : HeadKeep f g where
  head b hb := ⟨b, hh.trans hb, .inl ⟨id, (mapTerm_id _).symm⟩, fun s hs _ =>
    ⟨s, hs, id, (mapOperands_id _).symm⟩⟩

/-- A function whose blocks are mapped by `F` (bodies: renamed statements of the block). -/
theorem derived_map (N : Inst → Prop) (f : Function) (F : Block → Block)
    (hF : ∀ b ∈ f.blocks, (F b).params = b.params ∧ ∃ σ, (F b).term = mapTerm σ b.term)
    (hbody : ∀ b ∈ f.blocks, ∀ s ∈ (F b).body, ∃ s0 ∈ b.body, ∃ σ, s.inst = mapOperands σ s0.inst) :
    Derived N f { f with blocks := f.blocks.map F } where
  hdr := ⟨rfl, rfl, rfl, rfl, rfl⟩
  blk b' hb' := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hb'
    obtain ⟨hp, σ, ht⟩ := hF b hb
    exact ⟨b, hb, hp, .inl ⟨σ, ht⟩⟩
  st b' hb' s hs := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hb'
    exact .inl ⟨b, hb, hbody b hb s hs⟩

theorem headKeep_map (f : Function) (F : Block → Block)
    (hF : ∀ b, f.blocks.head? = some b → ∃ σ, (F b).term = mapTerm σ b.term)
    (hkeep : ∀ b, f.blocks.head? = some b → ∀ s0 ∈ b.body, isCallInd s0.inst = true →
      ∃ s ∈ (F b).body, ∃ σ, s.inst = mapOperands σ s0.inst) :
    HeadKeep f { f with blocks := f.blocks.map F } where
  head b hb := ⟨F b, by simp [List.head?_map, hb], .inl (hF b hb), hkeep b hb⟩

theorem raw_head (f : Function) : (removeUnreachableRaw f).blocks.head? = f.blocks.head? := by
  cases hfb : f.blocks with
  | nil => simp [removeUnreachableRaw, hfb]
  | cons b0 rest =>
    have hn : f.blocks ≠ [] := by rw [hfb]; exact List.cons_ne_nil _ _
    obtain ⟨b, h1, h2⟩ := corr_zero hn
    rw [hfb] at h2; simp only [List.getElem?_cons_zero, Option.some.injEq] at h2; subst h2
    rw [List.head?_eq_getElem?, h1]; rfl

theorem removeUnreachable_cases (f : Function) :
    removeUnreachable f = removeUnreachableRaw f ∨ removeUnreachable f = f := by
  by_cases h : unreachableOk f (removeUnreachableRaw f) = true
  · exact .inl (by simp [removeUnreachable, h])
  · exact .inr (by simp [removeUnreachable, h])

theorem sameHdr_removeUnreachable (f : Function) : SameHdr f (removeUnreachable f) := by
  rcases removeUnreachable_cases f with h | h <;> rw [h]
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact SameHdr.refl f

/-- **`removeUnreachable`** keeps a subset of the blocks and the entry block. -/
theorem derived_removeUnreachable (N : Inst → Prop) (f : Function) :
    Derived N f (removeUnreachable f) := by
  refine derived_sub N (sameHdr_removeUnreachable f) fun b hb => ?_
  rcases removeUnreachable_cases f with h | h <;> rw [h] at hb
  · exact (raw_sublist f).subset hb
  · exact hb

theorem headKeep_removeUnreachable (f : Function) : HeadKeep f (removeUnreachable f) := by
  rcases removeUnreachable_cases f with h | h <;> rw [h]
  · exact headKeep_of_head (raw_head f)
  · exact HeadKeep.refl f

/-- **DCE** filters the bodies; indirect calls are not removable. -/
theorem derived_dce (N : Inst → Prop) (g : Function) : Derived N g (dce g).1 := by
  rw [dce_eq]
  exact derived_map N g _ (fun b _ => ⟨rfl, id, (mapTerm_id _).symm⟩)
    (fun b _ s hs => ⟨s, (List.mem_filter.1 hs).1, id, (mapOperands_id _).symm⟩)

theorem headKeep_dce (g : Function) : HeadKeep g (dce g).1 := by
  rw [dce_eq]
  refine headKeep_map g _ (fun b _ => ⟨id, (mapTerm_id _).symm⟩) fun b _ s0 hs0 hc => ?_
  refine ⟨s0, List.mem_filter.2 ⟨hs0, ?_⟩, id, (mapOperands_id _).symm⟩
  have : removable s0.inst = false := by
    revert hc; generalize s0.inst = i; cases i <;> simp [isCallInd, removable, isPure]
  simp [dceKeep, this]

/-- GVN keeps the statements that are not pure. -/
theorem gvn_keep_nonpure {g : Function} {info : Info} (hc : Checked g info) {S : Subst}
    (hS : SubOk g info.cfg.idom (fun _ _ => True) S) {b : Block} (hb : b ∈ g.blocks) {s0 : Stmt}
    (hs0 : s0 ∈ b.body) (hp : isPure s0.inst = false) : keepG S s0 = true := by
  unfold keepG
  split
  · rename_i v hv
    cases hw : S[v]? with
    | none => simp [Std.HashMap.contains_eq_isSome_getElem?, hw]
    | some w =>
      exfalso
      obtain ⟨d0, j0, m, -, -, -, hpa, -, -, -, -, -, -⟩ := hS v w hw
      obtain ⟨d, hd⟩ := List.mem_iff_getElem?.1 hb
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hs0
      have := site_unique hc.unique hpa.site
        (mem_defSites.2 ⟨d, b, hd, .inr ⟨j, s0, hj, by simp [hv], rfl⟩⟩)
      simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at this
      obtain ⟨rfl, rfl⟩ := this
      obtain ⟨b', st', hb', hst', -, hi, hpure⟩ := hpa
      rw [hd] at hb'; cases hb'
      rw [hj] at hst'; cases hst'
      rw [← hi, hp] at hpure; cases hpure
  · rfl

/-- **GVN** renames and deletes statements and renames terminators. -/
theorem derived_gvn (N : Inst → Prop) {g : Function} {info : Info} (h : check g = .ok info)
    (local? : Inst → Bool) : Derived N g (gvnFull g info local?).1 := by
  have hc := checked_of_check h
  obtain ⟨-, he⟩ := gvnFull_spec hc local?
  rw [he]
  refine derived_map N g _ (fun b _ => ⟨rfl, _, rfl⟩) fun b _ s hs => ?_
  obtain ⟨s0, hs0, rfl⟩ := List.mem_map.1 hs
  exact ⟨s0, (List.mem_filter.1 hs0).1, _, rfl⟩

theorem headKeep_gvn {g : Function} {info : Info} (h : check g = .ok info) (local? : Inst → Bool) :
    HeadKeep g (gvnFull g info local?).1 := by
  have hc := checked_of_check h
  obtain ⟨hS, he⟩ := gvnFull_spec hc local?
  rw [he]
  refine headKeep_map g _ (fun b _ => ⟨_, rfl⟩) fun b hb s0 hs0 hci => ?_
  have hp : isPure s0.inst = false := by
    cases hpp : isPure s0.inst
    · rfl
    · rw [isCallInd_of_isPure hpp] at hci; cases hci
  refine ⟨renStmt _ s0, List.mem_map.2 ⟨s0, List.mem_filter.2 ⟨hs0, ?_⟩, rfl⟩, _, rfl⟩
  exact gvn_keep_nonpure hc hS (head_mem hb) hs0 hp

/-- The skeleton of a block: its body emptied. -/
def skel (b : Block) : Block := { b with body := [] }

/-- **LICM** (under the facts of its invariant): same header and skeleton, every statement of
the output a statement of the input. -/
theorem derived_licm (N : Inst → Prop) {g g' : Function} (hh : SameHdr g g')
    (hskel : g'.blocks.map skel = g.blocks.map skel)
    (hS : ∀ b' ∈ g'.blocks, ∀ s ∈ b'.body, ∃ b ∈ g.blocks, s ∈ b.body) : Derived N g g' where
  hdr := hh
  blk b' hb' := by
    have : skel b' ∈ g.blocks.map skel := hskel ▸ List.mem_map_of_mem hb'
    obtain ⟨b, hb, he⟩ := List.mem_map.1 this
    have hp := congrArg Block.params he
    have ht := congrArg Block.term he
    simp only [skel] at hp ht
    exact ⟨b, hb, hp.symm, .inl ⟨id, by rw [mapTerm_id, ht]⟩⟩
  st b' hb' s hs := by
    obtain ⟨b, hb, hsb⟩ := hS b' hb' s hs
    exact .inl ⟨b, hb, s, hsb, id, (mapOperands_id _).symm⟩

/-- LICM keeps the entry block's skeleton, and (`hK`) its statements that are not pure. -/
theorem headKeep_licm {g g' : Function} (hskel : g'.blocks.map skel = g.blocks.map skel)
    (hK : ∀ b, g.blocks.head? = some b → ∀ s ∈ b.body, isPure s.inst = false →
      ∃ b', g'.blocks.head? = some b' ∧ s ∈ b'.body) : HeadKeep g g' where
  head b hb := by
    have h1 : (g'.blocks.map skel).head? = (g.blocks.map skel).head? := by rw [hskel]
    simp only [List.head?_map, hb, Option.map_some] at h1
    obtain ⟨b', hb', he⟩ := Option.map_eq_some_iff.1 h1
    have ht := congrArg Block.term he
    simp only [skel] at ht
    refine ⟨b', hb', .inl ⟨id, by rw [mapTerm_id, ht]⟩, fun s0 hs0 hc => ?_⟩
    have hp : isPure s0.inst = false := by
      cases hpp : isPure s0.inst
      · rfl
      · rw [isCallInd_of_isPure hpp] at hc; cases hc
    obtain ⟨b'', hb'', hs⟩ := hK b hb s0 hs0 hp
    rw [hb'] at hb''; cases hb''
    exact ⟨s0, hs, id, (mapOperands_id _).symm⟩

/-- A statement the simplifier creates: a node allowed by `allowedIn f` / `skelAllowedIn f` (not
a call or indirect call), with renamed operands. -/
def NewSimp (f : Function) (i : Inst) : Prop :=
  ∃ n σ, (allowedIn f n = true ∨ skelAllowedIn f n = true) ∧ i = mapOperands σ n ∧
    notCall n = true ∧ isCallInd n = false

/-- The facts of the simplify stage the guards need (`g1` the simplifier's output on `g`, `f`
the pipeline's input whose `allowedIn`/`skelAllowedIn` it uses). -/
structure SimpGuard (f g g1 : Function) : Prop where
  hdr : SameHdr g g1
  len : g1.blocks.length = g.blocks.length
  blk : ∀ (i : Nat) (b b' : Block), g.blocks[i]? = some b → g1.blocks[i]? = some b' →
    b'.params = b.params ∧
    ((∃ σ, b'.term = mapTerm σ b.term) ∨ (isBranch b.term = true ∧ isBranch b'.term = true)) ∧
    (∀ s ∈ b'.body, (∃ s0 ∈ b.body, ∃ σ, s.inst = mapOperands σ s0.inst) ∨ NewSimp f s.inst) ∧
    (∀ s0 ∈ b.body, isCallInd s0.inst = true → ∃ s ∈ b'.body, ∃ σ, s.inst = mapOperands σ s0.inst)

theorem SimpGuard.corr {f g g1 : Function} (h : SimpGuard f g g1) {b' : Block}
    (hb' : b' ∈ g1.blocks) :
    ∃ (i : Nat) (b : Block), g.blocks[i]? = some b ∧ g1.blocks[i]? = some b' := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hb'
  have hil : i < g.blocks.length := by rw [← h.len]; exact (List.getElem?_eq_some_iff.1 hi).1
  exact ⟨i, _, List.getElem?_eq_getElem hil, hi⟩

/-- **Simplify** (under `SimpGuard`). -/
theorem SimpGuard.derived {f g g1 : Function} (h : SimpGuard f g g1) : Derived (NewSimp f) g g1 where
  hdr := h.hdr
  blk b' hb' := by
    obtain ⟨i, b, hb, hb'i⟩ := h.corr hb'
    obtain ⟨hp, ht, -, -⟩ := h.blk i b b' hb hb'i
    exact ⟨b, List.mem_of_getElem? hb, hp, ht⟩
  st b' hb' s hs := by
    obtain ⟨i, b, hb, hb'i⟩ := h.corr hb'
    obtain ⟨-, -, hst, -⟩ := h.blk i b b' hb hb'i
    rcases hst s hs with ⟨s0, hs0, σ, he⟩ | hn
    · exact .inl ⟨b, List.mem_of_getElem? hb, s0, hs0, σ, he⟩
    · exact .inr hn

theorem SimpGuard.headKeep {f g g1 : Function} (h : SimpGuard f g g1) : HeadKeep g g1 where
  head b hb := by
    have hb0 : g.blocks[0]? = some b := by rw [← List.head?_eq_getElem?]; exact hb
    have hl : 0 < g1.blocks.length := by
      rw [h.len]; exact (List.getElem?_eq_some_iff.1 hb0).1
    obtain ⟨b', hb'⟩ : ∃ b', g1.blocks[0]? = some b' := ⟨_, List.getElem?_eq_getElem hl⟩
    obtain ⟨-, ht, -, hk⟩ := h.blk 0 b b' hb0 hb'
    refine ⟨b', by rw [List.head?_eq_getElem?]; exact hb', ?_, hk⟩
    rcases ht with ht | ⟨hbr, -⟩
    · exact .inl ht
    · exact .inr hbr

theorem newSimp_ok {f : Function} {i : Inst} (h : NewSimp f i) :
    (Compile.functionE f = true → Compile.instE i = true) ∧ notCall i = true ∧
      isCallInd i = false := by
  obtain ⟨n, σ, hn, rfl, hc, hi⟩ := h
  refine ⟨fun hE => ?_, by rw [notCall_mapOperands]; exact hc,
    by rw [isCallInd_mapOperands]; exact hi⟩
  rw [instE_mapOperands]
  rcases hn with hn | hn
  · exact allowedIn_instE hn hE
  · exact skelAllowedIn_instE hn hE

/-! ## Per-stage `KeepsB` and `ShapeK` -/

theorem keepsB_removeUnreachable (f : Function) : KeepsB f (removeUnreachable f) :=
  (derived_removeUnreachable (fun _ => False) f).keepsB (KeepsB.refl f) fun _ h => h.elim

theorem keepsB_dce (g : Function) : KeepsB g (dce g).1 :=
  (derived_dce (fun _ => False) g).keepsB (KeepsB.refl g) fun _ h => h.elim

theorem keepsB_gvn {g : Function} {info : Info} (h : check g = .ok info) (local? : Inst → Bool) :
    KeepsB g (gvnFull g info local?).1 :=
  (derived_gvn (fun _ => False) h local?).keepsB (KeepsB.refl g) fun _ h => h.elim

theorem keepsB_licm {g g' : Function} (hh : SameHdr g g')
    (hskel : g'.blocks.map skel = g.blocks.map skel)
    (hS : ∀ b' ∈ g'.blocks, ∀ s ∈ b'.body, ∃ b ∈ g.blocks, s ∈ b.body) : KeepsB g g' :=
  (derived_licm (fun _ => False) hh hskel hS).keepsB (KeepsB.refl g) fun _ h => h.elim

/-- The simplify stage keeps `KeepsB f ·` from the pipeline's input `f` (whose `allowedIn` the
simplifier uses). -/
theorem keepsB_simp {f g g1 : Function} (h : KeepsB f g) (hs : SimpGuard f g g1) : KeepsB f g1 :=
  hs.derived.keepsB h fun _ hn => newSimp_ok hn

theorem shapeK_removeUnreachable (f : Function) : ShapeK f (removeUnreachable f) :=
  (derived_removeUnreachable (fun _ => False) f).shapeK (headKeep_removeUnreachable f)
    fun _ h => h.elim

theorem shapeK_dce (g : Function) : ShapeK g (dce g).1 :=
  (derived_dce (fun _ => False) g).shapeK (headKeep_dce g) fun _ h => h.elim

theorem shapeK_gvn {g : Function} {info : Info} (h : check g = .ok info) (local? : Inst → Bool) :
    ShapeK g (gvnFull g info local?).1 :=
  (derived_gvn (fun _ => False) h local?).shapeK (headKeep_gvn h local?) fun _ h => h.elim

theorem shapeK_licm {g g' : Function} (hh : SameHdr g g')
    (hskel : g'.blocks.map skel = g.blocks.map skel)
    (hS : ∀ b' ∈ g'.blocks, ∀ s ∈ b'.body, ∃ b ∈ g.blocks, s ∈ b.body)
    (hK : ∀ b, g.blocks.head? = some b → ∀ s ∈ b.body, isPure s.inst = false →
      ∃ b', g'.blocks.head? = some b' ∧ s ∈ b'.body) : ShapeK g g' :=
  (derived_licm (fun _ => False) hh hskel hS).shapeK (headKeep_licm hskel hK) fun _ h => h.elim

theorem shapeK_simp {f g g1 : Function} (hs : SimpGuard f g g1) : ShapeK g g1 :=
  hs.derived.shapeK hs.headKeep fun _ hn => (newSimp_ok hn).2.2

end Opt

namespace Opt.CompleteGuardsWitness

open Clif

/-- The entry block computes `v0 = 0`, makes an indirect call and branches on `v0`; `block1`
ends with a `return_call`. -/
def entryR : Block :=
  { id := 0, body := [{ results := [0], inst := .iconst .i32 0 }],
    term := .brif 0 { block := 1 } { block := 2 } }

/-- `block1`, the only block with a `return_call`, becomes unreachable once the branch on the
constant `v0 = 0` is folded. -/
def fnR : Function where
  name := "w"
  sig := {}
  externs := [(0, { name := "callee", sig := {} })]
  blocks := [entryR, { id := 1, term := .returnCall 0 [] }, { id := 2, term := .ret [] }]

/-- **`keepsShapeB` can reject**: the executable mid-end drops `block1` (and with it the only
`return_call`), so the guard fires and `optimizeExe` returns its input; `fnR` is not
`shapeSafeB`. -/
theorem counterexample :
    (optimizeX fnR exeConfig).blocks.map (·.id) = [0, 2] ∧
    keepsShapeB fnR (optimizeX fnR exeConfig) = false ∧ optimizeExe fnR exeConfig = fnR ∧
    shapeSafeB fnR = false := by
  native_decide

/-- The entry block has an indirect call and a branch. -/
def entryS : Block :=
  { id := 0, params := [(1, .i64)],
    body := [{ results := [0], inst := .iconst .i32 0 }, { inst := .callIndirect 0 1 [] }],
    term := .brif 0 { block := 1 } { block := 2 } }

def fnS : Function where
  name := "w"
  sig := { params := [{ ty := .i64 }] }
  sigDecls := [(0, {})]
  blocks := [entryS, { id := 1, term := .ret [] }, { id := 2, term := .ret [] }]

/-- The identity is a simplify output with the guard facts (non-vacuity of `SimpGuard`). -/
theorem simpGuard_id (f g : Function) : SimpGuard f g g where
  hdr := SameHdr.refl g
  len := rfl
  blk i b b' hb hb' := by
    rw [hb] at hb'; cases hb'
    exact ⟨rfl, .inl ⟨id, (mapTerm_id _).symm⟩,
      fun s hs => .inl ⟨s, hs, id, (mapOperands_id _).symm⟩,
      fun s hs _ => ⟨s, hs, id, (mapOperands_id _).symm⟩⟩

/-- Non-vacuity of the shape and subset guards: `fnS` (an indirect call in the entry block) is
`shapeSafeB`, and the guards accept `removeUnreachable`, DCE, and LICM / simplify instances
(no move, no rewrite) through `ShapeK` / `KeepsB`. -/
theorem witness :
    shapeSafeB fnS = true ∧ entryIndCallB fnS = true ∧
    keepsShapeB fnS (dce (removeUnreachable fnS)).1 = true ∧
    keepsBackendSubset fnS (dce (removeUnreachable fnS)).1 = true ∧
    keepsShapeB fnS fnS = true ∧ keepsBackendSubset fnS fnS = true := by
  have hsafe : shapeSafeB fnS = true := by native_decide
  have hL : KeepsB fnS fnS := keepsB_licm (SameHdr.refl _) rfl fun b hb s hs => ⟨b, hb, hs⟩
  have hLS : ShapeK fnS fnS := shapeK_licm (SameHdr.refl _) rfl (fun b hb s hs => ⟨b, hb, hs⟩)
    fun b hb s hs _ => ⟨b, hb, hs⟩
  refine ⟨hsafe, by native_decide,
    keepsShapeB_of_shapeK hsafe ((shapeK_removeUnreachable _).trans (shapeK_dce _)),
    keepsBackendSubset_of_keepsB ((keepsB_removeUnreachable _).trans (keepsB_dce _)),
    keepsShapeB_of_shapeK hsafe (hLS.trans (shapeK_simp (simpGuard_id fnS fnS))),
    keepsBackendSubset_of_keepsB (keepsB_simp hL (simpGuard_id fnS fnS))⟩

/-- `v1` recomputes `v0` (GVN removes it). -/
def fnG : Function where
  name := "w"
  sig := {}
  blocks := [{ id := 0, body := [{ results := [0], inst := .iconst .i32 7 },
    { results := [1], inst := .iconst .i32 7 }], term := .ret [1] }]

theorem checksG : (match check fnG with
    | .ok i => (gvnFull fnG i (fun _ => false)).2.1 == 1
    | .error _ => false) = true := by native_decide

/-- Non-vacuity of `keepsB_gvn` / `shapeK_gvn`: GVN removes a statement and both guards
accept. -/
theorem witnessGvn : ∃ i, check fnG = .ok i ∧ (gvnFull fnG i (fun _ => false)).2.1 = 1 ∧
    keepsBackendSubset fnG (gvnFull fnG i (fun _ => false)).1 = true ∧
    keepsShapeB fnG (gvnFull fnG i (fun _ => false)).1 = true := by
  have h := checksG
  split at h
  · rename_i i hi
    exact ⟨i, hi, by simpa using h, keepsBackendSubset_of_keepsB (keepsB_gvn hi _),
      keepsShapeB_of_shapeK (by native_decide) (shapeK_gvn hi _)⟩
  · cases h

end Opt.CompleteGuardsWitness
