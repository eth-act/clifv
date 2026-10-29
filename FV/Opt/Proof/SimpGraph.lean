module

public import FV.Opt.Proof.SimpDen
public import FV.Opt.Simplify

@[expose] public section

/-!
# The e-graph invariant of the simplify pass

For a fixed valuation `ρ` of the graph's leaves (block parameters and skeleton results), a
frame `fr` (slot bases, globals) and a memory `mem` (all symbols defined), the state `st` of
`Opt.simplify` denotes the valuation `gval st := den st.defs ρ fr mem` (`FV/Opt/Proof/SimpDen.lean`).
`GInv` is the invariant of the pass:

* the node of a value only refers to *known* values (graph nodes or available values), and
  every known value is below `next`, above which `ρ` is undefined; so inserting the node of a
  new value never changes `gval` on known values (`gval_insert`): the valuation only grows;
* available values (leaves, kept and emitted values) are defined and typed (`tot`), and so
  are all known values (`knownVal`: the graph's nodes are well-typed nodes over known values);
* partial nodes (`SState.partials`) are over values of the graph, and are not known;
* the recorded e-class members (`alts`) and hash-consing entries (`memo`) are justified
  forward from their key.

`optimizeAt_spec` (a rewrite of `v` returns a value with `v`'s value) and `runSkel_spec` apply
the rule obligations `Opt.SimplifySound`/`Opt.SkeletonSound` with `P := GInv ∧ Grow` and
`den := gval`.
-/

namespace Opt

open Clif

/-! ## Hash maps -/

theorem hm_get?_insert {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [DecidableEq α]
    (m : Std.HashMap α β) (k a : α) (v : β) :
    (m.insert k v).get? a = if k = a then some v else m.get? a := by
  rw [Std.HashMap.get?_insert]; by_cases h : k = a <;> simp [h]

theorem hm_contains_insert {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (m : Std.HashMap α β) (k a : α) (v : β) :
    (m.insert k v).contains a = (k == a || m.contains a) := Std.HashMap.contains_insert

theorem hm_contains_iff {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (m : Std.HashMap α β) (a : α) : m.contains a = true ↔ (m.get? a).isSome := by
  rw [Std.HashMap.contains_eq_isSome_getElem?]; rfl

/-! ## Evaluation facts -/

theorem nodeTy_icmp (cc : IntCC) (ty : Ty) (x y : ValueId) :
    SState.nodeTy (.icmp cc ty x y) = some .i8 := rfl

/-- The result type of an evaluated node is `nodeTy`. -/
theorem evalNode_ty {fr : Frame} {mem : Mem} {n : Inst} {a : Val}
    (h : evalNode fr mem n = some a) : SState.nodeTy n = some a.ty := by
  simp only [evalNode] at h
  split at h
  · rename_i r m he
    cases h
    cases hr : n.resultTypes (fun _ => none) (fun _ => none) with
    | some ts =>
      have := evalInst_types he hr
      simp only [SState.nodeTy, hr, Option.bind_some]
      rw [← this]; rfl
    | none =>
      exfalso
      cases n <;> simp only [Inst.resultTypes, Option.map_eq_none_iff, reduceCtorEq] at hr <;>
        (try (cases ‹FOp› <;> simp only [Inst.resultTypes, reduceCtorEq] at hr)) <;>
        simp [evalInst, hr, Res.ofOption, bind, Res.bind] at he
  · cases h

/-! ## The invariant -/

/-- The graph of a state: its nodes and its partial nodes. -/
def SState.graph (st : SState) : ValueId → Option Inst := fun x =>
  (st.defs.get? x).or (st.partials.get? x)

section Graph

variable (f : Function) (ρ : Valuation) (fr : Frame) (mem : Mem)

/-- The valuation of a state (module doc). -/
noncomputable def gval (st : SState) : Valuation := den st.graph ρ fr mem

/-- The environment of the valuation: the slot bases and globals of `f`, all symbols defined. -/
structure GoodEnv : Prop where
  glob : fr.func.globals = f.globals
  slots : ∀ s, (f.slots.lookup s).isSome → (fr.slots.lookup s).isSome
  syms : ∀ name, (mem.symbols name).isSome

/-- The invariant of the pass state (module doc). -/
structure GInv (st : SState) : Prop where
  fn : st.fn = f
  closed : ∀ x m, st.defs.get? x = some m → ∀ y ∈ operands m, st.known y = true
  fresh : ∀ x, st.known x = true → x < st.next
  freshρ : ∀ x, st.next ≤ x → ρ x = none
  leaf : ∀ x a, ρ x = some a → st.avail.contains x = true ∧ st.defs.get? x = none
  tot : ∀ x, st.avail.contains x = true →
    ∃ a, gval ρ fr mem st x = some a ∧ st.types.get? x = some a.ty
  types : ∀ x t a, st.types.get? x = some t → gval ρ fr mem st x = some a → a.ty = t
  alts : ∀ x ms, st.alts.get? x = some ms → st.known x = true ∧
    ∀ m ∈ ms, ∀ a, gval ρ fr mem st x = some a → gval ρ fr mem st m = some a
  memo : ∀ n w, st.memo.get? n = some w → (∀ y ∈ operands n, st.known y = true) ∧
    ∀ a, evalNode (withRegs fr (gval ρ fr mem st)) mem n = some a → gval ρ fr mem st w = some a
  /-- Partial nodes are fresh and not known, over values of the graph. -/
  partials : ∀ x, st.partials.contains x = true → x < st.next ∧ st.known x = false
  partialsClosed : ∀ x m, st.partials.get? x = some m → ∀ y ∈ operands m, st.inGraph y = true
  /-- Known values are defined and typed. -/
  knownVal : ∀ x, st.known x = true →
    ∃ a, gval ρ fr mem st x = some a ∧ st.types.get? x = some a.ty
  /-- A recorded class is justified forward from a known owner. -/
  classes : ∀ k ms, st.classes.get? k = some ms → ∃ o, st.known o = true ∧
    ∀ a, gval ρ fr mem st o = some a →
      gval ρ fr mem st k = some a ∧ ∀ m ∈ ms, gval ρ fr mem st m = some a

/-- How the state changes while the rules rewrite a value: the valuation and the known values
grow, the output side is untouched. -/
structure Grow (st st' : SState) : Prop where
  fix : ∀ x, st.inGraph x = true → gval ρ fr mem st' x = gval ρ fr mem st x
  known : ∀ x, st.known x = true → st'.known x = true
  inGraph : ∀ x, st.inGraph x = true → st'.inGraph x = true
  avail : st'.avail = st.avail
  alts : st'.alts = st.alts
  fn : st'.fn = st.fn
  trap : st'.trapBlocks = st.trapBlocks
  remat : st'.rematConst = st.rematConst

variable {f ρ fr mem}

theorem Grow.refl (st : SState) : Grow ρ fr mem st st :=
  ⟨fun _ _ => rfl, fun _ h => h, fun _ h => h, rfl, rfl, rfl, rfl, rfl⟩

theorem Grow.trans {st1 st2 st3 : SState} (h1 : Grow ρ fr mem st1 st2)
    (h2 : Grow ρ fr mem st2 st3) : Grow ρ fr mem st1 st3 :=
  ⟨fun x h => (h2.fix x (h1.inGraph x h)).trans (h1.fix x h), fun x h => h2.known x (h1.known x h),
   fun x h => h2.inGraph x (h1.inGraph x h),
   h2.avail.trans h1.avail, h2.alts.trans h1.alts, h2.fn.trans h1.fn, h2.trap.trans h1.trap,
   h2.remat.trans h1.remat⟩

theorem inGraph_of_known {st : SState} {x : ValueId} (hx : st.known x = true) :
    st.inGraph x = true := by
  simp [SState.inGraph, hx]

theorem inGraph_false {st : SState} {x : ValueId} (hx : st.inGraph x = false) :
    st.known x = false ∧ st.partials.contains x = false := by
  simpa [SState.inGraph] using hx

theorem known_false {st : SState} {x : ValueId} (hx : st.known x = false) :
    st.defs.get? x = none ∧ st.avail.contains x = false := by
  simp only [SState.known, Bool.or_eq_false_iff] at hx
  exact ⟨Std.HashMap.getElem?_eq_none_of_contains_eq_false hx.1, hx.2⟩

theorem known_of_defs {st : SState} {x : ValueId} {n : Inst} (hx : st.defs.get? x = some n) :
    st.known x = true := by
  cases hk : st.known x with
  | true => rfl
  | false => rw [(known_false hk).1] at hx; cases hx

theorem known_of_avail {st : SState} {x : ValueId} (hx : st.avail.contains x = true) :
    st.known x = true := by
  simp [SState.known, hx]

theorem graph_none {st : SState} {x : ValueId} (hk : st.known x = false)
    (hp : st.partials.contains x = false) : st.graph x = none := by
  show (st.defs.get? x).or (st.partials.get? x) = none
  rw [(known_false hk).1, Option.none_or, Std.HashMap.get?_eq_getElem?]
  exact Std.HashMap.getElem?_eq_none_of_contains_eq_false hp

theorem graph_of_defs {st : SState} {x : ValueId} {n : Inst} (hn : st.defs.get? x = some n) :
    st.graph x = some n := by
  show (st.defs.get? x).or (st.partials.get? x) = some n
  rw [hn]; rfl

theorem gval_unknown {st : SState} (h : GInv f ρ fr mem st) {x : ValueId}
    (hx : st.inGraph x = false) : gval ρ fr mem st x = none := by
  obtain ⟨hk, hp⟩ := inGraph_false hx
  obtain ⟨hd, ha⟩ := known_false hk
  rw [gval, den_leaf (graph_none hk hp)]
  cases hρ : ρ x with
  | none => rfl
  | some a => rw [(h.leaf x a hρ).1] at ha; cases ha

theorem inGraph_of_gval {st : SState} (h : GInv f ρ fr mem st) {x : ValueId} {a : Val}
    (hx : gval ρ fr mem st x = some a) : st.inGraph x = true := by
  cases hk : st.inGraph x with
  | true => rfl
  | false => rw [gval_unknown h hk] at hx; cases hx

theorem graph_insert (st : SState) (w : ValueId) (n : Inst) :
    SState.graph { st with defs := st.defs.insert w n } = graphInsert st.graph w n := by
  funext x
  simp only [SState.graph, graphInsert, hm_get?_insert]
  by_cases h : w = x
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The nodes of the graph are over values of the graph. -/
theorem GInv.graph_closed {st : SState} (h : GInv f ρ fr mem st) {x : ValueId} {m : Inst}
    (hm : st.graph x = some m) : ∀ y ∈ operands m, st.inGraph y = true := by
  intro y hy
  simp only [SState.graph] at hm
  cases hd : st.defs.get? x with
  | some m' =>
    rw [hd] at hm; simp only [Option.some_or, Option.some.injEq] at hm; subst hm
    exact inGraph_of_known (h.closed x _ hd y hy)
  | none =>
    rw [hd] at hm; simp only [Option.none_or] at hm
    exact h.partialsClosed x m hm y hy

/-- Inserting the node of a value outside the graph over values of the graph: `gval` is unchanged
on the graph and the new value gets the node's value. -/
theorem gval_insert {st st' : SState} (h : GInv f ρ fr mem st) {w : ValueId} {n : Inst}
    (hw : st.inGraph w = false) (hn : ∀ y ∈ operands n, st.inGraph y = true)
    (hg : st'.graph = graphInsert st.graph w n) :
    (∀ x, st.inGraph x = true → gval ρ fr mem st' x = gval ρ fr mem st x) ∧
      gval ρ fr mem st' w = evalNode (withRegs fr (gval ρ fr mem st)) mem n := by
  have hK : ∀ x m, st.inGraph x = true → st.graph x = some m →
      ∀ y ∈ operands m, st.inGraph y = true :=
    fun _ _ _ hm => h.graph_closed hm
  have hfix : ∀ x, st.inGraph x = true → gval ρ fr mem st' x = gval ρ fr mem st x := by
    intro x hx
    simp only [gval, hg]
    exact den_insert_fresh (K := fun x => st.inGraph x = true) (by simp [hw]) hK hx
  refine ⟨hfix, ?_⟩
  have hn' : st'.graph w = some n := by simp [hg, graphInsert]
  rw [gval, den_node hn']
  exact evalNode_congr rfl rfl rfl (fun y hy => hfix y (hn y hy))

theorem known_mono_defs {st st' : SState} (hd : ∀ x, (st.defs.get? x).isSome → (st'.defs.get? x).isSome)
    (ha : ∀ x, st.avail.contains x = true → st'.avail.contains x = true) {x : ValueId}
    (hx : st.known x = true) : st'.known x = true := by
  simp only [SState.known, Bool.or_eq_true] at hx ⊢
  rcases hx with hx | hx
  · left
    rw [Std.HashMap.contains_eq_isSome_getElem?] at hx ⊢
    exact hd x hx
  · exact .inr (ha x hx)

/-- A state over the same graph (and output), whose recorded classes, alternatives and
hash-consing entries are justified. -/
theorem GInv.of_graph {st st' : SState} (h : GInv f ρ fr mem st) (hd : st'.defs = st.defs)
    (ha : st'.avail = st.avail) (ht : st'.types = st.types) (hf : st'.fn = st.fn)
    (hn : st.next ≤ st'.next) (hp : st'.partials = st.partials)
    (halts : ∀ x ms, st'.alts.get? x = some ms → st.known x = true ∧
      ∀ m ∈ ms, ∀ a, gval ρ fr mem st x = some a → gval ρ fr mem st m = some a)
    (hmemo : ∀ n w, st'.memo.get? n = some w → (∀ y ∈ operands n, st.known y = true) ∧
      ∀ a, evalNode (withRegs fr (gval ρ fr mem st)) mem n = some a → gval ρ fr mem st w = some a)
    (hcls : ∀ k ms, st'.classes.get? k = some ms → ∃ o, st.known o = true ∧
      ∀ a, gval ρ fr mem st o = some a →
        gval ρ fr mem st k = some a ∧ ∀ m ∈ ms, gval ρ fr mem st m = some a) :
    GInv f ρ fr mem st' := by
  have hk : ∀ x, st'.known x = st.known x := by intro x; simp [SState.known, hd, ha]
  have hi : ∀ x, st'.inGraph x = st.inGraph x := by intro x; simp [SState.inGraph, hk, hp]
  have hgr : st'.graph = st.graph := by funext x; simp [SState.graph, hd, hp]
  have hg : gval ρ fr mem st' = gval ρ fr mem st := by simp only [gval, hgr]
  refine ⟨hf.trans h.fn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x m hx y hy; rw [hk]; rw [hd] at hx; exact h.closed x m hx y hy
  · intro x hx; rw [hk] at hx; exact Nat.lt_of_lt_of_le (h.fresh x hx) hn
  · intro x hx; exact h.freshρ x (Nat.le_trans hn hx)
  · intro x a hx; rw [ha, hd]; exact h.leaf x a hx
  · intro x hx; rw [hg, ht]; rw [ha] at hx; exact h.tot x hx
  · intro x t a hx; rw [hg]; rw [ht] at hx; exact h.types x t a hx
  · intro x ms hx; rw [hk, hg]; exact halts x ms hx
  · intro n w hx; rw [hg]
    obtain ⟨h1, h2⟩ := hmemo n w hx
    exact ⟨fun y hy => by rw [hk]; exact h1 y hy, h2⟩
  · intro x hx; rw [hk]; rw [hp] at hx
    exact ⟨Nat.lt_of_lt_of_le (h.partials x hx).1 hn, (h.partials x hx).2⟩
  · intro x m hx y hy; rw [hi]; rw [hp] at hx; exact h.partialsClosed x m hx y hy
  · intro x hx; rw [hg, ht]; rw [hk] at hx; exact h.knownVal x hx
  · intro k ms hx
    obtain ⟨o, ho, h2⟩ := hcls k ms hx
    exact ⟨o, by rw [hk]; exact ho, by rw [hg]; exact h2⟩

theorem Grow.of_graph {st st' : SState} (hd : st'.defs = st.defs)
    (ha : st'.avail = st.avail) (hp : st'.partials = st.partials) (hal : st'.alts = st.alts)
    (hf : st'.fn = st.fn) (htr : st'.trapBlocks = st.trapBlocks)
    (hr : st'.rematConst = st.rematConst) : Grow ρ fr mem st st' := by
  have hk : ∀ x, st'.known x = st.known x := by intro x; simp [SState.known, hd, ha]
  have hgr : st'.graph = st.graph := by funext x; simp [SState.graph, hd, hp]
  refine ⟨fun x _ => by simp only [gval, hgr], fun x hx => by rw [hk]; exact hx,
    fun x hx => by simp only [SState.inGraph, hk, hp]; exact hx, ha, hal, hf, htr, hr⟩

/-- States that differ only in fields the invariant does not mention (and a larger `next`). -/
theorem GInv.of_same {st st' : SState} (h : GInv f ρ fr mem st) (hd : st'.defs = st.defs)
    (ha : st'.avail = st.avail) (hal : st'.alts = st.alts) (hm : st'.memo = st.memo)
    (ht : st'.types = st.types) (hf : st'.fn = st.fn) (hn : st.next ≤ st'.next)
    (htr : st'.trapBlocks = st.trapBlocks) (hr : st'.rematConst = st.rematConst)
    (hp : st'.partials = st.partials) (hc : st'.classes = st.classes) :
    GInv f ρ fr mem st' ∧ Grow ρ fr mem st st' :=
  ⟨h.of_graph hd ha ht hf hn hp (by rw [hal]; exact h.alts) (by rw [hm]; exact h.memo)
    (by rw [hc]; exact h.classes), Grow.of_graph hd ha hp hal hf htr hr⟩

/-- Recording a justified hash-consing entry. -/
theorem memo_insert_spec {st st' : SState} (h : GInv f ρ fr mem st) {n : Inst} {b : ValueId}
    (hn : ∀ y ∈ operands n, st.known y = true)
    (hb : ∀ a, evalNode (withRegs fr (gval ρ fr mem st)) mem n = some a → gval ρ fr mem st b = some a)
    (hm : st'.memo = st.memo.insert n b) (hd : st'.defs = st.defs)
    (ha : st'.avail = st.avail) (hal : st'.alts = st.alts)
    (ht : st'.types = st.types) (hf : st'.fn = st.fn) (hn' : st.next ≤ st'.next)
    (htr : st'.trapBlocks = st.trapBlocks) (hr : st'.rematConst = st.rematConst)
    (hp : st'.partials = st.partials) (hc : st'.classes = st.classes) :
    GInv f ρ fr mem st' ∧ Grow ρ fr mem st st' := by
  refine ⟨h.of_graph hd ha ht hf hn' hp (by rw [hal]; exact h.alts) ?_ (by rw [hc]; exact h.classes),
    Grow.of_graph hd ha hp hal hf htr hr⟩
  intro n' w hx
  rw [hm, hm_get?_insert] at hx
  split at hx
  · rename_i he; subst he; cases hx; exact ⟨hn, hb⟩
  · exact h.memo n' w hx

theorem insertNode_fields (allowed : Inst → Bool) (st : SState) (n : Inst) :
    (st.insertNode allowed n).1 = st.next ∧
    (st.insertNode allowed n).2.defs = st.defs.insert st.next n ∧
    (st.insertNode allowed n).2.types = (match SState.nodeTy n with
      | some t => st.types.insert st.next t
      | none => st.types) ∧
    (st.insertNode allowed n).2.next = st.next + 1 ∧
    (st.insertNode allowed n).2.avail = st.avail ∧ (st.insertNode allowed n).2.alts = st.alts ∧
    (st.insertNode allowed n).2.memo = st.memo ∧ (st.insertNode allowed n).2.fn = st.fn ∧
    (st.insertNode allowed n).2.trapBlocks = st.trapBlocks ∧
    (st.insertNode allowed n).2.rematConst = st.rematConst := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases n <;> rfl

/-- A well-typed node over known values evaluates, to a value of type `nodeTy`. -/
theorem typedNode_total {st : SState} (h : GInv f ρ fr mem st) (hE : GoodEnv f fr mem)
    {n : Inst} (hok : st.nodeOk n = true) (hn : st.typedNode n = true) :
    ∃ a, evalNode (withRegs fr (gval ρ fr mem st)) mem n = some a ∧ SState.nodeTy n = some a.ty := by
  simp only [SState.nodeOk, List.all_eq_true] at hok
  simp only [SState.typedNode, Bool.and_eq_true] at hn
  obtain ⟨hp, ht⟩ := hn
  rw [h.fn] at ht
  obtain ⟨v, hv⟩ := evalInst_total (f := f) (fr := withRegs fr (gval ρ fr mem st)) (mem := mem)
    hp ht hE.glob (fun x hx => h.knownVal x (hok x hx)) hE.slots
    (fun _ _ name _ _ _ _ => hE.syms name)
  have he : evalNode (withRegs fr (gval ρ fr mem st)) mem n = some v := by simp [evalNode, hv]
  exact ⟨v, he, evalNode_ty he⟩

theorem next_not_inGraph {st : SState} (h : GInv f ρ fr mem st) : st.inGraph st.next = false := by
  cases hk : st.inGraph st.next with
  | false => rfl
  | true =>
    simp only [SState.inGraph, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · exact absurd (h.fresh _ hk) (Nat.lt_irrefl _)
    · exact absurd (h.partials _ hk).1 (Nat.lt_irrefl _)

/-- Inserting the node `n` over known values under the fresh value `st.next` (the value may
also become available, and gets a type consistent with its value). Stated on the fields of the
new state. -/
theorem fresh_spec {st st' : SState} (h : GInv f ρ fr mem st) {n : Inst}
    (hn : ∀ y ∈ operands n, st.known y = true)
    (hd : st'.defs = st.defs.insert st.next n)
    (htx : ∀ x, x ≠ st.next → st'.types.get? x = st.types.get? x)
    (htw : ∀ t a, st'.types.get? st.next = some t →
      evalNode (withRegs fr (gval ρ fr mem st)) mem n = some a → a.ty = t)
    (hnx : st'.next = st.next + 1)
    (ha : ∀ x, x ≠ st.next → st'.avail.contains x = st.avail.contains x)
    (hal : st'.alts = st.alts)
    (hm : st'.memo = st.memo) (hf : st'.fn = st.fn) (hc : st'.classes = st.classes)
    (hp : st'.partials = st.partials)
    (hwtot : ∃ a, evalNode (withRegs fr (gval ρ fr mem st)) mem n = some a ∧
      st'.types.get? st.next = some a.ty) :
    GInv f ρ fr mem st' ∧ (∀ x, st.inGraph x = true → gval ρ fr mem st' x = gval ρ fr mem st x) ∧
      (∀ x, st.known x = true → st'.known x = true) ∧
      (∀ x, st.inGraph x = true → st'.inGraph x = true) ∧ st'.known st.next = true ∧
      gval ρ fr mem st' st.next = evalNode (withRegs fr (gval ρ fr mem st)) mem n := by
  have hwg := next_not_inGraph h
  have hw : st.known st.next = false := (inGraph_false hwg).1
  have hwa : st.avail.contains st.next = false := by
    cases hk : st.avail.contains st.next with
    | false => rfl
    | true => rw [known_of_avail hk] at hw; cases hw
  have hg : st'.graph = graphInsert st.graph st.next n := by
    funext x
    simp only [SState.graph, graphInsert, hd, hp, hm_get?_insert]
    by_cases hx : st.next = x
    · subst hx; simp
    · simp [hx, Ne.symm hx]
  obtain ⟨hfix, hnew⟩ := gval_insert h hwg (fun y hy => inGraph_of_known (hn y hy)) hg
  have hdw : st'.defs.get? st.next = some n := by rw [hd, hm_get?_insert]; simp
  have hkw : st'.known st.next = true := known_of_defs hdw
  have hdx : ∀ x, x ≠ st.next → st'.defs.get? x = st.defs.get? x := by
    intro x hx; rw [hd, hm_get?_insert, if_neg (Ne.symm hx)]
  have hkm : ∀ x, st.known x = true → st'.known x = true := by
    intro x hx
    by_cases hxw : x = st.next
    · rw [hxw]; exact hkw
    apply known_mono_defs _ _ hx
    · intro y hy
      by_cases hyw : y = st.next
      · rw [hyw, hdw]; rfl
      · rw [hdx y hyw]; exact hy
    · intro y hy
      by_cases hyw : y = st.next
      · rw [hyw] at hy; rw [hy] at hwa; cases hwa
      · rw [ha y hyw]; exact hy
  have hkb : ∀ x, x ≠ st.next → st'.known x = true → st.known x = true := by
    intro x hxw hx
    cases hk : st.known x with
    | true => rfl
    | false =>
      obtain ⟨hd0, ha0⟩ := known_false hk
      simp only [SState.known, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · rw [Std.HashMap.contains_eq_isSome_getElem?] at hx
        have := hdx x hxw
        simp only [Std.HashMap.get?_eq_getElem?] at this hd0
        rw [this, hd0] at hx; cases hx
      · rw [ha x hxw] at hx; rw [hx] at ha0; cases ha0
  have him : ∀ x, st.inGraph x = true → st'.inGraph x = true := by
    intro x hx
    simp only [SState.inGraph, Bool.or_eq_true, hp] at hx ⊢
    exact hx.imp (hkm x) id
  have hunk : ∀ x, x ≠ st.next → st.inGraph x = false → gval ρ fr mem st' x = none := by
    intro x hx hk
    obtain ⟨hk1, hp1⟩ := inGraph_false hk
    have hd' : st'.graph x = none := by
      show (st'.defs.get? x).or (st'.partials.get? x) = none
      rw [hdx x hx, (known_false hk1).1, Option.none_or, hp, Std.HashMap.get?_eq_getElem?]
      exact Std.HashMap.getElem?_eq_none_of_contains_eq_false hp1
    rw [gval, den_leaf hd']
    cases hρ : ρ x with
    | none => rfl
    | some a => rw [known_of_avail (h.leaf x a hρ).1] at hk1; cases hk1
  refine ⟨⟨hf.trans h.fn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hfix, hkm, him, hkw, hnew⟩
  · -- closed
    intro x m hx y hy
    by_cases hxw : x = st.next
    · rw [hxw, hdw] at hx; cases hx; exact hkm y (hn y hy)
    · rw [hdx x hxw] at hx; exact hkm y (h.closed x m hx y hy)
  · -- fresh
    intro x hx
    rw [hnx]
    by_cases hxw : x = st.next
    · subst hxw; exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (h.fresh x (hkb x hxw hx))
  · intro x hx; rw [hnx] at hx; exact h.freshρ x (Nat.le_of_succ_le hx)
  · intro x a hx
    obtain ⟨h1', h2'⟩ := h.leaf x a hx
    have hxw : x ≠ st.next := by
      intro he; rw [he, h.freshρ _ (Nat.le_refl _)] at hx; cases hx
    exact ⟨by rw [ha x hxw]; exact h1', by rw [hdx x hxw]; exact h2'⟩
  · -- tot
    intro x hx
    by_cases hxw : x = st.next
    · subst hxw
      obtain ⟨a, h1', h2'⟩ := hwtot
      exact ⟨a, by rw [hnew]; exact h1', h2'⟩
    · rw [ha x hxw] at hx
      have hk := known_of_avail hx
      obtain ⟨a, h1', h2'⟩ := h.tot x hx
      exact ⟨a, by rw [hfix x (inGraph_of_known hk)]; exact h1', by rw [htx x hxw]; exact h2'⟩
  · -- types
    intro x t a hx hv
    by_cases hxw : x = st.next
    · subst hxw
      rw [hnew] at hv
      exact htw t a hx hv
    · rw [htx x hxw] at hx
      cases hk : st.inGraph x with
      | true => rw [hfix x hk] at hv; exact h.types x t a hx hv
      | false => rw [hunk x hxw hk] at hv; cases hv
  · -- alts
    intro x ms hx
    rw [hal] at hx
    obtain ⟨hk, hms⟩ := h.alts x ms hx
    refine ⟨hkm x hk, fun m hm a hv => ?_⟩
    rw [hfix x (inGraph_of_known hk)] at hv
    have := hms m hm a hv
    rw [hfix m (inGraph_of_gval h this)]; exact this
  · -- memo
    intro n' w hx
    rw [hm] at hx
    obtain ⟨hk, hw'⟩ := h.memo n' w hx
    refine ⟨fun y hy => hkm y (hk y hy), fun a hv => ?_⟩
    rw [evalNode_congr (fr := withRegs fr (gval ρ fr mem st)) (fr' := withRegs fr (gval ρ fr mem st'))
      rfl rfl rfl (fun y hy => hfix y (inGraph_of_known (hk y hy)))] at hv
    have := hw' a hv
    rw [hfix w (inGraph_of_gval h this)]; exact this
  · -- partials
    intro x hx
    rw [hp] at hx
    obtain ⟨h1, h2⟩ := h.partials x hx
    have hxw : x ≠ st.next := Nat.ne_of_lt h1
    refine ⟨by rw [hnx]; exact Nat.lt_succ_of_lt h1, ?_⟩
    cases hk : st'.known x with
    | false => rfl
    | true => rw [hkb x hxw hk] at h2; cases h2
  · intro x m hx y hy
    rw [hp] at hx
    exact him y (h.partialsClosed x m hx y hy)
  · -- knownVal
    intro x hx
    by_cases hxw : x = st.next
    · subst hxw
      obtain ⟨a, h1', h2'⟩ := hwtot
      exact ⟨a, by rw [hnew]; exact h1', h2'⟩
    · have hk := hkb x hxw hx
      obtain ⟨a, h1', h2'⟩ := h.knownVal x hk
      exact ⟨a, by rw [hfix x (inGraph_of_known hk)]; exact h1', by rw [htx x hxw]; exact h2'⟩
  · -- classes
    intro k ms hx
    rw [hc] at hx
    obtain ⟨o, hko, h2⟩ := h.classes k ms hx
    refine ⟨o, hkm o hko, fun a hv => ?_⟩
    rw [hfix o (inGraph_of_known hko)] at hv
    obtain ⟨hk1, hk2⟩ := h2 a hv
    refine ⟨by rw [hfix k (inGraph_of_gval h hk1)]; exact hk1, fun m hm => ?_⟩
    have := hk2 m hm
    rw [hfix m (inGraph_of_gval h this)]; exact this

/-- Inserting the well-typed node `n` over known values under the fresh value `st.next` (as
`insertNode` does). Stated on the fields of the new state. -/
theorem insert_spec {st st' : SState} (h : GInv f ρ fr mem st) (hE : GoodEnv f fr mem) {n : Inst}
    (hn : st.nodeOk n = true) (hty : st.typedNode n = true)
    (hd : st'.defs = st.defs.insert st.next n)
    (ht : st'.types = match SState.nodeTy n with
      | some t => st.types.insert st.next t
      | none => st.types)
    (hnx : st'.next = st.next + 1) (ha : st'.avail = st.avail) (hal : st'.alts = st.alts)
    (hm : st'.memo = st.memo) (hf : st'.fn = st.fn) (htr : st'.trapBlocks = st.trapBlocks)
    (hr : st'.rematConst = st.rematConst) (hc : st'.classes = st.classes)
    (hp : st'.partials = st.partials) :
    GInv f ρ fr mem st' ∧ Grow ρ fr mem st st' ∧ st'.known st.next = true ∧
      gval ρ fr mem st' st.next = evalNode (withRegs fr (gval ρ fr mem st)) mem n ∧
      (∀ x, st.inGraph x = true → gval ρ fr mem st' x = gval ρ fr mem st x) := by
  have hkn : ∀ y ∈ operands n, st.known y = true := by simpa [SState.nodeOk] using hn
  have htx : ∀ x, x ≠ st.next → st'.types.get? x = st.types.get? x := by
    intro x hx
    rw [ht]; split
    · rw [hm_get?_insert, if_neg (Ne.symm hx)]
    · rfl
  have htw : ∀ t a, st'.types.get? st.next = some t →
      evalNode (withRegs fr (gval ρ fr mem st)) mem n = some a → a.ty = t := by
    intro t a hx hv
    have hty := evalNode_ty hv
    rw [ht, hty] at hx
    simp at hx
    exact hx
  have hwtot : ∃ a, evalNode (withRegs fr (gval ρ fr mem st)) mem n = some a ∧
      st'.types.get? st.next = some a.ty := by
    obtain ⟨a, ha', hty'⟩ := typedNode_total h hE hn hty
    exact ⟨a, ha', by rw [ht, hty']; simp⟩
  obtain ⟨hI, hfix, hkm, him, hkw, hnew⟩ := fresh_spec h hkn hd htx htw hnx
    (fun x _ => by rw [ha]) hal hm hf hc hp hwtot
  exact ⟨hI, ⟨hfix, hkm, him, ha, hal, hf, htr, hr⟩, hkw, hnew, hfix⟩

/-- Recording the partial node `n` over values of the graph under the fresh `st.next`. -/
theorem insertPartial_spec {st : SState} (h : GInv f ρ fr mem st) {n : Inst}
    (hn : ∀ y ∈ operands n, st.inGraph y = true) :
    GInv f ρ fr mem (st.insertPartial n).2 ∧ Grow ρ fr mem st (st.insertPartial n).2 ∧
      gval ρ fr mem (st.insertPartial n).2 (st.insertPartial n).1 =
        evalNode (withRegs fr (gval ρ fr mem st)) mem n := by
  have hwg := next_not_inGraph h
  obtain ⟨hwk, hwp⟩ := inGraph_false hwg
  have hdw : st.defs.get? st.next = none := (known_false hwk).1
  have hg : (st.insertPartial n).2.graph = graphInsert st.graph st.next n := by
    funext x
    simp only [SState.graph, SState.insertPartial, graphInsert, hm_get?_insert]
    by_cases hx : st.next = x
    · subst hx
      have : st.defs[st.next]? = none := by simpa using hdw
      simp [this]
    · simp [hx, Ne.symm hx]
  obtain ⟨hfix, hnew⟩ := gval_insert h hwg hn hg
  have hk : ∀ x, (st.insertPartial n).2.known x = st.known x := fun _ => rfl
  have hpc : ∀ x, (st.insertPartial n).2.partials.contains x = true ↔
      x = st.next ∨ st.partials.contains x = true := by
    intro x
    simp only [SState.insertPartial, Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq]
    exact ⟨fun h => h.imp Eq.symm id, fun h => h.imp Eq.symm id⟩
  have him : ∀ x, st.inGraph x = true → (st.insertPartial n).2.inGraph x = true := by
    intro x hx
    simp only [SState.inGraph, Bool.or_eq_true, hk] at hx ⊢
    exact hx.imp id (fun hp => (hpc x).2 (.inr hp))
  have htx : ∀ x, x ≠ st.next → (st.insertPartial n).2.types.get? x = st.types.get? x := by
    intro x hx
    simp only [SState.insertPartial]; split
    · rw [hm_get?_insert, if_neg (Ne.symm hx)]
    · rfl
  have hunk : ∀ x, x ≠ st.next → st.inGraph x = false →
      gval ρ fr mem (st.insertPartial n).2 x = none := by
    intro x hx hx'
    obtain ⟨hk1, hp1⟩ := inGraph_false hx'
    have hd' : (st.insertPartial n).2.graph x = none := by
      rw [hg]; simp only [graphInsert, if_neg hx]
      exact graph_none hk1 hp1
    rw [gval, den_leaf hd']
    cases hρ : ρ x with
    | none => rfl
    | some a => rw [known_of_avail (h.leaf x a hρ).1] at hk1; cases hk1
  refine ⟨⟨h.fn, h.closed, fun x hx => Nat.lt_succ_of_lt (h.fresh x hx),
    fun x hx => h.freshρ x (Nat.le_of_succ_le hx), h.leaf, fun x hx => ?_, fun x t a hx hv => ?_,
    fun x ms hx => ?_, fun n' w hx => ?_, fun x hx => ?_, fun x m hx y hy => ?_,
    fun x hx => ?_, fun k ms hx => ?_⟩, ⟨hfix, fun _ h => h, him, rfl, rfl, rfl, rfl, rfl⟩, hnew⟩
  · -- tot
    obtain ⟨a, h1', h2'⟩ := h.tot x hx
    have hk' : st.known x = true := known_of_avail hx
    have hxw : x ≠ st.next := fun he => by rw [← he, hk'] at hwk; cases hwk
    exact ⟨a, by rw [hfix x (inGraph_of_known (known_of_avail hx))]; exact h1',
      by rw [htx x hxw]; exact h2'⟩
  · -- types
    by_cases hxw : x = st.next
    · subst hxw
      rw [hnew] at hv
      have hty := evalNode_ty hv
      have ht' : (st.insertPartial n).2.types.get? st.next = some a.ty := by
        simp [SState.insertPartial, hty, hm_get?_insert]
      rw [ht'] at hx; cases hx; rfl
    · rw [htx x hxw] at hx
      cases hk' : st.inGraph x with
      | true => rw [hfix x hk'] at hv; exact h.types x t a hx hv
      | false => rw [hunk x hxw hk'] at hv; cases hv
  · -- alts
    obtain ⟨hk1, hms⟩ := h.alts x ms hx
    refine ⟨hk1, fun m hm a hv => ?_⟩
    rw [hfix x (inGraph_of_known hk1)] at hv
    have := hms m hm a hv
    rw [hfix m (inGraph_of_gval h this)]; exact this
  · -- memo
    obtain ⟨hk1, hw'⟩ := h.memo n' w hx
    refine ⟨hk1, fun a hv => ?_⟩
    rw [evalNode_congr (fr := withRegs fr (gval ρ fr mem st))
      (fr' := withRegs fr (gval ρ fr mem (st.insertPartial n).2))
      rfl rfl rfl (fun y hy => hfix y (inGraph_of_known (hk1 y hy)))] at hv
    have := hw' a hv
    rw [hfix w (inGraph_of_gval h this)]; exact this
  · -- partials
    rcases (hpc x).1 hx with rfl | hx
    · exact ⟨Nat.lt_succ_self _, hwk⟩
    · exact ⟨Nat.lt_succ_of_lt (h.partials x hx).1, (h.partials x hx).2⟩
  · -- partialsClosed
    simp only [SState.insertPartial, hm_get?_insert] at hx
    split at hx
    · cases hx; exact him y (hn y hy)
    · exact him y (h.partialsClosed x m hx y hy)
  · -- knownVal
    obtain ⟨a, h1', h2'⟩ := h.knownVal x hx
    have hk' : st.known x = true := hx
    have hxw : x ≠ st.next := fun he => by rw [← he, hk'] at hwk; cases hwk
    exact ⟨a, by rw [hfix x (inGraph_of_known hx)]; exact h1', by rw [htx x hxw]; exact h2'⟩
  · -- classes
    obtain ⟨o, hko, h2⟩ := h.classes k ms hx
    refine ⟨o, hko, fun a hv => ?_⟩
    rw [hfix o (inGraph_of_known hko)] at hv
    obtain ⟨hk1, hk2⟩ := h2 a hv
    refine ⟨by rw [hfix k (inGraph_of_gval h hk1)]; exact hk1, fun m hm => ?_⟩
    have := hk2 m hm
    rw [hfix m (inGraph_of_gval h this)]; exact this

/-! ## Extraction -/

theorem mem_dedup {l acc : List (ValueId × Bool)} {c : ValueId × Bool}
    (h : c ∈ l.foldl (fun acc c => if acc.any (·.1 == c.1) then acc else acc ++ [c]) acc) :
    c ∈ acc ∨ c ∈ l := by
  induction l generalizing acc with
  | nil => exact .inl h
  | cons d ds ih =>
    simp only [List.foldl_cons] at h
    rcases ih h with h | h
    · split at h
      · exact .inl h
      · simp only [List.mem_append, List.mem_singleton] at h
        rcases h with h | rfl
        · exact .inl h
        · exact .inr (by simp)
    · exact .inr (by simp [h])

theorem foldl_choose {l : List ValueId} {p : ValueId → ValueId → Bool} {b : ValueId} :
    l.foldl (fun b x => if p x b then x else b) b = b ∨ l.foldl (fun b x => if p x b then x else b) b ∈ l := by
  induction l generalizing b with
  | nil => exact .inl rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split
    · rcases ih (b := x) with h | h
      · exact .inr (by simp [h])
      · exact .inr (by simp [h])
    · rcases ih (b := b) with h | h
      · exact .inl h
      · exact .inr (by simp [h])

/-- What `chooseBest` returns and records. -/
theorem chooseBest_spec (st : SState) (v : ValueId) (cands : List (ValueId × Bool)) :
    ((chooseBest st v cands).1 = v ∨ ∃ c ∈ cands, c.1 = (chooseBest st v cands).1) ∧
    (∃ cl, (chooseBest st v cands).2 = { st with classes := cl }) ∧
    (∀ k ms, (chooseBest st v cands).2.classes.get? k = some ms →
      st.classes.get? k = some ms ∨
        (k = (chooseBest st v cands).1 ∧ ∀ m ∈ ms, m = v ∨ ∃ c ∈ cands, c.1 = m)) := by
  have hsorted : ∀ c ∈ (((cands.take matchesLimit).filter (·.1 != v)).toArray.qsort
      (fun a b => a.1 < b.1)).toList.filter ((cands.take matchesLimit).filter (·.1 != v)).contains,
      c ∈ cands := by
    intro c hc
    simp only [List.mem_filter, List.contains_iff_mem] at hc
    exact List.mem_of_mem_take hc.2.1
  simp only [chooseBest]
  split
  · rename_i s b hs
    have hmem := List.mem_of_find?_eq_some hs
    rcases mem_dedup hmem with h | h
    · cases h
    · exact ⟨.inr ⟨_, hsorted _ h, rfl⟩, ⟨st.classes, rfl⟩, fun k ms h => .inl h⟩
  · refine ⟨?_, ⟨_, rfl⟩, ?_⟩
    · rcases foldl_choose with h | h
      · exact .inl h
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · exact .inl h
        · obtain ⟨c, hc, he⟩ := List.mem_map.1 (List.mem_of_mem_take h)
          rcases mem_dedup hc with h2 | h2
          · cases h2
          · exact .inr ⟨c, hsorted c h2, he⟩
    · intro k ms hk
      simp only [hm_get?_insert] at hk
      split at hk
      · rename_i he
        cases hk
        refine .inr ⟨he.symm, fun m hm => ?_⟩
        simp only [List.mem_filter, List.mem_cons] at hm
        rcases hm.1 with h | h
        · exact .inl h
        · obtain ⟨c, hc, he⟩ := List.mem_map.1 (List.mem_of_mem_take h)
          rcases mem_dedup hc with h2 | h2
          · cases h2
          · exact .inr ⟨c, hsorted c h2, he⟩
      · exact .inl hk

/-! ## Rewriting a value -/

/-- `make` of `optimizeAt` at depth `d + 1`, rewriting `v`. -/
def optMake (rules : SimplifyFn) (allowed : Inst → Bool) (d : Nat) (v : ValueId) (st : SState)
    (n : Inst) : ValueId × SState :=
  if !(operands n).all st.inGraph then st.dummy else
  if !st.nodeOk n || (operands n).contains v || !st.typedNode n then st.insertPartial n else
  match st.memo.get? n with
  | some w => (w, st)
  | none =>
    let (w, st) := st.insertNode allowed n
    let (b, st) := optimizeAt rules allowed d st w
    (b, { st with memo := st.memo.insert n b })

theorem optimizeAt_succ (rules : SimplifyFn) (allowed : Inst → Bool) (d : Nat) (st : SState)
    (v : ValueId) :
    optimizeAt rules allowed (d + 1) st v =
      match rules SState.enodes (fun st x => st.types.get? x) (optMake rules allowed d v) st v with
      | .error _ => (v, { st with stats := { st.stats with errors := st.stats.errors + 1 } })
      | .ok (cands, names, st) =>
        let fired := names.foldl (fun m n => m.insert n ((m.get? n).getD 0 + 1)) st.stats.fired
        chooseBest { st with stats := { st.stats with fired } } v (cands.filter (st.candOk v)) :=
  rfl

/-- The graph is a model of the valuation. -/
theorem graphModel (P : SState → Prop) (hP : ∀ st, P st → GInv f ρ fr mem st) :
    GraphModel SState.enodes (fun st x => st.types.get? x) P (gval ρ fr mem) fr mem where
  nodes := by
    intro st x a hst hx n hn
    have h := hP st hst
    simp only [SState.enodes, List.mem_append, Option.mem_toList, List.mem_filterMap] at hn
    rcases hn with hn | ⟨m, hm, hn⟩
    · rw [← hx]; exact (den_node (graph_of_defs hn)).symm
    · cases hal : st.alts.get? x with
      | none => rw [hal] at hm; simp at hm
      | some ms =>
        rw [hal] at hm
        have := (h.alts x ms hal).2 m hm a hx
        rw [← this]; exact (den_node (graph_of_defs hn)).symm
  types := by
    intro st x t a hst ht hx
    exact (hP st hst).types x t a ht hx

theorem gval_unknown_eval {st : SState} (h : GInv f ρ fr mem st) {n : Inst} {b : Val}
    (hn : (operands n).all st.inGraph = false)
    (he : evalNode (withRegs fr (gval ρ fr mem st)) mem n = some b) : False := by
  simp only [List.all_eq_false] at hn
  obtain ⟨y, hy, hk⟩ := hn
  simp only [Bool.not_eq_true] at hk
  obtain ⟨a, ha⟩ := evalInst_ops (evalNode_ok he) y hy
  simp only [gval_unknown h hk] at ha
  cases ha

/-- `make` on a node over a value outside the graph: a fresh value with no node. -/
theorem make_dummy_sound {st0 st1 : SState} (h1 : GInv f ρ fr mem st1)
    (g1 : Grow ρ fr mem st0 st1) {n : Inst} (hn : (operands n).all st1.inGraph = false) :
    (GInv f ρ fr mem st1.dummy.2 ∧ Grow ρ fr mem st0 st1.dummy.2) ∧
      Valuation.Le (gval ρ fr mem st1) (gval ρ fr mem st1.dummy.2) ∧
      ∀ b, evalNode (withRegs fr (gval ρ fr mem st1)) mem n = some b →
        gval ρ fr mem st1.dummy.2 st1.dummy.1 = some b := by
  have hd := h1.of_same (st' := st1.dummy.2) rfl rfl rfl rfl rfl rfl (Nat.le_succ _) rfl rfl rfl rfl
  refine ⟨⟨hd.1, g1.trans hd.2⟩, fun x a hx => ?_, fun b hb => (gval_unknown_eval h1 hn hb).elim⟩
  rw [hd.2.fix x (inGraph_of_gval h1 hx)]; exact hx

/-- `make` recording a partial node. -/
theorem make_partial_sound {st0 st1 : SState} (h1 : GInv f ρ fr mem st1)
    (g1 : Grow ρ fr mem st0 st1) {n : Inst} (hn : (operands n).all st1.inGraph = true) :
    (GInv f ρ fr mem (st1.insertPartial n).2 ∧ Grow ρ fr mem st0 (st1.insertPartial n).2) ∧
      Valuation.Le (gval ρ fr mem st1) (gval ρ fr mem (st1.insertPartial n).2) ∧
      ∀ b, evalNode (withRegs fr (gval ρ fr mem st1)) mem n = some b →
        gval ρ fr mem (st1.insertPartial n).2 (st1.insertPartial n).1 = some b := by
  obtain ⟨i2, g2, v2⟩ := insertPartial_spec h1 (by simpa using hn)
  refine ⟨⟨i2, g1.trans g2⟩, fun x a hx => ?_, fun b hb => by rw [v2]; exact hb⟩
  rw [g2.fix x (inGraph_of_gval h1 hx)]; exact hx

theorem nodeOk_typed_of {st : SState} {n : Inst} {b : Bool}
    (hc : ¬((!st.nodeOk n || b || !st.typedNode n) = true)) :
    st.nodeOk n = true ∧ b = false ∧ st.typedNode n = true := by
  cases h1 : st.nodeOk n <;> cases b <;> cases h2 : st.typedNode n <;> simp_all

section Opt

variable {rules : SimplifyFn} {allowed : Inst → Bool}

theorem optimizeAt_spec (hS : SimplifySound rules) (hE : GoodEnv f fr mem) :
    ∀ d st v, GInv f ρ fr mem st → st.known v = true →
      GInv f ρ fr mem (optimizeAt rules allowed d st v).2 ∧
      Grow ρ fr mem st (optimizeAt rules allowed d st v).2 ∧
      ∀ a, gval ρ fr mem st v = some a →
        gval ρ fr mem (optimizeAt rules allowed d st v).2 (optimizeAt rules allowed d st v).1 = some a := by
  intro d
  induction d with
  | zero => intro st v h _; exact ⟨h, Grow.refl st, fun _ ha => ha⟩
  | succ d ih =>
    intro st v h hv
    let P : SState → Prop := fun st' => GInv f ρ fr mem st' ∧ Grow ρ fr mem st st'
    have hG := graphModel (f := f) (ρ := ρ) (fr := fr) (mem := mem) P (fun _ h => h.1)
    have hM : MakeSound (optMake rules allowed d v) P (gval ρ fr mem) fr mem := by
      intro st1 n hP1
      obtain ⟨h1, g1⟩ := hP1
      unfold optMake
      cases hin : (operands n).all st1.inGraph with
      | false =>
        simp only [Bool.not_false, ite_true]
        exact make_dummy_sound h1 g1 hin
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        split
        · exact make_partial_sound h1 g1 hin
        rename_i hc
        obtain ⟨hok, -, hty⟩ := nodeOk_typed_of hc
        have hkn : ∀ y ∈ operands n, st1.known y = true := by
          simpa [SState.nodeOk] using hok
        cases hm : st1.memo.get? n with
        | some w =>
          exact ⟨⟨h1, g1⟩, fun _ _ h => h, fun b hb => (h1.memo n w hm).2 b hb⟩
        | none =>
          obtain ⟨e1, ed, et, enx, ea, eal, em, ef, etr, er⟩ := insertNode_fields allowed st1 n
          have ec : (st1.insertNode allowed n).2.classes = st1.classes := rfl
          have ep : (st1.insertNode allowed n).2.partials = st1.partials := rfl
          rcases hins : st1.insertNode allowed n with ⟨w, st2⟩
          rw [hins] at e1 ed et enx ea eal em ef etr er ec ep
          simp only at e1 ed et enx ea eal em ef etr er ec ep
          subst e1
          obtain ⟨i2, g2, k2, v2, f2⟩ := insert_spec (st' := st2) h1 hE hok hty ed et enx ea eal em
            ef etr er ec ep
          obtain ⟨i3, g3, v3⟩ := ih st2 st1.next i2 k2
          generalize optimizeAt rules allowed d st2 st1.next = r at i3 g3 v3 ⊢
          obtain ⟨b, st3⟩ := r
          simp only at i3 g3 v3 ⊢
          have hb : ∀ a, evalNode (withRegs fr (gval ρ fr mem st3)) mem n = some a →
              gval ρ fr mem st3 b = some a := by
            intro a ha
            apply v3 a
            rw [v2, ← ha]
            exact (evalNode_congr (fr := withRegs fr (gval ρ fr mem st1))
              (fr' := withRegs fr (gval ρ fr mem st3)) rfl rfl rfl
              (fun y hy => ((g2.trans g3).fix y (inGraph_of_known (hkn y hy))))).symm
          obtain ⟨i4, g4⟩ := memo_insert_spec (st' := { st3 with memo := st3.memo.insert n b })
            i3 (fun y hy => (g2.trans g3).known y (hkn y hy)) hb rfl rfl rfl rfl rfl rfl
            (Nat.le_refl _) rfl rfl rfl rfl
          have g := g1.trans (g2.trans (g3.trans g4))
          refine ⟨⟨i4, g⟩, fun x a hx => ?_, fun c hc => ?_⟩
          · rw [(g2.trans (g3.trans g4)).fix x (inGraph_of_gval h1 hx)]; exact hx
          · have : gval ρ fr mem st2 st1.next = some c := by rw [v2]; exact hc
            have := v3 c this
            rw [g4.fix _ (inGraph_of_gval i3 this)]; exact this
    rw [optimizeAt_succ]
    split
    · -- rules error
      have hd := h.of_same (st' := { st with stats := { st.stats with errors := st.stats.errors + 1 } })
        rfl rfl rfl rfl rfl rfl (Nat.le_refl _) rfl rfl rfl rfl
      exact ⟨hd.1, hd.2, fun a ha => by rw [hd.2.fix v (inGraph_of_known hv)]; exact ha⟩
    · rename_i cands names st1 hr
      obtain ⟨⟨h1, g1⟩, -, hc⟩ := hS SState.enodes (fun st x => st.types.get? x)
        (optMake rules allowed d v) P (gval ρ fr mem) fr mem hG hM st v cands names st1 ⟨h, Grow.refl st⟩ hr
      dsimp only
      generalize names.foldl (fun m n => m.insert n ((m.get? n).getD 0 + 1)) st1.stats.fired = fired
      generalize hcf : cands.filter (st1.candOk v) = cf
      have hcf' : ∀ c ∈ cf, c ∈ cands := by
        rw [← hcf]; exact fun c h => (List.mem_filter.1 h).1
      obtain ⟨h1', g1'⟩ := h1.of_same (st' := { st1 with stats := { st1.stats with fired } })
        rfl rfl rfl rfl rfl rfl (Nat.le_refl _) rfl rfl rfl rfl
      obtain ⟨hb, ⟨cl, hcl⟩, hcls⟩ := chooseBest_spec { st1 with stats := { st1.stats with fired } } v cf
      generalize chooseBest { st1 with stats := { st1.stats with fired } } v cf = r at hb hcl hcls ⊢
      obtain ⟨b, st2⟩ := r
      simp only at hb hcl hcls ⊢
      have g11 := g1.trans g1'
      have hfwd : ∀ a, gval ρ fr mem st v = some a → ∀ x, (x = v ∨ ∃ c ∈ cf, c.1 = x) →
          gval ρ fr mem { st1 with stats := { st1.stats with fired } } x = some a := by
        intro a ha x hx
        rcases hx with rfl | ⟨c, hc', rfl⟩
        · rw [g11.fix _ (inGraph_of_known hv)]; exact ha
        · have := hc a ha c (hcf' c hc')
          rw [g1'.fix _ (inGraph_of_gval h1 this)]; exact this
      have g2 : Grow ρ fr mem { st1 with stats := { st1.stats with fired } } st2 := by
        rw [hcl]; exact Grow.of_graph rfl rfl rfl rfl rfl rfl rfl
      have hg2 : gval ρ fr mem st2 = gval ρ fr mem { st1 with stats := { st1.stats with fired } } := by
        rw [hcl]; rfl
      refine ⟨?_, g11.trans g2, fun a ha => by rw [hg2]; exact hfwd a ha b hb⟩
      rw [hcl]
      refine h1'.of_graph rfl rfl rfl rfl (Nat.le_refl _) rfl (by exact h1'.alts) (by exact h1'.memo) ?_
      intro k ms hk
      have hk' : ({ st1 with stats := { st1.stats with fired }, classes := cl } : SState).classes.get? k =
          some ms := hk
      rw [← hcl] at hk'
      rcases hcls k ms hk' with hold | ⟨hkb, hms⟩
      · exact h1'.classes k ms hold
      · refine ⟨v, g11.known v hv, fun a ha => ?_⟩
        have ha' : gval ρ fr mem st v = some a := by rw [← g11.fix _ (inGraph_of_known hv)]; exact ha
        exact ⟨by rw [hkb]; exact hfwd a ha' b hb, fun m hm => hfwd a ha' m (hms m hm)⟩

/-- `make` for the skeleton rules keeps the invariant. -/
theorem skelMake_sound (hS : SimplifySound rules) (hE : GoodEnv f fr mem) (st0 : SState) :
    MakeSound (skelMake rules allowed) (fun st' => GInv f ρ fr mem st' ∧ Grow ρ fr mem st0 st')
      (gval ρ fr mem) fr mem := by
  intro st1 n hP1
  obtain ⟨h1, g1⟩ := hP1
  unfold skelMake
  cases hin : (operands n).all st1.inGraph with
  | false =>
    simp only [Bool.not_false, ite_true]
    exact make_dummy_sound h1 g1 hin
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    split
    · exact make_partial_sound h1 g1 hin
    rename_i hc
    obtain ⟨hok, -, hty⟩ := nodeOk_typed_of (b := false) (by simpa using hc)
    have hkn : ∀ y ∈ operands n, st1.known y = true := by
      simpa [SState.nodeOk] using hok
    cases hm : st1.memo.get? n with
    | some w =>
      exact ⟨⟨h1, g1⟩, fun _ _ h => h, fun b hb => (h1.memo n w hm).2 b hb⟩
    | none =>
      obtain ⟨e1, ed, et, enx, ea, eal, em, ef, etr, er⟩ := insertNode_fields allowed st1 n
      have ec : (st1.insertNode allowed n).2.classes = st1.classes := rfl
      have ep : (st1.insertNode allowed n).2.partials = st1.partials := rfl
      rcases hins : st1.insertNode allowed n with ⟨w, st2⟩
      rw [hins] at e1 ed et enx ea eal em ef etr er ec ep
      simp only at e1 ed et enx ea eal em ef etr er ec ep
      subst e1
      obtain ⟨i2, g2, k2, v2, f2⟩ := insert_spec (st' := st2) h1 hE hok hty ed et enx ea eal em ef
        etr er ec ep
      have hb2 : ∀ a, evalNode (withRegs fr (gval ρ fr mem st2)) mem n = some a →
          gval ρ fr mem st2 st1.next = some a := by
        intro a ha
        rw [v2, ← ha]
        exact (evalNode_congr (fr := withRegs fr (gval ρ fr mem st1))
          (fr' := withRegs fr (gval ρ fr mem st2)) rfl rfl rfl
          (fun y hy => f2 y (inGraph_of_known (hkn y hy)))).symm
      obtain ⟨i2', g2'⟩ := memo_insert_spec (st' := { st2 with memo := st2.memo.insert n st1.next })
        i2 (fun y hy => g2.known y (hkn y hy)) hb2 rfl rfl rfl rfl rfl rfl (Nat.le_refl _) rfl
        rfl rfl rfl
      obtain ⟨i3, g3, v3⟩ := optimizeAt_spec (allowed := allowed) hS hE rewriteLimit _ st1.next i2' k2
      generalize optimizeAt rules allowed rewriteLimit { st2 with memo := st2.memo.insert n st1.next }
        st1.next = r at i3 g3 v3 ⊢
      obtain ⟨b, st3⟩ := r
      simp only at i3 g3 v3 ⊢
      have g23 := g2.trans (g2'.trans g3)
      have hk2 : st2.inGraph st1.next = true := inGraph_of_known k2
      have hb : ∀ a, evalNode (withRegs fr (gval ρ fr mem st3)) mem n = some a →
          gval ρ fr mem st3 b = some a := by
        intro a ha
        apply v3 a
        rw [g2'.fix _ hk2, v2, ← ha]
        exact (evalNode_congr (fr := withRegs fr (gval ρ fr mem st1))
          (fr' := withRegs fr (gval ρ fr mem st3)) rfl rfl rfl
          (fun y hy => (g23.fix y (inGraph_of_known (hkn y hy))))).symm
      obtain ⟨i4, g4⟩ := memo_insert_spec (st' := { st3 with memo := st3.memo.insert n b })
        i3 (fun y hy => g23.known y (hkn y hy)) hb rfl rfl rfl rfl rfl rfl
        (Nat.le_refl _) rfl rfl rfl rfl
      refine ⟨⟨i4, g1.trans (g23.trans g4)⟩, fun x a hx => ?_, fun c hc => ?_⟩
      · rw [(g23.trans g4).fix x (inGraph_of_gval h1 hx)]; exact hx
      · have h0 : gval ρ fr mem st2 st1.next = some c := by rw [v2]; exact hc
        have := v3 c (by rw [g2'.fix _ hk2]; exact h0)
        rw [g4.fix _ (inGraph_of_gval i3 this)]; exact this

theorem chooseSkel_go_mem {l : List Isle.Opt.SkelSimp} {best : Option Isle.Opt.SkelSimp}
    {cost : Nat} {c : Isle.Opt.SkelSimp} (h : chooseSkel.go l best cost = some c) :
    c ∈ l ∨ best = some c := by
  induction l generalizing best cost with
  | nil => exact .inr h
  | cons d ds ih =>
    simp only [chooseSkel.go] at h
    split at h
    all_goals first
      | (cases h; exact .inl (by simp))
      | (split at h
         · rcases ih h with h' | h'
           · exact .inl (by simp [h'])
           · cases h'; exact .inl (by simp)
         · rcases ih h with h' | h'
           · exact .inl (by simp [h'])
           · exact .inr h')

theorem chooseSkel_mem {orig : Isle.Opt.SkelInst} {cands : List Isle.Opt.SkelSimp}
    {c : Isle.Opt.SkelSimp} (h : chooseSkel orig cands = some c) : c ∈ cands := by
  rcases chooseSkel_go_mem h with h | h
  · exact List.mem_of_mem_take (List.mem_reverse.1 h)
  · cases h

/-- An undefined read (`skelReads`) makes the original instruction or terminator stuck, so every
simplification refines it. -/
theorem skelRefines_of_undef {tb : BlockId → Option TrapCode} {fr : Frame} {mem : Mem}
    {i : Isle.Opt.SkelInst} {y : ValueId} (hy : y ∈ skelReads i) (hn : fr.regs y = none)
    (c : Isle.Opt.SkelSimp) : SkelRefines tb fr mem i c := by
  cases i with
  | inst i =>
    obtain ⟨m, hm⟩ : ∃ m, evalInst fr mem i = .stuck m := by
      cases he : evalInst fr mem i with
      | stuck m => exact ⟨m, rfl⟩
      | ok r =>
        obtain ⟨a, ha⟩ := evalInst_ops (fun m h => by rw [he] at h; cases h) y hy
        rw [hn] at ha; cases ha
      | trap t =>
        obtain ⟨a, ha⟩ := evalInst_ops (fun m h => by rw [he] at h; cases h) y hy
        rw [hn] at ha; cases ha
    unfold SkelRefines
    split <;> (try split) <;> simp_all [ResRefines]
  | term t =>
    obtain ⟨m, hm⟩ : ∃ m, termEval fr mem t = .stuck m := by
      cases t <;> simp only [skelReads, List.mem_singleton, List.not_mem_nil] at hy
      all_goals
        subst hy
        exact ⟨_, by simp [termEval, Frame.get, hn, Res.ofOption, bind, Res.bind]; rfl⟩
    unfold SkelRefines
    split <;> (try split) <;> simp_all [BrRefines, seqEval]

/-- A skeleton simplification chosen by `runSkel` refines the instruction or terminator. -/
theorem runSkel_spec {skel : SkeletonFn} (hS : SimplifySound rules) (hK : SkeletonSound skel)
    (hE : GoodEnv f fr mem) {st : SState} (h : GInv f ρ fr mem st) (i : Isle.Opt.SkelInst)
    (hk : ∀ y ∈ skelReads i, st.known y = true) :
    GInv f ρ fr mem (runSkel skel rules allowed st i).2 ∧
      Grow ρ fr mem st (runSkel skel rules allowed st i).2 ∧
      ∀ c, (runSkel skel rules allowed st i).1 = some c →
        SkelRefines (fun b => st.trapBlocks.get? b)
          (withRegs fr (gval ρ fr mem (runSkel skel rules allowed st i).2)) mem i c := by
  simp only [runSkel]
  split
  · exact ⟨h, Grow.refl st, fun c hc => by cases hc⟩
  · obtain ⟨h0, g0⟩ := h.of_same (st' := { st with made := {} }) rfl rfl rfl rfl rfl rfl
      (Nat.le_refl _) rfl rfl rfl rfl
    split
    · have hd := h.of_same (st' := { st with stats := { st.stats with errors := st.stats.errors + 1 } })
        rfl rfl rfl rfl rfl rfl (Nat.le_refl _) rfl rfl rfl rfl
      exact ⟨hd.1, hd.2, fun c hc => by cases hc⟩
    · rename_i cands names st1 hr
      let P : SState → Prop := fun st' => GInv f ρ fr mem st' ∧ Grow ρ fr mem { st with made := {} } st'
      obtain ⟨⟨h1, g1⟩, -, hc⟩ := hK SState.enodes (fun st x => st.types.get? x)
        (skelMake rules allowed) (fun st b => st.trapBlocks.get? b) P (gval ρ fr mem) fr mem
        (fun b => st.trapBlocks.get? b)
        (graphModel P (fun _ h => h.1)) (skelMake_sound hS hE _)
        (fun st' hP => by funext b; rw [hP.2.trap]) { st with made := {} } i cands names st1
        ⟨h0, Grow.refl _⟩ hr
      generalize names.foldl (fun m n => m.insert n ((m.get? n).getD 0 + 1)) st1.stats.fired = fired
      have g01 := g0.trans g1
      split
      · rename_i c hch
        let st2 : SState := { st1 with stats := { st1.stats with fired, skeleton := st1.stats.skeleton + 1 } }
        obtain ⟨h2, g2⟩ := h1.of_same (st' := st2) rfl rfl rfl rfl rfl rfl (Nat.le_refl _) rfl rfl
          rfl rfl
        refine ⟨h2, g01.trans g2, fun c' hc' => ?_⟩
        have hc2 : chooseSkel i (cands.filter (skelCandOk st1 i)) = some c' := hc'
        rw [hch] at hc2; cases hc2
        by_cases hd : ∀ y ∈ skelReads i, ∃ a, gval ρ fr mem { st with made := {} } y = some a
        · exact hc hd c (List.mem_filter.1 (chooseSkel_mem hch)).1
        · -- an undefined read: known, so still undefined, and the original is stuck
          simp only [Classical.not_forall, not_exists] at hd
          obtain ⟨y, hy, hn⟩ := hd
          apply skelRefines_of_undef hy
          show gval ρ fr mem st2 y = none
          rw [(g01.trans g2).fix y (inGraph_of_known (hk y hy))]
          exact Option.eq_none_iff_forall_ne_some.2 hn
      · obtain ⟨h2, g2⟩ := h1.of_same (st' := { st1 with stats := { st1.stats with fired } })
          rfl rfl rfl rfl rfl rfl (Nat.le_refl _) rfl rfl rfl rfl
        exact ⟨h2, g01.trans g2, fun c hc => by cases hc⟩

end Opt

end Graph

end Opt
