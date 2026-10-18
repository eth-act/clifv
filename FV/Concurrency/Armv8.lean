import FV.Concurrency.Exec

/-!
# The Armv8 axiomatic model, restricted to what Cranelift emits (T2, #38)

The memory events of the instructions Cranelift's aarch64 backend emits with cg_clif's flags
(`has_lse = 0`): plain loads and stores, `ldar` (acquire load), `stlr` (release store), `ldaxr`
(acquire exclusive load), `stlxr` (release exclusive store; only a successful one is a write event),
and `dmb ish` (a full barrier). `FV/Concurrency/Code.lean` assigns these kinds to `Backend.Insn`.

The model is the Armv8 axiomatic model of the Arm ARM (B2.3, "Definition of the Armv8 memory
model"; herd's `aarch64.cat`; Pulte et al., *Simplifying ARM concurrency*, POPL 2018):

* internal: `acyclic(po-loc ∪ rf ∪ co ∪ fr)`;
* atomic: `rmw ∩ (fre; coe) = ∅`;
* external: `acyclic(ob)`, `ob = obs ∪ aob ∪ bob`, `obs = rfe ∪ coe ∪ fre`, `aob = rmw`,
  `bob = po;[dmb];po ∪ [L];po;[A] ∪ [A];po ∪ po;[L]` (`A`: `ldar`/`ldaxr`, `L`: `stlr`/`stlxr`).

Each clause is a clause of the official model. The omitted ones (`dob`, the `[range(rmw)];rfi;[A|Q]`
part of `aob`, `po;[L];coi`, `dmb.ld`/`dmb.st`, `Q`) only add order, so this model allows every
execution Armv8 allows: a theorem "every `Consistent` execution …" holds for Armv8 itself
(`docs/plans/atomics.md` §2). The existing single-core Arm model (`docs/decisions/arm-model.md`,
"Atomics") is not changed.
-/

namespace Concurrency

open Rel

/-- Memory-event kinds of the Arm fragment. -/
inductive AKind where
  /-- `ldr*`, `ldp`, … -/
  | plainR
  /-- `str*`, `stp`, … -/
  | plainW
  /-- `ldar{b,h,}` -/
  | acqR
  /-- `stlr{b,h,}` -/
  | relW
  /-- `ldaxr{b,h,}` -/
  | acqXR
  /-- a successful `stlxr{b,h,}` -/
  | relXW
  /-- `dmb ish` -/
  | dmb
  deriving DecidableEq, Repr

/-- Direction of an event of a kind. -/
def AKind.dir : AKind → Dir
  | .plainR | .acqR | .acqXR => .R
  | .plainW | .relW | .relXW => .W
  | .dmb => .F

namespace Armv8

variable {E : Type} (X : Exec E) (k : E → AKind)

/-- The kinds agree with the execution's directions. -/
def KindOk : Prop := ∀ e, (k e).dir = X.dir e

/-- Acquire reads (`ldar`, `ldaxr`). -/
def A (e : E) : Prop := k e = .acqR ∨ k e = .acqXR

/-- Release writes (`stlr`, `stlxr`). -/
def L (e : E) : Prop := k e = .relW ∨ k e = .relXW

/-- Observed-by: `rfe ∪ coe ∪ fre`. -/
def obs : Rel E := fun a b => X.ext X.rf a b ∨ X.ext X.co a b ∨ X.ext X.fr a b

/-- Barrier-ordered-before, the clauses of the fragment. -/
def bob : Rel E := fun a b =>
  (∃ f, X.po a f ∧ k f = .dmb ∧ X.po f b) ∨ (L k a ∧ X.po a b ∧ A k b) ∨
    (A k a ∧ X.po a b) ∨ (X.po a b ∧ L k b)

/-- Ordered-before (one step): `obs ∪ aob ∪ bob` with `aob = rmw`. -/
def ob : Rel E := fun a b => obs X a b ∨ X.rmw a b ∨ bob X k a b

/-- **Armv8 consistency** (the fragment). -/
structure Consistent : Prop where
  internal : Acyclic (union X.poLoc X.com)
  atomic : ∀ a b, X.rmw a b → ¬ ∃ c, X.ext X.fr a c ∧ X.ext X.co c b
  external : Acyclic (ob X k)

variable {X k}

/-- `[A]; po ⊆ ob` (`ldar`, `ldaxr`). -/
theorem ob_acq {a b : E} (ha : A k a) (h : X.po a b) : ob X k a b :=
  .inr (.inr (.inr (.inr (.inl ⟨ha, h⟩))))

/-- `po; [L] ⊆ ob` (`stlr`, `stlxr`). -/
theorem ob_rel {a b : E} (h : X.po a b) (hb : L k b) : ob X k a b :=
  .inr (.inr (.inr (.inr (.inr ⟨h, hb⟩))))

/-- `[L]; po; [A] ⊆ ob`: a release followed by an acquire is ordered (Armv8 is RCsc). -/
theorem ob_rel_acq {a b : E} (ha : L k a) (h : X.po a b) (hb : A k b) : ob X k a b :=
  .inr (.inr (.inr (.inl ⟨ha, h, hb⟩)))

/-- **`fence` ↦ `dmb ish`**: the barrier orders every event before it with every event after
it. -/
theorem ob_dmb {a f b : E} (h1 : X.po a f) (hf : k f = .dmb) (h2 : X.po f b) : ob X k a b :=
  .inr (.inr (.inl ⟨f, h1, hf, h2⟩))

/-- External communication is in `ob`. -/
theorem ob_ext {a b : E} (h : X.com a b) (ht : X.tid a ≠ X.tid b) : ob X k a b := by
  rcases h with h | h | h
  · exact .inl (.inl ⟨h, ht⟩)
  · exact .inl (.inr (.inl ⟨h, ht⟩))
  · exact .inl (.inr (.inr ⟨h, ht⟩))

/-- `po` between acquire/release accesses is in `ob`. -/
theorem ob_po_AL {a b : E} (ha : A k a ∨ L k a) (hb : A k b ∨ L k b) (h : X.po a b) :
    ob X k a b := by
  rcases ha with ha | ha
  · exact ob_acq ha h
  · rcases hb with hb | hb
    · exact ob_rel_acq ha h hb
    · exact ob_rel h hb

/-- `com` is `ob` (external) or `po` (internal). -/
theorem com_ob_or_po (hX : X.Wf) (hc : Consistent X k) {a b : E} (h : X.com a b) :
    ob X k a b ∨ X.po a b := by
  by_cases ht : X.tid a = X.tid b
  · exact .inr (hX.com_int_po hc.internal h ht)
  · exact .inl (ob_ext h ht)

/-- **Theorem 1: the acquire/release accesses are sequentially consistent.** In an Armv8-consistent
execution, `po ∪ com` restricted to `ldar`/`ldaxr`/`stlr`/`stlxr` events is acyclic. -/
theorem atomics_sc (hX : X.Wf) (hc : Consistent X k) :
    Acyclic (restr (fun e => A k e ∨ L k e) (union X.po X.com)) := by
  refine hc.external.mono ?_
  rintro a b ⟨ha, h | h, hb⟩
  · exact ob_po_AL ha hb h
  · rcases com_ob_or_po hX hc h with h | h
    · exact h
    · exact ob_po_AL ha hb h

end Armv8

end Concurrency
