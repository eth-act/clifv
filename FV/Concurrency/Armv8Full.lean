module

public import FV.Concurrency.ArmFence

@[expose] public section

/-!
# The full Armv8 model and monotonicity (T2g, #305)

`Armv8.Consistent` is the Armv8 axiomatic model restricted to the clauses the instructions
Cranelift emits need (`FV/Concurrency/Armv8.lean`). Here is the whole model of `aarch64.cat`
(Arm ARM B2.3; Pulte et al., *Simplifying ARM concurrency*, POPL 2018, Fig. 6), over the event
kinds of every load, store and barrier class (`FKind`: the fragment's, `ldapr` (`Q`), `dmb ld`,
`dmb st`, `isb`) and the dependencies of an execution (`Deps`: `addr`, `data`, `ctrl`):

* internal: `acyclic(po-loc ∪ rf ∪ co ∪ fr)`; atomic: `rmw ∩ (fre; coe) = ∅`;
* external: `acyclic(ob)`, `ob = obs ∪ dob ∪ aob ∪ bob` with
  * `dob = addr ∪ data ∪ ctrl;[W] ∪ (ctrl ∪ addr;po);[ISB];po;[R] ∪ addr;po;[W] ∪ (addr ∪ data);rfi`,
  * `aob = rmw ∪ [range(rmw)];rfi;[A ∪ Q]`,
  * `bob = po;[dmb];po ∪ [L];po;[A] ∪ [R];po;[dmb ld];po ∪ [A ∪ Q];po ∪ [W];po;[dmb st];po;[W]
    ∪ po;[L] ∪ po;[L];coi`.

**Monotonicity** (`consistent_frag`): an execution of fragment kinds (what Cranelift emits:
`Code.lines_kinds`) that is consistent for the full model, with *any* dependencies, is
`Armv8.Consistent`: every fragment clause is a clause of the full model. So every theorem of the form
"every `Armv8.Consistent` execution …" (`Mapping.armv8_to_clif`, `armv8_to_clifF`,
`ProgE2E.program_correct*`) holds for Armv8 itself. The converse fails (the fragment ignores
dependencies): `MP+dmb+addr` is fragment-consistent and not Armv8-consistent
(`FVTest/Concurrency/LitmusFull.lean`).
-/

namespace Concurrency

open Rel

/-- The event kinds of the full model. -/
inductive FKind where
  /-- a kind of the fragment -/
  | frag (a : AKind)
  /-- `ldapr` (acquirePC, `Q`) -/
  | acqPcR
  /-- `dmb ld` -/
  | dmbLd
  /-- `dmb st` -/
  | dmbSt
  /-- `isb` -/
  | isb
  deriving DecidableEq, Repr

namespace Armv8Full

/-- The dependencies of an execution: address, data and control. -/
structure Deps (E : Type) where
  addr : Rel E
  data : Rel E
  ctrl : Rel E

variable {E : Type} (X : Exec E) (k : E → FKind) (d : Deps E)

/-- Acquire reads (`ldar`, `ldaxr`). -/
def A (e : E) : Prop := k e = .frag .acqR ∨ k e = .frag .acqXR

/-- AcquirePC reads (`ldapr`). -/
def Q (e : E) : Prop := k e = .acqPcR

/-- Release writes (`stlr`, `stlxr`). -/
def L (e : E) : Prop := k e = .frag .relW ∨ k e = .frag .relXW

/-- Internal reads-from. -/
def rfi (a b : E) : Prop := X.rf a b ∧ X.tid a = X.tid b

/-- Internal coherence. -/
def coi (a b : E) : Prop := X.co a b ∧ X.tid a = X.tid b

/-- Dependency-ordered-before. -/
def dob (a b : E) : Prop :=
  d.addr a b ∨ d.data a b ∨ (d.ctrl a b ∧ X.dir b = .W) ∨
    (∃ i, (d.ctrl a i ∨ ∃ c, d.addr a c ∧ X.po c i) ∧ k i = .isb ∧ X.po i b ∧ X.dir b = .R) ∨
    (∃ c, d.addr a c ∧ X.po c b ∧ X.dir b = .W) ∨
    (∃ c, (d.addr a c ∨ d.data a c) ∧ rfi X c b)

/-- Atomic-ordered-before. -/
def aob (a b : E) : Prop :=
  X.rmw a b ∨ ((∃ c, X.rmw c a) ∧ rfi X a b ∧ (A k b ∨ Q k b))

/-- Barrier-ordered-before. -/
def bob (a b : E) : Prop :=
  (∃ f, X.po a f ∧ k f = .frag .dmb ∧ X.po f b) ∨ (L k a ∧ X.po a b ∧ A k b) ∨
    (X.dir a = .R ∧ ∃ f, X.po a f ∧ k f = .dmbLd ∧ X.po f b) ∨ ((A k a ∨ Q k a) ∧ X.po a b) ∨
    (X.dir a = .W ∧ (∃ f, X.po a f ∧ k f = .dmbSt ∧ X.po f b) ∧ X.dir b = .W) ∨
    (X.po a b ∧ L k b) ∨ (∃ c, X.po a c ∧ L k c ∧ coi X c b)

/-- Ordered-before (one step). -/
def ob (a b : E) : Prop := Armv8.obs X a b ∨ dob X k d a b ∨ aob X k a b ∨ bob X k a b

/-- **Armv8 consistency** (`aarch64.cat`). -/
structure Consistent : Prop where
  internal : Acyclic (union X.poLoc X.com)
  atomic : ∀ a b, X.rmw a b → ¬ ∃ c, X.ext X.fr a c ∧ X.ext X.co c b
  external : Acyclic (ob X k d)

variable {X d}

/-- The fragment's `ob` is in the full model's (any dependencies). -/
theorem ob_frag {ak : E → AKind} {a b : E} (h : Armv8.ob X ak a b) :
    ob X (fun e => .frag (ak e)) d a b := by
  have hA : ∀ e, Armv8.A ak e → A (fun e => .frag (ak e)) e := fun e h => by
    rcases h with h | h <;> simp [A, h]
  have hL : ∀ e, Armv8.L ak e → L (fun e => .frag (ak e)) e := fun e h => by
    rcases h with h | h <;> simp [L, h]
  rcases h with h | h | ⟨f, h1, hf, h2⟩ | ⟨ha, h, hb⟩ | ⟨ha, h⟩ | ⟨h, hb⟩
  · exact .inl h
  · exact .inr (.inr (.inl (.inl h)))
  · exact .inr (.inr (.inr (.inl ⟨f, h1, by simp [hf], h2⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨hL a ha, h, hA b hb⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨.inl (hA a ha), h⟩))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h, hL b hb⟩))))))))

/-- **Monotonicity: the fragment model is weaker than Armv8.** An execution of the fragment's
kinds that is consistent for the full `aarch64.cat` model, with any dependencies, is
`Armv8.Consistent`. -/
theorem consistent_frag {ak : E → AKind} (hc : Consistent X (fun e => .frag (ak e)) d) :
    Armv8.Consistent X ak where
  internal := hc.internal
  atomic := hc.atomic
  external := hc.external.mono fun _ _ h => ob_frag h

end Armv8Full

/-- **Theorem 2 for Armv8 itself** (`Mapping.armv8_to_clif` with the full model). -/
theorem Mapping.armv8full_to_clif {E : Type} {X : Exec E} {ak : E → AKind} {S : E → Prop}
    {sk : E → SKind} (d : Armv8Full.Deps E) (hX : X.Wf)
    (hc : Armv8Full.Consistent X (fun e => .frag (ak e)) d) (hm : Compiled X ak S sk) :
    ClifMM.Consistent (X.restrict S) (srcKind sk S) :=
  armv8_to_clif hX (Armv8Full.consistent_frag hc) hm

/-- **`fence` ↦ `dmb ish` sound for Armv8 itself** (`Mapping.armv8_to_clifF` with the full
model). -/
theorem Mapping.armv8full_to_clifF {E : Type} {X : Exec E} {ak : E → AKind} {S : E → Prop}
    {sk : E → SKind} (d : Armv8Full.Deps E) (hX : X.Wf) (hm : Compiled X ak S sk)
    (hk : Armv8.KindOk X ak) (hc : Armv8Full.Consistent X (fun e => .frag (ak e)) d)
    (hrmw : RmwSc X S sk) : ClifMM.ConsistentF (X.restrict S) (srcKind sk S) :=
  armv8_to_clifF hX hm hk (Armv8Full.consistent_frag hc) hrmw

end Concurrency
