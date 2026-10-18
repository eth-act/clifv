import FV.Concurrency.Exec

/-!
# The Cranelift memory-model contract for CLIF (T2, #38)

Cranelift has no formal memory model. Its instruction documentation
(`cranelift/codegen/meta/src/shared/instructions.rs`) says every `atomic_load`, `atomic_store`,
`atomic_rmw` and `atomic_cas` "is sequentially consistent and creates happens-before edges that
order normal (non-atomic) loads and stores", and that `fence` is sequentially consistent and keeps
loads and stores of any kind from moving across it. cg_clif maps every Rust atomic ordering to these
operations (`rustc_codegen_cranelift/src/intrinsics/mod.rs` ignores the ordering). The contract is
therefore C++20/RC11 (Lahav et al., PLDI 2017) restricted to `seq_cst` accesses, non-atomic accesses
and `seq_cst` fences:

* `sw = [scW]; rf; [scR]`, `hb = (po ∪ sw)⁺`, `eco = com⁺`;
* coherence: `irreflexive(hb; eco?)`;
* atomicity: `rmw ∩ (fr; co) = ∅`;
* SC: `acyclic((po ∪ com)|At)` for the atomic accesses `At`.

RC11's `acyclic(po ∪ rf)` is not part of it: Armv8 does not give it for plain accesses, and such a
cycle through plain accesses is a race (undefined behaviour in Rust). `drf_sc`: a consistent
race-free execution is sequentially consistent. Plan: `docs/plans/atomics.md`.
-/

namespace Concurrency

open Rel

/-- Memory-event kinds of CLIF. -/
inductive SKind where
  /-- `load` (non-atomic) -/
  | naR
  /-- `store` (non-atomic) -/
  | naW
  /-- `atomic_load`, the read of `atomic_rmw`/`atomic_cas` -/
  | scR
  /-- `atomic_store`, the write of `atomic_rmw`/a successful `atomic_cas` -/
  | scW
  /-- `fence` -/
  | fence
  deriving DecidableEq, Repr

/-- Direction of an event of a kind. -/
def SKind.dir : SKind → Dir
  | .naR | .scR => .R
  | .naW | .scW => .W
  | .fence => .F

namespace ClifMM

variable {E : Type} (X : Exec E) (k : E → SKind)

/-- The kinds agree with the execution's directions. -/
def KindOk : Prop := ∀ e, (k e).dir = X.dir e

/-- Atomic accesses. -/
def At (e : E) : Prop := k e = .scR ∨ k e = .scW

/-- Synchronises-with: an atomic write read by an atomic read (every CLIF atomic is both a release
and an acquire). -/
def sw : Rel E := fun a b => k a = .scW ∧ X.rf a b ∧ k b = .scR

/-- Happens-before: `(po ∪ sw)⁺`. -/
def hb : Rel E := Relation.TransGen (union X.po (sw X k))

/-- Extended coherence order: `com⁺`. -/
def eco : Rel E := Relation.TransGen X.com

/-- **Consistency for the Cranelift contract.** -/
structure Consistent : Prop where
  /-- `irreflexive(hb; eco?)` -/
  coherence : ∀ a b, hb X k a b → opt (eco X) b a → False
  /-- `rmw ∩ (fr; co) = ∅` -/
  atomicity : ∀ a b, X.rmw a b → ¬ ∃ c, X.fr a c ∧ X.co c b
  /-- `acyclic((po ∪ com)|At)` -/
  sc : Acyclic (restr (At k) (union X.po X.com))

/-- Two distinct accesses of a location, one of them a write. -/
def Conflict (a b : E) : Prop :=
  a ≠ b ∧ X.loc a = X.loc b ∧ X.dir a ≠ .F ∧ X.dir b ≠ .F ∧ (X.dir a = .W ∨ X.dir b = .W)

/-- No data race: conflicting accesses, not both atomic, are ordered by `hb`. -/
def RaceFree : Prop :=
  ∀ a b, Conflict X a b → ¬ (At k a ∧ At k b) → hb X k a b ∨ hb X k b a

variable {X k}

theorem sw_at {a b : E} (h : sw X k a b) : At k a ∧ At k b := ⟨.inr h.1, .inl h.2.2⟩

/-- In a consistent race-free execution every `com` edge is `hb` or between atomics. -/
theorem com_hb_or_at (hX : X.Wf) (hc : Consistent X k) (hr : RaceFree X k) {a b : E}
    (h : X.com a b) : hb X k a b ∨ restr (At k) X.com a b := by
  by_cases hat : At k a ∧ At k b
  · exact .inr ⟨hat.1, h, hat.2⟩
  · have hcf : Conflict X a b :=
      ⟨hX.com_ne h, hX.com_loc h, (hX.com_notF h).1, (hX.com_notF h).2, hX.com_write h⟩
    rcases hr a b hcf hat with h' | h'
    · exact .inl h'
    · exact absurd (hc.coherence b a h' (.inr (.single h))) id

/-- **Theorem 3 (DRF-SC for an execution): a consistent, race-free execution is sequentially
consistent**, `acyclic(po ∪ com)`. -/
theorem drf_sc (hX : X.Wf) (hc : Consistent X k) (hr : RaceFree X k) : X.SC := by
  -- every `po ∪ com` edge is a path of `po` and atomic `com` steps
  let C : Rel E := restr (At k) X.com
  have hstep : ∀ a b, union X.po X.com a b → Relation.TransGen (union X.po C) a b := by
    rintro a b (h | h)
    · exact .single (.inl h)
    · rcases com_hb_or_at hX hc hr h with h | h
      · refine plus_mono ?_ h
        rintro x y (h | h)
        · exact .inl h
        · exact .inr ⟨(sw_at h).1, .inl h.2.1, (sw_at h).2⟩
      · exact .single (.inr h)
  intro a ha
  have hcyc := plus_flat hstep ha
  have hpo : Trans X.po := hX.po_trans
  rcases cycle_split hpo hcyc with h | ⟨b, hb⟩
  · exact hX.po_irrefl _ h
  · -- the cycle of `po?; C` steps runs through atomic events only
    have hend : ∀ x y, seq (opt X.po) C x y → At k y := by
      rintro x y ⟨z, -, hz⟩; exact hz.2.2
    have hlift : ∀ {x y}, At k x → Relation.TransGen (seq (opt X.po) C) x y →
        Relation.TransGen (restr (At k) (union X.po X.com)) x y := by
      intro x y hx hxy
      have one : ∀ u v, At k u → seq (opt X.po) C u v →
          Relation.TransGen (restr (At k) (union X.po X.com)) u v := by
        rintro u v hu ⟨z, hz | hz, hzc⟩
        · subst hz; exact .single ⟨hu, .inr hzc.2.1, hzc.2.2⟩
        · exact .tail (.single ⟨hu, .inl hz, hzc.1⟩) ⟨hzc.1, .inr hzc.2.1, hzc.2.2⟩
      induction hxy with
      | single h => exact one _ _ hx h
      | tail h1 h2 ih =>
        obtain ⟨c, hc⟩ := plus_last h1
        exact ih.trans (one _ _ (hend _ _ hc) h2)
    obtain ⟨c, hlast⟩ := plus_last hb
    exact hc.sc b (hlift (hend _ _ hlast) hb)

end ClifMM

end Concurrency
