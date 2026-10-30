import FV.Concurrency.ClifMM

/-!
# Rust/C++20 orderings and cg_clif's strengthening (T2f, #304)

Rust's memory model is C++20's (`docs/plans/atomics.md` §1). Its formal core is RC11 (Lahav et
al., PLDI 2017) — C++20 adopted RC11's fix of SC accesses and fences (P0668) — with every atomic
ordering: relaxed, acquire, release, acq_rel, seq_cst accesses, the read-modify-writes, and
fences of each ordering (`RKind`). RC11:

* release sequences `rs = [W]; po|loc?; [W_at]; (rf; rmw)*` (RC11; C++20's (P0982) drops
  `po|loc?`, a sub-relation, so every statement below holds for it too);
* `sw = [E⊒rel]; ([F]; po)?; rs; rf; [R_at]; (po; [F])?; [E⊒acq]`, `hb = (po ∪ sw)⁺`;
* coherence `irreflexive(hb; eco?)`, atomicity `rmw ∩ (fr; co) = ∅`,
* SC `acyclic(psc_base ∪ psc_F)` with `scb = po ∪ po≠loc; hb; po≠loc ∪ hb|loc ∪ co ∪ fr`,
  `psc_base = ([E_sc] ∪ [F_sc]; hb?); scb; ([E_sc] ∪ hb?; [F_sc])`,
  `psc_F = [F_sc]; (hb ∪ hb; eco; hb); [F_sc]`;
* no-thin-air `acyclic(po ∪ rf)` (RC11 only; C++20 has no such axiom, `ConsistentNoNTA`).

cg_clif ignores the ordering: every atomic access becomes a CLIF SC atomic and every fence a
`fence` (`strength`). The Cranelift contract of `FV/Concurrency/ClifMM.lean` gives fences no
meaning, which is too weak for this: `SB` with SC fences and plain accesses is contract-consistent
but forbidden by RC11 (`Witness`). `ClifMM.ConsistentF` adds Cranelift's documented fence semantics:
the SC axiom of RC11 with every atomic and every fence SC (`pscC`).

* `hb_mono`/`hb_strength`: the strengthened program has more happens-before;
* `strength_sound`: a `ConsistentF` execution of the strengthened program is RC11-consistent
  (without NTA) for the original orderings: every behaviour of the CLIF program is a behaviour of
  the Rust program;
* `raceFree_strength`: race-freedom for RC11's happens-before implies race-freedom for the
  contract's.
-/

namespace Concurrency

open Rel

/-- C++20/Rust memory orders. -/
inductive Ord where
  | rlx | acq | rel | acqrel | sc
  deriving DecidableEq, Repr

def Ord.isAcq : Ord → Bool
  | .acq | .acqrel | .sc => true
  | _ => false

def Ord.isRel : Ord → Bool
  | .rel | .acqrel | .sc => true
  | _ => false

/-- Event kinds of the source model. -/
inductive RKind where
  | naR | naW
  /-- an atomic load, or the read of a read-modify-write -/
  | R (o : Ord)
  /-- an atomic store, or the write of a read-modify-write -/
  | W (o : Ord)
  /-- a fence (`atomic_fence`, `compiler_fence`) -/
  | F (o : Ord)
  deriving DecidableEq, Repr

/-- cg_clif's strengthening: atomics to Cranelift's SC atomics, fences to `fence`. -/
def RKind.strength : RKind → SKind
  | .naR => .naR
  | .naW => .naW
  | .R _ => .scR
  | .W _ => .scW
  | .F _ => .fence

/-- All atomics and fences at `seq_cst` (the source kinds the contract's SC axiom is about). -/
def RKind.toSC : RKind → RKind
  | .R _ => .R .sc
  | .W _ => .W .sc
  | .F _ => .F .sc
  | k => k

namespace RC11

variable {E : Type} (X : Exec E) (k : E → RKind)

def IsAtW (e : E) : Prop := ∃ o, k e = .W o
def IsAtR (e : E) : Prop := ∃ o, k e = .R o
def IsF (e : E) : Prop := ∃ o, k e = .F o
/-- Release events: release writes and release fences. -/
def IsRel (e : E) : Prop := ∃ o, o.isRel = true ∧ (k e = .W o ∨ k e = .F o)
/-- Acquire events: acquire reads and acquire fences. -/
def IsAcq (e : E) : Prop := ∃ o, o.isAcq = true ∧ (k e = .R o ∨ k e = .F o)
/-- SC accesses. -/
def Esc (e : E) : Prop := k e = .R .sc ∨ k e = .W .sc
/-- SC fences. -/
def Fsc (e : E) : Prop := k e = .F .sc

/-- `(rf; rmw)*`. -/
inductive RfRmw : E → E → Prop
  | refl (a : E) : RfRmw a a
  | step {a b c d : E} : RfRmw a b → X.rf b c → X.rmw c d → RfRmw a d

/-- Release sequence: `[W]; po|loc?; [W_at]; (rf; rmw)*`. -/
def rs (a b : E) : Prop :=
  X.dir a = .W ∧ ∃ c, (c = a ∨ (X.po a c ∧ X.loc a = X.loc c)) ∧ IsAtW k c ∧ RfRmw X c b

/-- Synchronises-with. -/
def sw (a b : E) : Prop :=
  IsRel k a ∧ IsAcq k b ∧ ∃ x w r, (x = a ∨ (IsF k a ∧ X.po a x)) ∧ rs X k x w ∧ X.rf w r ∧
    IsAtR k r ∧ (r = b ∨ (IsF k b ∧ X.po r b))

/-- Happens-before. -/
def hb : Rel E := Relation.TransGen (union X.po (sw X k))

/-- `scb = po ∪ po≠loc; hb; po≠loc ∪ hb|loc ∪ co ∪ fr`. -/
def scb (a b : E) : Prop :=
  X.po a b ∨ (∃ c d, X.po a c ∧ X.loc a ≠ X.loc c ∧ hb X k c d ∧ X.po d b ∧ X.loc d ≠ X.loc b) ∨
    (hb X k a b ∧ X.loc a = X.loc b) ∨ X.co a b ∨ X.fr a b

/-- `psc_base = ([E_sc] ∪ [F_sc]; hb?); scb; ([E_sc] ∪ hb?; [F_sc])`. -/
def pscBase (a b : E) : Prop :=
  ∃ x y, ((x = a ∧ Esc k a) ∨ (Fsc k a ∧ opt (hb X k) a x)) ∧ scb X k x y ∧
    ((y = b ∧ Esc k b) ∨ (Fsc k b ∧ opt (hb X k) y b))

/-- `psc_F = [F_sc]; (hb ∪ hb; eco; hb); [F_sc]`. -/
def pscF (a b : E) : Prop :=
  Fsc k a ∧ Fsc k b ∧
    (hb X k a b ∨ ∃ c d, hb X k a c ∧ Relation.TransGen X.com c d ∧ hb X k d b)

/-- `psc = psc_base ∪ psc_F`. -/
def psc : Rel E := union (pscBase X k) (pscF X k)

/-- **RC11 consistency without no-thin-air** (the C++20 model). -/
structure ConsistentNoNTA : Prop where
  coherence : ∀ a b, hb X k a b → opt (Relation.TransGen X.com) b a → False
  atomicity : ∀ a b, X.rmw a b → ¬ ∃ c, X.fr a c ∧ X.co c b
  sc : Acyclic (psc X k)

/-- **RC11 consistency.** -/
structure Consistent : Prop extends ConsistentNoNTA X k where
  nta : Acyclic (union X.po X.rf)

/-- A data race for RC11: conflicting, not both atomic, unordered by `hb`. -/
def RaceFree : Prop :=
  ∀ a b, ClifMM.Conflict X a b → ¬ ((IsAtR k a ∨ IsAtW k a) ∧ (IsAtR k b ∨ IsAtW k b)) →
    hb X k a b ∨ hb X k b a

variable {X k}

/-! ### Monotonicity in the orderings -/

/-- `k'` is at least as strong as `k`: the same event classes, more release/acquire/SC. -/
structure Stronger (k k' : E → RKind) : Prop where
  atR : ∀ e, IsAtR k e → IsAtR k' e
  atW : ∀ e, IsAtW k e → IsAtW k' e
  isF : ∀ e, IsF k e → IsF k' e
  rel : ∀ e, IsRel k e → IsRel k' e
  acq : ∀ e, IsAcq k e → IsAcq k' e
  esc : ∀ e, Esc k e → Esc k' e
  fsc : ∀ e, Fsc k e → Fsc k' e

theorem rs_mono {k k' : E → RKind} (h : Stronger k k') {a b : E} (hr : rs X k a b) : rs X k' a b :=
  let ⟨hd, c, hc, hw, hrr⟩ := hr; ⟨hd, c, hc, h.atW _ hw, hrr⟩

theorem sw_mono {k k' : E → RKind} (h : Stronger k k') {a b : E} (hs : sw X k a b) : sw X k' a b := by
  obtain ⟨ha, hb, x, w, r, hx, hrs, hrf, hr, hrb⟩ := hs
  refine ⟨h.rel _ ha, h.acq _ hb, x, w, r, ?_, rs_mono h hrs, hrf, h.atR _ hr, ?_⟩
  · rcases hx with hx | ⟨hf, hpo⟩
    · exact .inl hx
    · exact .inr ⟨h.isF _ hf, hpo⟩
  · rcases hrb with hrb | ⟨hf, hpo⟩
    · exact .inl hrb
    · exact .inr ⟨h.isF _ hf, hpo⟩

theorem hb_mono {k k' : E → RKind} (h : Stronger k k') {a b : E} (hh : hb X k a b) : hb X k' a b :=
  plus_mono (fun _ _ h' => h'.elim .inl (fun h' => .inr (sw_mono h h'))) hh

theorem opt_hb_mono {k k' : E → RKind} (h : Stronger k k') {a b : E} (hh : opt (hb X k) a b) :
    opt (hb X k') a b :=
  hh.elim .inl (fun h' => .inr (hb_mono h h'))

theorem scb_mono {k k' : E → RKind} (h : Stronger k k') {a b : E} (hs : scb X k a b) : scb X k' a b := by
  rcases hs with h1 | ⟨c, d, h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩ | h1 | h1
  · exact .inl h1
  · exact .inr (.inl ⟨c, d, h1, h2, hb_mono h h3, h4, h5⟩)
  · exact .inr (.inr (.inl ⟨hb_mono h h1, h2⟩))
  · exact .inr (.inr (.inr (.inl h1)))
  · exact .inr (.inr (.inr (.inr h1)))

/-- **`psc` grows with the orderings.** -/
theorem psc_mono {k k' : E → RKind} (h : Stronger k k') {a b : E} (hp : psc X k a b) :
    psc X k' a b := by
  rcases hp with ⟨x, y, hl, hs, hr⟩ | ⟨ha, hb, hh⟩
  · refine .inl ⟨x, y, ?_, scb_mono h hs, ?_⟩
    · rcases hl with ⟨rfl, he⟩ | ⟨hf, hh⟩
      · exact .inl ⟨rfl, h.esc _ he⟩
      · exact .inr ⟨h.fsc _ hf, opt_hb_mono h hh⟩
    · rcases hr with ⟨rfl, he⟩ | ⟨hf, hh⟩
      · exact .inl ⟨rfl, h.esc _ he⟩
      · exact .inr ⟨h.fsc _ hf, opt_hb_mono h hh⟩
  · refine .inr ⟨h.fsc _ ha, h.fsc _ hb, ?_⟩
    rcases hh with hh | ⟨c, d, h1, h2, h3⟩
    · exact .inl (hb_mono h hh)
    · exact .inr ⟨c, d, hb_mono h h1, h2, hb_mono h h3⟩

/-- Every ordering raised to `seq_cst` is stronger. -/
theorem stronger_toSC (k : E → RKind) : Stronger k (fun e => (k e).toSC) where
  atR e := fun ⟨o, h⟩ => ⟨.sc, by simp [RKind.toSC, h]⟩
  atW e := fun ⟨o, h⟩ => ⟨.sc, by simp [RKind.toSC, h]⟩
  isF e := fun ⟨o, h⟩ => ⟨.sc, by simp [RKind.toSC, h]⟩
  rel e := fun ⟨o, _, h⟩ => ⟨.sc, rfl, by rcases h with h | h <;> simp [RKind.toSC, h]⟩
  acq e := fun ⟨o, _, h⟩ => ⟨.sc, rfl, by rcases h with h | h <;> simp [RKind.toSC, h]⟩
  esc e := fun h => by rcases h with h | h <;> simp [Esc, RKind.toSC, h]
  fsc e := fun h => by simp [Fsc, RKind.toSC] at h ⊢; simp [h]

end RC11

/-! ## cg_clif's strengthening -/

/-- The source kind of a CLIF kind with every atomic and fence at `seq_cst`. -/
def SKind.liftSC : SKind → RKind
  | .naR => .naR
  | .naW => .naW
  | .scR => .R .sc
  | .scW => .W .sc
  | .fence => .F .sc

theorem liftSC_strength (k : RKind) : k.strength.liftSC = k.toSC := by
  cases k <;> rfl

namespace ClifMM

variable {E : Type} (X : Exec E) (k : E → SKind)

/-- **The Cranelift contract with its documented fence semantics**: in addition, RC11's SC axiom
with every atomic access and every `fence` at `seq_cst` (Cranelift: "`fence` … is sequentially
consistent"; `atomic_*` "is sequentially consistent"). -/
structure ConsistentF : Prop extends Consistent X k where
  psc : Acyclic (RC11.psc X (fun e => (k e).liftSC))

end ClifMM

namespace RC11

variable {E : Type} {X : Exec E} {k : E → RKind}

/-- The read-modify-writes are atomic. -/
def RmwAt (X : Exec E) (k : E → RKind) : Prop := ∀ a b, X.rmw a b → IsAtR k a ∧ IsAtW k b

theorem at_strength {e : E} : ClifMM.At (fun e => (k e).strength) e ↔ (IsAtR k e ∨ IsAtW k e) := by
  constructor
  · intro h
    rcases hk : k e with _ | _ | o | o | o <;> rcases h with h | h <;>
      simp [hk, RKind.strength] at h
    · exact .inl ⟨o, hk⟩
    · exact .inr ⟨o, hk⟩
  · rintro (⟨o, h⟩ | ⟨o, h⟩)
    · exact .inl (by simp [h, RKind.strength])
    · exact .inr (by simp [h, RKind.strength])

/-- **The strengthened program has more happens-before**: RC11's `hb` (every ordering) is in the
contract's `hb` of the strengthened kinds. -/
theorem hb_strength (hX : X.Wf) (hrmw : RmwAt X k) {a b : E} (h : hb X k a b) :
    ClifMM.hb X (fun e => (k e).strength) a b := by
  have hsw : ∀ x y, X.rf x y → IsAtW k x → IsAtR k y →
      ClifMM.sw X (fun e => (k e).strength) x y := by
    rintro x y hxy ⟨o, hx⟩ ⟨o', hy⟩
    exact ⟨by simp [hx, RKind.strength], hxy, by simp [hy, RKind.strength]⟩
  -- `(rf; rmw)*` from an atomic write: `hb`-related or equal, ending at an atomic write
  have hrr : ∀ c w, IsAtW k c → RfRmw X c w →
      IsAtW k w ∧ opt (ClifMM.hb X (fun e => (k e).strength)) c w := by
    intro c w hc h
    induction h with
    | refl => exact ⟨hc, .inl rfl⟩
    | step _ h2 h3 ih =>
      obtain ⟨hb', hcb⟩ := ih
      have hr := hrmw _ _ h3
      have hstep : ClifMM.hb X (fun e => (k e).strength) _ _ :=
        .tail (.single (.inr (hsw _ _ h2 hb' hr.1))) (.inl (hX.rmw_po _ _ h3))
      refine ⟨hr.2, .inr ?_⟩
      rcases hcb with rfl | hcb
      · exact hstep
      · exact hcb.trans hstep
  -- glue `opt` segments around a path
  let H := ClifMM.hb X (fun e => (k e).strength)
  have optl : ∀ {x y z}, opt H x y → H y z → H x z := fun h1 h2 => by
    rcases h1 with rfl | h1
    · exact h2
    · exact h1.trans h2
  have optr : ∀ {x y z}, H x y → opt H y z → H x z := fun h1 h2 => by
    rcases h2 with rfl | h2
    · exact h1
    · exact h1.trans h2
  have po_opt : ∀ {x y}, opt X.po x y → opt H x y := fun h =>
    h.elim .inl (fun h => .inr (.single (.inl h)))
  refine plus_flat ?_ h
  rintro a b (h | ⟨-, -, x, w, r, hx, ⟨-, c, hc, hcw, hcr⟩, hwr, hr, hrb⟩)
  · exact .single (.inl h)
  · obtain ⟨hw, hcw'⟩ := hrr c w hcw hcr
    have hax : opt X.po a x := hx.elim (fun h => .inl h.symm) (fun h => .inr h.2)
    have hxc : opt X.po x c := hc.elim (fun h => .inl h.symm) (fun h => .inr h.1)
    have hrb' : opt X.po r b := hrb.elim (fun h => .inl h) (fun h => .inr h.2)
    have hmid : H w r := .single (.inr (hsw _ _ hwr hw hr))
    refine optl (po_opt hax) (optl (po_opt hxc) (optl hcw' (optr hmid (po_opt hrb'))))

/-- **Soundness of cg_clif's strengthening.** An execution of the strengthened program (every
atomic access a CLIF SC atomic, every fence a `fence`) that is consistent for the Cranelift
contract with its fence semantics is RC11-consistent (without no-thin-air, i.e. C++20-consistent)
for the original orderings: every behaviour of the CLIF program is a behaviour of the Rust
program. -/
theorem strength_sound (hX : X.Wf) (hrmw : RmwAt X k)
    (hc : ClifMM.ConsistentF X (fun e => (k e).strength)) : ConsistentNoNTA X k where
  coherence a b h he := hc.coherence a b (hb_strength hX hrmw h) he
  atomicity := hc.atomicity
  sc := by
    have e : (fun e => ((k e).strength).liftSC) = (fun e => (k e).toSC) :=
      funext fun e => liftSC_strength (k e)
    have hp := hc.psc
    rw [e] at hp
    exact hp.mono (fun a b h => psc_mono (stronger_toSC k) h)

/-- **Race-freedom transfers**: an RC11-race-free execution is race-free for the contract of the
strengthened program. -/
theorem raceFree_strength (hX : X.Wf) (hrmw : RmwAt X k) (hr : RaceFree X k) :
    ClifMM.RaceFree X (fun e => (k e).strength) := by
  intro a b hc hat
  rcases hr a b hc (fun h => hat ⟨at_strength.mpr h.1, at_strength.mpr h.2⟩) with h | h
  · exact .inl (hb_strength hX hrmw h)
  · exact .inr (hb_strength hX hrmw h)

/-- RC11's `hb` is in `(po ∪ com)⁺`. -/
theorem hb_sub (hX : X.Wf) {a b : E} (h : hb X k a b) :
    Relation.TransGen (union X.po X.com) a b := by
  let H := Relation.TransGen (union X.po X.com)
  have optl : ∀ {x y z}, opt X.po x y → H y z → H x z := fun h1 h2 => by
    rcases h1 with rfl | h1
    · exact h2
    · exact (Relation.TransGen.single (.inl h1)).trans h2
  have optr : ∀ {x y z}, H x y → opt X.po y z → H x z := fun h1 h2 => by
    rcases h2 with rfl | h2
    · exact h1
    · exact h1.tail (.inl h2)
  have hrr : ∀ c w, RfRmw X c w → opt H c w := by
    intro c w h
    induction h with
    | refl => exact .inl rfl
    | step _ h2 h3 ih =>
      have hs : H _ _ := .tail (.single (.inr (.inl h2))) (.inl (hX.rmw_po _ _ h3))
      rcases ih with rfl | ih
      · exact .inr hs
      · exact .inr (ih.trans hs)
  refine plus_flat ?_ h
  rintro a b (h | ⟨-, -, x, w, r, hx, ⟨-, c, hc, -, hcr⟩, hwr, -, hrb⟩)
  · exact .single (.inl h)
  · have hax : opt X.po a x := hx.elim (fun h => .inl h.symm) (fun h => .inr h.2)
    have hxc : opt X.po x c := hc.elim (fun h => .inl h.symm) (fun h => .inr h.1)
    have hrb' : opt X.po r b := hrb.elim (fun h => .inl h) (fun h => .inr h.2)
    have hwr' : H w r := .single (.inr (.inl hwr))
    refine optl hax (optl hxc ?_)
    rcases hrr c w hcr with rfl | hcw
    · exact optr hwr' hrb'
    · exact optr (hcw.trans hwr') hrb'

/-- `psc` is in `(po ∪ com)⁺`. -/
theorem psc_sub (hX : X.Wf) {a b : E} (h : psc X k a b) : Relation.TransGen (union X.po X.com) a b := by
  let H := Relation.TransGen (union X.po X.com)
  have optH : ∀ {x y}, opt (hb X k) x y → x = y ∨ H x y := fun h =>
    h.elim .inl (fun h => .inr (hb_sub hX h))
  have glue : ∀ {x y z}, (x = y ∨ H x y) → H y z → H x z := fun h1 h2 => by
    rcases h1 with rfl | h1
    · exact h2
    · exact h1.trans h2
  have glue' : ∀ {x y z}, H x y → (y = z ∨ H y z) → H x z := fun h1 h2 => by
    rcases h2 with rfl | h2
    · exact h1
    · exact h1.trans h2
  have hscb : ∀ {x y}, scb X k x y → H x y := by
    intro x y h
    rcases h with h | ⟨c, d, h1, -, h2, h3, -⟩ | ⟨h, -⟩ | h | h
    · exact .single (.inl h)
    · exact ((Relation.TransGen.single (.inl h1)).trans (hb_sub hX h2)).tail (.inl h3)
    · exact hb_sub hX h
    · exact .single (.inr (.inr (.inl h)))
    · exact .single (.inr (.inr (.inr h)))
  rcases h with ⟨x, y, hl, hs, hr⟩ | ⟨-, -, hh⟩
  · have hl' : a = x ∨ H a x := by
      rcases hl with ⟨rfl, -⟩ | ⟨-, hh⟩
      · exact .inl rfl
      · exact optH hh
    have hr' : y = b ∨ H y b := by
      rcases hr with ⟨rfl, -⟩ | ⟨-, hh⟩
      · exact .inl rfl
      · exact optH hh
    exact glue hl' (glue' (hscb hs) hr')
  · rcases hh with hh | ⟨c, d, h1, h2, h3⟩
    · exact hb_sub hX hh
    · exact ((hb_sub hX h1).trans (plus_mono (fun _ _ h => .inr h) h2)).trans (hb_sub hX h3)

/-- **An SC execution is RC11-consistent** (with no-thin-air), given atomicity. -/
theorem consistent_of_sc (hX : X.Wf) (hsc : X.SC)
    (hat : ∀ a b, X.rmw a b → ¬ ∃ c, X.fr a c ∧ X.co c b) : Consistent X k where
  coherence a b h he := by
    rcases he with rfl | he
    · exact hsc _ (hb_sub hX h)
    · exact hsc a ((hb_sub hX h).trans (plus_mono (fun _ _ h => .inr h) he))
  atomicity := hat
  sc := Acyclic.of_plus (fun _ _ h => psc_sub hX h) hsc
  nta := Acyclic.mono (fun _ _ h => h.elim .inl (fun h => .inr (.inl h))) hsc

/-- **For race-free executions the fence axiom is not needed**: a race-free execution of the
strengthened program, consistent for the contract of `FV/Concurrency/ClifMM.lean`, is
RC11-consistent (with no-thin-air) for the original orderings (DRF-SC). -/
theorem strength_sound_drf (hX : X.Wf) (hc : ClifMM.Consistent X (fun e => (k e).strength))
    (hr : ClifMM.RaceFree X (fun e => (k e).strength)) : Consistent X k :=
  consistent_of_sc hX (ClifMM.drf_sc hX hc hr) hc.atomicity

end RC11

namespace ClifMM

/-- An SC execution satisfies the contract with fences (given atomicity). -/
theorem consistentF_of_sc {E : Type} {X : Exec E} {k : E → SKind} (hX : X.Wf) (hsc : X.SC)
    (hat : ∀ a b, X.rmw a b → ¬ ∃ c, X.fr a c ∧ X.co c b) : ConsistentF X k where
  coherence a b h he := by
    have hp : Relation.TransGen (union X.po X.com) a b := by
      refine plus_flat ?_ h
      rintro x y (h | ⟨-, h, -⟩)
      · exact .single (.inl h)
      · exact .single (.inr (.inl h))
    rcases he with rfl | he
    · exact hsc _ hp
    · exact hsc a (hp.trans (plus_mono (fun _ _ h => .inr h) he))
  atomicity := hat
  sc := Acyclic.mono (fun _ _ h => h.2.1) hsc
  psc := Acyclic.of_plus (fun _ _ h => RC11.psc_sub hX h) hsc

end ClifMM

end Concurrency
