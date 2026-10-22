import FV.Concurrency.Armv8
import FV.Concurrency.ClifMM

/-!
# Soundness of Cranelift's atomics mapping to Armv8 (T2, #38)

The compilation-correctness statement in the style of the C11 → Armv8 mapping results (Lahav et
al., PLDI 2017; Podkopaev et al., POPL 2019), for the table Cranelift's aarch64 backend implements
with cg_clif's flags (`has_lse = 0`; `FV/Concurrency/Code.lean` proves it is the table of the code
`MInst.lines` emits):

| CLIF | Arm |
| --- | --- |
| `load` / `store` | plain read / write |
| `atomic_load` | `ldar` (`acqR`) |
| `atomic_store` | `stlr` (`relW`) |
| `atomic_rmw`, `atomic_cas` | `ldaxr` (`acqXR`) + successful `stlxr` (`relXW`), `rmw`-paired |
| `fence` | `dmb ish` |

An Arm execution of compiled code (`Compiled`) has the CLIF execution's events (`S`) with mapped
kinds, plus events the CLIF execution does not have: the `ldaxr` reads of failed LL/SC
iterations and the code's own plain accesses (GOT, jump tables, frame).
`armv8_to_clif`: if the Arm execution is Armv8-consistent, the CLIF execution (the restriction to
`S`) is consistent for the Cranelift contract. `armv8_drf_sc`: if it is moreover race-free, it is
sequentially consistent. Plan: `docs/plans/atomics.md`.
-/

namespace Concurrency

open Rel

/-- The mapping table: the Arm kinds a CLIF event kind may compile to. -/
def Maps : SKind → AKind → Prop
  | .naR, a => a = .plainR
  | .naW, a => a = .plainW
  | .scR, a => a = .acqR ∨ a = .acqXR
  | .scW, a => a = .relW ∨ a = .relXW
  | .fence, a => a = .dmb

instance (s : SKind) (a : AKind) : Decidable (Maps s a) := by
  cases s <;> unfold Maps <;> infer_instance

theorem Maps.dir {s : SKind} {a : AKind} (h : Maps s a) : s.dir = a.dir := by
  cases s <;> simp only [Maps] at h
  all_goals first
    | (subst h; rfl)
    | (rcases h with rfl | rfl <;> rfl)

namespace Exec

variable {E : Type}

/-- The execution restricted to the events `S`. -/
def restrict (X : Exec E) (S : E → Prop) : Exec {e // S e} where
  tid e := X.tid e.1
  dir e := X.dir e.1
  loc e := X.loc e.1
  po a b := X.po a.1 b.1
  rf a b := X.rf a.1 b.1
  co a b := X.co a.1 b.1
  rmw a b := X.rmw a.1 b.1
  ev e := X.ev e.1

variable {X : Exec E} {S : E → Prop}

theorem restrict_fr {a b : {e // S e}} (h : (X.restrict S).fr a b) : X.fr a.1 b.1 :=
  let ⟨w, h1, h2⟩ := h; ⟨w.1, h1, h2⟩

theorem restrict_com {a b : {e // S e}} (h : (X.restrict S).com a b) : X.com a.1 b.1 := by
  rcases h with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (restrict_fr h))

/-- The restriction to a set of events whose reads read from writes of the set is
well-formed. -/
theorem Wf.restrict (hX : X.Wf) (hrf : ∀ w r, X.rf w r → S r → S w) : (X.restrict S).Wf where
  po_irrefl a := hX.po_irrefl a.1
  po_trans a b c := hX.po_trans a.1 b.1 c.1
  po_tid a b := hX.po_tid a.1 b.1
  po_total a b ht hne := hX.po_total a.1 b.1 ht (fun h => hne (Subtype.ext h))
  rf_dir a b := hX.rf_dir a.1 b.1
  rf_loc a b := hX.rf_loc a.1 b.1
  rf_func a a' b h1 h2 := Subtype.ext (hX.rf_func a.1 a'.1 b.1 h1 h2)
  rf_total b hb := by
    obtain ⟨a, ha⟩ := hX.rf_total b.1 hb
    exact ⟨⟨a, hrf a b.1 ha b.2⟩, ha⟩
  co_dir a b := hX.co_dir a.1 b.1
  co_loc a b := hX.co_loc a.1 b.1
  co_irrefl a := hX.co_irrefl a.1
  co_trans a b c := hX.co_trans a.1 b.1 c.1
  co_total a b ha hb hl hne := hX.co_total a.1 b.1 ha hb hl (fun h => hne (Subtype.ext h))
  rmw_dir a b := hX.rmw_dir a.1 b.1
  rmw_loc a b := hX.rmw_loc a.1 b.1
  rmw_po a b := hX.rmw_po a.1 b.1
  rmw_imm a b c := hX.rmw_imm a.1 b.1 c.1

end Exec

namespace Armv8

variable {E : Type} {X : Exec E} {k : E → AKind}

/-- Release/acquire synchronisation on Arm: an `stlr`/`stlxr` read by an `ldar`/`ldaxr`. -/
def swA (X : Exec E) (k : E → AKind) : Rel E := fun a b => L k a ∧ X.rf a b ∧ A k b

/-- Happens-before on Arm: `(po ∪ swA)⁺`. -/
def hbA (X : Exec E) (k : E → AKind) : Rel E := Relation.TransGen (union X.po (swA X k))

theorem A_not_L {e : E} (ha : A k e) (hl : L k e) : False := by
  rcases ha with ha | ha <;> rcases hl with hl | hl <;> rw [ha] at hl <;> cases hl

theorem opt_po_trans (hX : X.Wf) {a b c : E} (h1 : opt X.po a b) (h2 : opt X.po b c) :
    opt X.po a c := by
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact .inr h1
    · exact .inr (hX.po_trans _ _ _ h1 h2)

/-- **`hb` on Arm is `po`, or starts with `po?` into a release, continues in `ob⁺` and ends with an
acquire followed by `po?`** (`[A]; po` and `po; [L]` are `bob`, an external `swA` edge is `rfe`). -/
theorem hb_shape (hX : X.Wf) (hc : Consistent X k) {a b : E} (h : hbA X k a b) :
    X.po a b ∨ ∃ l x, opt X.po a l ∧ L k l ∧ A k x ∧ Relation.TransGen (ob X k) l x ∧
      opt X.po x b := by
  induction h with
  | single h =>
    rcases h with h | ⟨hl, hrf, ha⟩
    · exact .inl h
    · rcases com_ob_or_po hX hc (.inl hrf) with h | h
      · exact .inr ⟨_, _, .inl rfl, hl, ha, .single h, .inl rfl⟩
      · exact .inl h
  | @tail c d _ h2 ih =>
    rcases ih with hac | ⟨l, x, hal, hl, hx, hob, hxc⟩
    · rcases h2 with h2 | ⟨hl, hrf, ha⟩
      · exact .inl (hX.po_trans _ _ _ hac h2)
      · rcases com_ob_or_po hX hc (.inl hrf) with h | h
        · exact .inr ⟨c, d, .inr hac, hl, ha, .single h, .inl rfl⟩
        · exact .inl (hX.po_trans _ _ _ hac h)
    · rcases h2 with h2 | ⟨hl', hrf, ha⟩
      · exact .inr ⟨l, x, hal, hl, hx, hob, opt_po_trans hX hxc (.inr h2)⟩
      · rcases com_ob_or_po hX hc (.inl hrf) with h | h
        · -- `x` (an acquire) is `po`-before the release `c`
          have hxpo : X.po x c := by
            rcases hxc with rfl | hxc
            · exact absurd hl' (fun hl' => A_not_L hx hl')
            · exact hxc
          exact .inr ⟨l, d, hal, hl, ha, (hob.tail (ob_acq hx hxpo)).tail h, .inl rfl⟩
        · exact .inr ⟨l, x, hal, hl, hx, hob, opt_po_trans hX hxc (.inr h)⟩

/-- Closing a cycle: from an acquire `x` back to a release `l` through `po?`, a middle part that
is `po?`, one `ob` step or two `ob` steps, and `po?`, is `ob⁺`. -/
theorem close (hX : X.Wf) {x u v l : E} (hx : A k x) (hl : L k l) (hxu : opt X.po x u)
    (hvl : opt X.po v l)
    (hm : opt X.po u v ∨ ob X k u v ∨ seq (ob X k) (ob X k) u v) :
    Relation.TransGen (ob X k) x l := by
  rcases hm with hm | hm | ⟨w, h1, h2⟩
  · rcases opt_po_trans hX (opt_po_trans hX hxu hm) hvl with rfl | h
    · exact absurd hl (fun hl => A_not_L hx hl)
    · exact .single (ob_acq hx h)
  all_goals
    -- the middle as a path `u → v`
    first
    | have hmid : Relation.TransGen (ob X k) u v := .single hm
    | have hmid : Relation.TransGen (ob X k) u v := .tail (.single h1) h2
    have hpre : Relation.TransGen (ob X k) x v := by
      rcases hxu with rfl | hxu
      · exact hmid
      · exact (Relation.TransGen.single (ob_acq hx hxu)).trans hmid
    rcases hvl with rfl | hvl
    · exact hpre
    · exact hpre.tail (ob_rel hvl hl)

/-- **Coherence for the CLIF contract on Arm**: `irreflexive(hbA; eco?)`. -/
theorem coherence (hX : X.Wf) (hc : Consistent X k) {a b : E} (h : hbA X k a b)
    (he : opt (Relation.TransGen X.com) b a) : False := by
  rcases he with rfl | he
  · rcases hb_shape hX hc h with h | ⟨l, x, hal, hl, hx, hob, hxa⟩
    · exact hX.po_irrefl _ h
    · exact hc.external l (hob.trans (close hX hx hl hxa hal (.inl (.inl rfl))))
  · rcases hb_shape hX hc h with h | ⟨l, x, hal, hl, hx, hob, hxb⟩
    · -- `po-loc a b` and `com⁺ b a`: an internal cycle
      have hpl : X.poLoc a b :=
        ⟨h, (hX.eco_loc he).symm, (hX.eco_notF he).2, (hX.eco_notF he).1⟩
      exact hc.internal a
        ((Relation.TransGen.single (.inl hpl)).trans (plus_mono (fun _ _ h => .inr h) he))
    · -- `l ob⁺ x`, `x po? b`, `b eco a`, `a po? l`: close the cycle per shape of `eco`
      have cyc : ∀ {u v}, opt X.po x u → opt X.po v l →
          (opt X.po u v ∨ ob X k u v ∨ seq (ob X k) (ob X k) u v) → False :=
        fun hxu hvl hm => hc.external l (hob.trans (close hX hx hl hxu hvl hm))
      have one : ∀ {u v}, X.com u v → ob X k u v ∨ X.po u v := com_ob_or_po hX hc
      have two : ∀ {c}, X.com b c → X.com c a → False := by
        intro c h1 h2
        rcases one h1 with h1 | h1 <;> rcases one h2 with h2 | h2
        · exact cyc hxb hal (.inr (.inr ⟨c, h1, h2⟩))
        · exact cyc hxb (opt_po_trans hX (.inr h2) hal) (.inr (.inl h1))
        · exact cyc (opt_po_trans hX hxb (.inr h1)) hal (.inr (.inl h2))
        · exact cyc hxb hal (.inl (.inr (hX.po_trans _ _ _ h1 h2)))
      have single : X.com b a → False := by
        intro h1
        rcases one h1 with h1 | h1
        · exact cyc hxb hal (.inr (.inl h1))
        · exact cyc hxb hal (.inl (.inr h1))
      rcases hX.eco_shape he with h1 | h1 | h1 | ⟨c, h1, h2⟩ | ⟨c, h1, h2⟩
      · exact single (.inl h1)
      · exact single (.inr (.inl h1))
      · exact single (.inr (.inr h1))
      · exact two (.inr (.inl h1)) (.inl h2)
      · exact two (.inr (.inr h1)) (.inl h2)

/-- **Atomicity of the exclusive pairs**: `rmw ∩ (fr; co) = ∅` (from the atomic axiom for the
external part, SC per location and the `po`-adjacency of the pair for the internal parts). -/
theorem atomicity (hX : X.Wf) (hc : Consistent X k) {a b c : E} (hr : X.rmw a b)
    (h1 : X.fr a c) (h2 : X.co c b) : False := by
  have hab : X.tid a = X.tid b := hX.po_tid _ _ (hX.rmw_po _ _ hr)
  by_cases hac : X.tid a = X.tid c
  · have hpo : X.po a c := hX.com_int_po hc.internal (.inr (.inr h1)) hac
    have hcb : c ≠ b := by rintro rfl; exact hX.co_irrefl _ h2
    rcases hX.po_total c b (hac.symm.trans hab) hcb with h | h
    · exact hX.rmw_imm _ _ _ hr hpo h (.inl (by rw [(hX.co_dir _ _ h2).1]; decide))
    · have hd := hX.co_dir _ _ h2
      have hpl : X.poLoc b c := by
        refine ⟨h, (hX.co_loc _ _ h2).symm, ?_, ?_⟩
        · rw [hd.2]; decide
        · rw [hd.1]; decide
      exact hc.internal b (.tail (.single (.inl hpl)) (.inr (.inr (.inl h2))))
  · exact hc.atomic a b hr ⟨c, ⟨h1, hac⟩, ⟨h2, fun h => hac (hab.trans h.symm)⟩⟩

end Armv8

namespace Mapping

variable {E : Type}

/-- **The Arm execution `X` (kinds `ak`) is the compiled image of the CLIF execution on `S`
(kinds `sk`)**: every CLIF event has a kind of the table and CLIF reads read from CLIF writes
(the atomic-update pairs between CLIF events are the CLIF `rmw`). The other Arm events are
unconstrained: in compiled code they are the `ldaxr` reads of failed LL/SC iterations and plain
accesses of the code's own data (GOT, jump tables, TLS descriptors, the frame:
`FV/Concurrency/Code.lean`), and more ordering on them only removes executions. `rf_src` is
where the single-thread frame separation (`Avoids`: the frame slots are not CLIF memory)
enters. -/
structure Compiled (X : Exec E) (ak : E → AKind) (S : E → Prop) (sk : E → SKind) : Prop where
  maps : ∀ e, S e → Maps (sk e) (ak e)
  rf_src : ∀ w r, X.rf w r → S r → S w

variable {X : Exec E} {ak : E → AKind} {S : E → Prop} {sk : E → SKind}

/-- The CLIF kinds on the restricted execution. -/
def srcKind (sk : E → SKind) (S : E → Prop) : {e // S e} → SKind := fun e => sk e.1

theorem srcKind_ok (hk : Armv8.KindOk X ak) (hm : Compiled X ak S sk) :
    ClifMM.KindOk (X.restrict S) (srcKind sk S) := by
  intro e
  exact (Maps.dir (hm.maps e.1 e.2)).trans (hk e.1)

theorem at_AL (hm : Compiled X ak S sk) {e : {e // S e}} (h : ClifMM.At (srcKind sk S) e) :
    Armv8.A ak e.1 ∨ Armv8.L ak e.1 := by
  have hmap := hm.maps e.1 e.2
  rcases h with h | h <;> simp only [srcKind] at h <;> rw [h] at hmap
  · exact .inl hmap
  · exact .inr hmap

theorem hb_src (hm : Compiled X ak S sk) {a b : {e // S e}}
    (h : ClifMM.hb (X.restrict S) (srcKind sk S) a b) : Armv8.hbA X ak a.1 b.1 := by
  refine plus_map Subtype.val ?_ h
  rintro x y (h | ⟨hx, hrf, hy⟩)
  · exact .inl h
  · have hmx := hm.maps x.1 x.2
    have hmy := hm.maps y.1 y.2
    simp only [srcKind] at hx hy
    rw [hx] at hmx; rw [hy] at hmy
    exact .inr ⟨hmx, hrf, hmy⟩

/-- **Theorem 2 (soundness of the mapping).** If the Arm execution of compiled code is
Armv8-consistent, the CLIF execution it is the image of is consistent for the Cranelift
contract. -/
theorem armv8_to_clif (hX : X.Wf) (hc : Armv8.Consistent X ak)
    (hm : Compiled X ak S sk) : ClifMM.Consistent (X.restrict S) (srcKind sk S) where
  coherence a b h he := by
    refine Armv8.coherence hX hc (hb_src hm h) ?_
    rcases he with rfl | he
    · exact .inl rfl
    · exact .inr (plus_map Subtype.val (fun _ _ h => Exec.restrict_com h) he)
  atomicity a b hr := by
    rintro ⟨c, h1, h2⟩
    exact Armv8.atomicity hX hc hr (Exec.restrict_fr h1) h2
  sc a h := by
    refine Armv8.atomics_sc hX hc a.1 (plus_map Subtype.val ?_ h)
    rintro x y ⟨hx, hxy, hy⟩
    refine ⟨at_AL hm hx, ?_, at_AL hm hy⟩
    rcases hxy with hxy | hxy
    · exact .inl hxy
    · exact .inr (Exec.restrict_com hxy)

/-- **Theorem 4: compiled race-free CLIF executions are sequentially consistent on Armv8.** -/
theorem armv8_drf_sc (hX : X.Wf) (hc : Armv8.Consistent X ak)
    (hm : Compiled X ak S sk) (hr : ClifMM.RaceFree (X.restrict S) (srcKind sk S)) :
    (X.restrict S).SC :=
  ClifMM.drf_sc (hX.restrict hm.rf_src) (armv8_to_clif hX hc hm) hr

end Mapping

end Concurrency
