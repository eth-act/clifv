import FV.Concurrency.CallComposeT

/-!
# `CStep` runs as `CStepS` runs (#473, step (4))

The layers realize an activation's segment by a `ClifCStepTerm.CRun` of `ClifThread.CStep`
steps. `CallComposeT.RealizedT` asks for runs of `CStepS`, which carry the own-initialisation
mask in the thread state's bytes (`maskOf`: the `none` bytes). A `CStep` ignores the thread
state's own bytes (it runs on any bytes agreeing with its events), so the thread states can be
given the bytes encoding the mask (`encB`, `encT`):

* `cstep_withBytes`, `cstep_strip`, `cstepI_strip`: `CStep`/`CStepI` do not see the own bytes of
  the states;
* **`cstepS_of_cstep`**: a `CStep` to a running state whose reads avoid the mask `U` is a `CStepS`
  step between the states encoding `U` and `U` without the written bytes;
* `ReadsAvoid U tr` (every step's reads avoid the mask before it), `maskAfter U tr`;
  **`crunS_of_crun`**: a `CRun` ending in a running state whose reads avoid the evolving mask is a
  `CRunS` run between the encoded states;
* `stop_encT`: `IselThread.Stop` does not see the encoded mask, so a `CStepS` realization ends
  where the `CStep` one does;
* `cstepS_ret_of_cstep`, **`cstepS_ret_iff`**: a bottom-frame return is a `CStepS` step exactly
  when the mask is empty (the returned state carries none), so the top-level contract ends
  before a return with masked bytes;
* `Refines.toTD`, `fresh0_of_mask`, **`Refines.toT_dirty`**, `uniform_of_parts`,
  **`Refines.toT_parts`**: the start-dirty set of a segment is its private set, its mask and the
  addresses that start no location of a thread-wide location partition (`PartDisj`, `OnParts`:
  no mixed-size accesses, the T2i restriction).
-/

namespace Concurrency.CallComposeT

open Prog ClifThread ClifThreadI

open Classical in
/-- **The bytes encoding the mask `U`**: `none` exactly at the masked bytes. -/
noncomputable def encB (U : Nat → Prop) : Bytes := fun a => if U a then none else some 0

/-- **The thread state carrying the mask `U` in its bytes.** -/
noncomputable def encT (U : Nat → Prop) : TState → TState
  | .run s => .run (withBytes s (encB U))
  | .ret v => .ret v

theorem maskOf_encT (U : Nat → Prop) (s : Clif.State) : maskOf (encT U (.run s)) = U := by
  funext a
  simp only [encT, maskOf, withBytes, encB]
  by_cases h : U a <;> simp [h]

theorem strip_encT (U : Nat → Prop) (t : TState) : strip (encT U t) = strip t := by
  cases t <;> rfl

/-- A `CStep` does not see the state's own bytes. -/
theorem cstep_withBytes {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {B : Bytes}
    {evs : List (Ev SKind BVal)} {t' : TState} :
    CStep env p (.run (withBytes s B)) evs t' ↔ CStep env p (.run s) evs t' := Iff.rfl

/-- A `CStep` determines its target up to the target's bytes. -/
theorem cstep_strip {env : Clif.Env} {p : Clif.Program} {t : TState}
    {evs : List (Ev SKind BVal)} {t' t'' : TState} (h : CStep env p t evs t')
    (e : strip t' = strip t'') : CStep env p t evs t'' := by
  cases t with
  | ret => exact h.elim
  | run s =>
    obtain ⟨hk, hB, hf⟩ := h
    exact ⟨hk, hB, fun B hB' => by
      obtain ⟨t3, h1, h2⟩ := hf B hB'
      exact ⟨t3, h1, h2.trans e⟩⟩

theorem slotByte_withBytes (s : Clif.State) (B : Bytes) :
    slotByte (.run (withBytes s B)) = slotByte (.run s) := rfl

/-- A `CStepI` determines its target up to the target's bytes and slot bytes. -/
theorem cstepI_strip {env : Clif.Env} {p : Clif.Program} {x : TStateI}
    {evs : List (Ev SKind BVal)} {t t' : TState} {V : Nat → Prop}
    (h : CStepI env p x evs (t, V)) (e : strip t = strip t')
    (hs : ∀ a, slotByte t a → slotByte t' a) : CStepI env p x evs (t', V) := by
  obtain ⟨t0, U⟩ := x
  cases t0 with
  | ret => exact h.elim
  | run s =>
    obtain ⟨hk, hB, hm, hf⟩ := h
    refine ⟨hk, hB, fun a ha => (hm a ha).imp_right (hs a), fun B hB' => ?_⟩
    obtain ⟨t3, h1, h2⟩ := hf B hB'
    exact ⟨t3, h1, h2.trans e⟩

/-- **A `CStep` whose reads avoid the mask is a `CStepS` step of the encoded states**
(module doc). -/
theorem cstepS_of_cstep {env : Clif.Env} {p : Clif.Program} {s s' : Clif.State}
    {evs : List (Ev SKind BVal)} (h : CStep env p (.run s) evs (.run s')) {U : Nat → Prop}
    (hr : ∀ e ∈ evs, e.dir = .R → ∀ k < e.n, ¬ U (e.loc + k)) :
    CStepS env p (encT U (.run s)) evs (encT (fun a => U a ∧ ¬ writes evs a) (.run s')) := by
  unfold CStepS
  rw [maskOf_encT, maskOf_encT]
  have h1 := cstepI_of_cstep (cstep_withBytes.mpr h : CStep env p (.run (withBytes s (encB U)))
    evs (.run s')) hr
  exact cstepI_strip h1 (strip_encT _ _).symm fun a ha => ha

/-- **The reads of the steps `tr` avoid the mask before each step** (the written bytes leave
it). -/
def ReadsAvoid : (Nat → Prop) → List (List (Ev SKind BVal)) → Prop
  | _, [] => True
  | U, evs :: tr => (∀ e ∈ evs, e.dir = .R → ∀ k < e.n, ¬ U (e.loc + k)) ∧
      ReadsAvoid (fun a => U a ∧ ¬ writes evs a) tr

/-- The mask after the steps `tr`. -/
def maskAfter : (Nat → Prop) → List (List (Ev SKind BVal)) → Nat → Prop
  | U, [] => U
  | U, evs :: tr => maskAfter (fun a => U a ∧ ¬ writes evs a) tr

/-- **A `CRun` to a running state whose reads avoid the evolving mask is a `CRunS` run of the
encoded states** (module doc). -/
theorem crunS_of_crun {env : Clif.Env} {p : Clif.Program} :
    ∀ {t : TState} {trS : List (List (Ev SKind BVal))} {t' : TState},
      ClifCStepTerm.CRun env p t trS t' → ∀ {s' : Clif.State}, t' = .run s' →
      ∀ {U : Nat → Prop}, ReadsAvoid U trS →
        CRunS env p (encT U t) trS (encT (maskAfter U trS) t')
  | _, _, _, .nil, _, _, _, _ => .nil
  | _, _, _, .cons (t := t0) (t' := t1) hs hr, s', e, U, ⟨ha, hrest⟩ => by
    cases t0 with
    | ret => exact hs.elim
    | run s =>
      cases t1 with
      | ret v =>
        cases hr with
        | nil => cases e
        | cons h2 _ => exact h2.elim
      | run s1 =>
        exact .cons (cstepS_of_cstep hs ha) (crunS_of_crun hr e hrest)

/-- **Where a realized prefix stops does not depend on the encoded mask**: `IselThread.Stop`
(no `CStep`, or an `atomic_cas` on read-only data) sees neither the state's own bytes. The
`CStepS` realization ends where the `CStep` one does (`Stop` of the CLIF thread state). -/
theorem stop_encT {env : Clif.Env} {p : Clif.Program} (U : Nat → Prop) (t : TState) :
    IselThread.Stop env p (encT U t) ↔ IselThread.Stop env p t := by
  cases t with
  | ret v => exact Iff.rfl
  | run s =>
    unfold IselThread.Stop IselThread.CasRO ClifCStepTerm.Done
    simp only [encT, cstep_withBytes]
    constructor
    · rintro (h | ⟨s', stm, rest, ty, fl, pp, ex, x, a, n, e, h1, h2, h3, h4⟩)
      · exact .inl h
      · cases e
        exact .inr ⟨s, stm, rest, ty, fl, pp, ex, x, a, n, rfl, h1, h2, h3, h4⟩
    · rintro (h | ⟨s', stm, rest, ty, fl, pp, ex, x, a, n, e, h1, h2, h3, h4⟩)
      · exact .inl h
      · cases e
        exact .inr ⟨withBytes s (encB U), stm, rest, ty, fl, pp, ex, x, a, n, rfl, h1, h2, h3, h4⟩

/-! ## Returns of the bottom frame -/

/-- **A `CStep` return whose reads avoid the mask and whose writes cover it is a `CStepS` step**
(the returned state carries the empty mask). -/
theorem cstepS_ret_of_cstep {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    {evs : List (Ev SKind BVal)} {v : List Clif.Val} (h : CStep env p (.run s) evs (.ret v))
    {U : Nat → Prop} (hr : ∀ e ∈ evs, e.dir = .R → ∀ k < e.n, ¬ U (e.loc + k))
    (hU : ∀ a, U a → writes evs a) : CStepS env p (encT U (.run s)) evs (.ret v) := by
  unfold CStepS
  rw [maskOf_encT]
  have h1 := cstepI_of_cstep (cstep_withBytes.mpr h : CStep env p (.run (withBytes s (encB U)))
    evs (.ret v)) hr
  have e : (fun a => U a ∧ ¬ writes evs a) = maskOf (.ret v) := by
    funext a; simp only [maskOf, eq_iff_iff, iff_false]; exact fun ⟨hu, hw⟩ => hw (hU a hu)
  rw [e] at h1
  exact cstepI_strip h1 rfl fun a ha => ha

/-- **An event-free return keeping the bytes is a `CStepS` step exactly from the empty mask**:
the returned state carries no mask, so a bottom frame cannot return with masked bytes (the
top-level contract ends before such a return). -/
theorem cstepS_ret_iff {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    {v : List Clif.Val} (hc : CStep env p (.run s) [] (.ret v))
    (h : ∀ B, res (Clif.step env p (withBytes s B)) = some (.ret v, B)) (U : Nat → Prop) : CStepS env p (encT U (.run s)) [] (.ret v) ↔ ∀ a, ¬ U a := by
  constructor
  · intro hS a hu
    obtain ⟨-, -, -, hf⟩ := hS
    obtain ⟨t'', h1, -⟩ := hf (fun _ => some 0) trivial
    rw [maskOf_encT] at h1
    simp only [encT, withBytes] at h1
    have h2 := h (mix U fun _ => some 0)
    simp only [withBytes] at h2
    rw [h2] at h1
    have h3 := congrFun (Option.some.inj h1 |> congrArg Prod.snd) a
    simp [mix, hu, maskOf, applyEvs] at h3
  · intro hU
    exact cstepS_ret_of_cstep hc (fun _ h => nomatch h) fun a ha => absurd ha (hU a)

/-! ## The refinement of a segment with a start-dirty set -/

/-- **A `Refines` with private set `P` is a `RefinesT` from a start-dirty set `D`** whose source
reads follow a source write at their location (`fresh0`); unmatched writes are in `P`, which
no source event touches, so `fresh` holds. -/
theorem Refines.toTD {K K' V : Type} {MK : K → K' → Prop} {P D : Nat → Prop}
    {pairT : Nat × Nat → Nat × Nat → Prop} {trS : List (List (Ev K V))}
    {trT : List (List (Ev K' V))} {ψ : Nat × Nat → Nat × Nat}
    (h : ThreadRefine.Refines MK P pairT trS trT ψ)
    (hD : ∀ p x, ThreadRefine.evAt trS p = some x → x.dir = .R → D x.loc →
      ∃ q x', ThreadRefine.evAt trS q = some x' ∧ x'.dir = .W ∧ x'.loc = x.loc ∧
        ThreadRefine.Lt (ψ q) (ψ p)) :
    PrivCohT.RefinesT MK D (fun _ => P) pairT trS trT ψ where
  ev := h.ev
  mono := h.mono
  len := h.len
  pair := h.pair
  pair_inv := h.pair_inv
  shared := h.shared
  priv := h.priv
  fresh0 := hD
  fresh p x hx hR q y hy hW hl _ hu :=
    absurd (hl ▸ h.priv q y hy hW hu) (h.shared p x hx (by rw [hR]; decide))

/-- **The writes of a trace that cover the first byte of a read of it start there** (no
mixed-size access to a location within the trace). -/
def Uniform (trS : List (List (Ev SKind BVal))) : Prop :=
  ∀ p x q y, ThreadRefine.evAt trS p = some x → ThreadRefine.evAt trS q = some y →
    x.dir = .R → y.dir = .W → y.loc ≤ x.loc → x.loc < y.loc + y.n → y.loc = x.loc

open ThreadRefine in
/-- **A read of a byte masked at the start follows a write there** (the mask makes a read of an
unwritten masked byte stuck): with the reads avoiding the evolving mask, uniform accesses and
nonempty reads, every source read at a location masked at the start follows a source write at
that location, in any order-preserving map `ψ`. -/
theorem fresh0_of_mask {ψ : Nat × Nat → Nat × Nat} :
    ∀ {trS : List (List (Ev SKind BVal))} {U : Nat → Prop}, ReadsAvoid U trS → Uniform trS →
      (∀ p x, evAt trS p = some x → 0 < x.n) →
      (∀ p q, (evAt trS p).isSome → (evAt trS q).isSome → Lt p q → Lt (ψ p) (ψ q)) →
      ∀ p x, evAt trS p = some x → x.dir = .R → U x.loc →
        ∃ q x', evAt trS q = some x' ∧ x'.dir = .W ∧ x'.loc = x.loc ∧ Lt (ψ q) (ψ p)
  | [], _, _, _, _, _, p, x, hx, _, _ => by simp [evAt] at hx
  | evs :: tr, U, ⟨ha, hrest⟩, hu, hpos, hmono, ⟨j, i⟩, x, hx, hR, hU => by
    cases j with
    | zero =>
      have hxm : x ∈ evs := by
        simp only [evAt, List.getElem?_cons_zero, Option.bind_some] at hx
        exact List.mem_of_getElem? hx
      exact absurd (by simpa using hU) (ha x hxm hR 0 (hpos _ x hx))
    | succ j =>
      by_cases hw : writes evs x.loc
      · obtain ⟨e, he, heW, hle, hlt⟩ := hw
        obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem he
        have hq : evAt (evs :: tr) (0, i') = some evs[i'] := by
          simp [evAt, List.getElem?_eq_getElem hi']
        refine ⟨(0, i'), evs[i'], hq, heW, hu _ _ _ _ hx hq hR heW hle hlt, ?_⟩
        exact hmono _ _ (by rw [hq]; rfl) (by rw [hx]; rfl) (.inl (Nat.succ_pos _))
      · have hx' : evAt tr (j, i) = some x := by simpa [evAt] using hx
        have hu' : Uniform tr := fun p x q y hp hq => hu (p.1 + 1, p.2) x (q.1 + 1, q.2) y
          (by simpa [evAt] using hp) (by simpa [evAt] using hq)
        obtain ⟨q, x', hq, hW, hl, hlt⟩ := fresh0_of_mask (ψ := fun r => ψ (r.1 + 1, r.2))
          hrest hu' (fun r y hr => hpos (r.1 + 1, r.2) y (by simpa [evAt] using hr))
          (fun r r' hr hr' hl => hmono _ _ (by simpa [evAt] using hr) (by simpa [evAt] using hr')
            (by rcases hl with h | ⟨h1, h2⟩
                · exact .inl (by simp only; omega)
                · exact .inr ⟨by simp only; omega, h2⟩))
          (j, i) x hx' hR ⟨hU, hw⟩
        exact ⟨(q.1 + 1, q.2), x', by simpa [evAt] using hq, hW, hl, hlt⟩

end Concurrency.CallComposeT

namespace Concurrency.CallComposeT

open Prog ClifThread ClifThreadI ThreadRefine

/-- **The start-dirty set of a segment** (#473 (4), `SegOkG`): a segment refined with private set
`P`, whose reads avoid the evolving mask from `U`, with uniform accesses (no mixed-size access to
a location within the trace; the thread-wide location partition gives it) and nonempty reads, is
a `RefinesT` from the start-dirty set `P ∪ U ∪ NS` for any set `NS` of addresses at which no
source read starts (addresses that start no location of the partition). -/
theorem Refines.toT_dirty {MK : SKind → AKind → Prop} {P U NS : Nat → Prop}
    {pairT : Nat × Nat → Nat × Nat → Prop} {trS : List (List (Ev SKind BVal))}
    {trT : List (List (Ev AKind BVal))} {ψ : Nat × Nat → Nat × Nat}
    (h : ThreadRefine.Refines MK P pairT trS trT ψ) (hra : ReadsAvoid U trS) (hu : Uniform trS)
    (hpos : ∀ p x, evAt trS p = some x → 0 < x.n)
    (hns : ∀ p x, evAt trS p = some x → x.dir = .R → ¬ NS x.loc) :
    PrivCohT.RefinesT MK (fun a => P a ∨ U a ∨ NS a) (fun _ => P) pairT trS trT ψ :=
  Refines.toTD h fun p x hx hR hD => by
    rcases hD with hP | hU | hN
    · exact absurd hP (h.shared p x hx (by rw [hR]; decide))
    · exact fresh0_of_mask hra hu hpos h.mono p x hx hR hU
    · exact absurd hN (hns p x hx hR)

/-- **A location partition**: overlapping locations start at the same address. -/
def PartDisj (Loc : Nat → Nat → Prop) : Prop :=
  ∀ a n b m, Loc a n → Loc b m → b ≤ a → a < b + m → b = a

/-- **Every read and write of the trace accesses a location of the partition.** -/
def OnParts (Loc : Nat → Nat → Prop) (trS : List (List (Ev SKind BVal))) : Prop :=
  ∀ p x, evAt trS p = some x → x.dir ≠ .F → Loc x.loc x.n

/-- **Accesses on a location partition are uniform** (thread-wide form of `Uniform`). -/
theorem uniform_of_parts {Loc : Nat → Nat → Prop} {trS : List (List (Ev SKind BVal))}
    (hd : PartDisj Loc) (ho : OnParts Loc trS) : Uniform trS :=
  fun p x q y hx hy hR hW hle hlt =>
    hd _ _ _ _ (ho p x hx (by rw [hR]; decide)) (ho q y hy (by rw [hW]; decide)) hle hlt

/-- **The start-dirty set on a location partition**: `Refines.toT_dirty` with the addresses that
start no location of the partition. -/
theorem Refines.toT_parts {MK : SKind → AKind → Prop} {P U : Nat → Prop} {Loc : Nat → Nat → Prop}
    {pairT : Nat × Nat → Nat × Nat → Prop} {trS : List (List (Ev SKind BVal))}
    {trT : List (List (Ev AKind BVal))} {ψ : Nat × Nat → Nat × Nat}
    (h : ThreadRefine.Refines MK P pairT trS trT ψ) (hra : ReadsAvoid U trS)
    (hd : PartDisj Loc) (ho : OnParts Loc trS) (hpos : ∀ p x, evAt trS p = some x → 0 < x.n) :
    PrivCohT.RefinesT MK (fun a => P a ∨ U a ∨ ¬ ∃ n, Loc a n) (fun _ => P) pairT trS trT ψ :=
  Refines.toT_dirty h hra (uniform_of_parts hd ho) hpos fun p x hx hR hn =>
    hn ⟨x.n, ho p x hx (by rw [hR]; decide)⟩

end Concurrency.CallComposeT
