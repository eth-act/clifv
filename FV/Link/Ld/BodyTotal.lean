import FV.Link.Ld.BuildProof
import FV.Link.Ld.LayoutProof

/-! # The body of `lean-ld`'s plan is built when its relocations apply (A1c, #409)

`assemble` (`FV/Link/Ld/Plan.lean`) builds the body from the plan's pieces (`buildBody`): each
piece's relocations applied (`Piece.relocated`), then its bytes placed at its file offset.
On `layout`'s plans every piece lies in the body (`layout_pieces_in`: its slot's file range,
`PInv`), so the body is built as soon as every relocation applies:

* `relocOkB ty r`: the relocation's value is in its type's range (`relocVal` succeeds,
  whatever the patched bytes: `relocVal_ok`);
* `Piece.relsOkB`: every relocation of a piece patches bytes inside the piece and `relocOkB`;
* **`buildBody_layout`**: on `layout`'s plan, `buildBody` succeeds when every piece's
  relocations are `relsOkB`; **`assemble_layout_ok`**: then `assemble` succeeds.

Witness: `tinyPiece_relsOk`.
-/

namespace Link.Ld

/-! ## One relocation -/

/-- **A relocation's value is in its type's range** (the checks of `relocVal`; a type
`relocVal` does not know fails). -/
def relocOkB (ty : Nat) (r : RelIn) : Bool :=
  let x := r.S + r.A
  let inR (v lo hi : Int) : Bool := decide (lo ≤ v ∧ v < hi)
  match ty with
  | 0 | 257 | 260 | 263 | 264 | 265 | 266 | 267 | 268 | 269 | 276 | 277 | 278 | 284 | 285 | 286
  | 299 | 312 | 542 | 551 | 563 | 564 | 569 => true
  | 258 => inR x (-2 ^ 31) (2 ^ 32)
  | 259 => inR x (-2 ^ 15) (2 ^ 16)
  | 261 => inR (x - r.P) (-2 ^ 31) (2 ^ 32)
  | 262 => inR (x - r.P) (-2 ^ 15) (2 ^ 16)
  | 274 => inR (x - r.P) (-2 ^ 20) (2 ^ 20)
  | 275 => inR ((page x - page r.P) / 4096) (-2 ^ 20) (2 ^ 20)
  | 279 => inR (x - r.P) (-2 ^ 15) (2 ^ 15)
  | 280 => inR (x - r.P) (-2 ^ 20) (2 ^ 20)
  | 282 | 283 => inR (x - r.P) (-2 ^ 27) (2 ^ 27) && (x - r.P) % 4 == 0
  | 311 => inR ((page (r.G + r.A) - page r.P) / 4096) (-2 ^ 20) (2 ^ 20)
  | 541 | 562 => inR r.tp 0 (2 ^ 32)
  | 549 => inR r.tp 0 (2 ^ 24)
  | 550 => inR r.tp 0 4096
  | _ => false

theorem inRange_ok {ty : Nat} {v lo hi : Int} (h : decide (lo ≤ v ∧ v < hi) = true) :
    inRange ty v lo hi = .ok () := by
  unfold inRange; simp only [of_decide_eq_true h, and_self, ↓reduceIte]; rfl

/-- **`relocVal` succeeds** on a relocation in its type's range, whatever the patched bytes. -/
theorem relocVal_ok {ty : Nat} {r : RelIn} (h : relocOkB ty r = true) (old : Nat) :
    ∃ v, relocVal ty r old = .ok v := by
  unfold relocOkB at h
  unfold relocVal
  split at h <;>
    first
    | (simp only [Bool.and_eq_true, beq_iff_eq] at h
       simp only [inRange_ok h.1, bind, Except.bind, h.2, bne_self_eq_false, Bool.false_eq_true,
         ↓reduceIte, pure, Except.pure]
       exact ⟨_, rfl⟩)
    | (simp only [inRange_ok h, bind, Except.bind, pure, Except.pure]; exact ⟨_, rfl⟩)
    | exact ⟨_, rfl⟩
    | cases h

/-! ## A piece -/

/-- **A piece's relocations apply**: each patches bytes inside the piece, in its type's range. -/
def Piece.relsOkB (p : Piece) : Bool :=
  p.rels.all fun r => decide (r.off + relocWidth r.ty ≤ p.bytes.size) && relocOkB r.ty r.ri

theorem applyRel_ok' {b : ByteArray} {r : Rel} (h1 : r.off + relocWidth r.ty ≤ b.size)
    (h2 : relocOkB r.ty r.ri = true) : ∃ b', applyRel b r = .ok b' := by
  obtain ⟨v, hv⟩ := relocVal_ok h2 (rdLE b r.off (relocWidth r.ty))
  unfold applyRel
  simp only [h1, ↓reduceIte, hv]
  exact ⟨_, rfl⟩

theorem foldlM_applyRel_ok : ∀ {rs : List Rel} {b : ByteArray},
    (∀ r ∈ rs, r.off + relocWidth r.ty ≤ b.size ∧ relocOkB r.ty r.ri = true) →
    ∃ b', rs.foldlM applyRel b = .ok b'
  | [], b, _ => ⟨b, rfl⟩
  | r :: rs, b, h => by
    obtain ⟨b1, h1⟩ := applyRel_ok' (h r (List.mem_cons_self ..)).1 (h r (List.mem_cons_self ..)).2
    have hs := applyRel_size h1
    obtain ⟨b2, h2⟩ := foldlM_applyRel_ok (rs := rs) (b := b1) fun r' hr' => by
      rw [hs]; exact h r' (List.mem_cons_of_mem _ hr')
    exact ⟨b2, by rw [List.foldlM_cons, h1]; exact h2⟩

/-- **A piece is relocated** when its relocations apply. -/
theorem relocated_ok {p : Piece} (h : p.relsOkB = true) : ∃ b, p.relocated = .ok b := by
  unfold Piece.relsOkB at h
  exact foldlM_applyRel_ok fun r hr => by
    have := List.all_eq_true.1 h r hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this

/-! ## The body -/

theorem body_ok : ∀ {ps : List Piece} {body : ByteArray},
    (∀ p ∈ ps, p.relsOkB = true ∧ p.fo + p.bytes.size ≤ body.size) →
    ∃ body', ps.foldlM bodyStep body = .ok body'
  | [], body, _ => ⟨body, rfl⟩
  | p :: ps, body, h => by
    obtain ⟨hr, hin⟩ := h p (List.mem_cons_self ..)
    obtain ⟨b, hb⟩ := relocated_ok hr
    have hstep : bodyStep body p = .ok (place body p.fo b) := by
      unfold bodyStep
      rw [hb]
      simp only [bind, Except.bind]
      rw [relocated_size hb]
      simp only [hin, ↓reduceIte, pure, Except.pure]
    obtain ⟨b2, h2⟩ := body_ok (ps := ps) (body := place body p.fo b) fun q hq => by
      rw [place_size (by rw [relocated_size hb]; exact hin)]
      exact h q (List.mem_cons_of_mem _ hq)
    exact ⟨b2, by rw [List.foldlM_cons, hstep]; exact h2⟩

/-- **The pieces of `layout`'s plan lie in its body.** -/
theorem layout_pieces_in {o : Opts} {st : St} {g : GcOut} {pl : Plan} {m : String}
    (h : layout o st g = .ok (pl, m)) : ∀ p ∈ pl.pieces, p.fo + p.bytes.size ≤ pl.size := by
  obtain ⟨ps, hps, -, hpcs, hsize⟩ := layout_eq h
  have hi := PInv_layPre o st g
  obtain ⟨-, hin⟩ := pieces_pairwise hps hi.slots
  intro p hp
  rw [hpcs] at hp
  obtain ⟨x, hx, hb, hfo, hsz⟩ := hin p hp
  have := (hi.slotsIn x hx hb).2
  rw [hsize]; omega

/-- **The body of `layout`'s plan is built** when every piece's relocations apply. -/
theorem buildBody_layout {o : Opts} {st : St} {g : GcOut} {pl : Plan} {m : String}
    (h : layout o st g = .ok (pl, m)) (hr : ∀ p ∈ pl.pieces, p.relsOkB = true) :
    ∃ body, buildBody pl.size pl.sorted = .ok body := by
  have hin := layout_pieces_in h
  unfold buildBody
  refine body_ok fun p hp => ?_
  have hp' := (List.mergeSort_perm pl.pieces _).mem_iff.1 hp
  refine ⟨hr p hp', ?_⟩
  show p.fo + p.bytes.size ≤ (⟨Array.replicate pl.size 0⟩ : ByteArray).size
  simp only [ByteArray.size, Array.size_replicate]
  exact hin p hp'

/-- **`assemble` succeeds on `layout`'s plan** when every piece's relocations apply. -/
theorem assemble_layout_ok {o : Opts} {st : St} {g : GcOut} {pl : Plan} {m : String}
    (h : layout o st g = .ok (pl, m)) (hr : ∀ p ∈ pl.pieces, p.relsOkB = true) :
    ∃ img, assemble pl = .ok img := by
  obtain ⟨body, hb⟩ := buildBody_layout h hr
  exact ⟨_, assemble_layout h hb⟩

/-! ## Non-vacuity -/

/-- `relocated_ok`'s premise holds of a piece with an `ABS64` (`FV/Link/Ld/BuildProof.lean`). -/
theorem tinyPiece_relsOk : tinyPiece.relsOkB = true := by decide +kernel

end Link.Ld
