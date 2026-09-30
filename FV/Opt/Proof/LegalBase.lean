import FV.Opt.Proof.LegalPat

/-!
# The legalisation relation: value images, the value relation, the source invariant

Facts `Opt.Legal.check` establishes (`Good`), and the relations the simulation
(`FV/Opt/Proof/LegalSim.lean`) maintains between a source frame of `f` and a target frame of
its legalisation `g`:

* `VRel`: every value `v < T0` the source defines is represented in the target — by itself
  (`plain` values) or by its pair, the low and high halves of the `i128` value (`RelV`);
* `SrcInv`: every value the source defines is consistent with its unique definition in `f`:
  its static type, its constant (`iconst`), the constant low half of an `iconcat` — what the
  shift-amount and `extend` plans rely on.

A target write never clobbers the image (`img`) of another source value: images of distinct
values are disjoint and no temporary is in an image (`img_disj`, `img_nonfresh`).
-/

namespace Opt.Legal

open Clif

/-- `omega` on goals with `ValueId`-typed facts (it does not unfold the abbreviation). -/
macro "vomega" : tactic => `(tactic| ((try simp only [Clif.ValueId] at *); omega))

/-! ## List lookups -/

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      have : a = k := by simpa using hk
      subst this; cases h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

theorem lookup_of_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (hnd : (l.map (·.1)).Nodup) (h : (a, b) ∈ l) : l.lookup a = some b := by
  induction l with
  | nil => cases h
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.lookup]
    rcases List.mem_cons.1 h with h | h
    · cases h; simp
    · have hne : a ≠ k := fun hak => hnd.1 (hak ▸ List.mem_map_of_mem (f := (·.1)) h)
      simp only [show (a == k) = false from by simpa using hne]
      exact ih hnd.2 h

/-! ## Facts of an accepted check -/

/-- What `check` establishes besides the per-block checks. -/
structure Good (C : Ctx) : Prop where
  name : C.g.name = C.f.name
  slots : C.g.slots = C.f.slots
  globals : C.g.globals = C.f.globals
  sig : sigExp C.f.sig = some C.g.sig
  defs : ((defsOf C.f).map (·.1)).Nodup
  ids : ∀ v ∈ idsOf C.f, v < C.T0
  cert : certOk C = true
  blocks : ∃ b bs b' bs', C.f.blocks = b :: bs ∧ C.g.blocks = b' :: bs' ∧
    bs.length = bs'.length ∧ blockOk C true b b' = true ∧
    ∀ x y, (x, y) ∈ bs.zip bs' → blockOk C false x y = true

theorem check_good {f g : Function} {cert : Legalize128.Cert} (h : check f g cert = true) :
    Good ⟨f, g, cert⟩ := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_⟩
  split at h9
  · rename_i b bs b' bs' hf hg
    simp only [Bool.and_eq_true, List.all_eq_true] at h9
    refine ⟨b, bs, b', bs', hf, hg, ?_, h9.1, fun x y hxy => h9.2 (x, y) hxy⟩
    rw [hf, hg] at h8; simpa using h8.symm
  · cases h9

theorem Good.zero_ge {C : Ctx} (hG : Good C) : C.T0 ≤ C.zero := by
  have := hG.cert
  simp only [certOk, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1

theorem Good.pair_facts {C : Ctx} (hG : Good C) {v a b : ValueId} (h : C.pair v = some (a, b)) :
    C.T0 ≤ a ∧ C.T0 ≤ b ∧ a ≠ b ∧ a ≠ C.zero ∧ b ≠ C.zero := by
  have hc := hG.cert
  simp only [certOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  have := hc.1.2 _ (lookup_mem h)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1.1.2, this.1.1.2, this.1.1.1.1, this.1.2, this.2⟩

theorem Good.pair_disj {C : Ctx} (hG : Good C) {v w a b c d : ValueId}
    (h1 : C.pair v = some (a, b)) (h2 : C.pair w = some (c, d)) (hvw : v ≠ w) :
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  have hc := hG.cert
  simp only [certOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  have := hc.2 _ (lookup_mem h1) _ (lookup_mem h2)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  rcases this with h | h
  · exact absurd h hvw
  · exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem mem_comps {C : Ctx} {v a b : ValueId} (h : C.pair v = some (a, b)) :
    a ∈ C.comps ∧ b ∈ C.comps := by
  have := lookup_mem h
  constructor <;> simp only [Ctx.comps, List.mem_flatMap] <;> exact ⟨(v, a, b), this, by simp⟩

theorem fresh_spec {C : Ctx} {t : ValueId} (h : C.fresh t = true) :
    C.T0 ≤ t ∧ t ≠ C.zero ∧ t ∉ C.comps := by
  simp only [Ctx.fresh, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## Images -/

/-- The target values representing a source value. -/
def img (C : Ctx) (v : ValueId) : List ValueId :=
  match C.pair v with
  | some (a, b) => [a, b]
  | none => [v]

theorem img_nonfresh {C : Ctx} (hG : Good C) {v w : ValueId} (hv : v < C.T0)
    (hw : w ∈ img C v) : C.fresh w = false := by
  cases hf : C.fresh w with
  | false => rfl
  | true =>
    obtain ⟨h1, -, h3⟩ := fresh_spec hf
    cases hp : C.pair v with
    | some ab =>
      obtain ⟨a, b⟩ := ab
      obtain ⟨ha, hb⟩ := mem_comps hp
      simp only [img, hp, List.mem_cons, List.mem_nil_iff, or_false] at hw
      rcases hw with rfl | rfl
      · exact absurd ha h3
      · exact absurd hb h3
    | none =>
      simp only [img, hp, List.mem_singleton] at hw
      vomega

theorem img_disj {C : Ctx} (hG : Good C) {u v w : ValueId} (hu : u < C.T0) (hv : v < C.T0)
    (huv : u ≠ v) (hw : w ∈ img C v) : w ∉ img C u := by
  intro hw'
  cases hpv : C.pair v with
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hf := hG.pair_facts hpv
    simp only [img, hpv, List.mem_cons, List.mem_nil_iff, or_false] at hw
    cases hpu : C.pair u with
    | some cd =>
      obtain ⟨c, d⟩ := cd
      obtain ⟨h1, h2, h3, h4⟩ := hG.pair_disj hpu hpv huv
      simp only [img, hpu, List.mem_cons, List.mem_nil_iff, or_false] at hw'
      rcases hw with rfl | rfl <;> rcases hw' with h | h <;> subst h <;> simp_all
    | none =>
      simp only [img, hpu, List.mem_singleton] at hw'
      rcases hw with rfl | rfl <;> vomega
  | none =>
    simp only [img, hpv, List.mem_singleton] at hw
    subst hw
    cases hpu : C.pair u with
    | some cd =>
      obtain ⟨c, d⟩ := cd
      have hf := hG.pair_facts hpu
      simp only [img, hpu, List.mem_cons, List.mem_nil_iff, or_false] at hw'
      rcases hw' with h | h <;> vomega
    | none =>
      simp only [img, hpu, List.mem_singleton] at hw'
      exact huv hw'.symm

/-! ## The value relation -/

/-- The target registers `ρ'` represent the source value `x` of `v`. -/
def RelV (C : Ctx) (ρ' : Regs) (v : ValueId) (x : Val) : Prop :=
  match C.pair v with
  | some (a, b) => ∃ l h : BitVec 64, x = ⟨.i128, h ++ l⟩ ∧ ρ' a = some ⟨.i64, l⟩ ∧
      ρ' b = some ⟨.i64, h⟩
  | none => ρ' v = some x

/-- Every value of `f` defined in the source registers is represented in the target. -/
def VRel (C : Ctx) (ρ ρ' : Regs) : Prop :=
  ∀ v x, v < C.T0 → ρ v = some x → RelV C ρ' v x

theorem RelV.plain {C : Ctx} {ρ' : Regs} {v : ValueId} {x : Val} (hp : C.pair v = none) :
    RelV C ρ' v x ↔ ρ' v = some x := by
  simp only [RelV, hp]

theorem RelV.pair {C : Ctx} {ρ' : Regs} {v a b : ValueId} {x : Val}
    (hp : C.pair v = some (a, b)) :
    RelV C ρ' v x ↔ ∃ l h : BitVec 64, x = ⟨.i128, h ++ l⟩ ∧ ρ' a = some ⟨.i64, l⟩ ∧
      ρ' b = some ⟨.i64, h⟩ := by
  simp only [RelV, hp]

theorem RelV.congr {C : Ctx} {ρ' ρ'' : Regs} {v : ValueId} {x : Val} (h : RelV C ρ' v x)
    (hag : ∀ w ∈ img C v, ρ'' w = ρ' w) : RelV C ρ'' v x := by
  cases hp : C.pair v with
  | some ab =>
    obtain ⟨a, b⟩ := ab
    rw [RelV.pair hp] at h ⊢
    simp only [img, hp, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq] at hag
    obtain ⟨l, hh, h1, h2, h3⟩ := h
    exact ⟨l, hh, h1, by rw [hag.1, h2], by rw [hag.2, h3]⟩
  | none =>
    rw [RelV.plain hp] at h ⊢
    simp only [img, hp, List.mem_singleton, forall_eq] at hag
    rw [hag, h]

/-- **Updating the relation.** The source defines `rs` (and keeps every other value); the
target represents the new values of `rs`, and keeps every non-fresh value outside the images
of `rs`. -/
theorem VRel.update {C : Ctx} (hG : Good C) {ρ ρ' ρ1 ρ1' : Regs} (h : VRel C ρ ρ')
    {rs : List ValueId} (hsrc : ∀ v, v ∉ rs → ρ1 v = ρ v)
    (hnew : ∀ v ∈ rs, v < C.T0 → ∀ x, ρ1 v = some x → RelV C ρ1' v x)
    (htgt : ∀ w, C.fresh w = false → (∀ v ∈ rs, v < C.T0 → w ∉ img C v) → ρ1' w = ρ' w) :
    VRel C ρ1 ρ1' := by
  intro v x hv hx
  by_cases hvr : v ∈ rs
  · exact hnew v hvr hv x hx
  · rw [hsrc v hvr] at hx
    refine (h v x hv hx).congr fun w hw => htgt w (img_nonfresh hG hv hw) fun u hu hut =>
      img_disj hG hut hv (fun h => hvr (h ▸ hu)) hw

/-- Target-only writes of fresh values keep the relation. -/
theorem VRel.fresh_writes {C : Ctx} (hG : Good C) {ρ ρ' ρ1' : Regs} (h : VRel C ρ ρ')
    (htgt : ∀ w, C.fresh w = false → ρ1' w = ρ' w) : VRel C ρ ρ1' :=
  VRel.update (rs := []) hG h (fun _ _ => rfl) (fun _ h => by cases h) (fun w hw _ => htgt w hw)

/-- A plain source value's target value. -/
theorem VRel.get_plain {C : Ctx} {ρ ρ' : Regs} (h : VRel C ρ ρ') {v : ValueId} {x : Val}
    (hv : v < C.T0) (hp : C.plain v = true) (hx : ρ v = some x) : ρ' v = some x := by
  have := h v x hv hx
  simp only [Ctx.plain, Option.isNone_iff_eq_none] at hp
  rwa [RelV.plain hp] at this

/-- An `i128` source value's pair. -/
theorem VRel.get_pair {C : Ctx} {ρ ρ' : Regs} (h : VRel C ρ ρ') {v a b : ValueId} {x : Val}
    (hv : v < C.T0) (hp : C.pair v = some (a, b)) (hx : ρ v = some x) :
    ∃ l h : BitVec 64, x = ⟨.i128, h ++ l⟩ ∧ ρ' a = some ⟨.i64, l⟩ ∧ ρ' b = some ⟨.i64, h⟩ :=
  (RelV.pair hp).1 (h v x hv hx)

/-! ## The source invariant -/

/-- The value `x` of `v` agrees with the unique definition of `v` in `f`. -/
def DefOk (f : Function) (v : ValueId) (x : Val) : Prop :=
  tyOf f v = some x.ty ∧ (∀ c, constOf f v = some c → x.bits.toNat = c) ∧
    (∀ c, concatConst f v = some c → x.bits.toNat % 2 ^ 64 = c)

def SrcInv (f : Function) (ρ : Regs) : Prop := ∀ v x, ρ v = some x → DefOk f v x

theorem mem_defsOf_stmt {f : Function} {B : Block} (hB : B ∈ f.blocks) {s : Stmt}
    (hs : s ∈ B.body) {i : Nat} {r : ValueId} (hi : s.results[i]? = some r) :
    (r, (s.inst.resultTypes (sigOfF f) (declOfF f)).bind (·[i]?), some s.inst) ∈ defsOf f := by
  simp only [defsOf, List.mem_flatMap]
  refine ⟨B, hB, ?_⟩
  simp only [blockDefs, List.mem_append, List.mem_flatMap]
  refine .inr ⟨s, hs, ?_⟩
  simp only [stmtDefs, List.mem_map]
  exact ⟨(r, i), List.mem_zipIdx_iff_getElem?.2 (by simpa using hi), rfl⟩

theorem mem_defsOf_param {f : Function} {B : Block} (hB : B ∈ f.blocks) {v : ValueId} {t : Ty}
    (hp : (v, t) ∈ B.params) : (v, some t, none) ∈ defsOf f := by
  simp only [defsOf, List.mem_flatMap]
  refine ⟨B, hB, ?_⟩
  simp only [blockDefs, List.mem_append, List.mem_map]
  exact .inl ⟨(v, t), hp, rfl⟩

end Opt.Legal
