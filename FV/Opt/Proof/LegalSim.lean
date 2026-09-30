import FV.Opt.Proof.LegalPlan

/-!
# The refinement theorem of `Opt.Legal.check`

A source frame of `f` and a target frame of its legalisation `g` are related (`FRel`) when
they run the same block at corresponding positions (`codeOk` of the remaining statements and
terminators), the target represents every source value (`VRel`), the source values agree
with their definitions (`SrcInv`) and the target holds the pad zero. Every source step is
matched by target steps (`step_sim`): pure plans by their pattern instances
(`pure_step`), the split `i128` load/store (`LegalMem`), the `__*ti3` helper calls
(`HelperOk`), expanded extern calls (`ExtLegal`), the condition patterns of `trapz`/`trapnz`
and `brif`, and branches with split block parameters. By induction on the fuel, the
legalised function refines the original under `Clif.runLoop` (`check_refines`): a return of
the source is a return of the target with the values expanded by the ABI groups of the
signature's returns, a trap the same trap.

Premises: calls of `f`/`g` go to the environment (`EnvOk`: no function of the program has an
extern's name), the environment's contracts (`HelperOk`, `ExtLegal`, `EnvKeepsAllocs`), valid
ranges below `2^64` at entry (`MemBounded`), and no memory-access trap in the source run
(`NoMemTrap`: the 16-byte access of the source and its two 8-byte halves agree whenever the
source access does not trap; `TrapsExplicit` of the backend theorem implies it).
-/

namespace Opt.Legal

open Clif Opt Opt.Legalize128

/-! ## Argument lists -/

/-- The value of the pad zero. -/
def zeroVal : Val := ⟨.i64, BitVec.ofInt 64 0⟩

theorem getMany_holds {fr : Frame} : ∀ {xs : List ValueId} {vs : List Val},
    fr.getMany xs = .ok vs → Holds fr.regs xs vs
  | [], vs, h => by
    simp only [Frame.getMany] at h
    cases h; trivial
  | x :: xs, vs, h => by
    simp only [Frame.getMany, Opt.Res.bind_eq_ok, Opt.Res.pure_eq_ok] at h
    obtain ⟨v, hv, vs', hvs, rfl⟩ := h
    exact ⟨get_ok hv, getMany_holds hvs⟩

theorem holds_getMany {fr : Frame} : ∀ {xs : List ValueId} {vs : List Val},
    Holds fr.regs xs vs → fr.getMany xs = .ok vs
  | [], [], _ => rfl
  | x :: xs, v :: vs, ⟨h1, h2⟩ => by
    simp only [Frame.getMany, Frame.get, h1, holds_getMany h2]
    rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem holds_append {ρ : Regs} : ∀ {xs ys : List ValueId} {vs ws : List Val},
    Holds ρ xs vs → Holds ρ ys ws → Holds ρ (xs ++ ys) (vs ++ ws)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, ⟨h1, h2⟩, h => ⟨h1, holds_append h2 h⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

theorem holds_mem {ρ : Regs} : ∀ {xs : List ValueId} {vs : List Val}, Holds ρ xs vs →
    ∀ x ∈ xs, ∃ v, ρ x = some v
  | [], [], _, x, hx => by cases hx
  | y :: ys, v :: vs, ⟨h1, h2⟩, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨v, h1⟩
    · exact holds_mem h2 x hx
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

/-- The expanded arguments hold the expanded values (the pads the zero). -/
theorem expandArgs_holds {C : Ctx} {ρ ρ' : Regs} (hV : VRel C ρ ρ')
    (hz : ρ' C.zero = some zeroVal) :
    ∀ {gs : List (List SlotEl)} {args args' : List ValueId} {vals : List Val},
    expandArgs C gs args = some args' → (∀ x ∈ args, x < C.T0) → Holds ρ args vals →
    ∃ vals', Holds ρ' args' vals' ∧ ExpRel gs vals vals'
  | [], [], args', vals, h, _, hv => by
    simp only [expandArgs, Option.some.injEq] at h
    subst h
    cases vals with
    | nil => exact ⟨[], trivial, trivial⟩
    | cons => exact hv.elim
  | g :: gs, v :: vs, args', vals, h, hlt, hv => by
    cases vals with
    | nil => exact hv.elim
    | cons x xs =>
      obtain ⟨hx, hxs⟩ := hv
      have hlt' : ∀ y ∈ vs, y < C.T0 := fun y hy => hlt y (List.mem_cons_of_mem _ hy)
      have hv0 : v < C.T0 := hlt v (List.mem_cons_self ..)
      match g, h with
      | [.val _], h =>
        simp only [expandArgs] at h
        split at h
        · rename_i hp
          obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.1 h
          obtain ⟨vals', h1, h2⟩ := expandArgs_holds hV hz hr hlt' hxs
          exact ⟨x :: vals', ⟨hV.get_plain hv0 hp hx, h1⟩, rfl, h2⟩
        · cases h
      | [.lo, .hi], h =>
        simp only [expandArgs] at h
        split at h
        · rename_i a b hp
          obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.1 h
          obtain ⟨vals', h1, h2⟩ := expandArgs_holds hV hz hr hlt' hxs
          obtain ⟨l, hh, rfl, ha, hb⟩ := hV.get_pair hv0 hp hx
          exact ⟨⟨.i64, l⟩ :: ⟨.i64, hh⟩ :: vals', ⟨ha, hb, h1⟩, ⟨l, hh, rfl, rfl, rfl⟩, h2⟩
        · cases h
      | [.pad, .lo, .hi], h =>
        simp only [expandArgs] at h
        split at h
        · rename_i a b hp
          obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.1 h
          obtain ⟨vals', h1, h2⟩ := expandArgs_holds hV hz hr hlt' hxs
          obtain ⟨l, hh, rfl, ha, hb⟩ := hV.get_pair hv0 hp hx
          exact ⟨zeroVal :: ⟨.i64, l⟩ :: ⟨.i64, hh⟩ :: vals', ⟨hz, ha, hb, h1⟩, rfl,
            ⟨l, hh, rfl, rfl, rfl⟩, h2⟩
        · cases h
      | [], h => simp [expandArgs] at h
      | [.pad], h => simp [expandArgs] at h
      | [.lo], h => simp [expandArgs] at h
      | [.hi], h => simp [expandArgs] at h
      | .val _ :: _ :: _, h => simp [expandArgs] at h
      | .lo :: .lo :: _, h => simp [expandArgs] at h
      | .lo :: .pad :: _, h => simp [expandArgs] at h
      | .lo :: .val _ :: _, h => simp [expandArgs] at h
      | .lo :: .hi :: _ :: _, h => simp [expandArgs] at h
      | .hi :: _ :: _, h => simp [expandArgs] at h
      | .pad :: .pad :: _, h => simp [expandArgs] at h
      | .pad :: .hi :: _, h => simp [expandArgs] at h
      | .pad :: .val _ :: _, h => simp [expandArgs] at h
      | [.pad, .lo], h => simp [expandArgs] at h
      | .pad :: .lo :: .lo :: _, h => simp [expandArgs] at h
      | .pad :: .lo :: .pad :: _, h => simp [expandArgs] at h
      | .pad :: .lo :: .val _ :: _, h => simp [expandArgs] at h
      | .pad :: .lo :: .hi :: _ :: _, h => simp [expandArgs] at h
  | [], _ :: _, _, _, h, _, _ => by simp [expandArgs] at h
  | _ :: _, [], _, _, h, _, _ => by simp [expandArgs] at h

theorem holds_setMany : ∀ {ρ ρ1 : Regs} {rs : List ValueId} {vs : List Val}, rs.Nodup →
    ρ.setMany rs vs = some ρ1 → Holds ρ1 rs vs
  | _, _, [], [], _, _ => trivial
  | ρ, ρ1, r :: rs, v :: vs, hnd, h => by
    simp only [Regs.setMany_cons] at h
    simp only [List.nodup_cons] at hnd
    exact ⟨by rw [setMany_other h hnd.1]; simp, holds_setMany hnd.2 h⟩
  | _, _, [], _ :: _, _, h => by simp [Regs.setMany] at h
  | _, _, _ :: _, [], _, h => by simp [Regs.setMany] at h

/-! ## Blocks -/

theorem find_zip {C : Ctx} {id : BlockId} : ∀ (bs bs' : List Block), bs.length = bs'.length →
    (∀ x y, (x, y) ∈ bs.zip bs' → blockOk C false x y = true) → ∀ {B : Block},
    bs.find? (·.id == id) = some B →
    ∃ B', bs'.find? (·.id == id) = some B' ∧ blockOk C false B B' = true
  | [], [], _, _, B, h => by simp at h
  | x :: xs, y :: ys, hl, hz, B, h => by
    have hxy := hz x y (by simp)
    have hid : y.id = x.id := by
      simp only [blockOk, Bool.and_eq_true, beq_iff_eq] at hxy; exact hxy.1.1
    simp only [List.find?_cons] at h ⊢
    cases hx : (x.id == id) with
    | true =>
      simp only [hx] at h
      cases h
      simp only [hid, hx]
      exact ⟨y, rfl, hxy⟩
    | false =>
      simp only [hx] at h
      simp only [hid, hx]
      exact find_zip xs ys (by simpa using hl) (fun a b hab => hz a b (by simp [hab])) h
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl

/-- A non-entry block of `f` and its rewrite. -/
theorem block_find {C : Ctx} (hG : Good C) {id : BlockId} {B : Block}
    (hB : C.f.block? id = some B) (hne : C.entryId? ≠ some id) :
    ∃ B', C.g.block? id = some B' ∧ blockOk C false B B' = true := by
  obtain ⟨b, bs, b', bs', hf, hg, hl, hb, hz⟩ := hG.blocks
  have hid : b'.id = b.id := by
    simp only [blockOk, Bool.and_eq_true, beq_iff_eq] at hb; exact hb.1.1
  have hbid : b.id ≠ id := by
    intro h; apply hne; simp [Ctx.entryId?, Function.entry?, hf, h]
  simp only [Function.block?, hf, List.find?_cons, show (b.id == id) = false by simpa using hbid,
    Bool.false_eq_true, ite_false] at hB
  simp only [Function.block?, hg, List.find?_cons, show (b'.id == id) = false by simpa [hid] using hbid,
    Bool.false_eq_true, ite_false]
  exact find_zip bs bs' hl hz hB

/-! ## Split block parameters -/

/-- The values of a branch to parameters `ps`: an `i128` value as its halves. -/
def BExp : List (ValueId × Ty) → List Val → List Val → Prop
  | [], [], [] => True
  | (_, t) :: ps, x :: xs, vs' =>
    if t = .i128 then ∃ a b rest, vs' = a :: b :: rest ∧ Halves x a b ∧ BExp ps xs rest
    else ∃ rest, vs' = x :: rest ∧ BExp ps xs rest
  | _, _, _ => False

theorem expandBC_holds {C : Ctx} {ρ ρ' : Regs} (hV : VRel C ρ ρ') :
    ∀ {ps : List (ValueId × Ty)} {args args' : List ValueId} {vals : List Val},
    expandBC C args ps = some args' → (∀ x ∈ args, x < C.T0) → Holds ρ args vals →
    ∃ vals', Holds ρ' args' vals' ∧ BExp ps vals vals'
  | [], [], args', vals, h, _, hv => by
    simp only [expandBC, Option.some.injEq] at h
    subst h
    cases vals with
    | nil => exact ⟨[], trivial, trivial⟩
    | cons => exact hv.elim
  | (p, t) :: ps, v :: vs, args', vals, h, hlt, hv => by
    cases vals with
    | nil => exact hv.elim
    | cons x xs =>
      obtain ⟨hx, hxs⟩ := hv
      have hlt' : ∀ y ∈ vs, y < C.T0 := fun y hy => hlt y (List.mem_cons_of_mem _ hy)
      have hv0 : v < C.T0 := hlt v (List.mem_cons_self ..)
      simp only [expandBC] at h
      by_cases ht : t = .i128
      · rw [if_pos (by simp [ht])] at h
        split at h
        · rename_i a b hp
          obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.1 h
          obtain ⟨vals', h1, h2⟩ := expandBC_holds hV hr hlt' hxs
          obtain ⟨l, hh, rfl, ha, hb⟩ := hV.get_pair hv0 hp hx
          refine ⟨⟨.i64, l⟩ :: ⟨.i64, hh⟩ :: vals', ⟨ha, hb, h1⟩, ?_⟩
          simp only [BExp, ht, ite_true]
          exact ⟨_, _, _, rfl, ⟨l, hh, rfl, rfl, rfl⟩, h2⟩
        · cases h
      · rw [if_neg (by simp [ht])] at h
        split at h
        · rename_i hp
          obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.1 h
          obtain ⟨vals', h1, h2⟩ := expandBC_holds hV hr hlt' hxs
          refine ⟨x :: vals', ⟨hV.get_plain hv0 hp hx, h1⟩, ?_⟩
          simp only [BExp, ht, ite_false]
          exact ⟨_, rfl, h2⟩
        · cases h
  | [], _ :: _, _, _, h, _, _ => by simp [expandBC] at h
  | _ :: _, [], _, _, h, _, _ => by simp [expandBC] at h

/-- The facts of `paramsOk` for a branch: target types, and every source parameter
represented after the parallel assignments. -/
theorem paramsOk_bind {C : Ctx} (hG : Good C) :
    ∀ {ps ps' : List (ValueId × Ty)} {vals vals' : List Val}, paramsOk C ps ps' = true →
    BExp ps vals vals' → vals.map (·.ty) = ps.map (·.2) →
    vals'.map (·.ty) = ps'.map (·.2) ∧
    (∀ {ρ1 ρ1' : Regs}, Holds ρ1 (ps.map (·.1)) vals → Holds ρ1' (ps'.map (·.1)) vals' →
      (ps.map (·.1)).Nodup → ∀ v ∈ ps.map (·.1), ∀ x, ρ1 v = some x → RelV C ρ1' v x) ∧
    (∀ w ∈ ps'.map (·.1), ∃ v ∈ ps.map (·.1), w ∈ img C v)
  | [], [], vals, vals', _, hb, _ => by
    cases vals with
    | cons => exact hb.elim
    | nil =>
      cases vals' with
      | cons => exact hb.elim
      | nil => exact ⟨rfl, ⟨fun _ _ _ v hv => by simp at hv, fun w hw => by simp at hw⟩⟩
  | (v, t) :: ps, ps', x :: xs, vals', hpo, hb, hty => by
    simp only [List.map_cons, List.cons.injEq] at hty
    simp only [BExp] at hb
    cases ps' with
    | nil => simp [paramsOk] at hpo
    | cons q ps'' =>
      obtain ⟨a, ta⟩ := q
      simp only [paramsOk] at hpo
      by_cases ht : t = .i128
      · rw [if_pos (by simp [ht])] at hpo
        rw [if_pos ht] at hb
        obtain ⟨a', b', rest, rfl, hh, hb⟩ := hb
        cases hp : C.pair v with
        | none => simp [hp] at hpo
        | some ab =>
        obtain ⟨a0, b0⟩ := ab
        cases ps'' with
        | nil => simp [hp] at hpo
        | cons q ps3 =>
          obtain ⟨b, tb⟩ := q
          simp only [hp, Bool.and_eq_true, beq_iff_eq] at hpo
          obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hpo⟩ := hpo
          obtain ⟨ih1, ih2, ih3⟩ := paramsOk_bind hG hpo hb hty.2
          obtain ⟨l, h, rfl, rfl, rfl⟩ := hh
          refine ⟨by simp [ih1], ?_, ?_⟩
          · intro ρ1 ρ1' h1 h1' hnd u hu y hy
            obtain ⟨h1a, h1b⟩ := h1
            obtain ⟨h1'a, h1'b, h1'c⟩ := h1'
            simp only [List.map_cons, List.nodup_cons] at hnd
            rcases List.mem_cons.1 hu with rfl | hu
            · rw [h1a] at hy; cases hy
              rw [RelV.pair hp]; exact ⟨l, h, rfl, h1'a, h1'b⟩
            · exact ih2 h1b h1'c hnd.2 u hu y hy
          · intro w hw
            simp only [List.map_cons, List.mem_cons] at hw
            rcases hw with rfl | rfl | hw
            · exact ⟨v, by simp, by simp [img, hp]⟩
            · exact ⟨v, by simp, by simp [img, hp]⟩
            · obtain ⟨u, hu, hw⟩ := ih3 w hw; exact ⟨u, List.mem_cons_of_mem _ hu, hw⟩
      · rw [if_neg (by simp [ht])] at hpo
        rw [if_neg ht] at hb
        obtain ⟨rest, rfl, hb⟩ := hb
        simp only [Bool.and_eq_true, beq_iff_eq] at hpo
        obtain ⟨⟨⟨rfl, rfl⟩, hpl⟩, hpo⟩ := hpo
        obtain ⟨ih1, ih2, ih3⟩ := paramsOk_bind hG hpo hb hty.2
        refine ⟨by simp [ih1, hty.1], ?_, ?_⟩
        · intro ρ1 ρ1' h1 h1' hnd u hu y hy
          obtain ⟨h1a, h1b⟩ := h1
          obtain ⟨h1'a, h1'c⟩ := h1'
          simp only [List.map_cons, List.nodup_cons] at hnd
          rcases List.mem_cons.1 hu with rfl | hu
          · rw [h1a] at hy; cases hy
            rw [RelV.plain (plain_iff.1 hpl)]; exact h1'a
          · exact ih2 h1b h1'c hnd.2 u hu y hy
        · intro w hw
          simp only [List.map_cons, List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact ⟨w, by simp, by simp [img, plain_iff.1 hpl]⟩
          · obtain ⟨u, hu, hw⟩ := ih3 w hw; exact ⟨u, List.mem_cons_of_mem _ hu, hw⟩
  | [], _ :: _, _, _, hpo, _, _ => by simp [paramsOk] at hpo
  | _ :: _, _, [], _, _, hb, _ => by simp [BExp] at hb

/-! ## Source definitions of block parameters -/

theorem params_nodup {f : Function} (hnd : ((defsOf f).map (·.1)).Nodup) {B : Block}
    (hB : B ∈ f.blocks) : (B.params.map (·.1)).Nodup := by
  have h1 : (B.params.map (fun p => (p.1, some p.2, (none : Option Inst)))).Sublist (defsOf f) :=
    (List.sublist_append_left _ _).trans (sublist_flatMap (blockDefs f) hB)
  have h2 := hnd.sublist (h1.map (·.1))
  simpa [List.map_map, Function.comp_def] using h2

theorem defOk_param {f : Function} (hnd : ((defsOf f).map (·.1)).Nodup) {B : Block}
    (hB : B ∈ f.blocks) {v : ValueId} {t : Ty} (hp : (v, t) ∈ B.params) {x : Val}
    (hx : x.ty = t) : DefOk f v x := by
  have hl := lookup_of_mem hnd (mem_defsOf_param hB hp)
  refine ⟨?_, ?_, ?_⟩
  · simp [tyOf, hl, hx]
  · intro c hc; simp [constOf, defInst, hl] at hc
  · intro c hc; simp [concatConst, defInst, hl] at hc

/-- The source invariant after entering a block of `f`. -/
theorem srcInv_enter {f : Function} (hnd : ((defsOf f).map (·.1)).Nodup) {B : Block}
    (hB : B ∈ f.blocks) {ρ ρ1 : Regs} (hinv : SrcInv f ρ) {vals : List Val}
    (hty : vals.map (·.ty) = B.params.map (·.2))
    (hset : ρ.setMany (B.params.map (·.1)) vals = some ρ1) : SrcInv f ρ1 := by
  intro v x hx
  by_cases hv : v ∈ B.params.map (·.1)
  · obtain ⟨i, hi, hvi⟩ := setMany_mem hset (params_nodup hnd hB) hv
    rw [hx] at hvi
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hi
    obtain ⟨⟨v', t⟩, hpi, rfl⟩ := hi
    have hmem : (v', t) ∈ B.params := List.mem_of_getElem? hpi
    have hxt : x.ty = t := by
      have := congrArg (·[i]?) hty
      simp only [List.getElem?_map, ← hvi, hpi, Option.map_some, Option.some.injEq] at this
      exact this
    exact defOk_param hnd hB hmem hxt
  · rw [setMany_other hset hv] at hx; exact hinv v x hx

/-! ## The frame relation -/

/-- Plain values of `f` are the same values in the target (defined or not). -/
def PlainEq (C : Ctx) (ρ ρ' : Regs) : Prop := ∀ v, v < C.T0 → C.pair v = none → ρ' v = ρ v

theorem PlainEq.update {C : Ctx} (hG : Good C) {ρ ρ' ρ1 ρ1' : Regs} (h : PlainEq C ρ ρ')
    {rs : List ValueId} (hsrc : ∀ v, v ∉ rs → ρ1 v = ρ v)
    (hnew : ∀ v ∈ rs, v < C.T0 → ∀ x, ρ1 v = some x → RelV C ρ1' v x)
    (htgt : ∀ w, C.fresh w = false → (∀ v ∈ rs, v < C.T0 → w ∉ img C v) → ρ1' w = ρ' w)
    (hdef : ∀ v ∈ rs, ∃ x, ρ1 v = some x) : PlainEq C ρ1 ρ1' := by
  intro v hv hp
  by_cases hvr : v ∈ rs
  · obtain ⟨x, hx⟩ := hdef v hvr
    have := hnew v hvr hv x hx
    rw [RelV.plain hp] at this
    rw [this, hx]
  · have hw : v ∈ img C v := by simp [img, hp]
    rw [hsrc v hvr, htgt v (img_nonfresh hG hv hw) fun u hu hut =>
      img_disj hG hut hv (fun h => hvr (h ▸ hu)) hw]
    exact h v hv hp

/-- The register-level part of the frame relation. -/
structure CRel (C : Ctx) (fr fr' : Frame) : Prop where
  func : fr.func = C.f
  func' : fr'.func = C.g
  slots : fr'.slots = fr.slots
  vrel : VRel C fr.regs fr'.regs
  peq : PlainEq C fr.regs fr'.regs
  src : SrcInv C.f fr.regs
  zero : fr'.regs C.zero = some zeroVal

/-- Frames of `f` and `g` at corresponding positions of a block of `f`. -/
structure FRel (C : Ctx) (fr fr' : Frame) : Prop extends CRel C fr fr' where
  blk : ∃ B ∈ C.f.blocks, fr.body <:+ B.body ∧ fr.term = B.term
  code : codeOk C fr.body fr.term fr'.body fr'.term = true

theorem zero_not_img {C : Ctx} (hG : Good C) {v : ValueId} (hv : v < C.T0) : C.zero ∉ img C v := by
  intro h
  cases hp : C.pair v with
  | some ab =>
    obtain ⟨a, b⟩ := ab
    obtain ⟨-, -, -, ha, hb⟩ := hG.pair_facts hp
    simp only [img, hp, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with h | h
    · exact ha h.symm
    · exact hb h.symm
  | none =>
    simp only [img, hp, List.mem_singleton] at h
    have := hG.zero_ge; vomega

theorem term_ops_lt {C : Ctx} (hG : Good C) {B : Block} (hB : B ∈ C.f.blocks) {x : ValueId}
    (hx : x ∈ termOps B.term) : x < C.T0 :=
  hG.ids x (by
    simp only [idsOf, List.mem_flatMap, List.mem_append]
    exact ⟨B, hB, .inr hx⟩)

theorem param_lt {C : Ctx} (hG : Good C) {B : Block} (hB : B ∈ C.f.blocks) {v : ValueId}
    (hv : v ∈ B.params.map (·.1)) : v < C.T0 :=
  hG.ids v (by
    simp only [idsOf, List.mem_flatMap, List.mem_append]
    exact ⟨B, hB, .inl (.inl hv)⟩)

theorem enterBlock_mk {fr : Frame} {bc : BlockCall} {b : Block} {args : List Val} {regs : Regs}
    (hb : fr.func.block? bc.block = some b) (ha : fr.getMany bc.args = .ok args)
    (ht : args.map (·.ty) = b.params.map (·.2))
    (hr : fr.regs.setMany (b.params.map (·.1)) args = some regs) :
    enterBlock fr bc = .ok { fr with regs, body := b.body, term := b.term } := by
  have hc : (args.map (·.ty) == b.params.map (·.2)) = true := by rw [ht]; exact beq_self_eq_true _
  simp only [enterBlock, hb, ha, bind, Res.bind, Res.ofOption, checkTys, hc, hr, Res.check,
    ite_true]
  rfl

/-- **Entering a block.** A branch of `f` and its rewrite (`bcOk`) enter corresponding blocks
with related frames. -/
theorem enter_sim {C : Ctx} (hG : Good C) {fr fr' : Frame} (hR : CRel C fr fr')
    {bc bc' : BlockCall} (hbc : bcOk C bc bc' = true) (hlt : ∀ x ∈ bc.args, x < C.T0)
    {fr1 : Frame} (h : enterBlock fr bc = .ok fr1) :
    ∃ fr1', enterBlock fr' bc' = .ok fr1' ∧ FRel C fr1 fr1' := by
  obtain ⟨B, args, regs1, hB, hargs, hty, hset, rfl⟩ := enterBlock_ok h
  rw [hR.func] at hB
  simp only [bcOk, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, hB] at hbc
  obtain ⟨⟨hblk, hne⟩, hexp⟩ := hbc
  obtain ⟨B', hB', hok⟩ := block_find hG hB hne
  simp only [blockOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.false_eq_true,
    ite_false] at hok
  obtain ⟨⟨-, hnd'⟩, hpo, hcode⟩ := hok
  have hBmem : B ∈ C.f.blocks := List.mem_of_find?_eq_some hB
  obtain ⟨vals', hv', hbe⟩ := expandBC_holds hR.vrel hexp hlt
    (getMany_holds hargs)
  obtain ⟨hty', hbind, hcov⟩ := paramsOk_bind hG hpo hbe hty
  have hlen : (B'.params.map (·.1)).length = vals'.length := by
    have := congrArg List.length hty'; simp only [List.length_map] at this ⊢; omega
  obtain ⟨regs1', hset'⟩ := setMany_of_len fr'.regs hlen
  have hnd := params_nodup hG.defs hBmem
  refine ⟨{ fr' with regs := regs1', body := B'.body, term := B'.term },
    enterBlock_mk (by rw [hR.func', hblk]; exact hB') (holds_getMany hv') hty' hset', ?_⟩
  have hzero : C.zero ∉ B'.params.map (·.1) := fun hz => by
    obtain ⟨u, hu, hzu⟩ := hcov _ hz
    exact zero_not_img hG (param_lt hG hBmem hu) hzu
  have hsrc : ∀ v, v ∉ B.params.map (·.1) → regs1 v = fr.regs v :=
    fun v hv => setMany_other hset hv
  have hnew : ∀ v ∈ B.params.map (·.1), v < C.T0 → ∀ x, regs1 v = some x → RelV C regs1' v x :=
    fun v hv _ x hx => hbind (holds_setMany hnd hset) (holds_setMany hnd' hset') hnd v hv x hx
  have htgt : ∀ w, C.fresh w = false → (∀ v ∈ B.params.map (·.1), v < C.T0 → w ∉ img C v) →
      regs1' w = fr'.regs w := fun w _ hni => setMany_other hset' fun hw => by
    obtain ⟨u, hu, hwu⟩ := hcov w hw
    exact hni u hu (param_lt hG hBmem hu) hwu
  have hdef : ∀ v ∈ B.params.map (·.1), ∃ x, regs1 v = some x :=
    holds_mem (holds_setMany hnd hset)
  exact ⟨⟨hR.func, hR.func', hR.slots, VRel.update hG hR.vrel hsrc hnew htgt,
    PlainEq.update hG hR.peq hsrc hnew htgt hdef, srcInv_enter hG.defs hBmem hR.src hty hset,
    by simp only; rw [setMany_other hset' hzero]; exact hR.zero⟩,
    ⟨B, hBmem, List.suffix_refl _, rfl⟩, hcode⟩

/-! ## Target runs -/

/-- The target run from `⟨fr', [], m⟩` reaches `⟨fr1', [], m1⟩`. -/
def TStep (env : Env) (p' : Program) (fr' : Frame) (m : Mem) (fr1' : Frame) (m1 : Mem) : Prop :=
  ∃ k, ∀ n, runLoop env p' (n + k) ⟨fr', [], m⟩ = runLoop env p' n ⟨fr1', [], m1⟩

theorem TStep.trans {env : Env} {p' : Program} {a b c : Frame} {ma mb mc : Mem}
    (h1 : TStep env p' a ma b mb) (h2 : TStep env p' b mb c mc) : TStep env p' a ma c mc := by
  obtain ⟨k1, h1⟩ := h1
  obtain ⟨k2, h2⟩ := h2
  exact ⟨k2 + k1, fun n => by rw [← Nat.add_assoc, h1, h2]⟩

theorem TStep.of_lstar {env : Env} {p' : Program} {fr' fr1' : Frame} {m m1 : Mem}
    (h : LStar fr' m fr1' m1) : TStep env p' fr' m fr1' m1 := by
  obtain ⟨k, hk⟩ := h.runLoop (env := env) (p := p')
  exact ⟨k, fun n => hk n []⟩

theorem TStep.of_step {env : Env} {p' : Program} {fr' fr1' : Frame} {m m1 : Mem}
    (h : step env p' ⟨fr', [], m⟩ = .next ⟨fr1', [], m1⟩) : TStep env p' fr' m fr1' m1 :=
  ⟨1, fun n => by rw [runLoop_succ, h]⟩

/-- The return groups of `f`. -/
def Ctx.rg (C : Ctx) : List (List SlotEl) := (groups C.f.sig.returns).getD []

/-- What the target does for a source step. -/
def SimOut (C : Ctx) (env : Env) (p' : Program) (fr' : Frame) (m : Mem) : StepResult → Prop
  | .next s1 => s1.callers = [] ∧ MemBounded s1.mem ∧
      ∃ fr1', FRel C s1.frame fr1' ∧ TStep env p' fr' m fr1' s1.mem
  | .done vals m1 => ∃ vals', ExpRel C.rg vals vals' ∧ ∃ k, runLoop env p' k ⟨fr', [], m⟩ = .returned vals' m1
  | .trapped c => ∃ k, runLoop env p' k ⟨fr', [], m⟩ = .trapped c
  | .stuck _ => True

theorem SimOut.pre {C : Ctx} {env : Env} {p' : Program} {fr' fr1' : Frame} {m m1 : Mem}
    {r : StepResult} (ht : TStep env p' fr' m fr1' m1) (hm : m1 = m ∨ ∀ s1, r ≠ .next s1)
    (h : SimOut C env p' fr1' m1 r) : SimOut C env p' fr' m r := by
  obtain ⟨k0, hk0⟩ := ht
  cases r with
  | next s1 =>
    rcases hm with rfl | hm
    · obtain ⟨h1, h2, fr2, h3, h4⟩ := h
      exact ⟨h1, h2, fr2, h3, TStep.trans ⟨k0, hk0⟩ h4⟩
    · exact absurd rfl (hm s1)
  | done vals m2 =>
    obtain ⟨vals', h1, k, hk⟩ := h
    exact ⟨vals', h1, k + k0, by rw [hk0, hk]⟩
  | trapped c =>
    obtain ⟨k, hk⟩ := h
    exact ⟨k + k0, by rw [hk0, hk]⟩
  | stuck _ => trivial

/-! ## After a statement -/

theorem frame_eta (fr : Frame) : fr = { fr with body := fr.body } := rfl

/-- The frame relation after a statement of `f` and its segment. -/
theorem frel_after {C : Ctx} (hG : Good C) {fr fr' : Frame} (hR : FRel C fr fr') {st : Stmt}
    {rest : List Stmt} (hb : fr.body = st :: rest) {ts2 : List Stmt}
    (hcode : codeOk C rest fr.term ts2 fr'.term = true) {vals : List Val} {ρ1 ρ1' : Regs}
    (hset : fr.regs.setMany st.results vals = some ρ1)
    (hnew : ∀ v ∈ st.results, v < C.T0 → ∀ x, ρ1 v = some x → RelV C ρ1' v x)
    (htgt : ∀ w, C.fresh w = false → (∀ v ∈ st.results, v < C.T0 → w ∉ img C v) →
      ρ1' w = fr'.regs w)
    (hsrc : SrcInv C.f ρ1) :
    FRel C { fr with regs := ρ1, body := rest } { fr' with regs := ρ1', body := ts2 } := by
  obtain ⟨B, hB, hsuf, hterm⟩ := hR.blk
  have hst : st ∈ B.body := hsuf.subset (by rw [hb]; exact List.mem_cons_self ..)
  have hnd := results_nodup hG.defs hB hst
  have hs : ∀ v, v ∉ st.results → ρ1 v = fr.regs v := fun v hv => setMany_other hset hv
  have hdef : ∀ v ∈ st.results, ∃ x, ρ1 v = some x := holds_mem (holds_setMany hnd hset)
  refine ⟨⟨hR.func, hR.func', hR.slots, VRel.update hG hR.vrel hs hnew htgt,
    PlainEq.update hG hR.peq hs hnew htgt hdef, hsrc, ?_⟩,
    ⟨B, hB, ?_, hterm⟩, hcode⟩
  · simp only
    rw [htgt C.zero (by simp [Ctx.fresh]) fun v _ hv => zero_not_img hG hv]
    exact hR.zero
  · rw [hb] at hsuf
    exact (List.suffix_cons st rest).trans hsuf

/-! ## Inverting `planOf` -/

theorem planOf_same {C : Ctx} {s : Stmt} (hp : planOf C s = some .same) :
    (∀ x ∈ instOps s.inst ++ s.results, C.plain x = true) ∧
    (∀ fn args, s.inst ≠ .call fn args) ∧ (∀ sig c args, s.inst ≠ .callIndirect sig c args) ∧
    (∀ t fn, s.inst ≠ .funcAddr t fn) := by
  obtain ⟨rs, inst⟩ := s
  unfold planOf at hp
  dsimp only at hp
  split at hp
  all_goals (repeat' (first | (simp [bind, Option.bind_eq_some_iff] at hp; done) | split at hp))
  all_goals refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp only [List.all_eq_true] at *; assumption)
    | (intro a b h; cases h; done)
    | (intro a b c h; cases h; done)
    | (intro a b h; simp_all; done)
    | (intro a b c h; simp_all; done)

macro "plan_inv " s:ident hp:ident : tactic => `(tactic| (
  obtain ⟨rs, inst⟩ := $s
  unfold planOf at $hp:ident
  dsimp only at $hp:ident
  split at $hp:ident
  all_goals (repeat' (first | (simp [bind, Option.bind_eq_some_iff] at $hp:ident; done) |
    split at $hp:ident))))

theorem planOf_load {C : Ctx} {s : Stmt} {rl rh p : ValueId} {fl : MemFlags} {off : Int}
    (hp : planOf C s = some (.load rl rh p fl off)) :
    s.inst = .load .load .i128 fl p off ∧ (∃ r, s.results = [r] ∧ C.pair r = some (rl, rh)) ∧
      C.plain p = true ∧ (fl.endianness == some .big) = false := by
  plan_inv s hp
  all_goals rename_i hc
  simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Plan.load.injEq] at hp
  obtain ⟨⟨a, b⟩, hr, rfl, rfl, rfl, rfl, rfl⟩ := hp
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
  exact ⟨rfl, ⟨_, rfl, hr⟩, hc.1, by simpa using hc.2⟩

theorem planOf_store {C : Ctx} {s : Stmt} {xl xh p : ValueId} {fl : MemFlags} {off : Int}
    (hp : planOf C s = some (.store xl xh p fl off)) :
    (∃ x, s.inst = .store .store .i128 fl x p off ∧ C.pair x = some (xl, xh)) ∧ s.results = [] ∧
      C.plain p = true ∧ (fl.endianness == some .big) = false := by
  plan_inv s hp
  all_goals rename_i hc
  simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Plan.store.injEq] at hp
  obtain ⟨⟨a, b⟩, hx, rfl, rfl, rfl, rfl, rfl⟩ := hp
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
  exact ⟨⟨_, rfl, hx⟩, rfl, hc.1, by simpa using hc.2⟩

theorem planOf_div {C : Ctx} {s : Stmt} {op : DivOp} {xl xh yl yh rl rh : ValueId}
    (hp : planOf C s = some (.div op xl xh yl yh rl rh)) :
    ∃ x y r, s.inst = .div op .i128 x y ∧ s.results = [r] ∧ C.pair x = some (xl, xh) ∧
      C.pair y = some (yl, yh) ∧ C.pair r = some (rl, rh) := by
  plan_inv s hp
  simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Plan.div.injEq] at hp
  obtain ⟨⟨a, b⟩, hx, ⟨c, d⟩, hy, ⟨e, f⟩, hr, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
  exact ⟨_, _, _, rfl, rfl, hx, hy, hr⟩

theorem planOf_call {C : Ctx} {s : Stmt} {fn : FnRef} {e : ExtFunc} {args' : List ValueId}
    {rg : List (List Opt.Legalize128.SlotEl)} {rs : List ValueId}
    (hp : planOf C s = some (.call fn e args' rg rs)) :
    ∃ args gs, s.inst = .call fn args ∧ s.results = rs ∧ C.f.extern? fn = some e ∧
      groups e.sig.params = some gs ∧ groups e.sig.returns = some rg ∧
      expandArgs C gs args = some args' := by
  plan_inv s hp
  simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Plan.call.injEq] at hp
  obtain ⟨e', he, gs, hg, rg', hrg, a', ha, rfl, rfl, rfl, rfl, rfl⟩ := hp
  exact ⟨_, gs, rfl, rfl, he, hg, hrg, ha⟩

theorem planOf_trap {C : Ctx} {s : Stmt} {lo hi : ValueId} {nz : Bool} {code : TrapCode}
    (hp : planOf C s = some (.trap lo hi nz code)) :
    ∃ c, (s.inst = .trapz c code ∧ nz = false ∨ s.inst = .trapnz c code ∧ nz = true) ∧
      s.results = [] ∧ C.pair c = some (lo, hi) := by
  plan_inv s hp
  all_goals simp only [Option.some.injEq, Plan.trap.injEq] at hp
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
    exact ⟨_, .inl ⟨rfl, rfl⟩, rfl, by assumption⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
    exact ⟨_, .inr ⟨rfl, rfl⟩, rfl, by assumption⟩

end Opt.Legal
