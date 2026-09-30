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

theorem planOf_pure_inst {C : Ctx} {s : Stmt} {pat : List Stmt} {ins outs : List ValueId}
    (hp : planOf C s = some (.pure pat ins outs)) :
    (∀ fn args, s.inst ≠ .call fn args) ∧ (∀ sig c args, s.inst ≠ .callIndirect sig c args) := by
  plan_inv s hp
  all_goals exact ⟨fun _ _ h => Inst.noConfusion h, fun _ _ _ h => Inst.noConfusion h⟩

/-! ## Statements -/

/-- The relation's view of the next statement: its plan and segment. -/
theorem code_cons {C : Ctx} {st : Stmt} {rest : List Stmt} {t : Terminator} {ts : List Stmt}
    {t' : Terminator} (h : codeOk C (st :: rest) t ts t' = true) :
    ∃ pl, planOf C st = some pl ∧ segOk C st pl (ts.take pl.len) = true ∧
      codeOk C rest t (ts.drop pl.len) t' = true := by
  simp only [codeOk] at h
  split at h
  · rename_i pl hpl
    simp only [Bool.and_eq_true] at h
    exact ⟨pl, hpl, h.1, h.2⟩
  · cases h

theorem frel_stmt {C : Ctx} {fr fr' : Frame} (hR : FRel C fr fr') {st : Stmt} {rest : List Stmt}
    (hb : fr.body = st :: rest) : ∃ B ∈ C.f.blocks, st ∈ B.body := by
  obtain ⟨B, hB, hsuf, -⟩ := hR.blk
  exact ⟨B, hB, hsuf.subset (by rw [hb]; exact List.mem_cons_self ..)⟩

theorem memBounded_eval {fr : Frame} {m m' : Mem} {i : Inst} {vals : List Val}
    (h : evalInst fr m i = .ok (vals, m')) (hM : MemBounded m) : MemBounded m' :=
  memBounded_of_allocs (evalInst_allocs h) hM

/-- **`same`**: the statement itself. -/
theorem sim_same {C : Ctx} (hG : Good C) {env : Env} {p p' : Program} {fr fr' : Frame}
    {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) {st : Stmt} {rest : List Stmt}
    (hb : fr.body = st :: rest) (hpl : planOf C st = some .same) {ts2 : List Stmt}
    (hb' : fr'.body = st :: ts2) (hcode : codeOk C rest fr.term ts2 fr'.term = true) :
    SimOut C env p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨hplain, hnc, hnci, hnfa⟩ := planOf_same hpl
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hnd := results_nodup hG.defs hB hst
  have hops : ∀ x ∈ instOps st.inst, fr'.regs x = fr.regs x := fun x hx =>
    hR.peq x (ops_lt hG hB hst hx) (plain_iff.1 (hplain x (List.mem_append_left _ hx)))
  have hev : evalInst fr' m st.inst = evalInst fr m st.inst :=
    evalInst_same hops hR.slots (by rw [hR.func', hR.func]; exact hG.globals) hnfa
  rw [step_inst env p ⟨fr, [], m⟩ st rest hb hnc hnci]
  have hstep' := step_inst env p' ⟨fr', [], m⟩ st ts2 hb' hnc hnci
  rw [hev] at hstep'
  cases hr : evalInst fr m st.inst with
  | ok vm =>
    obtain ⟨vals, mem⟩ := vm
    rw [hr] at hstep'
    simp only [StepResult.ofRes_ok, continueWith] at hstep' ⊢
    cases hs : fr.regs.setMany st.results vals with
    | none => trivial
    | some ρ1 =>
      obtain ⟨ρ1', hs'⟩ := setMany_of_len fr'.regs (setMany_len hs)
      simp only [hs'] at hstep'
      refine ⟨rfl, memBounded_eval hr hM, { fr' with regs := ρ1', body := ts2 }, ?_,
        TStep.of_step hstep'⟩
      refine frel_after hG hR hb hcode hs ?_ ?_ (srcInv_stmt hG.defs hB hst hR.src hr hs)
      · intro v hv _ x hx
        have hpv := plain_iff.1 (hplain v (List.mem_append_right _ hv))
        obtain ⟨i, hi, hvi⟩ := setMany_mem hs hnd hv
        rw [RelV.plain hpv, setMany_get hs' hnd hi, ← hvi, hx]
      · intro w _ hni
        refine setMany_other hs' fun hw => ?_
        have hpw := plain_iff.1 (hplain w (List.mem_append_right _ hw))
        exact hni w hw (res_lt hG hB hst hw) (by simp [img, hpw])
  | trap c =>
    rw [hr] at hstep'
    exact ⟨1, by rw [runLoop_succ, hstep']; rfl⟩
  | stuck msg => trivial

/-- **Pure plans**: the segment runs the pattern. -/
theorem sim_pure {C : Ctx} (hG : Good C) {env : Env} {p p' : Program} {fr fr' : Frame}
    {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) {st : Stmt} {rest : List Stmt}
    (hb : fr.body = st :: rest) {pat : List Stmt} {ins outs : List ValueId}
    (hpl : planOf C st = some (.pure pat ins outs)) {seg ts2 : List Stmt}
    (hseg : pureOk C pat ins outs seg = true) (hb' : fr'.body = seg ++ ts2)
    (hcode : codeOk C rest fr.term ts2 fr'.term = true) :
    SimOut C env p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hnd := results_nodup hG.defs hB hst
  obtain ⟨hnc, hnci⟩ := planOf_pure_inst hpl
  rw [step_inst env p ⟨fr, [], m⟩ st rest hb hnc hnci]
  cases hr : evalInst fr m st.inst with
  | ok vm =>
    obtain ⟨vals, mem⟩ := vm
    obtain ⟨rfl, hcov, inVals, ρ0, hH, hrun, hO⟩ := pure_step hG hB hst hpl hR.vrel hR.src hr
    simp only [StepResult.ofRes_ok, continueWith]
    cases hs : fr.regs.setMany st.results vals with
    | none => trivial
    | some ρ1 =>
      obtain ⟨regs', hl, hout, hkeep⟩ := pureOk_run hseg hH.len hrun (fr := fr') hH.get _ ts2
      have hfr' : { fr' with body := seg ++ ts2 } = fr' := by rw [← hb']
      rw [hfr'] at hl
      refine ⟨rfl, hM, { fr' with regs := regs', body := ts2 }, ?_, TStep.of_lstar hl⟩
      refine frel_after hG hR hb hcode hs ?_ ?_ (srcInv_stmt hG.defs hB hst hR.src hr hs)
      · intro v hv _ x hx
        obtain ⟨i, hi, hvi⟩ := setMany_mem hs hnd hv
        exact hO regs' hout i v x hi (by rw [← hvi, hx])
      · intro w hw hni
        refine hkeep w hw fun hwo => ?_
        obtain ⟨r, hr, hwr⟩ := hcov w hwo
        exact hni r hr (res_lt hG hB hst hr) hwr
  | trap c => exact absurd hr (pure_notrap hpl fr m c)
  | stuck msg => trivial

/-- A statement of `g` that evaluates and binds its results: one local step. -/
theorem lstep_eval {fr : Frame} {m m1 : Mem} {st : Stmt} {rest : List Stmt} {vals : List Val}
    {regs : Regs} (hb : fr.body = st :: rest) (hc : ∀ fn args, st.inst ≠ .call fn args)
    (hev : evalInst fr m st.inst = .ok (vals, m1)) (hs : fr.regs.setMany st.results vals = some regs) :
    lstep fr m = .next { fr with regs, body := rest } m1 := by
  rw [lstep_inst hb hc, hev]
  simp only [LRes.ofRes_ok, hs]

theorem setWidth_self {w : Nat} (x : BitVec w) : x.setWidth w = x := by simp

theorem eval_load64 {fr : Frame} {m : Mem} {fl : MemFlags} {q : ValueId} {off : Int} {pv : Val}
    {lo : BitVec 64} (hq : fr.regs q = some pv) (hl : m.load fl (effAddr pv off) 8 (8 * 8) = .ok lo) :
    evalInst fr m (.load .load .i64 fl q off) = .ok ([⟨.i64, lo⟩], m) := by
  simp only [evalInst, Frame.get, hq, Res.ofOption, LoadOp.size, Ty.bytes, LoadOp.signed,
    Bool.false_eq_true, ite_false, bind, Res.bind, Res.check, width_i64, Nat.reduceDiv,
    Nat.le_refl, decide_true, ite_true]
  erw [hl]
  simp [pure]

theorem mem_load_valid {m : Mem} {fl : MemFlags} {a n w : Nat} {x : BitVec w}
    (h : m.load fl a n w = .ok x) : m.valid a n = true := by
  simp only [Mem.load, Mem.checkAccess, Opt.Res.bind_eq_ok] at h
  obtain ⟨u, hc, -⟩ := h
  split at hc
  · assumption
  · split at hc <;> cases hc

/-- **Split load**: two 8-byte loads of the halves. -/
theorem sim_load {C : Ctx} (hG : Good C) {env : Env} {p p' : Program} {fr fr' : Frame}
    {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) {st : Stmt} {rest : List Stmt}
    (hb : fr.body = st :: rest) {rl rh q : ValueId} {fl : MemFlags} {off : Int}
    (hpl : planOf C st = some (.load rl rh q fl off)) {ts2 : List Stmt}
    (hb' : fr'.body = [S rl (.load .load .i64 fl q off), S rh (.load .load .i64 fl q (off + 8))] ++ ts2)
    (hrl : rl ≠ rh) (hrq : rl ≠ q)
    (hcode : codeOk C rest fr.term ts2 fr'.term = true)
    (hT : ∀ c, step env p ⟨fr, [], m⟩ ≠ .trapped c) :
    SimOut C env p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨hi, ⟨r, hrs, hr⟩, hpq, hbig⟩ := planOf_load hpl
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hq : q < C.T0 := ops_lt hG hB hst (by rw [hi]; simp [instOps])
  have hnc : ∀ fn args, st.inst ≠ .call fn args := fun _ _ h => by rw [hi] at h; cases h
  have hnci : ∀ sig c args, st.inst ≠ .callIndirect sig c args := fun _ _ _ h => by
    rw [hi] at h; cases h
  have hstep := step_inst env p ⟨fr, [], m⟩ st rest hb hnc hnci
  rw [hstep] at hT ⊢
  cases hev : evalInst fr m st.inst with
  | stuck msg => trivial
  | trap c => rw [hev] at hT; exact absurd rfl (hT c)
  | ok vm =>
    obtain ⟨vals, mem⟩ := vm
    have hev' := hev
    rw [hi] at hev'
    simp only [evalInst, Opt.Res.bind_eq_ok, LoadOp.size, Ty.bytes, LoadOp.signed,
      Bool.false_eq_true, ite_false, Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev'
    obtain ⟨pv, hpv, u, -, raw, hraw, rfl, rfl⟩ := hev'
    have hraw' : m.load fl (effAddr pv off) 16 (8 * 16) = .ok raw := hraw
    have hA := hM _ _ (mem_load_valid hraw')
    obtain ⟨hlo, hhi⟩ := load_split hbig hraw'
    rw [← effAddr_add8 pv off hA] at hhi
    have hpv' : fr'.regs q = some pv := by
      rw [hR.peq q hq (plain_iff.1 hpq)]; exact get_ok hpv
    simp only [StepResult.ofRes_ok, continueWith, hrs, Regs.setMany_cons, Regs.setMany_nil]
    -- the target: two loads
    have h1 := lstep_eval (fr := fr') (m := m) (st := S rl (.load .load .i64 fl q off))
      (rest := S rh (.load .load .i64 fl q (off + 8)) :: ts2) (by rw [hb']; rfl)
      (fun _ _ h => by cases h) (eval_load64 hpv' hlo) (by simp [S]; rfl)
    have h2 := lstep_eval (fr := ⟨fr'.func, fr'.regs.set rl ⟨.i64, raw.extractLsb' 0 64⟩,
        fr'.slots, S rh (.load .load .i64 fl q (off + 8)) :: ts2, fr'.term⟩) (m := m)
      (st := S rh (.load .load .i64 fl q (off + 8))) (rest := ts2) rfl (fun _ _ h => by cases h)
      (eval_load64 (by simp only; rw [Regs.set_other _ _ (Ne.symm hrq)]; exact hpv') hhi)
      (by simp [S]; rfl)
    refine ⟨rfl, hM, _, ?_, TStep.of_lstar (.step h1 (.step h2 (.refl _ _)))⟩
    have hset : fr.regs.setMany st.results [⟨.i128, BitVec.zeroExtend Ty.i128.width raw⟩] =
        some (fr.regs.set r ⟨.i128, BitVec.zeroExtend Ty.i128.width raw⟩) := by rw [hrs]; rfl
    refine frel_after hG hR hb hcode hset ?_ ?_ (srcInv_stmt hG.defs hB hst hR.src hev hset)
    · intro v hv _ x hx
      rw [hrs, List.mem_singleton] at hv
      subst hv
      simp only [Regs.set_same, Option.some.injEq] at hx
      subst hx
      rw [RelV.pair hr]
      refine ⟨raw.extractLsb' 0 64, raw.extractLsb' 64 64, ?_, ?_, ?_⟩
      · have e : BitVec.zeroExtend Ty.i128.width raw = raw := BitVec.setWidth_eq raw
        rw [e]
        exact congrArg _ (split128 raw).symm
      · rw [Regs.set_other _ _ hrl, Regs.set_same]; rfl
      · simp
    · intro w _ hni
      rw [hrs] at hni
      have := hni r (List.mem_singleton_self _) (res_lt hG hB hst (by rw [hrs]; simp))
      simp only [img, hr, List.mem_cons, List.mem_nil_iff, or_false, not_or] at this
      rw [Regs.set_other _ _ this.2, Regs.set_other _ _ this.1]

theorem eval_store64 {fr : Frame} {m m1 : Mem} {fl : MemFlags} {x q : ValueId} {off : Int}
    {pv : Val} {lo : BitVec 64} (hx : fr.regs x = some ⟨.i64, lo⟩) (hq : fr.regs q = some pv)
    (hs : m.store fl (effAddr pv off) 8 lo = .ok m1) :
    evalInst fr m (.store .store .i64 fl x q off) = .ok ([], m1) := by
  simp only [evalInst, Frame.getAs, Frame.get, hx, hq, Res.ofOption, as?_i64, StoreOp.size,
    Ty.bytes, bind, Res.bind, Res.check, width_i64, Nat.reduceDiv, Nat.le_refl, decide_true,
    ite_true]
  erw [hs]
  rfl

theorem mem_store_valid {w : Nat} {m : Mem} {fl : MemFlags} {a n : Nat} {x : BitVec w} {m' : Mem}
    (h : m.store fl a n x = .ok m') : m.valid a n = true := by
  obtain ⟨hc, -, -⟩ := store_inv h
  simp only [Mem.checkAccess] at hc
  split at hc
  · assumption
  · split at hc <;> cases hc

theorem memBounded_store {w : Nat} {m : Mem} {fl : MemFlags} {a n : Nat} {x : BitVec w}
    {m' : Mem} (h : m.store fl a n x = .ok m') (hM : MemBounded m) : MemBounded m' :=
  memBounded_of_allocs (Mem.store_allocs h) hM

/-- **Split store**: two 8-byte stores of the halves. -/
theorem sim_store {C : Ctx} (hG : Good C) {env : Env} {p p' : Program} {fr fr' : Frame}
    {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) {st : Stmt} {rest : List Stmt}
    (hb : fr.body = st :: rest) {xl xh q : ValueId} {fl : MemFlags} {off : Int}
    (hpl : planOf C st = some (.store xl xh q fl off)) {ts2 : List Stmt}
    (hb' : fr'.body = [{ results := [], inst := .store .store .i64 fl xl q off },
      { results := [], inst := .store .store .i64 fl xh q (off + 8) }] ++ ts2)
    (hcode : codeOk C rest fr.term ts2 fr'.term = true)
    (hT : ∀ c, step env p ⟨fr, [], m⟩ ≠ .trapped c) :
    SimOut C env p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨⟨x, hi, hx⟩, hrs, hpq, hbig⟩ := planOf_store hpl
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hx0 : x < C.T0 := ops_lt hG hB hst (by rw [hi]; simp [instOps])
  have hq : q < C.T0 := ops_lt hG hB hst (by rw [hi]; simp [instOps])
  have hnc : ∀ fn args, st.inst ≠ .call fn args := fun _ _ h => by rw [hi] at h; cases h
  have hnci : ∀ sig c args, st.inst ≠ .callIndirect sig c args := fun _ _ _ h => by
    rw [hi] at h; cases h
  have hstep := step_inst env p ⟨fr, [], m⟩ st rest hb hnc hnci
  rw [hstep] at hT ⊢
  cases hev : evalInst fr m st.inst with
  | stuck msg => trivial
  | trap c => rw [hev] at hT; exact absurd rfl (hT c)
  | ok vm =>
    obtain ⟨vals, mem⟩ := vm
    have hev' := hev
    rw [hi] at hev'
    simp only [evalInst, Opt.Res.bind_eq_ok, StoreOp.size, Ty.bytes, Opt.Res.pure_eq_ok,
      Prod.mk.injEq] at hev'
    obtain ⟨a, ha, pv, hpv, u, -, mem', hst', rfl, rfl⟩ := hev'
    obtain ⟨l, h, he, hl, hh⟩ := pairVal hR.vrel hx0 hx (getAs_ok ha)
    cases val_i128 he
    have hst16 : m.store fl (effAddr pv off) 16 (h ++ l) = .ok mem' := hst'
    have hA := hM _ _ (mem_store_valid hst16)
    obtain ⟨m1, hs1, hs2⟩ := store_split hbig hst16
    rw [append_lo, append_hi, ← effAddr_add8 pv off hA] at *
    have hpv' : fr'.regs q = some pv := by
      rw [hR.peq q hq (plain_iff.1 hpq)]; exact get_ok hpv
    simp only [StepResult.ofRes_ok, continueWith, hrs, Regs.setMany_nil]
    have h1 := lstep_eval (fr := fr') (m := m) (st := { results := [], inst := .store .store .i64 fl xl q off })
      (rest := { results := [], inst := .store .store .i64 fl xh q (off + 8) } :: ts2)
      (by rw [hb']; rfl) (fun _ _ h => by cases h) (eval_store64 hl hpv' hs1) rfl
    have h2 := lstep_eval (fr := ⟨fr'.func, fr'.regs, fr'.slots,
        { results := [], inst := .store .store .i64 fl xh q (off + 8) } :: ts2, fr'.term⟩) (m := m1)
      (st := { results := [], inst := .store .store .i64 fl xh q (off + 8) }) (rest := ts2) rfl
      (fun _ _ h => by cases h) (eval_store64 hh hpv' hs2) rfl
    refine ⟨rfl, memBounded_store hs2 (memBounded_store hs1 hM), _, ?_,
      TStep.of_lstar (.step h1 (.step h2 (.refl _ _)))⟩
    have hset : fr.regs.setMany st.results [] = some fr.regs := by rw [hrs]; rfl
    exact frel_after hG hR hb hcode hset (by rw [hrs]; simp) (fun _ _ _ => rfl)
      (srcInv_stmt hG.defs hB hst hR.src hev hset)

/-! ## Calls of externs -/

/-- A call of an extern the environment implements. -/
theorem step_extcall {env : Env} {p : Program} {s : State} {rest : List Stmt}
    {results : List ValueId} {fn : FnRef} {args : List ValueId} {ext : ExtFunc} {vals : List Val}
    {h : List Val → Mem → Outcome}
    (hb : s.frame.body = { results, inst := .call fn args } :: rest)
    (hext : s.frame.func.extern? fn = some ext) (hargs : s.frame.getMany args = .ok vals)
    (hty : vals.map (·.ty) = AbiParam.tys ext.sig.params) (hp : p.func? ext.name = none)
    (henv : env.extern ext.name = some h) :
    step env p s = match h vals s.mem with
      | .returned rvals mem' =>
        if rvals.map (·.ty) == AbiParam.tys ext.sig.returns then
          continueWith s rest results rvals mem'
        else .stuck s!"extern %{ext.name} returned values of the wrong types"
      | .trapped c => .trapped c
      | .stuck m => .stuck m
      | .outOfFuel => .stuck s!"extern %{ext.name} ran out of fuel" := by
  rw [step_call env p s rest results fn args hb]
  simp only [stepCall, hext, hargs, checkTys, hty, beq_self_eq_true, Res.ofOption, bind, Res.bind,
    Res.check, ite_true, pure, StepResult.ofRes_ok, hp, henv]
  rfl

theorem truthy_bool8 (b : Bool) : Sem.truthy (Sem.bool8 b) = b := by
  cases b <;> rfl

theorem truthy_bool8' (b : Bool) : @Sem.truthy Ty.i8.width (Sem.bool8 b) = b := by
  cases b <;> rfl

/-- **`div` at `i128`**: a call of the `__*ti3` helper. -/
theorem sim_div {C : Ctx} (hG : Good C) {env : Env} {p p' : Program} (hH : HelperOk env)
    (hext' : ∀ fn e, C.g.extern? fn = some e → p'.func? e.name = none)
    {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) {st : Stmt}
    {rest : List Stmt} (hb : fr.body = st :: rest) {op : DivOp} {xl xh yl yh rl rh : ValueId}
    (hpl : planOf C st = some (.div op xl xh yl yh rl rh)) {fn : FnRef} {ts2 : List Stmt}
    (hb' : fr'.body = { results := [rl, rh], inst := .call fn [xl, xh, yl, yh] } :: ts2)
    (hrl : rl ≠ rh) (hfn : C.g.extern? fn = some (helperExt op))
    (hcode : codeOk C rest fr.term ts2 fr'.term = true) :
    SimOut C env p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨x, y, r, hi, hrs, hx, hy, hr⟩ := planOf_div hpl
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hx0 : x < C.T0 := ops_lt hG hB hst (by rw [hi]; simp [instOps])
  have hy0 : y < C.T0 := ops_lt hG hB hst (by rw [hi]; simp [instOps])
  have hnc : ∀ fn args, st.inst ≠ .call fn args := fun _ _ h => by rw [hi] at h; cases h
  have hnci : ∀ sig c args, st.inst ≠ .callIndirect sig c args := fun _ _ _ h => by
    rw [hi] at h; cases h
  rw [step_inst env p ⟨fr, [], m⟩ st rest hb hnc hnci]
  obtain ⟨hf, hhf, hsem⟩ := hH op
  cases hev : evalInst fr m st.inst with
  | stuck msg => trivial
  | ok vm =>
    obtain ⟨vals, mem⟩ := vm
    have hev' := hev
    rw [hi] at hev'
    simp only [evalInst, Opt.Res.bind_eq_ok, Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev'
    obtain ⟨a, ha, b, hb2, res, hres, rfl, rfl⟩ := hev'
    obtain ⟨l, h, he, hl, hh⟩ := pairVal hR.vrel hx0 hx (getAs_ok ha)
    cases val_i128 he
    obtain ⟨bl, bh, he2, hbl, hbh⟩ := pairVal hR.vrel hy0 hy (getAs_ok hb2)
    cases val_i128 he2
    have hsem' := hsem l h bl bh m
    have e : @Sem.div (64 + 64) op (h ++ l) (bh ++ bl) =
        @Sem.div Ty.i128.width op (h ++ l) (bh ++ bl) := rfl
    rw [e] at hsem'
    have hdiv : @Sem.div Ty.i128.width op (h ++ l) (bh ++ bl) = .ok res := by
      revert hres
      cases Sem.div (w := Ty.i128.width) op (h ++ l) (bh ++ bl) with
      | ok v => intro hres; cases hres; rfl
      | error c => intro hres; cases hres
    rw [hdiv] at hsem'
    simp only [StepResult.ofRes_ok, continueWith, hrs, Regs.setMany_cons, Regs.setMany_nil]
    have hstep' := step_extcall (env := env) (p := p') (s := ⟨fr', [], m⟩) hb'
      (by rw [hR.func']; exact hfn)
      (holds_getMany (show Holds fr'.regs [xl, xh, yl, yh]
        [⟨.i64, l⟩, ⟨.i64, h⟩, ⟨.i64, bl⟩, ⟨.i64, bh⟩] from ⟨hl, hh, hbl, hbh, trivial⟩))
      rfl (hext' fn _ hfn) hhf
    simp only [hsem', helperExt, helperSig] at hstep'
    simp only [List.map_cons, List.map_nil, AbiParam.tys, beq_self_eq_true, ite_true,
      continueWith, Regs.setMany_cons, Regs.setMany_nil] at hstep'
    refine ⟨rfl, hM, _, ?_, TStep.of_step hstep'⟩
    have hset : fr.regs.setMany st.results [⟨.i128, res⟩] =
        some (fr.regs.set r ⟨.i128, res⟩) := by rw [hrs]; rfl
    refine frel_after hG hR hb hcode hset ?_ ?_ (srcInv_stmt hG.defs hB hst hR.src hev hset)
    · intro v hv _ z hz
      rw [hrs, List.mem_singleton] at hv
      subst hv
      simp only [Regs.set_same, Option.some.injEq] at hz
      subst hz
      rw [RelV.pair hr]
      refine ⟨res.extractLsb' 0 64, res.extractLsb' 64 64, ?_, ?_, ?_⟩
      · exact congrArg _ (split128 res).symm
      · rw [Regs.set_other _ _ hrl, Regs.set_same]; rfl
      · simp
    · intro w _ hni
      rw [hrs] at hni
      have := hni r (List.mem_singleton_self _) (res_lt hG hB hst (by rw [hrs]; simp))
      simp only [img, hr, List.mem_cons, List.mem_nil_iff, or_false, not_or] at this
      rw [Regs.set_other _ _ this.2, Regs.set_other _ _ this.1]
  | trap c =>
    have hev' := hev
    rw [hi] at hev'
    simp only [evalInst, Opt.Res.bind_eq_trap, getAs_ne_trap, false_or] at hev'
    obtain ⟨a, ha, b, hb2, hres⟩ := hev'
    obtain ⟨l, h, he, hl, hh⟩ := pairVal hR.vrel hx0 hx (getAs_ok ha)
    cases val_i128 he
    obtain ⟨bl, bh, he2, hbl, hbh⟩ := pairVal hR.vrel hy0 hy (getAs_ok hb2)
    cases val_i128 he2
    have hsem' := hsem l h bl bh m
    have e : @Sem.div (64 + 64) op (h ++ l) (bh ++ bl) =
        @Sem.div Ty.i128.width op (h ++ l) (bh ++ bl) := rfl
    rw [e] at hsem'
    have hdiv : @Sem.div Ty.i128.width op (h ++ l) (bh ++ bl) = .error c := by
      revert hres
      cases Sem.div (w := Ty.i128.width) op (h ++ l) (bh ++ bl) with
      | ok v => intro hres; simp [Res.ofExcept] at hres
      | error c' => intro hres; simp [Opt.Res.bind_eq_trap, Res.ofExcept] at hres; rw [hres]
    rw [hdiv] at hsem'
    have hstep' := step_extcall (env := env) (p := p') (s := ⟨fr', [], m⟩) hb'
      (by rw [hR.func']; exact hfn)
      (holds_getMany (show Holds fr'.regs [xl, xh, yl, yh]
        [⟨.i64, l⟩, ⟨.i64, h⟩, ⟨.i64, bl⟩, ⟨.i64, bh⟩] from ⟨hl, hh, hbl, hbh, trivial⟩))
      rfl (hext' fn _ hfn) hhf
    simp only [hsem'] at hstep'
    exact ⟨1, by rw [runLoop_succ, hstep']⟩

/-- The condition pattern on an `i128` condition: the target computes its truth value at the
fresh `c`, keeping every non-fresh value. -/
theorem cond_run {C : Ctx} {fr' : Frame} {m : Mem} {lo hi c : ValueId} {segA rest : List Stmt}
    (hseg : pureOk C Pat.cond [lo, hi] [c] segA = true) {l h : BitVec 64}
    (hl : fr'.regs lo = some ⟨.i64, l⟩) (hh : fr'.regs hi = some ⟨.i64, h⟩) :
    ∃ regs', LStar { fr' with body := segA ++ rest } m { fr' with regs := regs', body := rest } m ∧
      regs' c = some ⟨.i8, Sem.bool8 (Sem.truthy (h ++ l))⟩ ∧
      ∀ w, C.fresh w = false → w ≠ c → regs' w = fr'.regs w := by
  obtain ⟨ρ0, hrun, h2⟩ := pat_cond l h
  obtain ⟨regs', hl', hout, hkeep⟩ := pureOk_run hseg (inVals := [V64 l, V64 h]) rfl hrun
    (fr := fr') (Holds.get (show Holds fr'.regs [lo, hi] [V64 l, V64 h] from ⟨hl, hh, trivial⟩))
    m rest
  exact ⟨regs', hl', hout 0 (by simp) _ h2, fun w hw hwc => hkeep w hw (by simpa using hwc)⟩

theorem fresh_ne {C : Ctx} {c w : ValueId} (hc : C.fresh c = true) (hw : C.fresh w = false) :
    w ≠ c := by
  rintro rfl; rw [hc] at hw; cases hw

/-- **`trapz`/`trapnz` on an `i128` condition**: the condition pattern, then the trap. -/
theorem sim_trap {C : Ctx} (hG : Good C) {env : Env} {p p' : Program} {fr fr' : Frame}
    {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) {st : Stmt} {rest : List Stmt}
    (hb : fr.body = st :: rest) {lo hi : ValueId} {nz : Bool} {code : TrapCode}
    (hpl : planOf C st = some (.trap lo hi nz code)) {segA ts2 : List Stmt} {c : ValueId}
    (hseg : pureOk C Pat.cond [lo, hi] [c] segA = true) (hc : C.fresh c = true)
    (hb' : fr'.body = segA ++
      { results := [], inst := if nz then .trapnz c code else .trapz c code } :: ts2)
    (hcode : codeOk C rest fr.term ts2 fr'.term = true) :
    SimOut C env p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨c0, hi, hrs, hc0⟩ := planOf_trap hpl
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hc00 : c0 < C.T0 := ops_lt hG hB hst (by rcases hi with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [instOps])
  have hnc : ∀ fn args, st.inst ≠ .call fn args := fun _ _ h => by
    rcases hi with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at h <;> cases h
  have hnci : ∀ sig c args, st.inst ≠ .callIndirect sig c args := fun _ _ _ h => by
    rcases hi with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at h <;> cases h
  rw [step_inst env p ⟨fr, [], m⟩ st rest hb hnc hnci]
  cases hcv : fr.regs c0 with
  | none =>
    have : evalInst fr m st.inst = .stuck s!"use of undefined value v{c0}" := by
      rcases hi with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [evalInst, Frame.get, hcv, Res.ofOption, bind, Res.bind]
    rw [this]; trivial
  | some cv =>
    obtain ⟨l, h, rfl, hl, hh⟩ := pairVal hR.vrel hc00 hc0 hcv
    obtain ⟨regs', hls, hcr, hkeep⟩ := cond_run (fr' := fr') (m := m)
      (rest := { results := [], inst := if nz then .trapnz c code else .trapz c code } :: ts2) hseg hl hh
    have hfr : { fr' with body := segA ++
        { results := [], inst := if nz then .trapnz c code else .trapz c code } :: ts2 } = fr' := by
      rw [← hb']
    rw [hfr] at hls
    have hT := TStep.of_lstar (env := env) (p' := p') hls
    refine SimOut.pre hT (.inl rfl) ?_
    have hset : fr.regs.setMany st.results [] = some fr.regs := by rw [hrs]; rfl
    rcases hi with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · -- trapz: continue when the condition holds
      simp only [Bool.false_eq_true, ite_false]
      have hcv' : ({ fr' with regs := regs', body := { results := [], inst := .trapz c code } :: ts2 } :
          Frame).regs c = some ⟨.i8, Sem.bool8 (Sem.truthy (h ++ l))⟩ := hcr
      have hev : evalInst fr m st.inst =
          if Sem.truthy (h ++ l) then .ok ([], m) else .trap code := by
        rw [h1]; simp only [evalInst, Frame.get, hcv, Res.ofOption, bind, Res.bind]; rfl
      have hev' : evalInst { fr' with regs := regs', body := { results := [], inst := .trapz c code } :: ts2 } m (.trapz c code) =
          if Sem.truthy (h ++ l) then .ok ([], m) else .trap code := by
        simp only [evalInst, Frame.get, hcr, Res.ofOption, bind, Res.bind, truthy_bool8']; rfl
      rw [hev]
      by_cases hbt : Sem.truthy (h ++ l) = true
      · rw [if_pos hbt] at hev hev' ⊢
        simp only [StepResult.ofRes_ok, continueWith, hset]
        have h1s := lstep_eval (fr := { fr' with regs := regs', body := { results := [], inst := .trapz c code } :: ts2 }) (m := m) (st := { results := [], inst := .trapz c code })
          (rest := ts2) rfl (fun _ _ h => by cases h) hev' rfl
        refine ⟨rfl, hM, _, ?_, TStep.of_lstar (.single h1s)⟩
        exact frel_after hG hR hb hcode hset (by rw [hrs]; simp)
          (fun w hw _ => hkeep w hw (fresh_ne hc hw)) (srcInv_stmt hG.defs hB hst hR.src hev hset)
      · rw [if_neg hbt] at hev hev' ⊢
        refine ⟨1, ?_⟩
        rw [runLoop_succ, step_inst env p' ⟨{ fr' with regs := regs', body := { results := [], inst := .trapz c code } :: ts2 }, [], m⟩ { results := [], inst := .trapz c code }
          ts2 rfl (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)]
        simp only [hev']
        rfl
    · -- trapnz: continue when the condition fails
      simp only [ite_true]
      have hcv' : ({ fr' with regs := regs', body := { results := [], inst := .trapnz c code } :: ts2 } :
          Frame).regs c = some ⟨.i8, Sem.bool8 (Sem.truthy (h ++ l))⟩ := hcr
      have hev : evalInst fr m st.inst =
          if Sem.truthy (h ++ l) then .trap code else .ok ([], m) := by
        rw [h1]; simp only [evalInst, Frame.get, hcv, Res.ofOption, bind, Res.bind]; rfl
      have hev' : evalInst { fr' with regs := regs', body := { results := [], inst := .trapnz c code } :: ts2 } m (.trapnz c code) =
          if Sem.truthy (h ++ l) then .trap code else .ok ([], m) := by
        simp only [evalInst, Frame.get, hcr, Res.ofOption, bind, Res.bind, truthy_bool8']; rfl
      rw [hev]
      by_cases hbt : Sem.truthy (h ++ l) = true
      · rw [if_pos hbt] at hev hev' ⊢
        refine ⟨1, ?_⟩
        rw [runLoop_succ, step_inst env p' ⟨{ fr' with regs := regs', body := { results := [], inst := .trapnz c code } :: ts2 }, [], m⟩ { results := [], inst := .trapnz c code }
          ts2 rfl (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)]
        simp only [hev']
        rfl
      · rw [if_neg hbt] at hev hev' ⊢
        simp only [StepResult.ofRes_ok, continueWith, hset]
        have h1s := lstep_eval (fr := { fr' with regs := regs', body := { results := [], inst := .trapnz c code } :: ts2 }) (m := m) (st := { results := [], inst := .trapnz c code })
          (rest := ts2) rfl (fun _ _ h => by cases h) hev' rfl
        refine ⟨rfl, hM, _, ?_, TStep.of_lstar (.single h1s)⟩
        exact frel_after hG hR hb hcode hset (by rw [hrs]; simp)
          (fun w hw _ => hkeep w hw (fresh_ne hc hw)) (srcInv_stmt hG.defs hB hst hR.src hev hset)

/-! ## Calls with expanded arguments -/

/-- The source invariant after a statement whose results have the static types (not an
`iconst`/`iconcat`). -/
theorem srcInv_results {f : Function} (hnd : ((defsOf f).map (·.1)).Nodup) {B : Block}
    (hB : B ∈ f.blocks) {s : Stmt} (hs : s ∈ B.body) {ρ ρ1 : Regs} (hinv : SrcInv f ρ)
    {vals : List Val} (hty : s.inst.resultTypes (sigOfF f) (declOfF f) = some (vals.map (·.ty)))
    (hk : ∀ t k, s.inst ≠ .iconst t k) (hc : ∀ t lo hi, s.inst ≠ .iconcat t lo hi)
    (hset : ρ.setMany s.results vals = some ρ1) : SrcInv f ρ1 := by
  intro v x hx
  by_cases hv : v ∈ s.results
  · obtain ⟨i, hi, hvi⟩ := setMany_mem hset (results_nodup hnd hB hs) hv
    rw [hx] at hvi
    have hl := lookup_of_mem hnd (mem_defsOf_stmt hB hs hi)
    refine ⟨?_, ?_, ?_⟩
    · simp only [tyOf, hl, hty, Option.bind_some, List.getElem?_map, ← hvi, Option.map_some]
    · intro c hc'
      simp only [constOf, defInst, hl, Option.bind_some] at hc'
      split at hc'
      · rename_i t k hk'; exact absurd (Option.some.inj hk') (hk t k)
      · cases hc'
    · intro c hc'
      simp only [concatConst, defInst, hl, Option.bind_some] at hc'
      split at hc'
      · rename_i lo hi' hk'; exact absurd (Option.some.inj hk') (hc _ _ _)
      · cases hc'
  · rw [setMany_other hset hv] at hx; exact hinv v x hx

/-- The results of an expanded call: the source results represented, the target results images
or fresh pads. -/
theorem retsOk_bind {C : Ctx} {rg : List (List SlotEl)} {rs rs' : List ValueId}
    (h : retsOk C rg rs rs' = true) : ∀ {rv rv' : List Val}, ExpRel rg rv rv' →
    (∀ {ρ1 ρ1' : Regs}, Holds ρ1 rs rv → Holds ρ1' rs' rv' → rs.Nodup →
      ∀ v ∈ rs, ∀ x, ρ1 v = some x → RelV C ρ1' v x) ∧
    (∀ w ∈ rs', C.fresh w = true ∨ ∃ v ∈ rs, w ∈ img C v) ∧ rs'.length = rv'.length := by
  fun_induction retsOk C rg rs rs'
  case case1 =>
    intro rv rv' he
    cases rv with
    | cons => exact he.elim
    | nil =>
      cases rv' with
      | cons => exact he.elim
      | nil => exact ⟨fun _ _ _ v hv => by simp at hv, fun w hw => by simp at hw, rfl⟩
  case case2 p gs r rs r' rs' ih =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hp, rfl⟩, h⟩ := h
    intro rv rv' he
    rcases rv with _ | ⟨x, xs⟩
    · exact he.elim
    rcases rv' with _ | ⟨v', vs'⟩
    · exact he.elim
    obtain ⟨rfl, he⟩ := he
    obtain ⟨ih1, ih2, ih3⟩ := ih h he
    refine ⟨fun h1 h1' hnd u hu y hy => ?_, fun w hw => ?_, by simp [ih3]⟩
    · obtain ⟨h1a, h1b⟩ := h1
      obtain ⟨h1'a, h1'b⟩ := h1'
      simp only [List.nodup_cons] at hnd
      rcases List.mem_cons.1 hu with rfl | hu
      · rw [h1a] at hy; cases hy; rw [RelV.plain (plain_iff.1 hp)]; exact h1'a
      · exact ih1 h1b h1'b hnd.2 u hu y hy
    · rcases List.mem_cons.1 hw with rfl | hw
      · exact .inr ⟨w, by simp, by simp [img, plain_iff.1 hp]⟩
      · rcases ih2 w hw with h | ⟨u, hu, hwu⟩
        · exact .inl h
        · exact .inr ⟨u, List.mem_cons_of_mem _ hu, hwu⟩
  case case3 gs r rs a b rs' ih =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hp, h⟩ := h
    intro rv rv' he
    rcases rv with _ | ⟨x, xs⟩
    · exact he.elim
    rcases rv' with _ | ⟨va, _ | ⟨vb, vs'⟩⟩
    · exact he.elim
    · exact he.elim
    obtain ⟨⟨l, hh, rfl, rfl, rfl⟩, he⟩ := he
    obtain ⟨ih1, ih2, ih3⟩ := ih h he
    refine ⟨fun h1 h1' hnd u hu y hy => ?_, fun w hw => ?_, by simp [ih3]⟩
    · obtain ⟨h1a, h1b⟩ := h1
      obtain ⟨h1'a, h1'b, h1'c⟩ := h1'
      simp only [List.nodup_cons] at hnd
      rcases List.mem_cons.1 hu with rfl | hu
      · rw [h1a] at hy; cases hy; rw [RelV.pair hp]; exact ⟨l, hh, rfl, h1'a, h1'b⟩
      · exact ih1 h1b h1'c hnd.2 u hu y hy
    · simp only [List.mem_cons] at hw
      rcases hw with rfl | rfl | hw
      · exact .inr ⟨r, by simp, by simp [img, hp]⟩
      · exact .inr ⟨r, by simp, by simp [img, hp]⟩
      · rcases ih2 w hw with h | ⟨u, hu, hwu⟩
        · exact .inl h
        · exact .inr ⟨u, List.mem_cons_of_mem _ hu, hwu⟩
  case case4 gs r rs w0 a b rs' ih =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hf, hp⟩, h⟩ := h
    intro rv rv' he
    rcases rv with _ | ⟨x, xs⟩
    · exact he.elim
    rcases rv' with _ | ⟨vw, _ | ⟨va, _ | ⟨vb, vs'⟩⟩⟩
    · exact he.elim
    · exact he.elim
    · exact he.elim
    obtain ⟨-, ⟨l, hh, rfl, rfl, rfl⟩, he⟩ := he
    obtain ⟨ih1, ih2, ih3⟩ := ih h he
    refine ⟨fun h1 h1' hnd u hu y hy => ?_, fun w hw => ?_, by simp [ih3]⟩
    · obtain ⟨h1a, h1b⟩ := h1
      obtain ⟨-, h1'a, h1'b, h1'c⟩ := h1'
      simp only [List.nodup_cons] at hnd
      rcases List.mem_cons.1 hu with rfl | hu
      · rw [h1a] at hy; cases hy; rw [RelV.pair hp]; exact ⟨l, hh, rfl, h1'a, h1'b⟩
      · exact ih1 h1b h1'c hnd.2 u hu y hy
    · simp only [List.mem_cons] at hw
      rcases hw with rfl | rfl | rfl | hw
      · exact .inl hf
      · exact .inr ⟨r, by simp, by simp [img, hp]⟩
      · exact .inr ⟨r, by simp, by simp [img, hp]⟩
      · rcases ih2 w hw with h | ⟨u, hu, hwu⟩
        · exact .inl h
        · exact .inr ⟨u, List.mem_cons_of_mem _ hu, hwu⟩
  case case5 => cases h

end Opt.Legal
