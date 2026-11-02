import FV.Backend.Proof.IselPrgExt
import FV.Backend.Proof.IselPrgInv
import FV.Backend.Proof.IselFlowSplit

/-!
# Progress of the ISLE lowering (V7): soundness of the extractors and of the instruction data

The `ext` and `idata` fields of `Model` (`IselPrgModel`) for the transfer functions of
`IselPrgExt`, under the context invariant `PInv`:

* `aext_sound`: on a value `a` describes, an extern extractor `aext` accepts either succeeds with
  fields one of `aext`'s outputs describes, or fails where `aext` did not promise success. The
  type predicates (`tyPred`) are handled apart; the other extractors by `aext`'s dispatch, split
  once (`aext_split`, `gen_match_split`): per alternative, the concrete extractor (`externExtract`)
  is reduced at the alternative's term id (`ext_red`) and its outcome related to `aext`'s.
* `aidata_sound`: the `InstructionData` of an E instruction of `f` (`instData`) is variant `k` of
  `InstructionData` whose fields `aidata k` describes, by the instruction.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64 PA

variable {f : Clif.Function} {ctx : Ctx}

/-! ## Basics of `γ` -/

private theorem γL_nil' : γL f ctx [] [] := by simp [γL]

private theorem γL_cons' {a : PA} {as : List PA} {v : V} {vs : List V} (h1 : γ f ctx a v)
    (h2 : γL f ctx as vs) : γL f ctx (a :: as) (v :: vs) := by
  simp only [γL]; exact ⟨h1, h2⟩

private theorem γL1 {a : PA} {v : V} (h : γ f ctx a v) : γL f ctx [a] [v] := γL_cons' h γL_nil'

private theorem γL_cons_inv {a : PA} {as : List PA} {vs : List V} (h : γL f ctx (a :: as) vs) :
    ∃ w ws, vs = w :: ws ∧ γ f ctx a w ∧ γL f ctx as ws := by
  cases vs with
  | nil => simp [γL] at h
  | cons w ws => simp only [γL] at h; exact ⟨w, ws, rfl, h⟩

private theorem γL_nil_inv {vs : List V} (h : γL f ctx [] vs) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons w ws => simp [γL] at h

private theorem γ_int_any {i : Int} : γ f ctx (.int none none) (.int i) := by simp [γ]

private theorem γ_exact {i : Int} : γ f ctx (exact i) (.int i) := by simp [γ, exact]

private theorem γ_range {lo hi i : Int} (h1 : lo ≤ i) (h2 : i ≤ hi) : γ f ctx (range lo hi) (.int i) := by
  simp only [γ, range]; exact ⟨i, rfl, fun l e => by cases e; exact h1, fun h e => by cases e; exact h2⟩

private theorem γ_ty {t : CTy} {ts : List CTy} (h : t ∈ ts) : γ f ctx (.ty ts) (.ty t) := by
  simp only [γ]; exact ⟨t, h, rfl⟩

private theorem γ_label {l : Label} : γ f ctx .label (.label l) := by simp [γ]

private theorem γ_bool {b : Bool} : γ f ctx (.bool (some b)) (.bool b) := by simp [γ]

private theorem γ_extName {x : String} : γ f ctx (.op .extName none) (.op (.extName x)) := by
  simp [γ, OpOk]

private theorem γ_aDist {c : Bool} :
    γ f ctx aDist (.data tyRelocDistance
      (if c then VIdx.RelocDistance.Near else VIdx.RelocDistance.Far) []) := by
  cases c <;> simp [γ, γAny, γL, aDist, enumAlts]

private theorem γ_val_typed (hP : PInv f ctx) {x : Nat} (h : (ctx.valueType? x).isSome) :
    γ f ctx (.val eCTys) (.value x) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
  simp only [γ]; exact ⟨x, t, rfl, ht, hP.ctxInv.valTyE x t ht⟩

/-- A pruned abstract value describes nothing. -/
private theorem isBot_γ {a : PA} (h : a.isBot = true) (v : V) : ¬ γ f ctx a v := by
  intro hv
  cases a with
  | bot => simp [γ] at hv
  | ty ts =>
    cases ts with
    | nil => simp [γ] at hv
    | cons _ _ => simp [PA.isBot] at h
  | val ts =>
    cases ts with
    | nil => simp [γ] at hv
    | cons _ _ => simp [PA.isBot] at h
  | alts as =>
    cases as with
    | nil => simp [γ, γAny] at hv
    | cons _ _ => simp [PA.isBot] at h
  | _ => simp [PA.isBot] at h

/-- The exact integer of an integer value is its only member. -/
private theorem intOf_eq {lo hi : Option Int} {k i : Int} (hk : (PA.int lo hi).intOf = some k)
    (hl : ∀ l, lo = some l → l ≤ i) (hh : ∀ h, hi = some h → i ≤ h) : i = k := by
  match lo, hi, hk with
  | some l, some h, hk =>
    simp only [intOf] at hk
    split at hk
    · rename_i e
      cases hk
      have := hl _ rfl
      have := hh _ rfl
      simp only [beq_iff_eq] at e
      omega
    · cases hk

private theorem u64_lt (i : Int) : ((u64 i : Nat) : Int) ≤ 2 ^ 64 - 1 := by
  have h1 := Int.emod_nonneg i (by decide : (2 ^ 64 : Int) ≠ 0)
  have h2 := Int.emod_lt_of_pos i (by decide : (0 : Int) < 2 ^ 64)
  simp only [u64, Int.toNat_of_nonneg h1]
  omega

private theorem γ_u64 (i : Int) : γ f ctx (.int (some 0) (some (2 ^ 64 - 1))) (.int (u64 i : Int)) :=
  γ_range (by omega) (u64_lt i)

/-! ## Outcomes of an extractor -/

/-- The conclusion of `Model.ext` for an extractor outcome `r`. -/
def ExtConcl (f : Clif.Function) (ctx : Ctx) (r : ExtResult (List V)) (outs : List (List PA))
    (must : Bool) : Prop :=
  (∃ fs, r = .ok fs ∧ ∃ out ∈ outs, γL f ctx out fs) ∨ (r = .fail ∧ must = false)

private theorem concl_ok {r : ExtResult (List V)} {fs : List V} {out : List PA} {must : Bool}
    (he : r = .ok fs) (hg : γL f ctx out fs) : ExtConcl f ctx r [out] must :=
  .inl ⟨fs, he, out, List.mem_singleton_self _, hg⟩

private theorem concl_fail {r : ExtResult (List V)} {outs : List (List PA)} (he : r = .fail) :
    ExtConcl f ctx r outs false :=
  .inr ⟨he, rfl⟩

private theorem okOne_inv {fs : List PA} {outs : List (List PA)} {must : Bool}
    (h : okOne fs = some (outs, must)) : outs = [fs] ∧ must = true := by
  simp only [okOne, Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.symm⟩

private theorem mayOne_inv {fs : List PA} {outs : List (List PA)} {must : Bool}
    (h : mayOne fs = some (outs, must)) : outs = [fs] ∧ must = false := by
  simp only [mayOne, Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.symm⟩

private theorem noMatch_inv {outs : List (List PA)} {must : Bool}
    (h : noMatch = some (outs, must)) : outs = [] ∧ must = false := by
  simp only [noMatch, Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.symm⟩

/-- `aext`'s soundness at term id `id`, value `a`, result `r`. -/
def ExtOk (f : Clif.Function) (ctx : Ctx) (id : TermId) (a : PA)
    (r : Option (List (List PA) × Bool)) : Prop :=
  ∀ (term : Term), term.id = id → ∀ (outs : List (List PA)) (must : Bool) (v : V) (st : LState),
    r = some (outs, must) → γ f ctx a v → ExtConcl f ctx (externExtract ctx term v st) outs must

gen_match_split aext_split Backend.Proof.Prg.aext.match_9

/-- Reduce the goal's `externExtract` to its alternative at the literal term id of `hid`. -/
macro "ext_red " hid:ident : tactic =>
  `(tactic| (unfold externExtract; rw [$hid:ident]; conv => enter [3]; whnf))

private theorem concl_eq {r r' : ExtResult (List V)} {outs : List (List PA)} {must : Bool}
    (e : r = r') (h : ExtConcl f ctx r' outs must) : ExtConcl f ctx r outs must := e ▸ h

/-- Replace the goal's `externExtract` by `r`, its alternative at the literal term id of `hid`
(for alternatives that are an `if`, which `ext_red` would unfold). -/
macro "ext_is " hid:ident r:term : tactic =>
  `(tactic| refine concl_eq (r' := $r) (by unfold externExtract; rw [$hid:ident]; rfl) ?_)

/-! ## Facts from the context invariant -/

private theorem defClif_inv {n : Nat} {c : Clif.Inst} (h : ctx.defClif? n = some c) :
    ∃ j info, ctx.defInst? n = some j ∧ ctx.insts[j]? = some info ∧ info.clif = some c := by
  unfold Ctx.defClif? at h
  cases hj : ctx.defInst? n with
  | none => rw [hj] at h; cases h
  | some j =>
    cases hi : ctx.insts[j]? with
    | none => simp [hj, hi] at h
    | some info => simp [hj, hi] at h; exact ⟨j, info, rfl, hi, h⟩

private theorem instOf_defClif (hP : PInv f ctx) {n : Nat} {c : Clif.Inst}
    (h : ctx.defClif? n = some c) : InstOf f c := by
  obtain ⟨j, info, -, hi, hc⟩ := defClif_inv h
  exact hP.clifOf j info c hi hc

private theorem γ_defInst (hP : PInv f ctx) {x i : Nat} (hd : ctx.defInst? x = some i) :
    γ f ctx (.inst (.ty eCTys) .idata) (.inst i) := by
  obtain ⟨info, hi, hx⟩ := hP.ctxInv.defInst x i hd
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hP.ctxInv.defClif x i info hd hi)
  obtain ⟨tys, -, hres, hlen⟩ := hP.ctxInv.resTys i info c hi hc
  have hty : info.resTys.head?.getD .invalid ∈ eCTys := by
    cases hr : info.resTys with
    | nil =>
      rw [hr] at hres
      have : tys = [] := List.map_eq_nil_iff.mp hres.symm
      subst this
      rw [List.length_nil, List.length_eq_zero_iff] at hlen
      rw [hlen] at hx; cases hx
    | cons t ts =>
      exact hP.ctxInv.resTysE i info hi t (by rw [hr]; exact List.mem_cons_self ..)
  simp only [γ]
  exact ⟨i, info, rfl, hi, ⟨_, hty, rfl⟩,
    ⟨c, hP.clifOf i info c hi hc, hP.ctxInv.instE i info c hi hc, hP.ctxInv.data i info c hi hc⟩,
    hP.resTyped i info hi⟩

/-! ## Extractors -/

private theorem γ_imm12 {i : Imm12} : γ f ctx (.op .imm12 none) (.op (.imm12 i)) := by
  simp [γ, OpOk]

private theorem γ_extended {y : Nat} {e : ExtendOp} (h : (ctx.valueReg? y).isSome) :
    γ f ctx (.op .extended none) (.op (.extended y e)) := by
  simp only [γ, OpOk]; exact ⟨_, rfl, y, e, rfl, h⟩

private theorem contains_of_mem {ts : List CTy} {u : CTy} (ht : u ∈ ts) (h : (u == u) = true) :
    ts.contains u = true := by
  induction ts with
  | nil => cases ht
  | cons x xs ih =>
    simp only [List.contains_cons, Bool.or_eq_true]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact .inl h
    · exact .inr (ih ht)

private theorem eq_i64x2 {t : CTy} (h : (t == .vec 64 2 false) = true) : t = .vec 64 2 false := by
  cases t with
  | vec a b c =>
    have h1 : (a == 64 && (b == 2 && c == false)) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨rfl, rfl, rfl⟩ := h1
    rfl
  | _ => cases h

private theorem γ_labels {lo : Nat} {n : Option Nat} {ls : List Label} (h1 : lo ≤ ls.length)
    (h2 : n = none ∨ n = some ls.length) : γ f ctx (.labels lo n) (.labels ls) := by
  simp only [γ]; exact ⟨ls, rfl, h1, h2⟩

/-- The label fields of the label extractors. -/
macro "lab_fields" : tactic => `(tactic| first
  | exact γL1 γ_label
  | exact γL_cons' γ_label (γL1 γ_label)
  | (refine γL_cons' γ_label (γL1 (γ_labels ?_ ?_)) <;> (simp_all <;> omega)))

set_option hygiene false in
/-- Close a leaf of a dispatch on labels: `h` is `aext`'s verdict, the goal's outcome concrete. -/
macro "lab_fin " h:ident : tactic => `(tactic| first
  | (obtain ⟨rfl, rfl⟩ := noMatch_inv $h:ident; exact concl_fail rfl)
  | (obtain ⟨rfl, rfl⟩ := mayOne_inv $h:ident; exact concl_fail rfl)
  | (obtain ⟨rfl, rfl⟩ := mayOne_inv $h:ident; refine concl_ok rfl ?_; lab_fields)
  | (obtain ⟨rfl, rfl⟩ := okOne_inv $h:ident; refine concl_ok rfl ?_; lab_fields)
  | (exfalso; (simp_all <;> omega); done))

set_option maxHeartbeats 4000000 in
/-- **The extern extractors are sound** (`Model.ext`): on a value `a` describes, an extractor
`aext` accepts never throws, and either succeeds with fields one of `aext`'s outputs describes or
fails, where `aext` did not promise success. -/
theorem aext_sound (hP : PInv f ctx) (term : Term) (a : PA) (outs : List (List PA)) (must : Bool)
    (v : V) (st : LState) (h : aext term.id a = some (outs, must)) (hv : γ f ctx a v) :
    (∃ fs, externExtract ctx term v st = .ok fs ∧ ∃ out ∈ outs, γL f ctx out fs) ∨
      (externExtract ctx term v st = .fail ∧ must = false) := by
  show ExtConcl f ctx (externExtract ctx term v st) outs must
  cases hp : tyPred term.id with
  | some pr =>
    have e : ∀ t, externExtract ctx term (.ty t) st = if pr t then .ok [.ty t] else .fail := by
      intro t; unfold externExtract; rw [hp]
    unfold aext at h
    rw [hp] at h
    dsimp only at h
    cases a with
    | ty ts =>
      obtain ⟨t, ht, rfl⟩ := hv
      rw [e]
      dsimp only at h
      split at h
      · next hemp =>
        obtain ⟨rfl, rfl⟩ := noMatch_inv h
        have hf : pr t = false := by
          cases hq : pr t
          · rfl
          · have hm : t ∈ ts.filter pr := List.mem_filter.mpr ⟨ht, hq⟩
            rw [List.isEmpty_iff] at hemp
            rw [hemp] at hm; cases hm
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        exact concl_fail rfl
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        split
        · next hq => exact concl_ok rfl (γL1 (γ_ty (List.mem_filter.mpr ⟨ht, hq⟩)))
        · next hq =>
          refine .inr ⟨rfl, ?_⟩
          cases hall : ts.all pr
          · rfl
          · exact absurd (List.all_eq_true.mp hall t ht) hq
    | bot => exact absurd hv (isBot_γ rfl v)
    | _ => simp at h
  | none =>
  have key : ExtOk f ctx term.id a (aext term.id a) := by
    unfold aext
    rw [hp]
    dsimp only
    split
    · next hb => intro _ _ _ _ w _ _ hw; exact absurd hw (isBot_γ hb w)
    apply aext_split _ (ExtOk f ctx)
    -- offset32
    · intro lo hi term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      have hv0 := hv
      obtain ⟨i, rfl, -, -⟩ := hv
      ext_red hid
      exact concl_ok rfl (γL1 hv0)
    -- def_inst
    · intro ts term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := mayOne_inv h
      obtain ⟨x, t, rfl, -, -⟩ := hv
      ext_red hid
      cases hd : ctx.defInst? x with
      | none => exact concl_fail rfl
      | some i => exact concl_ok rfl (γL1 (γ_defInst hP hd))
    -- value_type
    · intro ts term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      obtain ⟨x, t, rfl, hxt, hts⟩ := hv
      ext_red hid
      rw [hxt]
      exact concl_ok rfl (γL1 (γ_ty hts))
    -- inst_data_value
    · intro t d term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      obtain ⟨j, info, rfl, hi, ht, hd, -⟩ := hv
      ext_red hid
      rw [hi]
      exact concl_ok rfl (γL_cons' ht (γL1 hd))
    -- first_result
    · intro t d term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := mayOne_inv h
      obtain ⟨j, info, rfl, hi, -, -, hr⟩ := hv
      ext_red hid
      rw [hi]
      dsimp only
      cases hres : info.results with
      | nil => exact concl_fail rfl
      | cons r rs =>
        exact concl_ok rfl (γL1 (γ_val_typed hP (hr r (by rw [hres]; exact List.mem_cons_self ..))))
    -- is_second_result
    · intro ts term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := mayOne_inv h
      have hv0 := hv
      obtain ⟨x, t, rfl, -, -⟩ := hv
      ext_red hid
      split
      · split
        · exact concl_ok rfl (γL1 hv0)
        · exact concl_fail rfl
      · exact concl_fail rfl
    -- i64_from_iconst
    · intro ts term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := mayOne_inv h
      obtain ⟨x, t, rfl, -, -⟩ := hv
      ext_red hid
      split
      · exact concl_ok rfl (γL1 γ_int_any)
      · exact concl_fail rfl
    -- maybe_uextend
    · intro ts term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      obtain ⟨x, t, rfl, hxt, -⟩ := hv
      ext_red hid
      split
      · next ty y hd =>
        exact concl_ok rfl (γL1 (γ_val_typed hP
          (hP.argsTyped _ (instOf_defClif hP hd) y (by simp [Driver.instArgs]))))
      · exact concl_ok rfl (γL1 (γ_val_typed hP (by rw [hxt]; rfl)))
    -- extended_value_from_value
    · intro ts term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := mayOne_inv h
      obtain ⟨x, t, rfl, -, -⟩ := hv
      ext_red hid
      split
      · next op ty y hd =>
        obtain ⟨b, hb, hb'⟩ := hP.extNarrow op ty y (instOf_defClif hP hd)
        have hr : (ctx.valueReg? y).isSome := by
          obtain ⟨n, hn⟩ := hP.ctxInv.typedSome y _ hb
          rw [hn]; rfl
        rw [hb]
        rcases hb' with rfl | rfl | rfl <;> cases op <;> exact concl_ok rfl (γL1 (γ_extended hr))
      · exact concl_fail rfl
    -- little_or_native_endian
    · intro n term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      have hv0 := hv
      obtain ⟨o, rfl, fl, rfl, hfl⟩ := hv
      ext_is hid (if fl.endianness == some .big then .fail else .ok [.op (.memFlags fl)])
      split
      · next hb => exact absurd (by simpa using hb) hfl
      · exact concl_ok rfl (γL1 hv0)
    -- u64_from_imm64
    · intro lo hi term hid outs must v st h hv
      obtain ⟨i, rfl, hl, hh⟩ := hv
      ext_red hid
      try dsimp only at h
      split at h
      · next k hk =>
        obtain ⟨rfl, rfl⟩ := okOne_inv h
        obtain rfl := intOf_eq hk hl hh
        exact concl_ok rfl (γL1 γ_exact)
      · obtain ⟨rfl, rfl⟩ := okOne_inv h
        exact concl_ok rfl (γL1 (γ_u64 i))
    -- nonzero_u64_from_imm64
    · intro lo hi term hid outs must v st h hv
      obtain ⟨i, rfl, hl, hh⟩ := hv
      ext_is hid (if i == 0 then .fail else .ok [.int (u64 i : Int)])
      try dsimp only at h
      split at h
      · next k hk =>
        obtain rfl := intOf_eq hk hl hh
        split at h
        · next hz =>
          obtain ⟨rfl, rfl⟩ := noMatch_inv h
          split
          · exact concl_fail rfl
          · contradiction
        · next hz =>
          obtain ⟨rfl, rfl⟩ := okOne_inv h
          split
          · contradiction
          · exact concl_ok rfl (γL1 γ_exact)
      · obtain ⟨rfl, rfl⟩ := mayOne_inv h
        split
        · exact concl_fail rfl
        · exact concl_ok rfl (γL1 (γ_u64 i))
    -- imm12_from_u64
    · intro a term hid outs must v st h hv
      try dsimp only at h
      unfold intTest at h
      split at h
      · next lo hi =>
        obtain ⟨i, rfl, hl, hh⟩ := hv
        ext_red hid
        split at h
        · next k hk =>
          obtain rfl := intOf_eq hk hl hh
          split at h
          · next hq =>
            obtain ⟨rfl, rfl⟩ := okOne_inv h
            have hq' : (Imm12.ofNat? (u64 i)).isSome = true := hq
            obtain ⟨imm, himm⟩ := Option.isSome_iff_exists.mp hq'
            rw [himm]; exact concl_ok rfl (γL1 γ_imm12)
          · next hq =>
            obtain ⟨rfl, rfl⟩ := noMatch_inv h
            have hq' : ¬ (Imm12.ofNat? (u64 i)).isSome = true := hq
            cases hm : Imm12.ofNat? (u64 i) with
            | none => exact concl_fail rfl
            | some _ => rw [hm] at hq'; exact absurd rfl hq'
        · obtain ⟨rfl, rfl⟩ := mayOne_inv h
          split
          · exact concl_ok rfl (γL1 γ_imm12)
          · exact concl_fail rfl
      · exact absurd hv (isBot_γ rfl v)
      · cases h
    -- i32_from_i64
    · intro lo hi term hid outs must v st h hv
      obtain ⟨i, rfl, hl, hh⟩ := hv
      ext_is hid (if -(2 ^ 31 : Int) ≤ i ∧ i < 2 ^ 31 then .ok [.int i] else .fail)
      try dsimp only at h
      split at h
      · next k hk =>
        obtain rfl := intOf_eq hk hl hh
        split at h
        · next hc =>
          obtain ⟨rfl, rfl⟩ := okOne_inv h
          split
          · exact concl_ok rfl (γL1 γ_exact)
          · contradiction
        · next hc =>
          obtain ⟨rfl, rfl⟩ := noMatch_inv h
          split
          · contradiction
          · exact concl_fail rfl
      · obtain ⟨rfl, rfl⟩ := mayOne_inv h
        split
        · next hc => exact concl_ok rfl (γL1 (γ_range (by omega) (by omega)))
        · exact concl_fail rfl
    -- u8_from_u64
    · intro lo hi term hid outs must v st h hv
      obtain ⟨i, rfl, hl, hh⟩ := hv
      ext_is hid (if 0 ≤ i ∧ i < 256 then .ok [.int i] else .fail)
      try dsimp only at h
      split at h
      · next k hk =>
        obtain rfl := intOf_eq hk hl hh
        split at h
        · next hc =>
          obtain ⟨rfl, rfl⟩ := okOne_inv h
          split
          · exact concl_ok rfl (γL1 γ_exact)
          · contradiction
        · next hc =>
          obtain ⟨rfl, rfl⟩ := noMatch_inv h
          split
          · contradiction
          · exact concl_fail rfl
      · obtain ⟨rfl, rfl⟩ := mayOne_inv h
        split
        · next hc => exact concl_ok rfl (γL1 (γ_range (by omega) (by omega)))
        · exact concl_fail rfl
    -- single_target
    · intro lo n term hid outs must v st h hv
      obtain ⟨ls, rfl, hlo, hn⟩ := hv
      try dsimp only at h
      rcases ls with _ | ⟨l, _ | ⟨l2, rest⟩⟩ <;> ext_red hid <;> repeat' split at h
      all_goals lab_fin h
    -- two_targets
    · intro lo n term hid outs must v st h hv
      obtain ⟨ls, rfl, hlo, hn⟩ := hv
      try dsimp only at h
      rcases ls with _ | ⟨l, _ | ⟨l2, _ | ⟨l3, rest⟩⟩⟩ <;> ext_red hid <;> repeat' split at h
      all_goals lab_fin h
    -- jump_table_targets
    · intro lo n term hid outs must v st h hv
      obtain ⟨ls, rfl, hlo, hn⟩ := hv
      try dsimp only at h
      rcases ls with _ | ⟨l, ls⟩ <;> ext_red hid <;> repeat' split at h
      all_goals lab_fin h
    -- value_list_slice (vals)
    · intro as term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      have hv0 := hv
      obtain ⟨xs, rfl, -⟩ := hv
      ext_red hid
      exact concl_ok rfl (γL1 hv0)
    -- value_list_slice (valsMin)
    · intro lo term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      have hv0 := hv
      obtain ⟨xs, rfl, -, -⟩ := hv
      ext_red hid
      exact concl_ok rfl (γL1 hv0)
    -- value_slice_unwrap (vals)
    · intro as term hid outs must v st h hv
      obtain ⟨xs, rfl, hxs⟩ := hv
      try dsimp only at h
      split at h
      · next b bs =>
        obtain ⟨rfl, rfl⟩ := okOne_inv h
        obtain ⟨w, ws, he, hb, hbs⟩ := γL_cons_inv hxs
        cases xs with
        | nil => cases he
        | cons x xs' =>
          simp only [List.map_cons, List.cons.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          ext_red hid
          exact concl_ok rfl (γL_cons' hb (γL1 (by simp only [γ]; exact ⟨xs', rfl, hbs⟩)))
      · obtain ⟨rfl, rfl⟩ := noMatch_inv h
        have hn := γL_nil_inv hxs
        cases xs with
        | nil => ext_red hid; exact concl_fail rfl
        | cons _ _ => cases hn
    -- value_slice_unwrap (valsMin)
    · intro lo term hid outs must v st h hv
      obtain ⟨xs, rfl, hlo, hty⟩ := hv
      try dsimp only at h
      cases xs with
      | nil =>
        ext_red hid
        split at h
        · simp only [List.length_nil] at hlo; omega
        · obtain ⟨rfl, rfl⟩ := mayOne_inv h; exact concl_fail rfl
      | cons x xs =>
        ext_red hid
        have hx := γ_val_typed hP (hty x List.mem_cons_self)
        have hr : γ f ctx (.valsMin (lo - 1)) (.values xs) := by
          simp only [γ]
          exact ⟨xs, rfl, by simp only [List.length_cons] at hlo; omega,
            fun y hy => hty y (List.mem_cons_of_mem _ hy)⟩
        have hr0 : γ f ctx (.valsMin 0) (.values xs) := by
          simp only [γ]
          exact ⟨xs, rfl, Nat.zero_le _, fun y hy => hty y (List.mem_cons_of_mem _ hy)⟩
        split at h
        · obtain ⟨rfl, rfl⟩ := okOne_inv h; exact concl_ok rfl (γL_cons' hx (γL1 hr))
        · obtain ⟨rfl, rfl⟩ := mayOne_inv h; exact concl_ok rfl (γL_cons' hx (γL1 hr0))
    -- value_array_2
    · intro x y term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      obtain ⟨xs, rfl, hxs⟩ := hv
      obtain ⟨w1, ws1, e1, h1, hxs⟩ := γL_cons_inv hxs
      obtain ⟨w2, ws2, e2, h2, hxs⟩ := γL_cons_inv hxs
      have e3 := γL_nil_inv hxs
      subst e3 e2
      rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp at e1
      obtain ⟨rfl, rfl⟩ := e1
      ext_red hid
      exact concl_ok rfl (γL_cons' h1 (γL1 h2))
    -- value_array_3
    · intro x y z term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      obtain ⟨xs, rfl, hxs⟩ := hv
      obtain ⟨w1, ws1, e1, h1, hxs⟩ := γL_cons_inv hxs
      obtain ⟨w2, ws2, e2, h2, hxs⟩ := γL_cons_inv hxs
      obtain ⟨w3, ws3, e3, h3, hxs⟩ := γL_cons_inv hxs
      have e4 := γL_nil_inv hxs
      subst e4 e3 e2
      rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> simp at e1
      obtain ⟨rfl, rfl, rfl⟩ := e1
      ext_red hid
      exact concl_ok rfl (γL_cons' h1 (γL_cons' h2 (γL1 h3)))
    -- symbol_value_data (globalValue)
    · intro n term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      obtain ⟨o, rfl, g, name, off, col, rfl, hg⟩ := hv
      ext_red hid
      rw [hg]
      exact concl_ok rfl (γL_cons' γ_extName (γL_cons' γ_aDist (γL1 γ_int_any)))
    -- symbol_value_data (tlsGlobalValue)
    · intro n term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      obtain ⟨o, rfl, g, name, off, col, rfl, hg⟩ := hv
      ext_red hid
      rw [hg]
      exact concl_ok rfl (γL_cons' γ_extName (γL_cons' γ_aDist (γL1 γ_int_any)))
    -- block_array_2
    · intro _ term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      obtain ⟨bs, rfl, hbs⟩ := hv
      rcases bs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      all_goals try (simp at hbs; done)
      ext_red hid
      exact concl_ok rfl (γL_cons' (by simp [γ]) (γL1 (by simp [γ])))
    -- func_ref_data (funcRef)
    · intro n term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      obtain ⟨o, rfl, fn, ext, rfl, hext, hsig, hn⟩ := hv
      ext_red hid
      rw [hext]
      exact concl_ok rfl (γL_cons' (by simp only [γ, OpOk]; exact ⟨_, rfl, _, rfl, hsig, hn⟩)
        (γL_cons' γ_extName (γL_cons' γ_aDist (γL1 γ_bool))))
    -- func_ref_data (funcRefTry)
    · intro n term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      obtain ⟨o, rfl, fn, ext, rfl, hext, hsig, htr⟩ := hv
      ext_red hid
      rw [hext]
      exact concl_ok rfl (γL_cons' (by simp only [γ, OpOk]; exact ⟨_, rfl, _, rfl, hsig, htr⟩)
        (γL_cons' γ_extName (γL_cons' γ_aDist (γL1 γ_bool))))
    -- multi_lane
    · intro ts term hid outs must v st h hv
      obtain ⟨t, ht, rfl⟩ := hv
      ext_is hid (if t.laneCount > 1 then .ok [.int t.laneBits, .int t.laneCount] else .fail)
      try dsimp only at h
      split
      · next hc =>
        split at h
        · next hall =>
          have := List.all_eq_true.mp hall t ht
          simp only [decide_eq_true_eq] at this
          omega
        · obtain ⟨rfl, rfl⟩ := mayOne_inv h
          exact concl_ok rfl (γL_cons' γ_int_any (γL1 γ_int_any))
      · split at h
        · obtain ⟨rfl, rfl⟩ := noMatch_inv h; exact concl_fail rfl
        · obtain ⟨rfl, rfl⟩ := mayOne_inv h; exact concl_fail rfl
    -- dynamic_lane
    · intro ts term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := noMatch_inv h
      obtain ⟨t, -, rfl⟩ := hv
      ext_red hid
      exact concl_fail rfl
    -- not_i64x2
    · intro ts term hid outs must v st h hv
      obtain ⟨t, ht, rfl⟩ := hv
      ext_is hid (if t == .vec 64 2 false then .fail else .ok [])
      try dsimp only at h
      split
      · next hc =>
        split at h
        · obtain ⟨rfl, rfl⟩ := mayOne_inv h; exact concl_fail rfl
        · next hn => exact absurd (contains_of_mem (eq_i64x2 hc ▸ ht) rfl) hn
      · split at h
        · obtain ⟨rfl, rfl⟩ := mayOne_inv h; exact concl_ok rfl γL_nil'
        · obtain ⟨rfl, rfl⟩ := okOne_inv h; exact concl_ok rfl γL_nil'
    -- use_lse
    · intro t d term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := noMatch_inv h
      obtain ⟨j, info, rfl, -⟩ := hv
      ext_red hid
      exact concl_fail rfl
    -- use_dotprod
    · intro t d term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := noMatch_inv h
      obtain ⟨j, info, rfl, -⟩ := hv
      ext_red hid
      exact concl_fail rfl
    -- use_i8mm
    · intro t d term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := noMatch_inv h
      obtain ⟨j, info, rfl, -⟩ := hv
      ext_red hid
      exact concl_fail rfl
    -- sign_return_address_disabled
    · intro x term hid outs must v st h _
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      ext_red hid
      exact concl_ok rfl γL_nil'
    -- tls_model
    · intro ts term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      obtain ⟨t, -, rfl⟩ := hv
      ext_red hid
      exact concl_ok rfl (γL1 (by simp [γ, γL]))
    -- exception_sig (exnTable)
    · intro n term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      obtain ⟨o, rfl, s, items, rfl, hs, hn⟩ := hv
      ext_red hid
      exact concl_ok rfl (γL1 (by simp only [γ, OpOk]; exact ⟨_, rfl, s, rfl, hs, hn⟩))
    -- exception_sig (exnTry)
    · intro n term hid outs must v st h hv
      obtain ⟨rfl, rfl⟩ := okOne_inv h
      obtain ⟨o, rfl, s, items, rfl, hs, htr, -⟩ := hv
      ext_red hid
      exact concl_ok rfl (γL1 (by simp only [γ, OpOk]; exact ⟨_, rfl, s, rfl, hs, htr⟩))
    -- the others
    · intro _ _ term _ outs must v st h _
      cases h
  exact key term rfl outs must v st h hv

/-! ## The `InstructionData` of an E instruction -/

private theorem γAny_of_mem {as : List PA} {a : PA} {v : V} (ha : a ∈ as) (h : γ f ctx a v) :
    γAny f ctx as v := by
  induction as with
  | nil => cases ha
  | cons b bs ih =>
    simp only [γAny]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact .inl h
    · exact .inr (ih ha)

private theorem γ_enum {ty : TypeId} {os : List Nat} {w : V} {k : Nat} (h : w = .data ty k [])
    (hk : k ∈ os) : γ f ctx (enumAlts ty os) w := by
  subst h
  simp only [enumAlts, γ]
  exact γAny_of_mem (List.mem_map.mpr ⟨k, hk, rfl⟩) (by simp [γ, γL])

private theorem γ_vals2 (hP : PInv f ctx) {x y : Nat} (hx : (ctx.valueType? x).isSome)
    (hy : (ctx.valueType? y).isSome) : γ f ctx (.vals [aV, aV]) (.values [x, y]) := by
  simp only [γ]
  exact ⟨[x, y], rfl, γL_cons' (γ_val_typed hP hx) (γL1 (γ_val_typed hP hy))⟩

private theorem γ_vals3 (hP : PInv f ctx) {x y z : Nat} (hx : (ctx.valueType? x).isSome)
    (hy : (ctx.valueType? y).isSome) (hz : (ctx.valueType? z).isSome) :
    γ f ctx (.vals [aV, aV, aV]) (.values [x, y, z]) := by
  simp only [γ]
  exact ⟨[x, y, z], rfl, γL_cons' (γ_val_typed hP hx)
    (γL_cons' (γ_val_typed hP hy) (γL1 (γ_val_typed hP hz)))⟩

private theorem γ_valsMin {lo : Nat} {xs : List Nat} (hl : lo ≤ xs.length)
    (ht : ∀ x ∈ xs, (ctx.valueType? x).isSome) : γ f ctx (.valsMin lo) (.values xs) := by
  simp only [γ]; exact ⟨xs, rfl, hl, ht⟩

private theorem γ_memFlags {fl : Clif.MemFlags}
    (h : ¬ (fl.endianness == some Clif.Endianness.big) = true) :
    γ f ctx (.op .memFlags none) (.op (.memFlags fl)) := by
  simp only [γ, OpOk]; exact ⟨_, rfl, fl, rfl, by simpa using h⟩

private theorem γ_gv {g : Nat} {name : String} {off : Int} {col : Bool} (hf : ctx.func = f)
    (h : f.globals.lookup g = some (.symbol name off col)) :
    γ f ctx (.alts [.op .globalValue none, .op .tlsGlobalValue none]) (.op (.globalValue g)) := by
  subst hf; simp only [γ, γAny, OpOk]; exact .inl ⟨_, rfl, g, name, off, col, rfl, h⟩

private theorem γ_tls {g : Nat} {name : String} {off : Int} {col : Bool} (hf : ctx.func = f)
    (h : f.globals.lookup g = some (.tlsSymbol name off col)) :
    γ f ctx (.alts [.op .globalValue none, .op .tlsGlobalValue none]) (.op (.tlsGlobalValue g)) := by
  subst hf; simp only [γ, γAny, OpOk]; exact .inr (.inl ⟨_, rfl, g, name, off, col, rfl, h⟩)

private theorem γ_slot {s : Nat} (h : (ctx.slotOff.lookup s).isSome) :
    γ f ctx (.op .stackSlot none) (.op (.stackSlot s)) := by
  simp only [γ, OpOk]; exact ⟨_, rfl, s, rfl, h⟩

private theorem γ_funcRef {fn : Nat} (hf : ctx.func = f)
    (h : ∃ ext, f.extern? fn = some ext ∧ SigOk ext.sig) :
    γ f ctx (.op .funcRef none) (.op (.funcRef fn)) := by
  obtain ⟨ext, he, hs⟩ := h
  subst hf; simp only [γ, OpOk]; exact ⟨_, rfl, fn, ext, rfl, he, hs, .inl rfl⟩

private theorem γ_sig {s : Clif.Signature} (h : SigOk s) :
    γ f ctx (.op .sig none) (.op (.sig s)) := by
  simp only [γ, OpOk]; exact ⟨_, rfl, s, rfl, h, .inl rfl⟩

set_option hygiene false in
/-- Close the goal of `aidata_sound` for one instruction whose data is computed: the format's
fields, by kind (`hP`, `hargs`, `hfunc`, `hc` from `aidata_sound`'s context). -/
macro "idata_fin" : tactic => `(tactic| (
  refine ⟨_, _, _, rfl, rfl, ?_⟩
  repeat' first
    | exact γL_nil'
    | refine γL_cons' ?_ ?_
    | exact γ_enum rfl (by decide)
    | exact γ_int_any
    | exact γ_val_typed hP (hargs _ (by simp [Driver.instArgs]))
    | exact γ_vals2 hP (hargs _ (by simp [Driver.instArgs])) (hargs _ (by simp [Driver.instArgs]))
    | exact γ_vals3 hP (hargs _ (by simp [Driver.instArgs])) (hargs _ (by simp [Driver.instArgs]))
        (hargs _ (by simp [Driver.instArgs]))
    | exact γ_valsMin (by simp) (fun x hx => hargs x (by simpa [Driver.instArgs] using hx))
    | exact γ_memFlags ‹_›
    | exact γ_gv hfunc ‹_›
    | exact γ_tls hfunc ‹_›
    | exact γ_slot (hP.slots _ _ _ hc)
    | exact γ_funcRef hfunc (hP.callees _ _ hc (.inl ⟨_, rfl⟩))
    | exact γ_funcRef hfunc (hP.callees _ _ hc (.inr ⟨_, rfl⟩))
    | exact γ_sig (hP.indSigs _ _ _ _ hc ‹_›)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The `InstructionData` of an E instruction** (`Model.idata`): the data `instData` gives an
E instruction of `f` is variant `k` of `InstructionData` with fields `aidata k` describes. -/
theorem aidata_sound (hP : PInv f ctx) (v : V) (hv : γ f ctx .idata v) :
    ∃ k fs afs, v = .data tyInstData k fs ∧ aidata k = some afs ∧ γL f ctx afs fs := by
  simp only [γ] at hv
  obtain ⟨c, hc, hE, h⟩ := hv
  have hargs := hP.argsTyped c hc
  have hfunc := hP.ctxInv.func
  cases c
  case' unary op _ _ => cases op
  case' binary op _ _ _ => cases op
  case' div op _ _ _ => cases op
  case' icmp cc _ _ _ => cases cc
  case' extend op _ _ => cases op
  case' load op _ _ _ _ => cases op
  case' store op _ _ _ _ _ => cases op
  case' atomicRmw op _ _ _ _ => cases op
  all_goals try simp only [instData, unaryOpcode, binaryOpcode, divOpcode, loadOpcode, storeOpcode,
    rmwOpName] at h
  all_goals (repeat' split at h)
  all_goals try (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
  -- the float constants of S11e4 are outside E (`Compile.instE`)
  all_goals try (subst_vars; simp [Compile.instE, Compile.tyE] at hE; done)
  all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; idata_fin)

end Backend.Proof.Prg
