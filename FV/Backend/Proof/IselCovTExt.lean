import FV.Backend.Proof.IselCovTFns
import FV.Backend.Proof.IselCovExt

/-!
# Form coverage over float-capable contexts (typed V3): the extractors

`ext_sound`: `aext` describes the outputs of every extern extractor, in a float-capable context
(`CtxInvT`) whose instruction data is clean (`Cov.Clean`) and whose statements belong to the
instruction families (`FamCover`). The typed atoms follow the extractors' semantics: `value_type`
of `.value n` is `n`'s type, `def_inst` gives `n`'s defining instruction (of a family that may
define a value of `n`'s types), `first_result` the first result (of the family's first-result
types), `maybe_uextend` the value or the operand of its `uextend` (an integer position),
`value_array_*`/`value_slice_unwrap`/`value_list_slice` the positions of a `.values` list.
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (Clean ExtCov externExtract_cov sem_extract)
open Backend.Proof (ext_flagOff)

/-- **Every statement of the context belongs to an instruction family.** -/
def FamCover (ctx : Ctx) : Prop :=
  ∀ (j : Nat) (info : IInfo) (c : Clif.Inst), ctx.insts[j]? = some info → info.clif = some c →
    ∃ (i : Nat) (F : Fam), famTab[i]? = some F ∧ FamOk ctx F info

/-! ## The extractors' outputs -/

section Extract
variable {ctx : Ctx} {t : Term} {v : V} {st : LState} {fs : List V}

theorem ext_value_type (hid : t.id = TId.value_type) (h : externExtract ctx t v st = .ok fs) :
    ∃ n ty, v = .value n ∧ ctx.valueType? n = some ty ∧ fs = [.ty ty] := by
  unfold externExtract at h
  rw [hid, show tyPred TId.value_type = none from rfl] at h
  cases v
  case value n =>
    simp only at h
    split at h
    · cases h; exact ⟨n, _, rfl, ‹_›, rfl⟩
    · cases h
  all_goals simp only at h; cases h

theorem ext_def_inst (hid : t.id = TId.def_inst) (h : externExtract ctx t v st = .ok fs) :
    ∃ n i, v = .value n ∧ ctx.defInst? n = some i ∧ fs = [.inst i] := by
  unfold externExtract at h
  rw [hid, show tyPred TId.def_inst = none from rfl] at h
  cases v
  case value n =>
    simp only at h
    split at h
    · cases h; exact ⟨n, _, rfl, ‹_›, rfl⟩
    · cases h
  all_goals simp only at h; cases h

theorem ext_inst_data (hid : t.id = TId.inst_data_value) (h : externExtract ctx t v st = .ok fs) :
    ∃ i info, v = .inst i ∧ ctx.insts[i]? = some info ∧
      fs = [.ty (info.resTys.head?.getD .invalid), info.data] := by
  unfold externExtract at h
  rw [hid, show tyPred TId.inst_data_value = none from rfl] at h
  cases v
  case inst i =>
    simp only at h
    split at h
    · cases h; exact ⟨i, _, rfl, ‹_›, rfl⟩
    · cases h
  all_goals simp only at h; cases h

theorem ext_first_result (hid : t.id = TId.first_result) (h : externExtract ctx t v st = .ok fs) :
    ∃ i info r, v = .inst i ∧ ctx.insts[i]? = some info ∧ info.results.head? = some r ∧
      fs = [.value r] := by
  unfold externExtract at h
  rw [hid, show tyPred TId.first_result = none from rfl] at h
  cases v
  case inst i =>
    simp only at h
    split at h
    · split at h
      · cases h; exact ⟨i, _, _, rfl, ‹_›, ‹_›, rfl⟩
      · cases h
    · cases h
  all_goals simp only at h; cases h

theorem ext_second_result (hid : t.id = TId.is_second_result)
    (h : externExtract ctx t v st = .ok fs) : ∃ n, v = .value n ∧ fs = [.value n] := by
  unfold externExtract at h
  rw [hid, show tyPred TId.is_second_result = none from rfl] at h
  cases v
  case value n =>
    simp only at h
    split at h
    · split at h
      · cases h; exact ⟨n, rfl, rfl⟩
      · cases h
    · cases h
  all_goals simp only at h; cases h

theorem ext_maybe_uextend (hid : t.id = TId.maybe_uextend)
    (h : externExtract ctx t v st = .ok fs) :
    ∃ n, v = .value n ∧ (fs = [.value n] ∨
      ∃ ty x, ctx.defClif? n = some (.extend .uextend ty x) ∧ fs = [.value x]) := by
  unfold externExtract at h
  rw [hid, show tyPred TId.maybe_uextend = none from rfl] at h
  cases v
  case value n =>
    simp only at h
    split at h
    · cases h; exact ⟨n, rfl, .inr ⟨_, _, ‹_›, rfl⟩⟩
    · cases h; exact ⟨n, rfl, .inl rfl⟩
  all_goals simp only at h; cases h

theorem ext_array_2 (hid : t.id = TId.value_array_2) (h : externExtract ctx t v st = .ok fs) :
    ∃ a b, v = .values [a, b] ∧ fs = [.value a, .value b] := by
  unfold externExtract at h
  rw [hid, show tyPred TId.value_array_2 = none from rfl] at h
  cases v
  case values xs =>
    rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    all_goals simp only at h
    all_goals first | (cases h; exact ⟨_, _, rfl, rfl⟩) | cases h
  all_goals simp only at h; cases h

theorem ext_array_3 (hid : t.id = TId.value_array_3) (h : externExtract ctx t v st = .ok fs) :
    ∃ a b c, v = .values [a, b, c] ∧ fs = [.value a, .value b, .value c] := by
  unfold externExtract at h
  rw [hid, show tyPred TId.value_array_3 = none from rfl] at h
  cases v
  case values xs =>
    rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
    all_goals simp only at h
    all_goals first | (cases h; exact ⟨_, _, _, rfl, rfl⟩) | cases h
  all_goals simp only at h; cases h

theorem ext_slice_unwrap (hid : t.id = TId.value_slice_unwrap)
    (h : externExtract ctx t v st = .ok fs) :
    ∃ x xs, v = .values (x :: xs) ∧ fs = [.value x, .values xs] := by
  unfold externExtract at h
  rw [hid, show tyPred TId.value_slice_unwrap = none from rfl] at h
  cases v
  case values xs =>
    rcases xs with _ | ⟨a, rest⟩
    all_goals simp only at h
    all_goals first | (cases h; exact ⟨_, _, rfl, rfl⟩) | cases h
  all_goals simp only at h; cases h

theorem ext_list_slice (hid : t.id = TId.value_list_slice)
    (h : externExtract ctx t v st = .ok fs) : ∃ xs, v = .values xs ∧ fs = [.values xs] := by
  unfold externExtract at h
  rw [hid, show tyPred TId.value_list_slice = none from rfl] at h
  cases v
  case values xs =>
    simp only at h
    cases h; exact ⟨_, rfl, rfl⟩
  all_goals simp only at h; cases h

theorem ext_extended (hid : t.id = TId.extended_value_from_value)
    (h : externExtract ctx t v st = .ok fs) :
    ∃ x e b, fs = [.op (.extended x e)] ∧ ctx.valueType? x = some (.int b) := by
  unfold externExtract at h
  rw [hid, show tyPred TId.extended_value_from_value = none from rfl] at h
  cases v
  case value n =>
    simp only at h
    split at h
    · rename_i op ty x _
      split at h
      · rename_i b hb
        split at h
        · cases h; exact ⟨x, _, b, rfl, hb⟩
        · cases h
      · cases h
    · cases h
  all_goals simp only at h; cases h

end Extract

/-! ## Typed values -/

section Vals
variable {f : Clif.Function} {ctx : Ctx}

/-- Every value of a float-capable context has a type of `anyCTys` (or none). -/
theorem valIn_any (hctx : CtxInvT f ctx) (x : Nat) : ValIn ctx x anyCTys :=
  ⟨fun t ht => hctx.valTyM x t ht, fun _ => ⟨.int 8, by simp [anyCTys, eCTys], rfl⟩⟩

theorem γ_vM (hctx : CtxInvT f ctx) (x : Nat) : γ f ctx vM (.value x) := ⟨x, rfl, valIn_any hctx x⟩

theorem valIn_app {x : Nat} {ts : List CTy} (us : List CTy) (h : ValIn ctx x ts) :
    ValIn ctx x (ts ++ us) :=
  ⟨fun t ht => List.mem_append_left _ (h.1 t ht), fun hn => by
    obtain ⟨t, ht, hc⟩ := h.2 hn; exact ⟨t, List.mem_append_left _ ht, hc⟩⟩

/-- An integer-position value has an E type. -/
theorem valIn_intPos {x : Nat} (h : IntPos ctx x) : ValIn ctx x eCTys :=
  ⟨h, fun _ => ⟨.int 8, by simp [eCTys], rfl⟩⟩

end Vals

/-! ## Soundness -/

variable {f : Clif.Function} {ctx : Ctx}

theorem holdsP_single {a : AT} {w : V} (h : γ f ctx a w) : HoldsP f ctx [a] [w] := by
  intro i v hv
  cases i with
  | zero => simp at hv; subst hv; exact h
  | succ i => simp at hv

theorem holdsP_two {a b : AT} {v w : V} (ha : γ f ctx a v) (hb : γ f ctx b w) :
    HoldsP f ctx [a, b] [v, w] := by
  intro i u hu
  rcases i with _ | _ | i
  · simp at hu; subst hu; exact ha
  · simp at hu; subst hu; exact hb
  · simp at hu

theorem holdsP_all {as : List AT} {fs : List V}
    (h : ∀ i w, fs[i]? = some w → i < as.length → γ f ctx (as.getD i .top) w) : HoldsP f ctx as fs := by
  intro i w hw
  by_cases hi : i < as.length
  · exact h i w hw hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact γ_top w

theorem γ_c0 {w : V} (h : w.regsIn = [] ∧ covV w = true) : γ f ctx .c0 w :=
  ⟨fun r hr => (by rw [h.1] at hr; cases hr), fun _ => h.2⟩

/-- `γ_c0` from the integer analysis's `Cov.covV` (clean instruction data, extractor outputs). -/
theorem γ_c0c {w : V} (h : w.regsIn = [] ∧ Cov.covV w = true) : γ f ctx .c0 w :=
  γ_c0 ⟨h.1, covV_of_cov h.2⟩

/-- The value of a `.vals` position. -/
theorem valsN_sound (hctx : CtxInvT f ctx) {a : AT} {xs : List Nat} (hv : γ f ctx a (.values xs))
    (n : Nat) (hn : xs.length = n) : HoldsP f ctx (valsN n a) (xs.map .value) := by
  apply holdsP_all
  intro i w hw hi
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hw
  obtain ⟨x, hx, rfl⟩ := hw
  cases a with
  | vals tss =>
    obtain ⟨xs', he, hlen, hall⟩ := hv
    cases he
    simp only [valsN]
    split
    · rename_i hl
      have hi' : i < tss.length := hlen ▸ (List.getElem?_eq_some_iff.mp hx).1
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi']
      exact ⟨x, rfl, hall i x _ hx (List.getElem?_eq_getElem hi')⟩
    · rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split
      · exact γ_vM hctx x
      · exact γ_top _
  | valsAll ts =>
    obtain ⟨xs', he, hall⟩ := hv
    cases he
    simp only [valsN]
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split
    · exact ⟨x, rfl, hall x (List.mem_of_getElem? hx)⟩
    · exact γ_top _
  | _ =>
    simp only [valsN]
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split
    · exact γ_vM hctx x
    · exact γ_top _

/-- The first-result types of an `inst_data_value` of families `fs`. -/
theorem mem_resOf {fs : List Nat} {i : Nat} (hi : i ∈ fs) {F : Fam} (hF : famTab[i]? = some F)
    {t : CTy} (ht : t ∈ F.res) : t ∈ resOf fs := by
  unfold resOf
  refine List.mem_flatMap.mpr ⟨i, hi, ?_⟩
  rw [List.getD_eq_getElem?_getD, hF]
  exact ht

theorem valIn_mono {x : Nat} {ts us : List CTy} (h : ValIn ctx x ts) (hsub : ∀ t ∈ ts, t ∈ us) :
    ValIn ctx x us :=
  ⟨fun t ht => hsub t (h.1 t ht), fun hn => by
    obtain ⟨t, ht, hc⟩ := h.2 hn; exact ⟨t, hsub t ht, hc⟩⟩

/-- `dataOf fs` describes the data of an instruction of a family of `fs`. -/
theorem dataOf_sound {fs : List Nat} {i : Nat} (hi : i ∈ fs) {F : Fam}
    (hF : famTab[i]? = some F) {d : V} (hd : γP ctx noInst F.data d) : γ f ctx (dataOf fs) d := by
  unfold dataOf
  split
  · rename_i j
    simp only [List.mem_singleton] at hi
    subst hi
    rw [List.getD_eq_getElem?_getD, hF]
    exact γ_of_noInst hd
  · show γAny f ctx _ d
    rw [γAny_iff]
    refine ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
    rw [List.getD_eq_getElem?_getD, hF]
    exact γ_of_noInst hd

/-- The definition of a value of a type of `ts` is of a family `famsFor ts` names. -/
theorem mem_famsFor {i : Nat} {F : Fam} (hF : famTab[i]? = some F) {x : Nat} {ts : List CTy}
    (hx : ValIn ctx x ts) (hxa : ValIn ctx x F.all) : i ∈ famsFor ts := by
  unfold famsFor
  have hlt : i < famTab.length := (List.getElem?_eq_some_iff.mp hF).1
  refine List.mem_filter.mpr ⟨List.mem_range.mpr hlt, ?_⟩
  rw [List.getD_eq_getElem?_getD, hF]
  simp only [Option.getD_some, compat, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true]
  cases hty : ctx.valueType? x with
  | some t => exact .inl ⟨t, hx.1 t hty, t, hxa.1 t hty, decide_eq_true rfl⟩
  | none =>
    obtain ⟨t, ht, hc⟩ := hx.2 hty
    obtain ⟨u, hu, hcu⟩ := hxa.2 hty
    exact .inr ⟨⟨t, ht, by simp [hc]⟩, ⟨u, hu, by simp [hcu]⟩⟩

set_option maxHeartbeats 1000000 in
/-- **Extractors**: `aext` describes the outputs of every extern extractor. -/
theorem ext_sound (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) (a : AT)
    (term : Term) (v : V) (st : LState) (fs : List V) (hv : γ f ctx a v)
    (h : (sem ctx).extract term v st = .ok fs) : HoldsP f ctx (aext term.id a) fs := by
  rw [sem_extract] at h
  cases hp : tyPred term.id with
  | some q =>
    unfold externExtract at h
    rw [hp] at h
    cases v with
    | ty ty =>
      simp only at h
      split at h
      · rename_i hq
        cases h
        unfold aext
        rw [hp]
        simp only
        split
        · rename_i ts hts
          apply holdsP_single
          cases a with
          | ty ts' =>
            simp only [tysOf', Option.some.injEq] at hts
            subst hts
            obtain ⟨t, ht, he⟩ := hv
            cases he
            exact ⟨_, List.mem_filter.mpr ⟨ht, hq⟩, rfl⟩
          | _ => simp [tysOf'] at hts
        · exact holdsP_single (γ_top _)
      · cases h
    | _ => simp only at h; cases h
  | none =>
    have hc := externExtract_cov ctx term v st hp fs h
    have hclean := hc.clean hcl
    unfold aext
    rw [hp]
    dsimp only
    by_cases hid : (term.id == TId.value_type) = true
    · rw [if_pos hid]
      obtain ⟨n, ty, rfl, hty, rfl⟩ := ext_value_type (by simpa using hid) h
      split
      all_goals apply holdsP_single
      · rename_i ts
        obtain ⟨x, hx, hxv⟩ := hv
        cases hx
        exact ⟨ty, hxv.1 ty hty, rfl⟩
      · exact ⟨ty, hctx.valTyM n ty hty, rfl⟩
    rw [if_neg hid]
    by_cases hid : (term.id == TId.inst_data_value) = true
    · rw [if_pos hid]
      obtain ⟨i, info, rfl, hi, rfl⟩ := ext_inst_data (by simpa using hid) h
      split
      · rename_i fs'
        obtain ⟨j, info', he, hi', k, hk, F, hF, hok⟩ := hv
        cases he
        rw [hi] at hi'; cases hi'
        exact holdsP_two ⟨_, mem_resOf hk hF hok.1, rfl⟩ (dataOf_sound hk hF hok.2.2.2)
      · refine holdsP_two ?_ (γ_c0c (hcl i info hi))
        cases hr : info.resTys with
        | nil => exact ⟨.invalid, List.mem_cons_self, rfl⟩
        | cons t ts =>
          exact ⟨t, List.mem_cons_of_mem _
            (hctx.resTysM i info hi t (by rw [hr]; exact List.mem_cons_self)), rfl⟩
    rw [if_neg hid]
    by_cases hid : (term.id == TId.def_inst) = true
    · rw [if_pos hid]
      obtain ⟨n, i, rfl, hdi, rfl⟩ := ext_def_inst (by simpa using hid) h
      obtain ⟨info, hi, hres⟩ := hctx.defInst n i hdi
      obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.mp (hctx.defClif n i info hdi hi)
      obtain ⟨k, F, hF, hok⟩ := hfam i info c hi hc'
      split
      · rename_i ts
        apply holdsP_single
        refine ⟨i, info, rfl, hi, k, ?_, F, hF, hok⟩
        obtain ⟨x, hx, hxv⟩ := hv
        cases hx
        exact mem_famsFor hF hxv (hok.2.2.1 n hres)
      · apply holdsP_single
        exact ⟨i, info, rfl, hi, k, mem_allFams (List.getElem?_eq_some_iff.mp hF).1, F, hF, hok⟩
    rw [if_neg hid]
    by_cases hid : (term.id == TId.first_result) = true
    · rw [if_pos hid]
      obtain ⟨i, info, r, rfl, hi, hr, rfl⟩ := ext_first_result (by simpa using hid) h
      split
      all_goals apply holdsP_single
      · rename_i fs'
        obtain ⟨j, info', he, hi', k, hk, F, hF, hok⟩ := hv
        cases he
        rw [hi] at hi'; cases hi'
        exact ⟨r, rfl, valIn_mono (hok.2.1 r (by rw [hr]; rfl)) fun t ht => mem_resOf hk hF ht⟩
      · exact γ_vM hctx r
    rw [if_neg hid]
    by_cases hid : (term.id == TId.is_second_result) = true
    · rw [if_pos hid]
      obtain ⟨n, rfl, rfl⟩ := ext_second_result (by simpa using hid) h
      split
      all_goals apply holdsP_single
      · exact hv
      · exact γ_vM hctx n
    rw [if_neg hid]
    by_cases hid : (term.id == TId.maybe_uextend) = true
    · rw [if_pos hid]
      obtain ⟨n, rfl, hor⟩ := ext_maybe_uextend (by simpa using hid) h
      rcases hor with rfl | ⟨ty, x, hdc, rfl⟩
      · split
        all_goals apply holdsP_single
        · rename_i ts
          obtain ⟨y, hy, hyv⟩ := hv
          cases hy
          exact ⟨n, rfl, valIn_app _ hyv⟩
        · exact γ_vM hctx n
      · have hxint : ValIn ctx x eCTys := by
          unfold Ctx.defClif? at hdc
          obtain ⟨d, hd, hdc⟩ := bind_some_ex hdc
          obtain ⟨info, hi, hdc⟩ := bind_some_ex hdc
          exact valIn_intPos (hctx.intOps d info _ hi hdc x (by simp [intArgs]))
        split
        all_goals apply holdsP_single
        · exact ⟨x, rfl, valIn_mono hxint fun t ht => List.mem_append_right _ ht⟩
        · exact ⟨x, rfl, valIn_mono hxint fun t ht => List.mem_append_left _ ht⟩
    rw [if_neg hid]
    by_cases hid : (term.id == TId.value_array_2) = true
    · rw [if_pos hid]
      obtain ⟨a', b', rfl, rfl⟩ := ext_array_2 (by simpa using hid) h
      exact valsN_sound hctx hv 2 rfl
    rw [if_neg hid]
    by_cases hid : (term.id == TId.value_array_3) = true
    · rw [if_pos hid]
      obtain ⟨a', b', c', rfl, rfl⟩ := ext_array_3 (by simpa using hid) h
      exact valsN_sound hctx hv 3 rfl
    rw [if_neg hid]
    by_cases hid : (term.id == TId.value_slice_unwrap) = true
    · rw [if_pos hid]
      obtain ⟨x, xs, rfl, rfl⟩ := ext_slice_unwrap (by simpa using hid) h
      split
      · rename_i ts rest
        obtain ⟨ys, he, hlen, hall⟩ := hv
        cases he
        refine holdsP_two ⟨x, rfl, hall 0 x ts rfl rfl⟩ ⟨xs, rfl, by simpa using hlen, ?_⟩
        intro i y us hy hus
        exact hall (i + 1) y us (by simpa using hy) (by simpa using hus)
      · rename_i ts
        obtain ⟨ys, he, hall⟩ := hv
        cases he
        exact holdsP_two ⟨x, rfl, hall x List.mem_cons_self⟩
          ⟨xs, rfl, fun y hy => hall y (List.mem_cons_of_mem _ hy)⟩
      · exact holdsP_two (γ_vM hctx x) ⟨xs, rfl, fun y _ => valIn_any hctx y⟩
    rw [if_neg hid]
    by_cases hid : (term.id == TId.value_list_slice) = true
    · rw [if_pos hid]
      obtain ⟨xs, rfl, rfl⟩ := ext_list_slice (by simpa using hid) h
      split
      all_goals apply holdsP_single
      · exact hv
      · exact hv
      · exact ⟨xs, rfl, fun y _ => valIn_any hctx y⟩
    rw [if_neg hid]
    by_cases hid : (term.id == TId.extended_value_from_value) = true
    · rw [if_pos hid]
      obtain ⟨x, e, b, rfl, hb⟩ := ext_extended (by simpa using hid) h
      exact holdsP_single ⟨x, e, b, rfl, hb⟩
    rw [if_neg hid]
    by_cases hfo : flagOff term.id = true
    · rw [if_pos hfo]
      split
      · rename_i fs'
        obtain ⟨j, -, rfl, -⟩ := hv
        rw [ext_flagOff hfo] at h
        cases h
      · show HoldsP f ctx (List.replicate 4 _) fs
        exact holdsP_replicate (fun w hw => γ_c0c (hclean w hw)) 4
    rw [if_neg hfo]
    by_cases hid : (term.id == TId.multi_lane) = true
    · rw [if_pos hid]
      obtain ⟨t, rfl, hl⟩ := hc.lane (by simpa using hid)
      split
      · rename_i ts hts
        cases a with
        | ty ts' =>
          simp only [tysOf', Option.some.injEq] at hts
          subst hts
          obtain ⟨t', ht', he⟩ := hv
          cases he
          split
          · show HoldsP f ctx (List.replicate 2 _) fs
            exact holdsP_replicate (fun w hw => γ_c0c (hclean w hw)) 2
          · rename_i hno
            exact absurd (List.any_eq_true.mpr ⟨_, ht', by simpa using hl⟩) hno
        | _ => simp [tysOf'] at hts
      · show HoldsP f ctx (List.replicate 2 _) fs
        exact holdsP_replicate (fun w hw => γ_c0c (hclean w hw)) 2
    rw [if_neg hid]
    by_cases hid : (term.id == TId.dynamic_lane) = true
    · exact absurd (by simpa using hid) hc.dyn
    rw [if_neg hid]
    by_cases hid : (term.id == TId.tls_model) = true
    · rw [if_pos hid, hc.tls (by simpa using hid)]
      exact holdsP_single ⟨[], rfl, trivial⟩
    rw [if_neg hid]
    show HoldsP f ctx (List.replicate 4 _) fs
    exact holdsP_replicate (fun w hw => γ_c0c (hclean w hw)) 4

end Backend.Proof.CovT
