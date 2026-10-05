import FV.Backend.Proof.IselCovData

/-!
# Form coverage of the ISLE lowering (V3): the extern helpers

The fields of `CovModel` for the driver's semantics: extractors (`ext_sound`), constructors
(`ctor_sound`: results and emitted instructions), the `operand_size` oracle. The model's state
invariant is `CovSince s0`: every instruction emitted since `s0` is covered.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

/-! ## Extractors -/

/-- What the extern extractors give, for `aext`. -/
structure ExtCov (ctx : Ctx) (id : TermId) (v : V) (fs : List V) : Prop where
  clean : (∀ (i : Nat) (info : IInfo), ctx.insts[i]? = some info → info.data.regsIn = [] ∧ covV info.data = true) →
    ∀ w ∈ fs, w.regsIn = [] ∧ covV w = true
  vty : id = TId.value_type → ∃ n ty, ctx.valueType? n = some ty ∧ fs = [.ty ty]
  idv : id = TId.inst_data_value → ∃ i info, v = .inst i ∧ ctx.insts[i]? = some info ∧
    fs = [.ty (info.resTys.head?.getD .invalid), info.data]
  di : id = TId.def_inst → ∃ n i, ctx.defInst? n = some i ∧ fs = [.inst i]
  vals : id = TId.maybe_uextend ∨ id = TId.is_second_result ∨ id = TId.first_result ∨
    id = TId.value_array_2 ∨ id = TId.value_array_3 → ∀ w ∈ fs, ∃ x, w = .value x
  slice : id = TId.value_slice_unwrap → ∃ x xs, fs = [.value x, .values xs]
  lane : id = TId.multi_lane → ∃ t, v = .ty t ∧ t.laneCount > 1
  dyn : id ≠ TId.dynamic_lane
  tls : id = TId.tls_model → fs = [.data tyTlsModel VIdx.TlsModel.ElfGd []]

/-- `ExtCov` of every successful result. -/
def ExtCovP (ctx : Ctx) (id : TermId) (v : V) (r : ExtResult (List V)) : Prop :=
  ∀ fs, r = .ok fs → ExtCov ctx id v fs

set_option maxHeartbeats 4000000 in
/-- **Every extern extractor** satisfies `ExtCov` (the type predicates are handled apart). -/
theorem externExtract_cov (ctx : Ctx) (t : Term) (v : V) (st : LState) (hp : tyPred t.id = none) :
    ExtCovP ctx t.id v (externExtract ctx t v st) := by
  unfold externExtract
  rw [hp]
  apply externExtract_split _ (ExtCovP ctx)
  all_goals
    intros
    unfold ExtCovP
    intro fs h
    try dsimp only at h
    repeat' (split at h)
    all_goals try (cases h; done)
  all_goals cases h
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro hx; exact absurd hx (by decide))
    | (intro hx; rcases hx with hx | hx | hx | hx | hx <;> exact absurd hx (by decide))
    | (intro hx; exact absurd rfl hx)
    | (exact by decide)
    | skip
  all_goals first
    | (intro _ w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
       rcases hw with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩)
    | (intro _ w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
       subst hw; exact ⟨rfl, rfl⟩)
    | (intro hcl w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
       rcases hw with rfl | rfl
       · exact ⟨rfl, rfl⟩
       · exact hcl _ _ ‹_›)
    | (intro _ w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
       rcases hw with rfl | rfl | rfl | rfl <;>
         exact ⟨rfl, by first | rfl | simp [covV_data, covVL]⟩)
    | (intro _ w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
       subst hw; exact ⟨rfl, by first | rfl | simp [covV_data, covVL]⟩)
    | (intro _ w hw; simp at hw; done)
    | skip
  all_goals first
    | (intro _; exact ⟨_, _, ‹_›, rfl⟩)
    | (intro _; exact ⟨_, _, rfl, ‹_›, rfl⟩)
    | (intro _; exact ⟨_, _, rfl⟩)
    | (intro _; exact ⟨_, rfl, ‹_›⟩)
    | (intro _ w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
       rcases hw with rfl | rfl | rfl <;> exact ⟨_, rfl⟩)
    | (intro _ w hw; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
       subst hw; exact ⟨_, rfl⟩)
    | (intro _; rfl)

variable {f : Clif.Function} {ctx : Ctx}

theorem γ_c0 {w : V} (h : w.regsIn = [] ∧ covV w = true) : γ f ctx .c0 w :=
  ⟨fun r hr => (by rw [h.1] at hr; cases hr), fun _ => h.2⟩

theorem holdsP_single {a : AW} {w : V} (h : γ f ctx a w) : HoldsP f ctx [a] [w] := by
  intro i v hv
  cases i with
  | zero => simp at hv; subst hv; exact h
  | succ i => simp at hv

theorem holdsP_all {as : List AW} {fs : List V}
    (h : ∀ i w, fs[i]? = some w → i < as.length → γ f ctx (as.getD i .top) w) : HoldsP f ctx as fs := by
  intro i w hw
  by_cases hi : i < as.length
  · exact h i w hw hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact γ_top w

theorem sem_extract (ctx : Ctx) : (sem ctx).extract = externExtract ctx := rfl

/-- Every context instruction's data is clean. -/
def Clean (ctx : Ctx) : Prop :=
  ∀ (i : Nat) (info : IInfo), ctx.insts[i]? = some info → info.data.regsIn = [] ∧ covV info.data = true

set_option maxHeartbeats 1000000 in
/-- **Extractors**: `aext` describes the outputs of every extern extractor. -/
theorem ext_sound (hctx : CtxInv f ctx) (hcl : Clean ctx) (a : AW) (term : Term) (v : V)
    (st : LState) (fs : List V) (hv : γ f ctx a v) (h : (sem ctx).extract term v st = .ok fs) :
    HoldsP f ctx (aext term.id a) fs := by
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
            simp only [tysOf, Option.some.injEq] at hts
            subst hts
            obtain ⟨t, ht, he⟩ := hv
            cases he
            exact ⟨_, List.mem_filter.mpr ⟨ht, hq⟩, rfl⟩
          | _ => simp [tysOf] at hts
        · exact holdsP_single (γ_top _)
      · cases h
    | _ => simp only at h; cases h
  | none =>
    have hc := externExtract_cov ctx term v st hp fs h
    have hclean := hc.clean hcl
    unfold aext
    rw [hp]
    simp only
    split
    · rename_i hid
      obtain ⟨n, ty, hty, rfl⟩ := hc.vty (by simpa using hid)
      exact holdsP_single ⟨ty, hctx.valTyE n ty hty, rfl⟩
    split
    · rename_i _ hid
      obtain ⟨i, info, rfl, hi, rfl⟩ := hc.idv (by simpa using hid)
      apply holdsP_all
      intro j w hw hj
      cases j with
      | zero =>
        simp at hw; subst hw
        exact ⟨_, head_resTy_ex hctx hi, rfl⟩
      | succ j =>
        cases j with
        | zero =>
          simp at hw; subst hw
          have hd := hcl i info hi
          simp only [List.getD_cons_succ, List.getD_cons_zero]
          split
          · rename_i hx
            have hx' := hv.1
            obtain ⟨j', info', c, he, hi', hc', hd'⟩ := hx'
            cases he
            rw [hi] at hi'; cases hi'
            exact ⟨⟨c, hctx.instE i info c hi hc', hd'⟩, hd.1, hd.2⟩
          · exact γ_c0 hd
        | succ j => simp only [List.length_cons, List.length_nil] at hj; omega
    split
    · rename_i _ _ hid
      obtain ⟨n, i, hdi, rfl⟩ := hc.di (by simpa using hid)
      obtain ⟨info, hi, -⟩ := hctx.defInst n i hdi
      obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.mp (hctx.defClif n i info hdi hi)
      exact holdsP_single ⟨⟨i, info, c, rfl, hi, hc', hctx.data i info c hi hc'⟩, rfl, rfl⟩
    split
    · rename_i _ _ _ hid
      have hval := hc.vals (by
        simp only [Bool.or_eq_true, beq_iff_eq] at hid
        rcases hid with (h | h) | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h)))
      show HoldsP f ctx (List.replicate 1 _) fs
      exact holdsP_replicate (fun w hw => by
        obtain ⟨x, rfl⟩ := hval w hw; exact ⟨⟨x, rfl⟩, rfl, rfl⟩) 1
    split
    · rename_i _ _ _ _ hid
      have hval := hc.vals (.inr (.inr (.inr (.inl (by simpa using hid)))))
      show HoldsP f ctx (List.replicate 2 _) fs
      exact holdsP_replicate (fun w hw => by
        obtain ⟨x, rfl⟩ := hval w hw; exact ⟨⟨x, rfl⟩, rfl, rfl⟩) 2
    split
    · rename_i _ _ _ _ _ hid
      have hval := hc.vals (.inr (.inr (.inr (.inr (by simpa using hid)))))
      show HoldsP f ctx (List.replicate 3 _) fs
      exact holdsP_replicate (fun w hw => by
        obtain ⟨x, rfl⟩ := hval w hw; exact ⟨⟨x, rfl⟩, rfl, rfl⟩) 3
    split
    · rename_i _ _ _ _ _ _ hid
      obtain ⟨x, xs, rfl⟩ := hc.slice (by simpa using hid)
      apply holdsP_all
      intro j w hw hj
      cases j with
      | zero => simp at hw; subst hw; exact ⟨⟨x, rfl⟩, rfl, rfl⟩
      | succ j =>
        cases j with
        | zero => simp at hw; subst hw; exact γ_c0 ⟨rfl, rfl⟩
        | succ j => simp only [List.length_cons, List.length_nil] at hj; omega
    split
    · rename_i _ _ _ _ _ _ _ hid
      obtain ⟨t, rfl, hl⟩ := hc.lane (by simpa using hid)
      split
      · rename_i ts hts
        cases a with
        | ty ts' =>
          simp only [tysOf, Option.some.injEq] at hts
          subst hts
          obtain ⟨t', ht', he⟩ := hv
          cases he
          split
          · show HoldsP f ctx (List.replicate 2 _) fs
            exact holdsP_replicate (fun w hw => γ_c0 (hclean w hw)) 2
          · rename_i hno
            exact absurd (List.any_eq_true.mpr ⟨_, ht', by simpa using hl⟩) hno
        | _ => simp [tysOf] at hts
      · show HoldsP f ctx (List.replicate 2 _) fs
        exact holdsP_replicate (fun w hw => γ_c0 (hclean w hw)) 2
    split
    · rename_i _ _ _ _ _ _ _ _ hid
      exact absurd (by simpa using hid) hc.dyn
    split
    · rename_i _ _ _ _ _ _ _ _ _ hid
      rw [hc.tls (by simpa using hid)]
      exact holdsP_single ⟨[], rfl, trivial⟩
    · show HoldsP f ctx (List.replicate 4 _) fs
      exact holdsP_replicate (fun w hw => γ_c0 (hclean w hw)) 4

end Backend.Proof.Cov
