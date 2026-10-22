import FV.Backend.Proof.IselCovExt
import FV.Backend.Proof.IselCovFnsT
import FV.Backend.Proof.IselCovSemT
import FV.Compile.SubsetT

/-!
# Form coverage over float-capable contexts: the extern extractors

`ext_soundT`: `aextT` (`IselCovFnsT`) describes the outputs of every extern extractor on a
float-capable context (`CtxInvT`, `Clean`), at the scope `S` with the opcode split `iOps`/`fOps`
(`InstSplit`, `InstScopeT`): the type extractors give `mCTys` (`valTyM`), and `inst_data_value`'s
data output is the instruction's data, which `InstSplit` describes (`instSplit_data`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

theorem γ_c0T {w : V} (h : w.regsIn = [] ∧ covV w = true) : γT S iOps fOps f ctx .c0 w :=
  ⟨fun r hr => (by rw [h.1] at hr; cases hr), fun _ => h.2⟩

theorem holdsP_singleT {a : AW} {w : V} (h : γT S iOps fOps f ctx a w) : HoldsPT S iOps fOps f ctx [a] [w] := by
  intro i v hv
  cases i with
  | zero => simp at hv; subst hv; exact h
  | succ i => simp at hv

theorem holdsP_allT {as : List AW} {fs : List V}
    (h : ∀ i w, fs[i]? = some w → i < as.length → γT S iOps fOps f ctx (as.getD i .top) w) : HoldsPT S iOps fOps f ctx as fs := by
  intro i w hw
  by_cases hi : i < as.length
  · exact h i w hw hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact γT_top w

set_option maxHeartbeats 1000000 in
/-- **Extractors**: `aext` describes the outputs of every extern extractor. -/
theorem ext_soundT (hctx : CtxInvT f ctx) (hsp : InstSplit S f ctx iOps fOps)
    (hsc : InstScopeT ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true) (hcl : Clean ctx) (a : AW) (term : Term) (v : V)
    (st : LState) (fs : List V) (hv : γT S iOps fOps f ctx a v) (h : (sem ctx).extract term v st = .ok fs) :
    HoldsPT S iOps fOps f ctx (aextT term.id a) fs := by
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
        unfold aextT
        rw [hp]
        simp only
        split
        · rename_i ts hts
          apply holdsPT_single
          cases a with
          | ty ts' =>
            simp only [tysOf, Option.some.injEq] at hts
            subst hts
            obtain ⟨t, ht, he⟩ := hv
            cases he
            exact ⟨_, List.mem_filter.mpr ⟨ht, hq⟩, rfl⟩
          | _ => simp [tysOf] at hts
        · exact holdsP_singleT (γT_top _)
      · cases h
    | _ => simp only at h; cases h
  | none =>
    have hc := externExtract_cov ctx term v st hp fs h
    have hclean := hc.clean hcl
    unfold aextT
    rw [hp]
    simp only
    split
    · rename_i hid
      obtain ⟨n, ty, hty, rfl⟩ := hc.vty (by simpa using hid)
      exact holdsP_singleT ⟨ty, hctx.valTyM n ty hty, rfl⟩
    split
    · rename_i _ hid
      obtain ⟨i, info, rfl, hi, rfl⟩ := hc.idv (by simpa using hid)
      apply holdsP_allT
      intro j w hw hj
      cases j with
      | zero =>
        simp at hw; subst hw
        exact ⟨_, head_resTy_exT hctx hi, rfl⟩
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
            have hD := instSplit_data hsp hi hc' (hctx.data i info c hi hc')
            exact ⟨hD, hd.1, hd.2⟩
          · exact γ_c0T hd
        | succ j => simp only [List.length_cons, List.length_nil] at hj; omega
    split
    · rename_i _ _ hid
      obtain ⟨n, i, hdi, rfl⟩ := hc.di (by simpa using hid)
      obtain ⟨info, hi, -⟩ := hctx.defInst n i hdi
      obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.mp (hctx.defClif n i info hdi hi)
      exact holdsP_singleT ⟨⟨i, info, c, rfl, hi, hc', hctx.data i info c hi hc'⟩, rfl, rfl⟩
    split
    · rename_i _ _ _ hid
      have hval := hc.vals (by
        simp only [Bool.or_eq_true, beq_iff_eq] at hid
        rcases hid with (h | h) | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h)))
      show HoldsPT S iOps fOps f ctx (List.replicate 1 _) fs
      exact holdsPT_replicate (fun w hw => by
        obtain ⟨x, rfl⟩ := hval w hw; exact ⟨⟨x, rfl⟩, rfl, rfl⟩) 1
    split
    · rename_i _ _ _ _ hid
      have hval := hc.vals (.inr (.inr (.inr (.inl (by simpa using hid)))))
      show HoldsPT S iOps fOps f ctx (List.replicate 2 _) fs
      exact holdsPT_replicate (fun w hw => by
        obtain ⟨x, rfl⟩ := hval w hw; exact ⟨⟨x, rfl⟩, rfl, rfl⟩) 2
    split
    · rename_i _ _ _ _ _ hid
      have hval := hc.vals (.inr (.inr (.inr (.inr (by simpa using hid)))))
      show HoldsPT S iOps fOps f ctx (List.replicate 3 _) fs
      exact holdsPT_replicate (fun w hw => by
        obtain ⟨x, rfl⟩ := hval w hw; exact ⟨⟨x, rfl⟩, rfl, rfl⟩) 3
    split
    · rename_i _ _ _ _ _ _ hid
      obtain ⟨x, xs, rfl⟩ := hc.slice (by simpa using hid)
      apply holdsP_allT
      intro j w hw hj
      cases j with
      | zero => simp at hw; subst hw; exact ⟨⟨x, rfl⟩, rfl, rfl⟩
      | succ j =>
        cases j with
        | zero => simp at hw; subst hw; exact γ_c0T ⟨rfl, rfl⟩
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
          · show HoldsPT S iOps fOps f ctx (List.replicate 2 _) fs
            exact holdsPT_replicate (fun w hw => γ_c0T (hclean w hw)) 2
          · rename_i hno
            exact absurd (List.any_eq_true.mpr ⟨_, ht', by simpa using hl⟩) hno
        | _ => simp [tysOf] at hts
      · show HoldsPT S iOps fOps f ctx (List.replicate 2 _) fs
        exact holdsPT_replicate (fun w hw => γ_c0T (hclean w hw)) 2
    split
    · rename_i _ _ _ _ _ _ _ _ hid
      exact absurd (by simpa using hid) hc.dyn
    split
    · rename_i _ _ _ _ _ _ _ _ _ hid
      rw [hc.tls (by simpa using hid)]
      exact holdsP_singleT ⟨[], rfl, trivial⟩
    · show HoldsPT S iOps fOps f ctx (List.replicate 4 _) fs
      exact holdsPT_replicate (fun w hw => γ_c0T (hclean w hw)) 4

end Backend.Proof.Cov
