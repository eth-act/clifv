module

public import FV.Opt.Proof.UnreachableX
public import FV.Opt.Proof.SimWinU

@[expose] public section

/-!
# `removeUnreachable` refines with handler edges (S10f, #233)

`Opt.removeUnreachable_simX` (`FV/Opt/Proof/UnreachableX.lean`) with the handler edges of
`IsSimU`: the frames run the same terminator, so a `try_call`'s table is the same on both
sides; a handler resumes both frames at the same block with the payload bound at each side's
fresh value, and the registers of `US` stay equal (as for the normal-return successor, `hpost`).
-/

namespace Opt

open Clif

/-- **`removeUnreachable` refines with handler edges** (`removeUnreachable_simX`). -/
theorem removeUnreachable_simU (f : Function) (hC : freshOkB f = true) :
    FunSimU f (removeUnreachable f) := by
  have hsd := removeUnreachable_sigDecls f
  revert hC hsd
  unfold freshOkB removeUnreachable
  by_cases hok : unreachableOk f (removeUnreachableRaw f) = true
  case neg => simp only [hok]; intro _ _; exact FunSimU.refl f
  simp only [hok, ite_true]
  generalize removeUnreachableRaw f = g at hok ⊢
  intro hC hsd
  obtain ⟨hn, hs, hsl, hgl, hex, hhd, hbl⟩ := unreachableOk_spec hok
  have hsub : ∀ b ∈ g.blocks, b ∈ f.blocks := by
    simp only [unreachableOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hok
    exact fun b hb => (hok.2 b hb).1
  have hle := freshValue_le_of_sub hsub
  -- every operand of `g` is in `US f g`
  have hops : ∀ b ∈ g.blocks, (∀ st ∈ b.body, ∀ v ∈ operands st.inst, US f g v) ∧
      ∀ v ∈ termOperands b.term, US f g v := by
    intro b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hC
    rcases hC with hC | hC
    · obtain ⟨h1, h2⟩ := closedB_spec hC hb
      exact ⟨fun st hst v hv => .inl (h1 st hst v hv), fun v hv => .inl (h2 v hv)⟩
    · exact ⟨fun _ _ _ _ => .inr hC, fun _ _ => .inr hC⟩
  have hheadOps : ∀ fr fr', UR f g fr fr' → ∀ v ∈ headOps fr, US f g v := by
    rintro fr fr' ⟨-, -, -, -, -, ⟨b, hb, hsuf, ht⟩, -⟩ v hv
    unfold headOps at hv
    split at hv
    · rename_i st _ hbd
      exact (hops b hb).1 st (hsuf.subset (by rw [hbd]; simp)) v hv
    · rw [ht] at hv; exact (hops b hb).2 v hv
  -- a step of `f`'s frame, run in `g` with `g`'s registers
  have hstep : ∀ fr fr' m, UR f g fr fr' →
      (∀ X1 m1, lstep fr m = .next X1 m1 → ∃ Y1, lstep fr' m = .next Y1 m1 ∧ UR f g X1 Y1) ∧
      (∀ r, (∀ X1 m1, r ≠ .next X1 m1) → (∀ msg, r ≠ .stuck msg) → lstep fr m = r →
        lstep fr' m = r) := by
    intro fr fr' m hr
    obtain ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, ht⟩, hag⟩ := hr
    have hw : lstep { fr with func := g } m = (lstep fr m).withFunc g :=
      lstep_withFunc (by rw [hf, hex]) (by rw [hf, hgl]) (by rw [hf, hs])
        (fun id hid => by rw [hf]; exact (hbl b hb id (ht ▸ hid)).2)
    obtain ⟨hA, hB⟩ := lstep_agree (S := US f g) (X := { fr with func := g }) (Y := fr') (m := m)
      hg hsl' hb' ht' hag (hheadOps fr fr' ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, ht⟩, hag⟩)
    refine ⟨fun X1 m1 h => ?_, fun r hn hns h => ?_⟩
    · have h' : lstep { fr with func := g } m = .next { X1 with func := g } m1 := by
        rw [hw, h]; rfl
      obtain ⟨Y1, hY, h1, h2, h3, h4, h5⟩ := hA _ _ h'
      refine ⟨Y1, hY, (lstep_next_frame h).1.trans hf, h1, h2, h3, h4, ?_, h5⟩
      have hI : FrameInv (fun _ => True) { fr with func := g } :=
        ⟨trivial, b, hb, hsuf, ht⟩
      obtain ⟨-, b2, hb2, hs2, ht2⟩ := lstep_next_inv hI h'
      exact ⟨b2, hb2, hs2, ht2⟩
    · have h' : lstep { fr with func := g } m = r := by
        rw [hw, h]
        cases r <;> first | rfl | exact absurd rfl (hn _ _)
      exact hB r hn hns h'
  refine FunSimU.ofWU hn hs hsl hex fun syms => ⟨UR f g, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- `IsSim`
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro fr _ ⟨hf, hg, hsl', -⟩; exact ⟨hsl', by rw [hg, hf, hs]⟩
    · rintro fr fr' m fr1 m1 hr hm hl
      obtain ⟨Y1, hY, hr1⟩ := (hstep fr fr' m hr).1 fr1 m1 hl
      exact ⟨Y1, .single hY, hr1⟩
    · rintro fr fr' m ext vals rs rest hr hm hl
      refine ⟨fr', rs, rest, .refl _ _, (hstep fr fr' m hr).2 _ (fun _ _ h => by cases h)
        (fun _ h => by cases h) hl, ?_⟩
      obtain ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, ht⟩, hag⟩ := hr
      obtain ⟨st, fn, args, hbd, -, -, -⟩ := lstep_call_inv hl
      intro vs regs _ hset
      obtain ⟨regs', hset', hag'⟩ := setMany_agree hag hset
      refine ⟨regs', hset', hf, hg, hsl', rfl, ht', ⟨b, hb, ?_, ht⟩, hag'⟩
      exact (List.suffix_cons st rest).trans (hbd ▸ hsuf)
    · rintro fr fr' m vals hr hm hl
      exact ⟨fr', .refl _ _, (hstep fr fr' m hr).2 _ (fun _ _ h => by cases h)
        (fun _ h => by cases h) hl⟩
    · rintro fr fr' m ext vals hr hm hl
      exact ⟨fr', .refl _ _, (hstep fr fr' m hr).2 _ (fun _ _ h => by cases h)
        (fun _ h => by cases h) hl⟩
    · rintro fr fr' m c hr hm hl
      exact ⟨fr', m, .refl _ _, (hstep fr fr' m hr).2 _ (fun _ _ h => by cases h)
        (fun _ h => by cases h) hl⟩
  · -- `call_indirect`
    rintro fr fr' m st rest sig callee args d a vals hr - - - hm hbd hi hca
    obtain ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, ht⟩, hag⟩ := hr
    have hst : st ∈ b.body := hsuf.subset (by rw [hbd]; simp)
    have hopsS := (hops b hb).1 st hst
    rw [hi] at hopsS
    refine ⟨fr', st, rest, sig, callee, args, .refl _ _, by rw [hb', hbd], hi, ?_, ?_⟩
    · rw [← hca]
      unfold ciArgs
      rw [getMany_congr (fr := fr) (fr' := fr') (fun v hv => hag v (hopsS v (by simp [operands, hv])))]
      simp only [Frame.get, hag callee (hopsS callee (by simp [operands])), hg, hf, hsd]
    · intro vs regs _ hset
      obtain ⟨regs', hset', hag'⟩ := setMany_agree hag hset
      refine ⟨regs', hset', hf, hg, hsl', rfl, ht', ⟨b, hb, ?_, ht⟩, hag'⟩
      exact (List.suffix_cons st rest).trans (hbd ▸ hsuf)
  · -- `try_call`, `try_call_indirect`
    have hpost : ∀ (fr fr' : Frame) (n : Nat) (bc bc' : BlockCall) (et : ExnTable)
        (hops' : ∀ v ∈ et.normal.vals, US f g v), UR f g fr fr' → Win fr fr' →
        (∃ b ∈ g.blocks, fr.term = b.term ∧ bc.block ∈ termSuccs b.term) →
        tryNormal et fr.func.freshValue = .ok bc → tryNormal et fr'.func.freshValue = .ok bc' →
        ∀ rtys, TCont (UR f g) fr (tryRets n fr.func.freshValue) bc fr'
          (tryRets n fr'.func.freshValue) bc' rtys := by
      rintro fr fr' n bc bc' et hops' hr hw ⟨b, hb, -, hsucc⟩ hbc hbc' rtys vs regs _ hset
      obtain ⟨hf, hg, hsl', hb', ht', -, hag⟩ := hr
      obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := tryRets n fr'.func.freshValue)
        (vs := vs) (by have := (setMany_spec hset).1; simp only [tryRets, List.length_map,
          List.length_range] at this ⊢; exact this)
      have hW := setMany_tryRets hset
      have hW' := setMany_tryRets hset'
      rw [hf] at hW; rw [hg] at hW'
      -- the registers after binding the results agree on `US`
      have hagr : Agree (US f g) regs regs' := by
        intro v hv
        rcases hv with hv | hv
        · have h1 : v ∉ tryRets n fr.func.freshValue := by
            intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
            have he' : fr.func.freshValue + j = v := he
            rw [hf] at he'; exact no_window he' hv hle
          have h2 : v ∉ tryRets n fr'.func.freshValue := by
            intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
            have he' : fr'.func.freshValue + j = v := he
            rw [hg] at he'; exact no_window he' hv (Nat.le_refl _)
          rw [((setMany_spec hset').2 v).1 h2, ((setMany_spec hset).2 v).1 h1]
          exact hag v (.inl hv)
        · by_cases hv' : f.freshValue ≤ v
          · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hv'
            have := hW' i; rw [hv] at this
            rw [this, hW i]
            split
            · rfl
            · exact hag (f.freshValue + i) (.inr hv)
          · have h1 : v ∉ tryRets n fr.func.freshValue := by
              intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
              have he' : fr.func.freshValue + j = v := he
              rw [hf] at he'; exact hv' (he' ▸ Nat.le_add_right _ _)
            have h2 : v ∉ tryRets n fr'.func.freshValue := by
              intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
              have he' : fr'.func.freshValue + j = v := he
              rw [hg, hv] at he'; exact hv' (he' ▸ Nat.le_add_right _ _)
            rw [((setMany_spec hset').2 v).1 h2, ((setMany_spec hset).2 v).1 h1]
            exact hag v (.inr hv)
      refine ⟨regs', hset', fun fr1 he => ?_⟩
      obtain ⟨b2, args2, regs2, hb2, hga2, hty2, hs2, rfl⟩ := enterBlock_ok he
      simp only at hb2 hga2 hs2
      obtain ⟨bc2, hbc2, hblk, hpw⟩ := tryNormal_pair id (et := et) (et' := et)
        (by rw [TryDest.mapVals_id]) (b2 := fr'.func.freshValue) hbc
      rw [hbc'] at hbc2; cases hbc2
      have hgb : g.block? bc'.block = some b2 := by
        rw [hblk, (hbl b hb _ hsucc).2, ← hf]; exact hb2
      have hga' : Frame.getMany { fr' with regs := regs' } bc'.args = .ok args2 := by
        refine getMany_pw2 (A := { fr with regs }) (hpw.imp fun x y h => ?_) hga2
        simp only
        rcases h with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
        · rw [hx, hy]; exact hagr v (hops' v hv)
        · rw [hx, hy]; simp only [hf, hg]; rw [hW i, hW' i]
          split
          · rfl
          · have := hw i; rw [hf, hg] at this; exact this.symm
      obtain ⟨regs2', hs2', hag2⟩ := setMany_agree hagr hs2
      refine ⟨_, enterBlock_of (fr := { fr' with regs := regs' }) (by rw [hg]; exact hgb) hga' hty2
        hs2', hf, hg, hsl', rfl, rfl, ⟨b2, block?_mem hgb, List.suffix_refl _, rfl⟩, hag2⟩
    -- the handler edges: the same table, the payload bound at each side's fresh value
    have hhand : ∀ (fr fr' : Frame) (et : ExnTable)
        (hops' : ∀ d ∈ et.handlers, ∀ v ∈ d.vals, US f g v), UR f g fr fr' → Win fr fr' →
        (∃ b ∈ g.blocks, fr.term = b.term ∧ ∀ d ∈ et.handlers, d.block ∈ termSuccs b.term) →
        HCont (UR f g) fr et fr' et := by
      rintro fr fr' et hops' hr hw ⟨b, hb, -, hsucc⟩ e
      obtain ⟨hf, hg, hsl', hb', ht', -, hag⟩ := hr
      refine ⟨fun hn => catchIn_eq_none.2 (catchIn_eq_none.1 hn), fun fr1 hc => ?_⟩
      obtain ⟨d, bc, regs, hd, hbc, hset, rfl⟩ := catchIn_ok hc
      obtain ⟨bc', hbc', hblk, hpw⟩ := tryHandler_pair id (b2 := fr'.func.freshValue) hbc
      rw [TryDest.mapVals_id] at hbc'
      obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs)
        (xs := (List.range e.payload.length).map (fr'.func.freshValue + ·)) (vs := e.payload)
        (by simp)
      have hW := setMany_tryRets (n := e.payload.length) (W := fr.func.freshValue) hset
      have hW' := setMany_tryRets (n := e.payload.length) (W := fr'.func.freshValue) hset'
      rw [hf] at hW; rw [hg] at hW'
      have hagr : Agree (US f g) regs regs' := by
        intro v hv
        rcases hv with hv | hv
        · have h1 : v ∉ tryRets e.payload.length fr.func.freshValue := by
            intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
            have he' : fr.func.freshValue + j = v := he
            rw [hf] at he'; exact no_window he' hv hle
          have h2 : v ∉ tryRets e.payload.length fr'.func.freshValue := by
            intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
            have he' : fr'.func.freshValue + j = v := he
            rw [hg] at he'; exact no_window he' hv (Nat.le_refl _)
          rw [((setMany_spec hset').2 v).1 h2, ((setMany_spec hset).2 v).1 h1]
          exact hag v (.inl hv)
        · by_cases hv' : f.freshValue ≤ v
          · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hv'
            have := hW' i; rw [hv] at this
            rw [this, hW i]
            split
            · rfl
            · exact hag (f.freshValue + i) (.inr hv)
          · have h1 : v ∉ tryRets e.payload.length fr.func.freshValue := by
              intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
              have he' : fr.func.freshValue + j = v := he
              rw [hf] at he'; exact hv' (he' ▸ Nat.le_add_right _ _)
            have h2 : v ∉ tryRets e.payload.length fr'.func.freshValue := by
              intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
              have he' : fr'.func.freshValue + j = v := he
              rw [hg, hv] at he'; exact hv' (he' ▸ Nat.le_add_right _ _)
            rw [((setMany_spec hset').2 v).1 h2, ((setMany_spec hset).2 v).1 h1]
            exact hag v (.inr hv)
      have hd' : d ∈ et.handlers := catch?_mem hd
      refine ⟨_, catchIn_of hd hbc' hset', rfl, rfl, bc, bc', rfl, rfl, fun fr1 he => ?_⟩
      have he0 : enterBlock { fr with regs } bc = .ok fr1 := by
        rw [← enterBlock_bt { fr with regs } [] (.jump bc)]; exact he
      obtain ⟨b2, args2, regs2, hb2, hga2, hty2, hs2, rfl⟩ := enterBlock_ok he0
      simp only at hb2 hga2 hs2
      have hsucc' : bc.block ∈ termSuccs b.term := by
        rw [tryHandler_block hbc]; exact hsucc d hd'
      have hgb : g.block? bc'.block = some b2 := by
        rw [hblk, (hbl b hb _ hsucc').2, ← hf]; exact hb2
      have hga' : Frame.getMany { fr' with regs := regs' } bc'.args = .ok args2 := by
        refine getMany_pw2 (A := { fr with regs }) (hpw.imp fun x y h => ?_) hga2
        simp only
        rcases h with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
        · rw [hx, hy]; exact hagr v (hops' d hd' v hv)
        · rw [hx, hy]; simp only [hf, hg]; rw [hW i, hW' i]
          split
          · rfl
          · have := hw i; rw [hf, hg] at this; exact this.symm
      obtain ⟨regs2', hs2', hag2⟩ := setMany_agree hagr hs2
      refine ⟨_, (enterBlock_bt { fr' with regs := regs' } [] (.jump bc') bc').trans
        (enterBlock_of (fr := { fr' with regs := regs' }) (by rw [hg]; exact hgb) hga' hty2 hs2'),
        hf, hg, hsl', rfl, rfl, ⟨b2, block?_mem hgb, List.suffix_refl _, rfl⟩, hag2⟩
    refine ⟨?_, ?_⟩
    · rintro fr fr' m fn args et n base bc ext vals hr - - hw hm hbd ht htc hca
      obtain ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, htb⟩, hag⟩ := hr
      have hopsT := (hops b hb).2
      rw [← htb, ht] at hopsT
      obtain ⟨rfl, hbc⟩ := tcArgs_base htc
      obtain ⟨bc', hbc', -⟩ := tryNormal_pair id (et := et) (et' := et)
        (by rw [TryDest.mapVals_id]) (b2 := fr'.func.freshValue) hbc
      have htc' : tcArgs fr' fn et = .ok (n, fr'.func.freshValue, bc') := by
        obtain ⟨e0, s0, he0, hs0, hc0, -, -, hn0⟩ := tcArgs_ok.1 htc
        refine tcArgs_ok.2 ⟨e0, s0, ?_, ?_, hc0, rfl, hbc', hn0⟩
        · rw [← he0]; simp only [Function.extern?, hg, hf, hex]
        · rw [← hs0, hg, hf, hsd]
      have hca' : callArgs fr' fn args = .ok (ext, vals) := by
        rw [← hca]
        unfold callArgs
        rw [getMany_congr (fr := fr) (fr' := fr') (fun v hv => hag v (hopsT v (by simp [termOperands, hv])))]
        simp only [Function.extern?, hg, hf, hex]
      refine ⟨fr', fn, args, et, _, bc', .refl _ _, by rw [hb', hbd], by rw [ht', ht], htc', hca',
        ?_, ?_⟩
      · exact hpost fr fr' n bc bc' et (fun v hv => hopsT v (normal_vals_sub v hv))
          ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, htb⟩, hag⟩ hw
          ⟨b, hb, htb, by rw [← htb, ht]; exact normal_succ hbc⟩ hbc hbc' _
      · exact hhand fr fr' et
          (fun d hd v hv => hopsT v (by simp [termOperands, handler_vals hd hv]))
          ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, htb⟩, hag⟩ hw
          ⟨b, hb, htb, fun d hd => by rw [← htb, ht]; exact handler_succ hd⟩
    · rintro fr fr' m callee args et n base bc d a vals hr - - hw hm hbd ht htc hca
      obtain ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, htb⟩, hag⟩ := hr
      have hopsT := (hops b hb).2
      rw [← htb, ht] at hopsT
      obtain ⟨rfl, hbc⟩ := ticArgs_base htc
      obtain ⟨bc', hbc', -⟩ := tryNormal_pair id (et := et) (et' := et)
        (by rw [TryDest.mapVals_id]) (b2 := fr'.func.freshValue) hbc
      have htc' : ticArgs fr' et = .ok (n, fr'.func.freshValue, bc') := by
        obtain ⟨s0, hs0, -, -, hn0⟩ := ticArgs_ok.1 htc
        exact ticArgs_ok.2 ⟨s0, by rw [← hs0, hg, hf, hsd], rfl, hbc', hn0⟩
      have hca' : ciArgs fr' et.sig callee args = .ok (d, a, vals) := by
        rw [← hca]
        unfold ciArgs
        rw [getMany_congr (fr := fr) (fr' := fr')
          (fun v hv => hag v (hopsT v (by simp [termOperands, hv])))]
        simp only [Frame.get, hag callee (hopsT callee (by simp [termOperands])), hg, hf, hsd]
      refine ⟨fr', callee, args, et, _, bc', .refl _ _, by rw [hb', hbd], by rw [ht', ht], htc', hca',
        ?_, ?_⟩
      · exact hpost fr fr' n bc bc' et (fun v hv => hopsT v (normal_vals_sub' v hv))
          ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, htb⟩, hag⟩ hw
          ⟨b, hb, htb, by rw [← htb, ht]; exact normal_succ hbc⟩ hbc hbc' _
      · exact hhand fr fr' et
          (fun d hd v hv => hopsT v (by simp [termOperands, handler_vals hd hv]))
          ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, htb⟩, hag⟩ hw
          ⟨b, hb, htb, fun d hd => by rw [← htb, ht]; exact handler_succ hd⟩
  · intro b hb
    have hb' : g.entry? = some b := by simpa [Function.entry?, hhd] using hb
    refine ⟨b, hb', rfl, fun args regs slots _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl,
      ⟨b, List.mem_of_mem_head? hb', List.suffix_refl _, rfl⟩, fun _ _ => rfl⟩⟩

end Opt
