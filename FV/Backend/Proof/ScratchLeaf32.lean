import FV.Backend.Proof.IselPrgCtorBase

/-!
# Progress of the ISLE lowering (V7): the extern constructors' transfer function is sound

`actor_sound` (the `ctor` field of `Model`): for the context `ctx` of `f` (`PInv`), whenever
`actor` (`IselPrgExt`) gives a result for a constructor call on abstract arguments, the concrete
call `externCtor ctx term vs st` on values those arguments describe either succeeds with a value
the result describes, or fails and `actor` did not promise success; it never reaches an
`unmodeled` case.

`actor` mirrors `externCtor`'s dispatch: the type predicates first (`tyPred`), then one alternative
per term id and argument shape. The second dispatch is split with `gen_match_split` (one goal per
alternative of `actor`, `ActP`); each goal fixes the term id, so `red_head` evaluates `externCtor`
on the argument shapes the abstract arguments force, down to the helper's own test.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64 PA

gen_match_split actor_split Backend.Proof.Prg.actor.match_5

variable {f : Clif.Function} {ctx : Ctx}

namespace CS

set_option hygiene false in
/-- Introduce the call of an alternative of `actor`: its result `h`, the term (with the
alternative's id), the values `vs` and their description `hvs`. -/
macro "cintro" : tactic =>
  `(tactic| (intro a must h term vs st hid hvs; cases term; dsimp only at hid; subst hid))

set_option hygiene false in
/-- No values. -/
macro "gl0" : tactic => `(tactic| obtain rfl := CS.γL_nil hvs)
set_option hygiene false in
/-- One value `w1` (`hw1`). -/
macro "gl1" : tactic => `(tactic| (obtain ⟨w1, vs, rfl, hw1, hvs⟩ := CS.γL_cons hvs; gl0))
set_option hygiene false in
/-- One more value `w` (`hw`). -/
macro "glc " w:ident hw:ident : tactic =>
  `(tactic| obtain ⟨$w, vs, rfl, $hw, hvs⟩ := CS.γL_cons hvs)
set_option hygiene false in
/-- Two values. -/
macro "gl2" : tactic => `(tactic| (glc w1 hw1; glc w2 hw2; gl0))
set_option hygiene false in
/-- Three values. -/
macro "gl3" : tactic => `(tactic| (glc w1 hw1; glc w2 hw2; glc w3 hw3; gl0))
set_option hygiene false in
/-- Four values. -/
macro "gl4" : tactic => `(tactic| (glc w1 hw1; glc w2 hw2; glc w3 hw3; glc w4 hw4; gl0))
set_option hygiene false in
/-- Five values. -/
macro "gl5" : tactic =>
  `(tactic| (glc w1 hw1; glc w2 hw2; glc w3 hw3; glc w4 hw4; glc w5 hw5; gl0))
set_option hygiene false in
/-- Six values. -/
macro "gl6" : tactic =>
  `(tactic| (glc w1 hw1; glc w2 hw2; glc w3 hw3; glc w4 hw4; glc w5 hw5; glc w6 hw6; gl0))
set_option hygiene false in
/-- A sure result: `a` and `must = true`. -/
macro "cok" : tactic =>
  `(tactic| (simp only [cOk, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h))
set_option hygiene false in
/-- A literal result pair. -/
macro "cres" : tactic =>
  `(tactic| (simp only [cMay, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h))

end CS

set_option maxHeartbeats 4000000 in
/-- Every alternative of `actor`'s dispatch past the type predicates is sound. -/
theorem actor_none_sound (hP : PInv f ctx) (id : TermId) (as : List PA) (hp : tyPred id = none) :
    CS.ActP f ctx id as (actor id as) := by
  unfold actor
  rw [hp]
  dsimp only
  apply actor_split _ (CS.ActP f ctx)
  -- i64_sextend_imm64
  · intro tA x; cintro; gl2
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨ts, t, rfl, ht, rfl⟩ := CS.ty_sh hc.1 hw1
      obtain ⟨i, rfl⟩ := CS.int_sh hc.2 hw2
      red_head externCtor
      apply CS.fin_ok
      split at h
      · rename_i t' v hts hv
        cok
        simp only [tysOf, Option.some.injEq] at hts
        subst hts
        simp only [List.mem_singleton] at ht
        subst ht
        have := CS.intOf_sh hv hw2
        simp only [V.int.injEq] at this
        subst this
        exact CS.γ_exact _
      · cok
        exact CS.γ_intAny _
    · cases h
  -- ty_bits
  · intro tA; cintro; gl1
    obtain ⟨t, rfl, ha⟩ := CS.tyInt_sh h hw1
    red_head externCtor
    exact CS.fin_ok ha
  -- ty_bytes
  · intro tA; cintro; gl1
    obtain ⟨t, rfl, ha⟩ := CS.tyInt_sh h hw1
    red_head externCtor
    exact CS.fin_ok ha
  -- ty_mask
  · intro tA; cintro; gl1
    obtain ⟨t, rfl, ha⟩ := CS.tyInt_sh h hw1
    red_head externCtor
    exact CS.fin_ok ha
  -- offset32_to_i32
  · intro x; cintro; gl1
    obtain ⟨i, rfl, ha⟩ := CS.intOp1_sh h hw1
    red_head externCtor
    exact CS.fin_ok ha
  -- i32_to_offset32
  · intro x; cintro; gl1
    obtain ⟨i, rfl, ha⟩ := CS.intOp1_sh h hw1
    red_head externCtor
    exact CS.fin_ok ha
  -- signed_cond_code
  · intro cc; cintro; gl1
    obtain ⟨k, rfl, hok, hfail⟩ := CS.ccFilter_sh h hw1
    red_head externCtor
    split
    · exact CS.fin_ok (hok ‹_›)
    · exact CS.fin_fail (hfail (Bool.eq_false_iff.2 ‹_›))
  -- unsigned_cond_code
  · intro cc; cintro; gl1
    obtain ⟨k, rfl, hok, hfail⟩ := CS.ccFilter_sh h hw1
    red_head externCtor
    split
    · exact CS.fin_ok (hok ‹_›)
    · exact CS.fin_fail (hfail (Bool.eq_false_iff.2 ‹_›))
  -- trap_code_division_by_zero
  · intro _; cintro; gl0; cok
    red_head externCtor
    exact CS.fin_ok ⟨_, rfl, _, rfl⟩
  -- trap_code_integer_overflow
  · intro _; cintro; gl0; cok
    red_head externCtor
    exact CS.fin_ok ⟨_, rfl, _, rfl⟩
  -- safe_divisor_from_imm64
  · intro tA x; cintro; gl2
    obtain ⟨t, i, rfl, rfl, hok, hfail⟩ := CS.exactTest_sh h hw1 hw2
    red_head externCtor
    split
    · rename_i hc
      exact CS.fin_fail (hfail (by simp [hc]))
    · rename_i hc
      have hc' := Bool.eq_false_iff.2 hc
      obtain rfl := hok (by simp [hc'])
      exact CS.fin_ok (CS.γ_intAny _)
  -- value_reg
  · intro r; cintro; gl1
    split at h
    · rename_i hr; cok
      obtain ⟨x, rfl⟩ := CS.reg_sh hr hw1
      red_head externCtor
      exact CS.fin_ok ⟨_, rfl, rfl⟩
    · cases h
  -- value_regs
  · intro r s; cintro; gl2
    split at h
    · rename_i hr; cok
      simp only [Bool.and_eq_true] at hr
      obtain ⟨x, rfl⟩ := CS.reg_sh hr.1 hw1
      obtain ⟨y, rfl⟩ := CS.reg_sh hr.2 hw2
      red_head externCtor
      exact CS.fin_ok ⟨_, rfl, rfl⟩
    · cases h
  -- output_none
  · intro _; cintro; gl0; cok
    red_head externCtor
    exact CS.fin_ok ⟨[], rfl, by simp, .inr rfl⟩
  -- output
  · intro n; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨rs, rfl, hl⟩ := hw1
    red_head externCtor
    apply CS.fin_ok
    split
    · rename_i hn
      simp only [beq_iff_eq] at hn
      subst hn
      exact ⟨[rs], rfl, by simpa using hl, .inr rfl⟩
    · trivial
  -- output_vec
  · intro n; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨rss, rfl, h1, h2⟩ := hw1
    red_head externCtor
    exact CS.fin_ok ⟨rss, rfl, h1, h2⟩
  -- temp_writable_reg
  · intro tA; cintro; gl1
    split at h
    · rename_i hc; cok
      obtain ⟨t, ht, rfl⟩ := CS.tysAll_sh hc hw1
      obtain ⟨cls, hcls⟩ := Option.isSome_iff_exists.1 ht
      red_head externCtor
      rw [hcls]
      exact CS.fin_ok ⟨_, rfl⟩
    · cases h
  -- opportunistic_def
  · intro _ _; cintro; gl2; cok
    red_head externCtor
    exact CS.fin_ok CS.γ_unit
  -- put_in_reg
  · intro ts; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨x, t, rfl, ht, -⟩ := hw1
    red_head externCtor
    rw [hP.ctxInv.typedReg x t ht]
    exact CS.fin_ok ⟨_, rfl⟩
  -- put_in_regs
  · intro ts; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨x, t, rfl, ht, -⟩ := hw1
    red_head externCtor
    rw [hP.ctxInv.typedReg x t ht]
    exact CS.fin_ok ⟨_, rfl, rfl⟩
  -- put_in_regs_vec (values)
  · intro xs; cintro; gl1
    split at h
    · rename_i hall; cok
      simp only [γ] at hw1
      obtain ⟨ns, rfl, hns⟩ := hw1
      have htyped : ∀ x ∈ ns, (ctx.valueType? x).isSome = true := by
        intro x hx
        obtain ⟨b, hb, hbx⟩ := γL_mem hns (.value x) (List.mem_map_of_mem hx)
        obtain ⟨y, t, hy, ht⟩ := CS.val_sh (List.all_eq_true.1 hall b hb) hbx
        simp only [V.value.injEq] at hy
        subst hy
        simp [ht]
      obtain ⟨rs, hrs, hl⟩ := CS.mapM_reg hP ns htyped
      red_head externCtor
      rw [hrs]
      refine CS.fin_ok ⟨_, rfl, by simp, .inr ?_⟩
      simp [hl, γL_length hns]
    · cases h
  -- put_in_regs_vec (at least `lo` values)
  · intro lo; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨ns, rfl, -, htyped⟩ := hw1
    obtain ⟨rs, hrs, -⟩ := CS.mapM_reg hP ns htyped
    red_head externCtor
    rw [hrs]
    exact CS.fin_ok ⟨_, rfl, by simp, .inl rfl⟩
  -- value_regs_get
  · intro n i; cintro; gl2
    split at h
    · rename_i k hk
      split at h
      · rename_i hb; cok
        simp only [γ] at hw1
        obtain ⟨rs, rfl, hl⟩ := hw1
        have := CS.intOf_sh hk hw2
        subst this
        red_head externCtor
        have hlt : k.toNat < rs.length := by omega
        rw [List.getElem?_eq_getElem hlt]
        exact CS.fin_ok ⟨_, rfl⟩
      · cases h
    · cases h
  -- jump_table_size
  · intro lo n; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨ls, rfl, -⟩ := hw1
    red_head externCtor
    exact CS.fin_ok ⟨_, rfl, fun l hl => by simp at hl; omega, by simp⟩
  -- writable_reg_to_reg
  · intro r; cintro; gl1; cok
    red_head externCtor
    exact CS.fin_ok hw1
  -- invalid_reg
  · intro _; cintro; gl0; cok
    red_head externCtor
    exact CS.fin_ok ⟨_, rfl⟩
  -- is_sinkable_inst
  · intro _; cintro; gl1
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    red_head externCtor
    exact CS.fin_fail rfl
  -- emit
  · intro i; cintro; gl1
    split at h
    · rename_i hi; cok
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (ofvOk_sound hi hw1)
      red_head externCtor
      rw [hm]
      exact CS.fin_ok CS.γ_unit
    · cases h
  -- box_external_name
  · intro n; cintro; gl1; cok
    red_head externCtor
    exact CS.fin_ok hw1
  -- abi_sig
  · intro s; cintro; gl1; cok
    red_head externCtor
    exact CS.fin_ok hw1
  -- abi_stackslot_addr
  · intro rd n o; cintro; gl3
    split at h
    · rename_i ho; cok
      simp only [γ] at hw2
      obtain ⟨_, rfl, s, rfl, hs⟩ := hw2
      obtain ⟨off, rfl⟩ := CS.int_sh ho hw3
      obtain ⟨base, hb⟩ := Option.isSome_iff_exists.1 hs
      red_head externCtor
      rw [hb]
      exact CS.fin_ok ⟨_, rfl, hw1, ⟨_, rfl, CS.γ_intAny _, trivial⟩, trivial⟩
    · cases h
  -- abi_stackslot_offset_into_slot_region
  · intro n pa pb; cintro; gl3
    split at h
    · rename_i hc; cok
      simp only [Bool.and_eq_true] at hc
      simp only [γ] at hw1
      obtain ⟨_, rfl, s, rfl, hs⟩ := hw1
      obtain ⟨i, rfl⟩ := CS.int_sh hc.1 hw2
      obtain ⟨j, rfl⟩ := CS.int_sh hc.2 hw3
      obtain ⟨base, hb⟩ := Option.isSome_iff_exists.1 hs
      red_head externCtor
      rw [hb]
      exact CS.fin_ok (CS.γ_intAny _)
    · cases h
  -- gen_return
  · intro n; cintro; gl1
    split at h
    · rename_i hn; cok
      simp only [γ] at hw1
      obtain ⟨rss, rfl, h1, h2⟩ := hw1
      have hlen : rss.length ≤ 8 := by
        rcases h2 with h2 | h2 <;> simp only [reduceCtorEq, Option.some.injEq] at h2; omega
      red_head externCtor
      split
      · exact CS.fin_ok CS.γ_unit
      · rename_i hno
        exact absurd (CS.single_mapM_eq (fun _ => rfl) rss h1) (hno _ _ (CS.retRegs_some hlen))
    · cases h
  -- gen_call_output (signature)
  · intro n; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨_, rfl, s, rfl, hs, hn⟩ := hw1
    red_head externCtor
    obtain ⟨rss, hr, hl, h1⟩ := CS.foldOut (sigRets s) #[] st
    refine CS.fin_ok ⟨_, rfl, ?_, ?_⟩ <;> rw [hr]
    · simpa using h1
    · rcases hn with rfl | rfl
      · exact .inl rfl
      · exact .inr (by simp [hl])
  -- gen_call_output (`try_call` signature)
  · intro n; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨_, rfl, s, rfl, hs, -⟩ := hw1
    red_head externCtor
    obtain ⟨rss, hr, hl, h1⟩ := CS.foldOut (sigRets s) #[] st
    refine CS.fin_ok ⟨_, rfl, ?_, .inl rfl⟩
    rw [hr]
    simpa using h1
  -- gen_call_args (signature)
  · intro n m; cintro; gl2; cok
    simp only [γ] at hw1 hw2
    obtain ⟨_, rfl, s, rfl, hs, -⟩ := hw1
    obtain ⟨rss, rfl, h1, -⟩ := hw2
    obtain ⟨⟨locs, k⟩, hl⟩ := hs.1
    red_head externCtor
    split
    · exact CS.fin_ok ⟨_, rfl, _, rfl⟩
    · rename_i he
      rw [hl] at he
      cases he
    · rename_i hmn _
      exact (CS.single_mapM_ne hmn (fun _ => rfl) h1).elim
  -- gen_call_args (`try_call` signature)
  · intro n m; cintro; gl2; cok
    simp only [γ] at hw1 hw2
    obtain ⟨_, rfl, s, rfl, hs, -⟩ := hw1
    obtain ⟨rss, rfl, h1, -⟩ := hw2
    obtain ⟨⟨locs, k⟩, hl⟩ := hs.1
    red_head externCtor
    split
    · exact CS.fin_ok ⟨_, rfl, _, rfl⟩
    · rename_i he
      rw [hl] at he
      cases he
    · rename_i hmn _
      exact (CS.single_mapM_ne hmn (fun _ => rfl) h1).elim
  -- gen_call_rets (signature)
  · intro n m; cintro; gl2
    split at h
    · rename_i hm; cok
      simp only [γ] at hw1 hw2
      obtain ⟨_, rfl, s, rfl, hs, -⟩ := hw1
      obtain ⟨rss, rfl, h1, h2⟩ := hw2
      have hlen : rss.length ≤ 8 := by
        rcases h2 with h2 | h2 <;> simp only [reduceCtorEq, Option.some.injEq] at h2; omega
      red_head externCtor
      split
      · exact CS.fin_ok ⟨_, rfl, _, rfl⟩
      · rename_i hno
        exact absurd (CS.single_mapM_eq (fun _ => rfl) rss h1) (hno _ _ (CS.retRegs_some hlen))
    · cases h
  -- gen_call_rets (`try_call` signature)
  · intro n m; cintro; gl2
    split at h
    · rename_i hm; cok
      simp only [γ] at hw1 hw2
      obtain ⟨_, rfl, s, rfl, hs, -⟩ := hw1
      obtain ⟨rss, rfl, h1, h2⟩ := hw2
      have hlen : rss.length ≤ 8 := by
        rcases h2 with h2 | h2 <;> simp only [reduceCtorEq, Option.some.injEq] at h2; omega
      red_head externCtor
      split
      · exact CS.fin_ok ⟨_, rfl, _, rfl⟩
      · rename_i hno
        exact absurd (CS.single_mapM_eq (fun _ => rfl) rss h1) (hno _ _ (CS.retRegs_some hlen))
    · cases h
  -- try_call_none
  · intro _; cintro; gl0; cok
    red_head externCtor
    exact CS.fin_ok ⟨_, rfl, rfl⟩
  -- try_call_info
  · intro m lo k; cintro; gl2
    split at h
    · rename_i hk; cok
      simp only [beq_iff_eq] at hk
      subst hk
      simp only [γ] at hw1 hw2
      obtain ⟨_, rfl, s, items, rfl, -, -, hm⟩ := hw1
      obtain ⟨ls, rfl, -, hls⟩ := hw2
      have hlen : ls.length = items.length + 1 := by
        rcases hm with hm | hm <;> rcases hls with hl | hl <;>
          simp only [reduceCtorEq, Option.some.injEq] at hm hl <;> omega
      red_head externCtor
      split
      · exact CS.fin_ok ⟨_, rfl, _, rfl⟩
      · rename_i he
        simp [tryInfoOf, hlen] at he
    · cases h
  -- gen_try_call_rets
  · intro n; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨_, rfl, s, rfl, hs, hlen⟩ := hw1
    red_head externCtor
    rw [CS.retRegs_some hs.2]
    dsimp only
    split
    · rename_i hne
      simp [hlen] at hne
    · exact CS.fin_ok ⟨_, rfl, _, rfl⟩
  -- gen_call_info (signature)
  · intro n1 n2 n3 n4 x1 x2; cintro; gl6; cok
    simp only [γ] at hw1 hw2 hw3 hw4
    obtain ⟨_, rfl, s, rfl, hs, -⟩ := hw1
    obtain ⟨_, rfl, nm, rfl⟩ := hw2
    obtain ⟨_, rfl, us, rfl⟩ := hw3
    obtain ⟨_, rfl, ds, rfl⟩ := hw4
    obtain ⟨⟨locs, k⟩, hl⟩ := hs.1
    red_head externCtor
    rw [hl]
    exact CS.fin_ok ⟨_, rfl, _, rfl⟩
  -- gen_call_info (`try_call` signature)
  · intro n1 n2 n3 n4 x1 x2; cintro; gl6; cok
    simp only [γ] at hw1 hw2 hw3 hw4
    obtain ⟨_, rfl, s, rfl, hs, -⟩ := hw1
    obtain ⟨_, rfl, nm, rfl⟩ := hw2
    obtain ⟨_, rfl, us, rfl⟩ := hw3
    obtain ⟨_, rfl, ds, rfl⟩ := hw4
    obtain ⟨⟨locs, k⟩, hl⟩ := hs.1
    red_head externCtor
    rw [hl]
    exact CS.fin_ok ⟨_, rfl, _, rfl⟩
  -- gen_call_ind_info (signature)
  · intro n1 r n3 n4 x1; cintro; gl5
    split at h
    · rename_i hr; cok
      obtain ⟨rr, rfl⟩ := CS.reg_sh hr hw2
      simp only [γ] at hw1 hw3 hw4
      obtain ⟨_, rfl, s, rfl, hs, -⟩ := hw1
      obtain ⟨_, rfl, us, rfl⟩ := hw3
      obtain ⟨_, rfl, ds, rfl⟩ := hw4
      obtain ⟨⟨locs, k⟩, hl⟩ := hs.1
      red_head externCtor
      rw [hl]
      exact CS.fin_ok ⟨_, rfl, _, rfl⟩
    · cases h
  -- gen_call_ind_info (`try_call` signature)
  · intro n1 r n3 n4 x1; cintro; gl5
    split at h
    · rename_i hr; cok
      obtain ⟨rr, rfl⟩ := CS.reg_sh hr hw2
      simp only [γ] at hw1 hw3 hw4
      obtain ⟨_, rfl, s, rfl, hs, -⟩ := hw1
      obtain ⟨_, rfl, us, rfl⟩ := hw3
      obtain ⟨_, rfl, ds, rfl⟩ := hw4
      obtain ⟨⟨locs, k⟩, hl⟩ := hs.1
      red_head externCtor
      rw [hl]
      exact CS.fin_ok ⟨_, rfl, _, rfl⟩
    · cases h
  -- use_fp16
  · intro _; cintro; gl0; cok
    red_head externCtor
    exact CS.fin_ok ⟨_, rfl, .inr rfl⟩
  -- is_pic
  · intro _; cintro; gl0; cok
    red_head externCtor
    exact CS.fin_ok ⟨_, rfl, .inr rfl⟩

  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  -- bfm_imms
  · intro tA pa pb; cintro; gl3
    split at h
    · rename_i hc; cok
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨h1, h2⟩, h3⟩ := hc
      obtain ⟨_, t, -, -, rfl⟩ := CS.ty_sh h1 hw1
      obtain ⟨i, rfl⟩ := CS.int_sh h2 hw2
      obtain ⟨j, rfl⟩ := CS.int_sh h3 hw3
      red_head externCtor
      exact CS.fin_ok ⟨_, rfl, _, rfl⟩
    · cases h
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry

end Backend.Proof.Prg
