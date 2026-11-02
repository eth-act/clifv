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
alternative of `actor`, `ActP`); each goal fixes the term id, so `red_safe` evaluates `externCtor`
on the argument shapes the abstract arguments force, down to the helper's own test (`red_safe`).
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64 PA

gen_match_split Backend.Proof.Prg.CS.actor_split Backend.Proof.Prg.actor.match_5

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

/-- `retRegsC` places every value: one register per class entry. -/
theorem retRegsC_len : ∀ {cs : List RegClass} {nx nv : Nat} {ps : List Reg},
    retRegsC cs nx nv = some ps → ps.length = cs.length
  | [], _, _, ps, h => by simp only [retRegsC, Option.some.injEq] at h; subst h; rfl
  | .int :: cs, nx, nv, ps, h => by
    simp only [retRegsC] at h
    split at h
    · obtain ⟨qs, hq, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [retRegsC_len hq]
    · cases h
  | .float :: cs, nx, nv, ps, h => by
    simp only [retRegsC] at h
    split at h
    · obtain ⟨qs, hq, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [retRegsC_len hq]
    · cases h

set_option maxHeartbeats 4000000 in
/-- Every alternative of `actor`'s dispatch past the type predicates is sound. -/
theorem actor_none_sound (hP : PInv f ctx) (id : TermId) (as : List PA) (hp : tyPred id = none) :
    CS.ActP f ctx id as (actor id as) := by
  unfold actor
  rw [hp]
  dsimp only
  apply CS.actor_split _ (CS.ActP f ctx)
  -- i64_sextend_imm64
  · intro tA x; cintro; gl2
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨ts, t, rfl, ht, rfl⟩ := CS.ty_sh hc.1 hw1
      obtain ⟨i, rfl⟩ := CS.int_sh hc.2 hw2
      red_safe externCtor
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
    red_safe externCtor
    exact CS.fin_ok ha
  -- ty_bytes
  · intro tA; cintro; gl1
    obtain ⟨t, rfl, ha⟩ := CS.tyInt_sh h hw1
    red_safe externCtor
    exact CS.fin_ok ha
  -- ty_mask
  · intro tA; cintro; gl1
    obtain ⟨t, rfl, ha⟩ := CS.tyInt_sh h hw1
    red_safe externCtor
    exact CS.fin_ok ha
  -- offset32_to_i32
  · intro x; cintro; gl1
    obtain ⟨i, rfl, ha⟩ := CS.intOp1_sh h hw1
    red_safe externCtor
    exact CS.fin_ok ha
  -- i32_to_offset32
  · intro x; cintro; gl1
    obtain ⟨i, rfl, ha⟩ := CS.intOp1_sh h hw1
    red_safe externCtor
    exact CS.fin_ok ha
  -- signed_cond_code
  · intro cc; cintro; gl1
    obtain ⟨k, rfl, hok, hfail⟩ := CS.ccFilter_sh h hw1
    red_safe externCtor
    split
    · exact CS.fin_ok (hok ‹_›)
    · exact CS.fin_fail (hfail (Bool.eq_false_iff.2 ‹_›))
  -- unsigned_cond_code
  · intro cc; cintro; gl1
    obtain ⟨k, rfl, hok, hfail⟩ := CS.ccFilter_sh h hw1
    red_safe externCtor
    split
    · exact CS.fin_ok (hok ‹_›)
    · exact CS.fin_fail (hfail (Bool.eq_false_iff.2 ‹_›))
  -- trap_code_division_by_zero
  · intro _; cintro; gl0; cok
    red_safe externCtor
    exact CS.fin_ok ⟨_, rfl, _, rfl⟩
  -- trap_code_integer_overflow
  · intro _; cintro; gl0; cok
    red_safe externCtor
    exact CS.fin_ok ⟨_, rfl, _, rfl⟩
  -- safe_divisor_from_imm64
  · intro tA x; cintro; gl2
    obtain ⟨t, i, rfl, rfl, hok, hfail⟩ := CS.exactTest_sh h hw1 hw2
    red_safe externCtor
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
      red_safe externCtor
      exact CS.fin_ok ⟨_, rfl, rfl⟩
    · cases h
  -- value_regs
  · intro r s; cintro; gl2
    split at h
    · rename_i hr; cok
      simp only [Bool.and_eq_true] at hr
      obtain ⟨x, rfl⟩ := CS.reg_sh hr.1 hw1
      obtain ⟨y, rfl⟩ := CS.reg_sh hr.2 hw2
      red_safe externCtor
      exact CS.fin_ok ⟨_, rfl, rfl⟩
    · cases h
  -- output_none
  · intro _; cintro; gl0; cok
    red_safe externCtor
    exact CS.fin_ok ⟨[], rfl, by simp, .inr rfl⟩
  -- output
  · intro n; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨rs, rfl, hl⟩ := hw1
    red_safe externCtor
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
    red_safe externCtor
    exact CS.fin_ok ⟨rss, rfl, h1, h2⟩
  -- temp_writable_reg
  · intro tA; cintro; gl1
    split at h
    · rename_i hc; cok
      obtain ⟨t, ht, rfl⟩ := CS.tysAll_sh hc hw1
      obtain ⟨cls, hcls⟩ := Option.isSome_iff_exists.1 ht
      red_safe externCtor
      rw [hcls]
      exact CS.fin_ok ⟨_, rfl⟩
    · cases h
  -- opportunistic_def
  · intro _ _; cintro; gl2; cok
    red_safe externCtor
    exact CS.fin_ok CS.γ_unit
  -- put_in_reg
  · intro ts; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨x, t, rfl, ht, -⟩ := hw1
    red_safe externCtor
    obtain ⟨n, hn⟩ := hP.ctxInv.typedSome x t ht
    rw [hn]
    exact CS.fin_ok ⟨_, rfl⟩
  -- put_in_regs
  · intro ts; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨x, t, rfl, ht, -⟩ := hw1
    red_safe externCtor
    obtain ⟨n, hn⟩ := hP.ctxInv.typedSome x t ht
    rw [hn]
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
      red_safe externCtor
      rw [hrs]
      refine CS.fin_ok ⟨_, rfl, by simp, .inr ?_⟩
      simp [hl, γL_length hns]
    · cases h
  -- put_in_regs_vec (at least `lo` values)
  · intro lo; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨ns, rfl, -, htyped⟩ := hw1
    obtain ⟨rs, hrs, -⟩ := CS.mapM_reg hP ns htyped
    red_safe externCtor
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
        red_safe externCtor
        have hlt : k.toNat < rs.length := by omega
        rw [List.getElem?_eq_getElem hlt]
        exact CS.fin_ok ⟨_, rfl⟩
      · cases h
    · cases h
  -- jump_table_size
  · intro lo n; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨ls, rfl, -⟩ := hw1
    red_safe externCtor
    exact CS.fin_ok ⟨_, rfl, fun l hl => by simp at hl; omega, by simp⟩
  -- writable_reg_to_reg
  · intro r; cintro; gl1; cok
    red_safe externCtor
    exact CS.fin_ok hw1
  -- invalid_reg
  · intro _; cintro; gl0; cok
    red_safe externCtor
    exact CS.fin_ok ⟨_, rfl⟩
  -- is_sinkable_inst
  · intro _; cintro; gl1
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    red_safe externCtor
    exact CS.fin_fail rfl
  -- emit
  · intro i; cintro; gl1
    split at h
    · rename_i hi; cok
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (ofvOk_sound hi hw1)
      red_safe externCtor
      rw [hm]
      exact CS.fin_ok CS.γ_unit
    · cases h
  -- box_external_name
  · intro n; cintro; gl1; cok
    red_safe externCtor
    exact CS.fin_ok hw1
  -- abi_sig
  · intro s; cintro; gl1; cok
    red_safe externCtor
    exact CS.fin_ok hw1
  -- abi_stackslot_addr
  · intro rd n o; cintro; gl3
    split at h
    · rename_i ho; cok
      simp only [γ] at hw2
      obtain ⟨_, rfl, s, rfl, hs⟩ := hw2
      obtain ⟨off, rfl⟩ := CS.int_sh ho hw3
      obtain ⟨base, hb⟩ := Option.isSome_iff_exists.1 hs
      red_safe externCtor
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
      red_safe externCtor
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
      red_safe externCtor
      split
      · split
        · exact CS.fin_ok CS.γ_unit
        · rename_i hno
          obtain ⟨ps, hps⟩ := retRegsC_some (regsClasses rss) 0 0 (by simp [regsClasses]; omega)
            (by simp [regsClasses]; omega)
          exact absurd (CS.single_mapM_eq (fun _ => rfl) rss h1) (hno _ _ hps)
      · contradiction
    · cases h
  -- gen_call_output (signature)
  · intro n; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨_, rfl, s, rfl, hs, hn⟩ := hw1
    red_safe externCtor
    obtain ⟨rss, hr, hl, h1⟩ := CS.foldOut retClass (sigRets s) #[] st
    refine CS.fin_ok ⟨_, rfl, ?_, ?_⟩ <;> rw [hr]
    · simpa using h1
    · rcases hn with rfl | rfl
      · exact .inl rfl
      · exact .inr (by simp [hl])
  -- gen_call_output (`try_call` signature)
  · intro n; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨_, rfl, s, rfl, hs, -⟩ := hw1
    red_safe externCtor
    obtain ⟨rss, hr, hl, h1⟩ := CS.foldOut retClass (sigRets s) #[] st
    refine CS.fin_ok ⟨_, rfl, ?_, .inl rfl⟩
    rw [hr]
    simpa using h1
  -- gen_call_args (signature)
  · intro n m; cintro; gl2; cok
    simp only [γ] at hw1 hw2
    obtain ⟨_, rfl, s, rfl, hs, -⟩ := hw1
    obtain ⟨rss, rfl, h1, -⟩ := hw2
    obtain ⟨⟨locs, k⟩, hl⟩ := hs.1
    red_safe externCtor
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
    red_safe externCtor
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
      red_safe externCtor
      split
      · split
        · exact CS.fin_ok ⟨_, rfl, _, rfl⟩
        · rename_i hno
          obtain ⟨ps, hps⟩ := retRegsC_some (regsClasses rss) 0 0 (by simp [regsClasses]; omega)
            (by simp [regsClasses]; omega)
          exact absurd (CS.single_mapM_eq (fun _ => rfl) rss h1) (hno _ _ hps)
      · contradiction
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
      red_safe externCtor
      split
      · split
        · exact CS.fin_ok ⟨_, rfl, _, rfl⟩
        · rename_i hno
          obtain ⟨ps, hps⟩ := retRegsC_some (regsClasses rss) 0 0 (by simp [regsClasses]; omega)
            (by simp [regsClasses]; omega)
          exact absurd (CS.single_mapM_eq (fun _ => rfl) rss h1) (hno _ _ hps)
      · contradiction
    · cases h
  -- try_call_none
  · intro _; cintro; gl0; cok
    red_safe externCtor
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
      red_safe externCtor
      split
      · exact CS.fin_ok ⟨_, rfl, _, rfl⟩
      · rename_i he
        simp [tryInfoOf, hlen] at he
    · cases h
  -- gen_try_call_rets
  · intro n; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨_, rfl, s, rfl, hs, hlen⟩ := hw1
    red_safe externCtor
    obtain ⟨ps, hps⟩ := retRegsC_some ((sigRets s).map retClass) 0 0 (by simpa using hs.2)
      (by simpa using hs.2)
    rw [hps]
    dsimp only
    split
    · rename_i hne
      simp [retRegsC_len hps, hlen] at hne
    · exact CS.fin_ok ⟨_, rfl, _, rfl⟩
  -- gen_call_info (signature)
  · intro n1 n2 n3 n4 x1 x2; cintro; gl6; cok
    simp only [γ] at hw1 hw2 hw3 hw4
    obtain ⟨_, rfl, s, rfl, hs, -⟩ := hw1
    obtain ⟨_, rfl, nm, rfl⟩ := hw2
    obtain ⟨_, rfl, us, rfl⟩ := hw3
    obtain ⟨_, rfl, ds, rfl⟩ := hw4
    obtain ⟨⟨locs, k⟩, hl⟩ := hs.1
    red_safe externCtor
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
    red_safe externCtor
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
      red_safe externCtor
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
      red_safe externCtor
      rw [hl]
      exact CS.fin_ok ⟨_, rfl, _, rfl⟩
    · cases h
  -- use_fp16
  · intro _; cintro; gl0; cok
    red_safe externCtor
    exact CS.fin_ok ⟨_, rfl, .inr rfl⟩
  -- is_pic
  · intro _; cintro; gl0; cok
    red_safe externCtor
    exact CS.fin_ok ⟨_, rfl, .inr rfl⟩
  -- move_wide_const_from_u64
  · intro tA x; cintro; gl2
    obtain ⟨t, i, rfl, rfl, hok, hfail⟩ := CS.exactTest_sh h hw1 hw2
    red_safe externCtor
    cases hm : MoveWideConst.ofNat? (if t.bits < 64 then u64 i % 2 ^ t.bits else u64 i) with
    | none => exact CS.fin_fail (hfail (by simp [hm]))
    | some c =>
      obtain rfl := hok (by simp [hm])
      exact CS.fin_ok ⟨_, rfl, _, rfl⟩
  -- move_wide_const_from_inverted_u64
  · intro tA x; cintro; gl2
    obtain ⟨t, i, rfl, rfl, hok, hfail⟩ := CS.exactTest_sh h hw1 hw2
    red_safe externCtor
    cases hm : MoveWideConst.ofNat? (if t.bits < 64 then (2 ^ 64 - 1 - u64 i) % 2 ^ t.bits
        else 2 ^ 64 - 1 - u64 i) with
    | none => exact CS.fin_fail (hfail (by simp [hm]))
    | some c =>
      obtain rfl := hok (by simp [hm])
      exact CS.fin_ok ⟨_, rfl, _, rfl⟩
  -- imm_logic_from_u64
  · intro tA x; cintro; gl2
    obtain ⟨t, i, rfl, rfl, hok, hfail⟩ := CS.exactTest_sh h hw1 hw2
    red_safe externCtor
    split
    · rename_i hc
      cases hm : ImmLogic.ofNat? (u64 i) (.ofBits t.bits) with
      | none => exact CS.fin_fail (hfail (by simp [hm]))
      | some c =>
        obtain rfl := hok (by simp [hc, hm])
        exact CS.fin_ok ⟨_, rfl, _, rfl⟩
    · rename_i hc
      exact CS.fin_fail (hfail (by simp [Bool.eq_false_iff.2 hc]))
  -- imm_size_from_type
  · intro tA; cintro; gl1
    split at h
    · rename_i ts hts
      obtain ⟨t, ht, rfl⟩ := CS.tysOf_sh hts hw1
      red_safe externCtor
      split at h
      · rename_i he
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hn : (t == .int 32 || t == .int 64) = false := by
          rw [Bool.eq_false_iff]
          intro hc
          have : t ∈ ts.filter (fun t => t == .int 32 || t == .int 64) := List.mem_filter.2 ⟨ht, hc⟩
          rw [List.isEmpty_iff] at he
          rw [he] at this
          cases this
        simp only [Bool.or_eq_false_iff] at hn
        simp only [hn.1, hn.2, Bool.false_eq_true, ↓reduceIte]
        exact CS.fin_fail rfl
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        split
        · exact CS.fin_ok (CS.γ_intAny _)
        · split
          · exact CS.fin_ok (CS.γ_intAny _)
          · rename_i h1 h2
            refine CS.fin_fail ?_
            rw [Bool.eq_false_iff]
            intro hall
            have := List.all_eq_true.1 hall t ht
            simp only [Bool.or_eq_true] at this
            rcases this with this | this
            · exact h1 this
            · exact h2 this
    · cases h
  -- imm_logic_from_imm64
  · intro tA x; cintro; gl2
    obtain ⟨t, i, rfl, rfl, hok, hfail⟩ := CS.exactTest_sh h hw1 hw2
    red_safe externCtor
    generalize (if t.bits < 32 then CTy.int 32 else t) = T at hok hfail ⊢
    split
    · rename_i hc
      cases hm : ImmLogic.ofNat? (u64 i) (.ofBits T.bits) with
      | none => exact CS.fin_fail (hfail (by simp [hm]))
      | some c =>
        obtain rfl := hok (by simp [hc, hm])
        exact CS.fin_ok ⟨_, rfl, _, rfl⟩
    · rename_i hc
      exact CS.fin_fail (hfail (by simp [Bool.eq_false_iff.2 hc]))
  -- imm_shift_from_imm64
  · intro tA x; cintro; gl2
    split at h
    · rename_i hx
      split at h
      · rename_i ts hts
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨t, ht, rfl⟩ := CS.tysOf_sh hts hw1
        obtain ⟨i, rfl⟩ := CS.int_sh hx hw2
        red_safe externCtor
        split
        · rename_i hlt
          exact CS.fin_ok ⟨_, rfl, _, rfl, hlt⟩
        · rename_i hge
          refine CS.fin_fail ?_
          rw [Bool.eq_false_iff]
          intro hall
          have := List.all_eq_true.1 hall t ht
          simp only [decide_eq_true_eq] at this
          exact hge (Nat.lt_of_le_of_lt Nat.and_le_right (by omega))
      · cases h
    · cases h
  -- imm_shift_from_u8
  · intro x; cintro; gl1
    split at h
    · rename_i n hn
      split at h
      · rename_i hc; cok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨i, rfl, hi⟩ := CS.hiOf_sh hn hw1
        red_safe externCtor
        rw [CS.ite_t (by omega)]
        exact CS.fin_ok ⟨_, rfl, _, rfl, by omega⟩
      · cases h
    · cases h
  -- u8_into_uimm5
  · intro x; cintro; gl1
    split at h
    · rename_i n hn
      split at h
      · rename_i hc; cok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨i, rfl, hi⟩ := CS.hiOf_sh hn hw1
        red_safe externCtor
        rw [CS.ite_t (by omega)]
        exact CS.fin_ok ⟨_, rfl, _, rfl⟩
      · cases h
    · cases h
  -- u8_into_imm12
  · intro x; cintro; gl1
    split at h
    · rename_i l u hl hu
      split at h
      · rename_i hc; cok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨i, rfl, hli⟩ := CS.loOf_sh hl hw1
        obtain ⟨j, hj, hiu⟩ := CS.hiOf_sh hu hw1
        simp only [V.int.injEq] at hj
        subst hj
        red_safe externCtor
        rw [CS.imm12_small (by omega)]
        exact CS.fin_ok ⟨_, rfl, _, rfl⟩
      · cases h
    · cases h
  -- u64_into_imm_logic
  · intro tA x; cintro; gl2
    simp only [tyIntAll, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ts, hts, n, hn, h⟩ := h
    split at h
    · rename_i hall; cok
      obtain ⟨t, ht, rfl⟩ := CS.tysOf_sh hts hw1
      have := CS.intOf_sh hn hw2
      subst this
      have hok := List.all_eq_true.1 hall t ht
      simp only [Bool.and_eq_true] at hok
      red_safe externCtor
      rw [CS.ite_t hok.1]
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hok.2
      rw [hc]
      exact CS.fin_ok ⟨_, rfl, _, rfl⟩
    · cases h
  -- branch_target
  · intro _; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨l, rfl⟩ := hw1
    red_safe externCtor
    exact CS.fin_ok ⟨_, rfl⟩
  -- targets_jt_space
  · intro lo n; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨ls, rfl, -⟩ := hw1
    red_safe externCtor
    exact CS.fin_ok ⟨_, rfl, fun l hl => by simp at hl; omega, by simp⟩
  -- lshl_from_imm64
  · intro tA x; cintro; gl2
    obtain ⟨t, i, rfl, rfl, hok, hfail⟩ := CS.exactTest_sh h hw1 hw2
    red_safe externCtor
    cases hs : shiftImm? (u64 i) with
    | none => exact CS.fin_fail (hfail (by simp [hs]))
    | some s =>
      dsimp only
      by_cases hb : t.bits ≤ 255
      · obtain rfl := hok (by simp [hs, hb])
        rw [CS.ite_t hb]
        exact CS.fin_ok ⟨_, rfl, _, rfl⟩
      · rw [CS.ite_f hb]
        exact CS.fin_fail (hfail (by simp [hs, hb]))
  -- ashr_from_u64
  · intro tA x; cintro; gl2
    obtain ⟨t, i, rfl, rfl, hok, hfail⟩ := CS.exactTest_sh h hw1 hw2
    red_safe externCtor
    cases hs : shiftImm? i.toNat with
    | none => exact CS.fin_fail (hfail (by simp [hs]))
    | some s =>
      dsimp only
      by_cases hb : t.bits ≤ 255
      · obtain rfl := hok (by simp [hs, hb])
        rw [CS.ite_t hb]
        exact CS.fin_ok ⟨_, rfl, _, rfl⟩
      · rw [CS.ite_f hb]
        exact CS.fin_fail (hfail (by simp [hs, hb]))
  -- put_extended_in_reg
  · intro n; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨_, rfl, x, e, rfl, hx⟩ := hw1
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hx
    red_safe externCtor
    rw [hr]
    exact CS.fin_ok ⟨_, rfl⟩
  -- get_extended_op
  · intro n; cintro; gl1; cok
    simp only [γ] at hw1
    obtain ⟨_, rfl, x, e, rfl, -⟩ := hw1
    red_safe externCtor
    exact CS.fin_ok (CS.γ_enumAlts (List.mem_map_of_mem (by cases e <;> simp [ExtendOp.all])))
  -- nzcv
  · intro pa pb pc pd; cintro; gl4
    split at h
    · rename_i hc; cok
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
      obtain ⟨_, rfl⟩ := CS.bool_sh h1 hw1
      obtain ⟨_, rfl⟩ := CS.bool_sh h2 hw2
      obtain ⟨_, rfl⟩ := CS.bool_sh h3 hw3
      obtain ⟨_, rfl⟩ := CS.bool_sh h4 hw4
      red_safe externCtor
      exact CS.fin_ok ⟨_, rfl, _, rfl⟩
    · cases h
  -- cond_br_zero
  · intro r s; cintro; gl2; cok
    red_safe externCtor
    exact CS.fin_ok ⟨_, rfl, hw1, hw2, trivial⟩
  -- cond_br_not_zero
  · intro r s; cintro; gl2; cok
    red_safe externCtor
    exact CS.fin_ok ⟨_, rfl, hw1, hw2, trivial⟩
  -- cond_br_cond
  · intro c; cintro; gl1; cok
    red_safe externCtor
    exact CS.fin_ok ⟨_, rfl, hw1, trivial⟩
  -- zero_reg
  · intro _; cintro; gl0; cok
    red_safe externCtor
    exact CS.fin_ok ⟨_, rfl⟩
  -- writable_zero_reg
  · intro _; cintro; gl0; cok
    red_safe externCtor
    exact CS.fin_ok ⟨_, rfl⟩
  -- a64_extr_imm
  · intro tA n; cintro; gl2
    split at h
    · rename_i hc; cok
      obtain ⟨t, ht, rfl⟩ := CS.tysAll_sh hc hw1
      simp only [γ] at hw2
      obtain ⟨_, rfl, s, rfl, -⟩ := hw2
      red_safe externCtor
      split
      · exact CS.fin_ok ⟨_, rfl, _, rfl⟩
      · split
        · exact CS.fin_ok ⟨_, rfl, _, rfl⟩
        · rename_i h1 h2
          simp only [Bool.or_eq_true] at ht
          rcases ht with ht | ht
          · exact absurd ht h1
          · exact absurd ht h2
    · cases h
  -- load_constant_full
  · intro tA e sz x; cintro; gl4
    split at h
    · rename_i hc; cok
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
      obtain ⟨_, t, -, -, rfl⟩ := CS.ty_sh h1 hw1
      obtain ⟨k, y, rfl, -⟩ := CS.enum_sh h2 hw2
      obtain ⟨sk, size, rfl, hsz⟩ := CS.enum_sh h3 hw3
      obtain ⟨i, rfl⟩ := CS.int_sh h4 hw4
      red_safe externCtor
      have e2 : (V.data tyOperandSize sk []).size? = some size := by
        simp [V.size?, V.enum?, V.enumOf?, hsz]
      rw [e2]
      exact CS.fin_ok ⟨_, rfl⟩
    · cases h
  -- uimm12_scaled_from_i64
  · intro x tA; cintro; gl2
    obtain ⟨t, i, rfl, rfl, hok, hfail⟩ := CS.exactTest_sh h hw2 hw1
    red_safe externCtor
    cases hu : uimm12Scaled? i t.bytes with
    | none => exact CS.fin_fail (hfail (by simp [hu]))
    | some c =>
      obtain rfl := hok (by simp [hu])
      exact CS.fin_ok ⟨_, rfl, _, rfl⟩
  -- uimm12_scaled_nonzero_from_i64
  · intro x tA; cintro; gl2
    obtain ⟨t, i, rfl, rfl, hok, hfail⟩ := CS.exactTest_sh h hw2 hw1
    red_safe externCtor
    split
    · rename_i hz
      exact CS.fin_fail (hfail (by simp [beq_iff_eq.1 hz]))
    · rename_i hz
      have hz' : i ≠ 0 := fun e => hz (beq_iff_eq.2 e)
      cases hu : uimm12Scaled? i t.bytes with
      | none => exact CS.fin_fail (hfail (by simp [hu]))
      | some c =>
        obtain rfl := hok (by simp [hu, hz'])
        exact CS.fin_ok ⟨_, rfl, _, rfl⟩
  -- simm9_from_i64
  · intro x; cintro; gl1
    split at h
    · rename_i hx
      obtain ⟨i, rfl⟩ := CS.int_sh hx hw1
      red_safe externCtor
      split at h
      · rename_i v hv
        have := CS.intOf_sh hv hw1
        simp only [V.int.injEq] at this
        subst this
        split at h
        · rename_i hs; cok
          obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hs
          rw [hc]
          exact CS.fin_ok ⟨_, rfl, _, rfl⟩
        · rename_i hs
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases hc : simm9? i with
          | none => exact CS.fin_fail rfl
          | some c => simp [hc] at hs
      · cres
        cases hc : simm9? i with
        | none => exact CS.fin_fail rfl
        | some c => exact CS.fin_ok ⟨_, rfl, _, rfl⟩
    · cases h
  -- cond_code
  · intro cc; cintro; gl1
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, cOk, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨ks, hks, cs, hcs, rfl, rfl⟩ := h
    obtain ⟨k, hk, rfl⟩ := CS.enumsOf_sound hks hw1
    obtain ⟨c, hc, hcm⟩ := CS.mapM_some_mem hcs k hk
    red_safe externCtor
    have e : ((V.data tyIntCC k []).intcc? >>= condOfIntCC) = some c := by
      simp [V.intcc?, V.enum?, V.enumOf?, hc]
    rw [e]
    exact CS.fin_ok (CS.γ_enumAlts (List.mem_map_of_mem hcm))
  -- invert_cond
  · intro c; cintro; gl1
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, cOk, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨ks, hks, cs, hcs, rfl, rfl⟩ := h
    obtain ⟨k, hk, rfl⟩ := CS.enumsOf_sound hks hw1
    obtain ⟨cd, hcd, hcm⟩ := CS.mapM_some_mem hcs k hk
    red_safe externCtor
    have e : (V.data tyCond k []).cond? = some cd := by
      simp [V.cond?, V.enum?, V.enumOf?, hcd]
    rw [e]
    exact CS.fin_ok (CS.γ_enumAlts (List.mem_map_of_mem (f := fun c : Cond => c.invert.idx) hcm))
  -- shift_masked_imm
  · intro tA x; cintro; gl2
    split at h
    · rename_i hc; cok
      simp only [Bool.and_eq_true] at hc
      obtain ⟨_, t, -, -, rfl⟩ := CS.ty_sh hc.1 hw1
      obtain ⟨i, rfl⟩ := CS.int_sh hc.2 hw2
      red_safe externCtor
      exact CS.fin_ok (CS.γ_intAny _)
    · cases h
  -- shift_mask
  · intro tA; cintro; gl1
    split at h
    · rename_i hc; cok
      obtain ⟨t, ht, rfl⟩ := CS.tysAll_sh hc hw1
      obtain ⟨c, hcl⟩ := Option.isSome_iff_exists.1 ht
      red_safe externCtor
      rw [hcl]
      exact CS.fin_ok ⟨_, rfl, _, rfl⟩
    · cases h
  -- bfm_immr
  · intro tA pa pb; cintro; gl3
    split at h
    · rename_i hc; cok
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨h1, h2⟩, h3⟩ := hc
      obtain ⟨_, t, -, -, rfl⟩ := CS.ty_sh h1 hw1
      obtain ⟨i, rfl⟩ := CS.int_sh h2 hw2
      obtain ⟨j, rfl⟩ := CS.int_sh h3 hw3
      red_safe externCtor
      exact CS.fin_ok ⟨_, rfl, _, rfl⟩
    · cases h
  -- bfm_imms
  · intro tA pa pb; cintro; gl3
    split at h
    · rename_i hc; cok
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨h1, h2⟩, h3⟩ := hc
      obtain ⟨_, t, -, -, rfl⟩ := CS.ty_sh h1 hw1
      obtain ⟨i, rfl⟩ := CS.int_sh h2 hw2
      obtain ⟨j, rfl⟩ := CS.int_sh h3 hw3
      red_safe externCtor
      exact CS.fin_ok ⟨_, rfl, _, rfl⟩
    · cases h
  -- negate_imm_shift
  · intro tA n; cintro; gl2
    split at h
    · rename_i hc; cok
      obtain ⟨t, ht, rfl⟩ := CS.tysAll_sh hc hw1
      simp only [decide_eq_true_eq] at ht
      simp only [γ] at hw2
      obtain ⟨_, rfl, s, rfl, -⟩ := hw2
      red_safe externCtor
      exact CS.fin_ok ⟨_, rfl, _, rfl, Nat.lt_of_le_of_lt Nat.and_le_right (by omega)⟩
    · cases h
  -- rotr_mask
  · intro tA; cintro; gl1
    split at h
    · rename_i hc; cok
      obtain ⟨t, ht, rfl⟩ := CS.tysAll_sh hc hw1
      obtain ⟨c, hcl⟩ := Option.isSome_iff_exists.1 ht
      red_safe externCtor
      rw [hcl]
      exact CS.fin_ok ⟨_, rfl, _, rfl⟩
    · cases h
  -- rotr_opposite_amount
  · intro tA n; cintro; gl2
    split at h
    · rename_i hc; cok
      obtain ⟨t, ht, rfl⟩ := CS.tysAll_sh hc hw1
      simp only [decide_eq_true_eq] at ht
      simp only [γ] at hw2
      obtain ⟨_, rfl, s, rfl, -⟩ := hw2
      red_safe externCtor
      rw [CS.ite_t (by omega)]
      exact CS.fin_ok ⟨_, rfl, _, rfl, by omega⟩
    · cases h
  -- test_and_compare_bit_const
  · intro tA x; cintro; gl2
    split at h
    · rename_i hc; cres
      simp only [Bool.and_eq_true] at hc
      obtain ⟨_, t, -, -, rfl⟩ := CS.ty_sh hc.1 hw1
      obtain ⟨i, rfl⟩ := CS.int_sh hc.2 hw2
      red_safe externCtor
      split
      · rename_i bit hb
        have hm : bit ∈ (List.range 64).filter (fun b => (u64 i).testBit b) := by
          rw [hb]; exact List.mem_singleton_self _
        have := List.mem_range.1 (List.mem_filter.1 hm).1
        split
        · exact CS.fin_ok (CS.γ_range (by omega) (by omega))
        · exact CS.fin_fail rfl
      · exact CS.fin_fail rfl
    · cases h
  -- i32_checked_add
  · intro pa pb; cintro; gl2
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨i, rfl⟩ := CS.int_sh hc.1 hw1
      obtain ⟨j, rfl⟩ := CS.int_sh hc.2 hw2
      red_safe externCtor
      split at h
      · rename_i x y hx hy
        have e1 := CS.intOf_sh hx hw1
        have e2 := CS.intOf_sh hy hw2
        simp only [V.int.injEq] at e1 e2
        subst e1 e2
        split at h
        · rename_i hr; cok
          rw [CS.ite_t hr]
          exact CS.fin_ok (CS.γ_exact _)
        · rename_i hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [CS.ite_f hr]
          exact CS.fin_fail rfl
      · cres
        split
        · exact CS.fin_ok (CS.γ_intAny _)
        · exact CS.fin_fail rfl
    · cases h
  -- i64_checked_neg
  · intro pa; cintro; gl1
    obtain ⟨i, rfl, hok, hnone⟩ := CS.exactTest1_sh h hw1
    red_safe externCtor
    split
    · rename_i hc
      exact CS.fin_fail (hnone (ite_eq_left hc))
    · rename_i hc
      exact CS.fin_ok (hok _ (ite_eq_right hc))
  -- u64_eq
  · intro pa pb; cintro; gl2
    obtain ⟨i, j, rfl, rfl, ha⟩ := CS.boolOp2_sh h hw1 hw2
    red_safe externCtor
    exact CS.fin_ok ha
  -- u64_gt
  · intro pa pb; cintro; gl2
    obtain ⟨i, j, rfl, rfl, ha⟩ := CS.boolOp2_sh h hw1 hw2
    red_safe externCtor
    exact CS.fin_ok ha
  -- u64_wrapping_add
  · intro pa pb; cintro; gl2
    obtain ⟨i, j, rfl, rfl, ha⟩ := CS.intOp2_sh h hw1 hw2
    red_safe externCtor
    exact CS.fin_ok ha
  -- u64_wrapping_sub
  · intro pa pb; cintro; gl2
    obtain ⟨i, j, rfl, rfl, ha⟩ := CS.intOp2_sh h hw1 hw2
    red_safe externCtor
    exact CS.fin_ok ha
  -- u64_wrapping_shl
  · intro pa pb; cintro; gl2
    obtain ⟨i, j, rfl, rfl, ha⟩ := CS.intOp2_sh h hw1 hw2
    red_safe externCtor
    exact CS.fin_ok ha
  -- u64_is_odd
  · intro pa; cintro; gl1
    split at h
    · rename_i hc; cok
      obtain ⟨i, rfl⟩ := CS.int_sh hc hw1
      red_safe externCtor
      refine CS.fin_ok ⟨_, rfl, ?_⟩
      cases hx : pa.intOf with
      | none => exact .inl rfl
      | some v =>
        have := CS.intOf_sh hx hw1
        simp only [V.int.injEq] at this
        subst this
        exact .inr rfl
    · cases h
  -- u8_into_u32
  · intro pa; cintro; gl1
    obtain ⟨i, rfl, ha⟩ := CS.intOp1_sh h hw1
    red_safe externCtor
    exact CS.fin_ok ha
  -- u8_into_u64
  · intro pa; cintro; gl1
    obtain ⟨i, rfl, ha⟩ := CS.intOp1_sh h hw1
    red_safe externCtor
    exact CS.fin_ok ha
  -- u16_into_u64
  · intro pa; cintro; gl1
    obtain ⟨i, rfl, ha⟩ := CS.intOp1_sh h hw1
    red_safe externCtor
    exact CS.fin_ok ha
  -- i32_into_i64
  · intro pa; cintro; gl1
    obtain ⟨i, rfl, ha⟩ := CS.intOp1_sh h hw1
    red_safe externCtor
    exact CS.fin_ok ha
  -- u32_into_u64
  · intro pa; cintro; gl1
    obtain ⟨i, rfl, ha⟩ := CS.intOp1_sh h hw1
    red_safe externCtor
    exact CS.fin_ok ha
  -- i64_cast_unsigned
  · intro pa; cintro; gl1
    obtain ⟨i, rfl, ha⟩ := CS.intOp1_sh h hw1
    red_safe externCtor
    exact CS.fin_ok ha
  -- value_array_2
  · intro pa pb; cintro; gl2
    split at h
    · rename_i hc; cok
      simp only [Bool.and_eq_true] at hc
      obtain ⟨n1, t1, rfl, -⟩ := CS.val_sh hc.1 hw1
      obtain ⟨n2, t2, rfl, -⟩ := CS.val_sh hc.2 hw2
      red_safe externCtor
      exact CS.fin_ok ⟨[n1, n2], rfl, hw1, hw2, trivial⟩
    · cases h
  -- value_array_3
  · intro pa pb pc; cintro; gl3
    split at h
    · rename_i hc; cok
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨h1, h2⟩, h3⟩ := hc
      obtain ⟨n1, t1, rfl, -⟩ := CS.val_sh h1 hw1
      obtain ⟨n2, t2, rfl, -⟩ := CS.val_sh h2 hw2
      obtain ⟨n3, t3, rfl, -⟩ := CS.val_sh h3 hw3
      red_safe externCtor
      exact CS.fin_ok ⟨[n1, n2, n3], rfl, hw1, hw2, hw3, trivial⟩
    · cases h
  -- block_array_2
  · intro na nb; cintro; gl2; cok
    simp only [γ] at hw1 hw2
    obtain ⟨bs1, rfl, h1⟩ := hw1
    obtain ⟨bs2, rfl, h2⟩ := hw2
    red_safe externCtor
    exact CS.fin_ok ⟨_, rfl, by simp [h1, h2]⟩
  -- no other alternative
  · intro _ _ _ _ h
    cases h

/-- **The extern constructors' transfer function is sound** (`Model.ctor`): when `actor` gives
a result for a call on abstract arguments, the call `externCtor ctx term vs st` on values they
describe either succeeds with a value the result describes, or fails and `actor` did not promise
success (it never reaches an `unmodeled` case). -/
theorem actor_sound (hP : PInv f ctx) (term : Term) (as : List PA) (a : PA) (must : Bool)
    (vs : List V) (st : LState)
    (h : actor term.id as = some (a, must)) (hv : γL f ctx as vs) :
    (∃ w st', externCtor ctx term vs st = .ok (w, st') ∧ γ f ctx a w) ∨
      (externCtor ctx term vs st = .fail ∧ must = false) := by
  cases hp : tyPred term.id with
  | none => exact actor_none_sound hP term.id as hp a must h term vs st rfl hv
  | some pr =>
    unfold actor at h
    rw [hp] at h
    try dsimp only at h
    split at h
    · rename_i ts
      obtain ⟨w1, vs, rfl, hw1, hvs⟩ := CS.γL_cons hv
      obtain rfl := CS.γL_nil hvs
      simp only [γ] at hw1
      obtain ⟨t, ht, rfl⟩ := hw1
      have hE : externCtor ctx term [.ty t] st =
          if pr t = true then .ok (.ty t, st) else .fail := by
        unfold externCtor
        rw [hp]
      rw [hE]
      try dsimp only at h
      split at h
      · rename_i he
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hn : pr t = false := by
          rw [Bool.eq_false_iff]
          intro hc
          have : t ∈ ts.filter pr := List.mem_filter.2 ⟨ht, hc⟩
          rw [List.isEmpty_iff] at he
          rw [he] at this
          cases this
        rw [CS.ite_f (by simp [hn])]
        exact .inr ⟨rfl, rfl⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        split
        · rename_i hc
          exact .inl ⟨_, _, rfl, t, List.mem_filter.2 ⟨ht, hc⟩, rfl⟩
        · rename_i hc
          refine .inr ⟨rfl, ?_⟩
          rw [Bool.eq_false_iff]
          intro hall
          exact hc (List.all_eq_true.1 hall t ht)
    · cases h

end Backend.Proof.Prg
