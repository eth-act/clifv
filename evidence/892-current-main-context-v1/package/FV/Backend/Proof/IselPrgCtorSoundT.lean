import FV.Backend.Proof.IselPrgExtT
import FV.Backend.Proof.IselPrgCtorNoneT

/-!
# Progress of the ISLE lowering over the typed scope: `actorT` is sound

`actorT_sound` (the `ctor` field of `Model` for `actorT`, under `PInvT`): whenever `actorT`
(`IselPrgExtT`) gives a result for a constructor call on abstract arguments, the concrete call
`externCtor ctx term vs st` on values those arguments describe either succeeds with a value the
result describes, or fails and `actorT` did not promise success.

* `emit`: `ofvOkT_sound`, `MInst.ofV` decodes every value `ofvOkT` accepts: V7's `minstOk_sound`
  and `minstOkF_sound` for the float instructions;
* the float constants' immediates `asimd_mov_mod_imm_zero`, `asimd_fp_mod_imm_from_u64`;
* the type predicates and the other constructors: V7's proofs (`actor_none_soundT`).
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64 PA

gen_match_split Backend.Proof.Prg.CS.minstOkF_split Backend.Proof.Prg.minstOkF.match_1

variable {f : Clif.Function} {ctx : Ctx}

namespace CS

theorem op_fpModImm_acc {a : PA} {w : V} (h : isOp .fpModImm a = true) (hw : γ f ctx a w) :
    ∃ x, w.fpModImm? = some x := by
  obtain ⟨o, n, rfl, ho⟩ := op_sh h hw
  obtain ⟨x, rfl⟩ := ho
  exact ⟨x, rfl⟩

theorem op_movModImm_acc {a : PA} {w : V} (h : isOp .movModImm a = true) (hw : γ f ctx a w) :
    ∃ x, w.movModImm? = some x := by
  obtain ⟨o, n, rfl, ho⟩ := op_sh h hw
  obtain ⟨x, rfl⟩ := ho
  exact ⟨x, rfl⟩

end CS

set_option hygiene false in
/-- Three fields `w1 w2 w3` of `ws` (`hws`). -/
macro "ws3" : tactic => `(tactic| (
  obtain ⟨w1, ws, rfl, hw1, hws⟩ := CS.γL_cons hws
  obtain ⟨w2, ws, rfl, hw2, hws⟩ := CS.γL_cons hws
  obtain ⟨w3, ws, rfl, hw3, hws⟩ := CS.γL_cons hws))

set_option hygiene false in
/-- A load/store of a float register: register, address mode, flags. -/
macro "fpu_ls" : tactic => `(tactic| (
  intro p1 p2 p3 h ws hws
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  ws3
  obtain rfl := CS.γL_nil hws
  obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
  obtain ⟨_, e2⟩ := amodeOk_acc h2 hw2
  obtain ⟨_, e3⟩ := CS.op_memFlags_acc h3 hw3
  red_safe MInst.ofV
  simp only [e1, e2, e3] <;> rfl))

set_option hygiene false in
/-- A float conditional select: three registers and a condition. -/
macro "fpu_csel" : tactic => `(tactic| (
  intro p1 p2 p3 p4 h ws hws
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  ws3
  obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
  obtain rfl := CS.γL_nil hws
  obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
  obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
  obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
  obtain ⟨_, e4⟩ := CS.enum_acc h4 hw4 V.cond? (fun _ => rfl)
  red_safe MInst.ofV
  simp only [e1, e2, e3, e4] <;> rfl))

set_option hygiene false in
/-- An operation, a destination and a source (`FpuRound`, `FpuToInt`, `IntToFpu`). -/
macro "fpu_op_rr " acc:term : tactic => `(tactic| (
  intro p1 p2 p3 h ws hws
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  ws3
  obtain rfl := CS.γL_nil hws
  obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 $acc (fun _ => rfl)
  obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
  obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
  red_safe MInst.ofV
  simp only [e1, e2, e3] <;> rfl))

/-- **`minstOkF` is sound**: `MInst.ofV` decodes every value of the float variant `k` with
fields `fs` describe. -/
theorem minstOkF_sound {k : Nat} {fs : List PA} (h : minstOkF k fs = true) {ws : List V}
    (hws : γL f ctx fs ws) : (MInst.ofV (.data tyMInst k ws)).isSome = true := by
  revert ws
  revert h
  unfold minstOkF
  apply CS.minstOkF_split _ (fun k fs r => r = true → ∀ ws, γL f ctx fs ws →
    (MInst.ofV (.data tyMInst k ws)).isSome = true)
  -- FpuLoad32, FpuLoad64, FpuStore32, FpuStore64
  · fpu_ls
  · fpu_ls
  · fpu_ls
  · fpu_ls
  -- FpuCSel32, FpuCSel64
  · fpu_csel
  · fpu_csel
  -- FpuMoveFPImm
  · intro p1 p2 p3 h ws hws
    simp only [sSize, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    ws3
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.op_fpModImm_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.enum_acc h3 hw3 V.scalarSize? (fun _ => rfl)
    red_safe MInst.ofV
    simp only [e1, e2, e3] <;> rfl
  -- VecDupImm
  · intro p1 p2 p3 p4 h ws hws
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    ws3
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.reg_acc h1 hw1
    obtain ⟨_, e2⟩ := CS.op_movModImm_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.bool_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.enum_acc h4 hw4 V.vectorSize? (fun _ => rfl)
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4] <;> rfl
  -- FpuRR
  · intro p1 p2 p3 p4 h ws hws
    simp only [sSize, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    ws3
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.fpuOp1? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.scalarSize? (fun _ => rfl)
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4] <;> rfl
  -- FpuRRR
  · intro p1 p2 p3 p4 p5 h ws hws
    simp only [sSize, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    ws3
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.fpuOp2? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.scalarSize? (fun _ => rfl)
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.reg_acc h5 hw5
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5] <;> rfl
  -- FpuRRRR
  · intro p1 p2 p3 p4 p5 p6 h ws hws
    simp only [sSize, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    ws3
    obtain ⟨w4, ws, rfl, hw4, hws⟩ := CS.γL_cons hws
    obtain ⟨w5, ws, rfl, hw5, hws⟩ := CS.γL_cons hws
    obtain ⟨w6, ws, rfl, hw6, hws⟩ := CS.γL_cons hws
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.fpuOp3? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.enum_acc h2 hw2 V.scalarSize? (fun _ => rfl)
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    obtain ⟨_, e4⟩ := CS.reg_acc h4 hw4
    obtain ⟨_, e5⟩ := CS.reg_acc h5 hw5
    obtain ⟨_, e6⟩ := CS.reg_acc h6 hw6
    red_safe MInst.ofV
    simp only [e1, e2, e3, e4, e5, e6] <;> rfl
  -- FpuCmp
  · intro p1 p2 p3 h ws hws
    simp only [sSize, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    ws3
    obtain rfl := CS.γL_nil hws
    obtain ⟨_, e1⟩ := CS.enum_acc h1 hw1 V.scalarSize? (fun _ => rfl)
    obtain ⟨_, e2⟩ := CS.reg_acc h2 hw2
    obtain ⟨_, e3⟩ := CS.reg_acc h3 hw3
    red_safe MInst.ofV
    simp only [e1, e2, e3] <;> rfl
  -- FpuRound, FpuToInt, IntToFpu
  · fpu_op_rr V.fpuRoundMode?
  · fpu_op_rr V.fpuToIntOp?
  · fpu_op_rr V.intToFpuOp?
  · intro _ _ h; cases h

mutual
/-- `ofvOkT_sound`, by recursion on the abstract value. -/
theorem ofvOkT_sound' : ∀ {a : PA} {v : V}, ofvOkT a = true → γ f ctx a v →
    (MInst.ofV v).isSome = true
  | .bot, _, _, hv => by simp [γ] at hv
  | .alts as, v, h, hv => by
    simp only [ofvOkT] at h
    simp only [γ] at hv
    exact ofvOkTL_sound' h hv
  | .data t k fs, v, h, hv => by
    simp only [ofvOkT, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hm⟩ := h
    simp only [γ] at hv
    obtain ⟨ws, rfl, hws⟩ := hv
    rcases hm with hm | hm
    · exact minstOk_sound hm hws
    · exact minstOkF_sound hm hws
  | .any, _, h, _
  | .int _ _, _, h, _
  | .bool _, _, h, _
  | .ty _, _, h, _
  | .inst _ _, _, h, _
  | .val _, _, h, _
  | .vals _, _, h, _
  | .valsMin _, _, h, _
  | .reg, _, h, _
  | .regs _, _, h, _
  | .regsVec _, _, h, _
  | .label, _, h, _
  | .labels _ _, _, h, _
  | .blockCalls _, _, h, _
  | .idata, _, h, _
  | .op _ _, _, h, _ => by simp [ofvOkT] at h
/-- `ofvOkT_sound'` for alternatives. -/
theorem ofvOkTL_sound' : ∀ {as : List PA} {v : V}, ofvOkTL as = true → γAny f ctx as v →
    (MInst.ofV v).isSome = true
  | [], _, _, hv => by simp [γAny] at hv
  | a :: as, v, h, hv => by
    simp only [ofvOkTL, Bool.and_eq_true] at h
    simp only [γAny] at hv
    rcases hv with hv | hv
    · exact ofvOkT_sound' h.1 hv
    · exact ofvOkTL_sound' h.2 hv
end

/-- **`emit` decodes every instruction value `ofvOkT` accepts.** -/
theorem ofvOkT_sound {a : PA} {v : V} (h : ofvOkT a = true) (hv : γ f ctx a v) :
    (MInst.ofV v).isSome := ofvOkT_sound' h hv

/-- The alternatives of `actorT` past the type predicates are sound: the float ones here, the
others V7's (`actor_none_soundTB`). -/
theorem actorT_none_soundB (hP : PInvTB f ctx) (id : TermId) (as : List PA) (hp : tyPred id = none) :
    CS.ActP f ctx id as (actorT id as) := by
  unfold actorT
  rw [hp]
  dsimp only
  split
  -- emit
  · cintro; gl1
    split at h
    · rename_i hi; cok
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (ofvOkT_sound hi hw1)
      red_safe externCtor
      rw [hm]
      exact CS.fin_ok CS.γ_unit
    · cases h
  -- asimd_mov_mod_imm_zero
  · cintro; gl1
    split at h
    · rename_i hs; cok
      obtain ⟨sz, e1⟩ := CS.enum_acc hs hw1 V.scalarSize? (fun _ => rfl)
      red_safe externCtor
      rw [e1]
      exact CS.fin_ok (by simp [γ, OpOk])
    · cases h
  -- asimd_fp_mod_imm_from_u64
  · cintro; gl2
    split at h
    · rename_i hxs
      simp only [Bool.and_eq_true] at hxs
      cres
      obtain ⟨i, rfl⟩ := CS.int_sh hxs.1 hw1
      obtain ⟨sz, e2⟩ := CS.enum_acc hxs.2 hw2 V.scalarSize? (fun _ => rfl)
      red_safe externCtor
      rw [e2]
      cases hm : fpModImm? (u64 i) sz with
      | none => simp only [hm, Option.map_none]; exact CS.fin_fail rfl
      | some m => simp only [hm, Option.map_some]; exact CS.fin_ok (by simp [γ, OpOk])
    · cases h
  -- the others: V7's
  · exact actor_none_soundTB hP _ _ hp

/-- `actorT_none_soundB` under `PInvT`. -/
theorem actorT_none_sound (hP : PInvT f ctx) (id : TermId) (as : List PA) (hp : tyPred id = none) :
    CS.ActP f ctx id as (actorT id as) :=
  actorT_none_soundB hP.toB id as hp

/-- **The extern constructors' transfer function over a float-capable context is sound**
(`Model.ctor` for `actorT`). -/
theorem actorT_soundB (hP : PInvTB f ctx) (term : Term) (as : List PA) (a : PA) (must : Bool)
    (vs : List V) (st : LState)
    (h : actorT term.id as = some (a, must)) (hv : γL f ctx as vs) :
    (∃ w st', externCtor ctx term vs st = .ok (w, st') ∧ γ f ctx a w) ∨
      (externCtor ctx term vs st = .fail ∧ must = false) := by
  cases hp : tyPred term.id with
  | none => exact actorT_none_soundB hP term.id as hp a must h term vs st rfl hv
  | some pr =>
    unfold actorT at h
    rw [hp] at h
    dsimp only at h
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


/-- **The extern constructors' transfer function over the typed scope is sound**
(`Model.ctor` for `actorT`). -/
theorem actorT_sound (hP : PInvT f ctx) (term : Term) (as : List PA) (a : PA) (must : Bool)
    (vs : List V) (st : LState)
    (h : actorT term.id as = some (a, must)) (hv : γL f ctx as vs) :
    (∃ w st', externCtor ctx term vs st = .ok (w, st') ∧ γ f ctx a w) ∨
      (externCtor ctx term vs st = .fail ∧ must = false) :=
  actorT_soundB hP.toB term as a must vs st h hv

end Backend.Proof.Prg
