import FV.Backend.Proof.DefGenOracle
import FV.Backend.Proof.DefGenWrap
import FV.Backend.Proof.DefGenSound
import FV.Backend.Proof.KillDriver
import FV.Backend.Proof.IselFlowData
import FV.Backend.Proof.IselShpTotal
import FV.Backend.Proof.IselShpOracle

/-!
# Definedness of the ISLE runs: the model of the embedding (`DModel`)

`dModel`: the extern extractors (`aext`), the extern constructors (`actor`), the oracle terms
(`emit_side_effect`, `side_effect`: `aOracle`) and the constructor-tree terms (`wrapper`) of the
driver's semantics meet their transfers, for a context whose reached values and instructions
(`c.R`, `c.I`, `c.root`) are closed under the facts the extractors read (instruction data,
results, definitions, operands of definitions), whose value registers are the values' vregs, and
whose `try_call` registers are vregs.
-/

namespace Backend.Proof.DefGen

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Spill Backend.Proof.Kill
  Backend.Proof.DefRun Isle Isle.Aarch64 Isle.Interp

/-! ## The state invariant through emitted code -/

section State
variable {ctx : Ctx} {c : SC} {s0 : LState}

theorem DD_append {D : Nat → Prop} {ms1 ms2 : List MInst} :
    ∀ n, DD c (DD c D ms1) ms2 n → DD c D (ms1 ++ ms2) n := by
  intro n h
  rcases h with (h | ⟨h1, m, hm, h2⟩) | ⟨h1, m, hm, h2⟩
  · exact .inl h
  · exact .inr ⟨h1, m, List.mem_append_left _ hm, h2⟩
  · exact .inr ⟨h1, m, List.mem_append_right _ hm, h2⟩

/-- **Emitting `ms`**, each instruction reading vregs defined before it, keeps the invariant;
the fresh defs of `ms` are defined afterwards. -/
theorem isD_emit {s s' : LState} {ms : List MInst} (hI : IsD ctx c s0 s)
    (hv : s.nextVreg ≤ s'.nextVreg) (he : s'.emitted = s.emitted ++ ms.toArray)
    (hu : ∀ (k : Nat) m, ms[k]? = some m → ∀ u ∈ useVregs m,
      DD c (Dn ctx c s0 s) (ms.take k) u) :
    IsD ctx c s0 s' ∧ RsD s s' ∧ (∀ n, Dn ctx c s0 s n → Dn ctx c s0 s' n) ∧
      ∀ m ∈ ms, ∀ n ∈ defVregs m, c.lo ≤ n → Dn ctx c s0 s' n := by
  obtain ⟨⟨ms0, h0, hold⟩, hlo⟩ := hI
  have e' : s'.emitted = s0.emitted ++ (ms0 ++ ms).toArray := by rw [he, h0]; simp
  have hs : emittedSince s0 s = ms0 := emittedSince_of' h0
  have hs' : emittedSince s0 s' = ms0 ++ ms := emittedSince_of' e'
  refine ⟨⟨⟨ms0 ++ ms, e', fun k m hk u hu' => ?_⟩, by omega⟩, ⟨hv, ms, he⟩, fun n hn => ?_,
    fun m hm n hn hlo' => ?_⟩
  · by_cases hlt : k < ms0.length
    · rw [List.getElem?_append_left hlt] at hk
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact hold k m hk u hu'
    · have hge : ms0.length ≤ k := by omega
      rw [List.getElem?_append_right hge] at hk
      have := hu _ m hk u hu'
      unfold Dn at this
      rw [hs] at this
      rw [List.take_append, List.take_of_length_le hge]
      exact DD_append u this
  · unfold Dn at hn ⊢
    rw [hs] at hn
    rw [hs']
    rcases hn with h | ⟨h1, m, hm, h2⟩
    · exact .inl h
    · exact .inr ⟨h1, m, List.mem_append_left _ hm, h2⟩
  · unfold Dn
    rw [hs']
    exact .inr ⟨hlo', m, List.mem_append_right _ hm, hn⟩

/-- A step that emits nothing keeps the invariant and the defined vregs. -/
theorem isD_keep {s s' : LState} (hI : IsD ctx c s0 s) (hv : s.nextVreg ≤ s'.nextVreg)
    (he : s'.emitted = s.emitted) :
    IsD ctx c s0 s' ∧ RsD s s' ∧ ∀ n, Dn ctx c s0 s n → Dn ctx c s0 s' n := by
  obtain ⟨h1, h2, h3, -⟩ := isD_emit (ms := []) hI hv (by simp [he]) (fun k m h => by simp at h)
  exact ⟨h1, h2, h3⟩

end State

/-! ## Clean values -/

section Clean
variable {c : SC}

theorem Cl_of_atoms {b z : Bool} {D : Nat → Prop} {v : V} (hr : v.regsIn = [])
    (hv : ∀ n ∈ v.valsIn, c.R n) (hi : v.instsIn = []) : Cl c b z D v := by
  refine ⟨fun r h => ?_, hv, by simp [hi]⟩
  have := regsU_sub v r h
  rw [hr] at this
  cases this

end Clean

/-! ## Extern extractors -/

/-- The extractors that may succeed. -/
def ExtIds (x : TermId) (r : ExtResult (List V)) : Prop :=
  ∀ fs, r = .ok fs → (tyPred x).isSome = true ∨ x ∈ clean0Ext ∨ x ∈ valueExt ∨
    x = TId.inst_data_value ∨ x = TId.first_result

set_option maxHeartbeats 2000000 in
/-- **Only the grouped extern extractors succeed.** -/
theorem externExtract_ids (ctx : Ctx) (t : Term) (v : V) (st : LState) :
    ExtIds t.id (externExtract ctx t v st) := by
  unfold externExtract
  split
  · intro fs h
    split at h
    · rename_i hp _
      left
      rw [hp]
      rfl
    · cases h
  · intro fs h; cases h
  · apply externExtract_split _ (fun x _ r => ExtIds x r)
    all_goals
      intros
      unfold ExtIds
      intro fs h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals decide

section Ext
variable {ctx : Ctx} {c : SC}

/-- **The extern extractors' transfer is sound.** -/
theorem extOK
    (hroot : ∀ info, ctx.insts[c.root]? = some info → DataOk c.R info.data)
    (hinst : ∀ j info, c.I j → ctx.insts[j]? = some info →
      DataOk c.R info.data ∧ ∀ n ∈ info.results, c.R n)
    (hdefI : ∀ n j, c.R n → ctx.defInst? n = some j → c.I j)
    (hargs : ∀ n j info cl, c.R n → ctx.defInst? n = some j → ctx.insts[j]? = some info →
      info.clif = some cl → ∀ y ∈ Driver.instArgs cl, c.R y) :
    ExtOK c ctx := by
  intro term a e env D v s fs he hv h f hf
  have hs := externExtract_ok ctx term v s fs h
  have hid := externExtract_ids ctx term v s fs h
  unfold aext
  by_cases h1 : ((tyPred term.id).isSome || clean0Ext.contains term.id) = true
  · rw [if_pos h1]
    have h1' : (tyPred term.id).isSome = true ∨ term.id ∈ clean0Ext := by
      simpa [List.contains_iff_mem] using h1
    obtain ⟨r0, v0, i0, -⟩ := hs.c0 h1' f hf
    exact Cl_of_atoms r0 (by simp [v0]) i0
  rw [if_neg h1]
  by_cases h2 : (valueExt.contains term.id || term.id == TId.inst_data_value) = true
  · rw [if_pos h2]
    split
    · rename_i hfit
      obtain ⟨-, hvR, hvI⟩ := fitsCl_sound he F true true a hv hfit
      by_cases hx : term.id ∈ valueExt
      · obtain ⟨r0, -, hfv, hfi⟩ := hs.val hx f hf
        refine ⟨fun r hr => ?_, fun n hn => ?_, fun j hj => ?_⟩
        · have := regsU_sub f r hr
          rw [r0] at this
          cases this
        · rcases hfv n hn with hn | ⟨m, hm, j, info, cl, h1, h2, h3, h4⟩
          · exact hvR n hn
          · exact hargs m j info cl (hvR m hm) h1 h2 h3 n h4
        · obtain ⟨m, hm, hd⟩ := hfi j hj
          exact .inr (hdefI m j (hvR m hm) hd)
      · have hx' : term.id = TId.inst_data_value := by
          simp only [Bool.or_eq_true, List.contains_iff_mem, beq_iff_eq] at h2
          exact h2.resolve_left hx
        obtain ⟨i, info, rfl, hi, rfl⟩ := hs.idv hx'
        have hdat : DataOk c.R info.data := by
          rcases hvI i (by simp [V.instsIn]) with ⟨-, rfl⟩ | hI
          · exact hroot info hi
          · exact (hinst i info hI hi).1
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
        rcases hf with rfl | rfl
        · exact Cl_of_atoms rfl (by simp [V.valsIn]) rfl
        · exact Cl_of_atoms hdat.1 hdat.2.2.2 hdat.2.1
    · trivial
  rw [if_neg h2]
  by_cases h3 : (term.id == TId.first_result) = true
  · rw [if_pos h3]
    split
    · rename_i hfit
      obtain ⟨-, -, hvI⟩ := fitsCl_sound he F false true a hv hfit
      obtain ⟨i, info, r, rfl, hi, hr, rfl⟩ := hs.fr (by simpa using h3)
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
      subst hf
      have hI : c.I i := by
        rcases hvI i (by simp [V.instsIn]) with ⟨h, -⟩ | hI
        · cases h
        · exact hI
      have hrR := (hinst i info hI hi).2 r (List.mem_of_mem_head? hr)
      exact Cl_of_atoms rfl (by simp [V.valsIn, hrR]) rfl
    · trivial
  · exfalso
    rcases hid with h | h | h | h | h
    · exact h1 (by simp [h])
    · exact h1 (by simp [List.contains_iff_mem, h])
    · exact h2 (by simp [List.contains_iff_mem, h])
    · exact h2 (by simp [h])
    · exact h3 (by simp [h])

end Ext

/-! ## Extern constructors: what each one does -/

/-- The extern constructors `actor` treats specially (the others: `genericCl`). -/
def ctorSpecials : List TermId :=
  [TId.temp_writable_reg, TId.gen_call_output, TId.invalid_reg, TId.abi_dynamic_stackslot_addr,
   TId.writable_reg_to_reg, TId.value_reg, TId.value_regs, TId.zero_reg, TId.writable_zero_reg,
   TId.emit, TId.load_constant_full, TId.opportunistic_def, TId.put_in_reg, TId.put_in_regs,
   TId.put_in_regs_vec, TId.put_extended_in_reg, TId.abi_stackslot_addr, TId.gen_call_rets,
   TId.gen_try_call_rets, TId.gen_call_info, TId.gen_call_ind_info, TId.gen_return,
   TId.gen_call_args]

/-- `loadConstantFull`'s state (register `r`, state `s`, from `st0`): every instruction reads
fresh vregs an earlier one defines, and `r` is a fresh vreg one defines. -/
def LCD (st0 : LState) (r : Reg) (s : LState) : Prop :=
  st0.nextVreg ≤ s.nextVreg ∧ ∃ ms : List MInst, s.emitted = st0.emitted ++ ms.toArray ∧
    (∀ (k : Nat) m, ms[k]? = some m → ∀ u ∈ useVregs m,
      st0.nextVreg ≤ u ∧ ∃ m' ∈ ms.take k, u ∈ defVregs m') ∧
    ∃ n cl, r = .vreg n cl ∧ st0.nextVreg ≤ n ∧ ∃ m ∈ ms, n ∈ defVregs m

theorem defVregs_of {m : MInst} (hall : ∀ r ∈ useRegsK m ++ defRegsK m, ∃ n c, r = .vreg n c)
    {n : Nat} {c : RegClass} (h : Reg.vreg n c ∈ defRegsK m) : n ∈ defVregs m :=
  (operands_okRegs (fun r hr => .inl (hall r hr))).2 n c h

theorem lcd_step {st0 s : LState} {ms : List MInst} {m : MInst} (hle : st0.nextVreg ≤ s.nextVreg)
    (he : s.emitted = st0.emitted ++ ms.toArray)
    (hms : ∀ (k : Nat) m', ms[k]? = some m' → ∀ u ∈ useVregs m',
      st0.nextVreg ≤ u ∧ ∃ m'' ∈ ms.take k, u ∈ defVregs m'')
    (hu : ∀ u ∈ useVregs m, st0.nextVreg ≤ u ∧ ∃ m' ∈ ms, u ∈ defVregs m')
    (hd : s.nextVreg ∈ defVregs m) :
    LCD st0 (s.fresh .int).1 ((s.fresh .int).2.emit m) := by
  refine ⟨by simp [LState.fresh, LState.emit]; omega, ms ++ [m],
    by simp [LState.fresh, LState.emit, he], fun k m' hk u hu' => ?_,
    s.nextVreg, .int, rfl, hle, m, by simp, hd⟩
  by_cases hlt : k < ms.length
  · rw [List.getElem?_append_left hlt] at hk
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact hms k m' hk u hu'
  · have hge : ms.length ≤ k := by omega
    rw [List.getElem?_append_right hge] at hk
    rw [List.take_append, List.take_of_length_le hge]
    cases hj : k - ms.length with
    | zero =>
      rw [hj] at hk
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      obtain ⟨h1, m'', h2, h3⟩ := hu u hu'
      exact ⟨h1, m'', by simpa using h2, h3⟩
    | succ j =>
      rw [hj] at hk
      simp at hk

/-- **`loadConstantFull`**: a chain of fresh defs, each `movk` reading the previous one. -/
theorem loadConstantFull_d (bits : Nat) (se : Bool) (sz : OperandSize) (value : Nat)
    (st : LState) :
    LCD st (loadConstantFull bits se sz value st).1 (loadConstantFull bits se sz value st).2 := by
  unfold loadConstantFull
  dsimp only
  refine foldl_inv (fun x : Reg × LState × Nat => LCD st x.1 x.2.1) _ _ _ ?_ ?_
  · refine lcd_step (ms := []) (Nat.le_refl _) (by simp) (fun k m h => by simp at h)
      (fun u hu => ?_) (defVregs_of (c := .int) (by simp [useRegsK, defRegsK, MInst.uses,
        MInst.defs, pairUses, pairDefs, LState.fresh]) (by simp [defRegsK, MInst.defs,
        LState.fresh]))
    obtain ⟨c, hc⟩ := useVregs_mem hu
    simp [useRegsK, MInst.uses, pairUses] at hc
  · intro sh _ x hx
    refine ite_inv (I := fun x : Reg × LState × Nat => LCD st x.1 x.2.1) (fun _ => hx) fun _ => ?_
    refine ite_inv (I := fun x : Reg × LState × Nat => LCD st x.1 x.2.1) (fun _ => ?_) fun _ => hx
    obtain ⟨hle, ms, he, hms, n, cl, hrd, hn, m0, hm0, hd0⟩ := hx
    refine lcd_step (s := x.2.1) hle he hms (fun u hu => ?_) (defVregs_of (c := .int) ?_ ?_)
    · obtain ⟨c, hc⟩ := useVregs_mem hu
      simp only [useRegsK, MInst.uses, pairUses, List.append_nil, List.mem_singleton, hrd,
        Reg.vreg.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      exact ⟨hn, m0, hm0, hd0⟩
    · simp [useRegsK, defRegsK, MInst.uses, MInst.defs, pairUses, pairDefs, LState.fresh, hrd]
    · simp [defRegsK, MInst.defs, LState.fresh]

/-- `gen_call_output`: fresh registers, nothing emitted. -/
theorem callOutput_d {st : LState} {β : Type}
    (F : Array (List Reg) × LState → β → Array (List Reg) × LState) (l : List β)
    (hF : ∀ a b, F a b = (a.1.push [(a.2.fresh .int).1], (a.2.fresh .int).2)) :
    ((l.foldl F (#[], st)).2.emitted = st.emitted ∧
      st.nextVreg ≤ (l.foldl F (#[], st)).2.nextVreg) ∧
    ∀ r ∈ regsU (.regsVec (l.foldl F (#[], st)).1.toList), ∃ n cl, r = .vreg n cl ∧
      st.nextVreg ≤ n := by
  have := foldl_inv (fun a : Array (List Reg) × LState =>
      (∀ rs ∈ a.1.toList, ∀ r ∈ rs, ∃ n c, r = .vreg n c ∧ st.nextVreg ≤ n) ∧
      st.nextVreg ≤ a.2.nextVreg ∧ a.2.emitted = st.emitted)
    F l (#[], st) (by simp) (by
      intro b _ a ⟨h1, h2, h4⟩
      rw [hF]
      refine ⟨?_, by simp [LState.fresh]; omega, by simp [LState.fresh, h4]⟩
      intro rs hrs r hr
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hrs
      rcases hrs with hrs | rfl
      · exact h1 rs hrs r hr
      · simp only [List.mem_singleton] at hr
        subst hr
        exact ⟨a.2.nextVreg, .int, rfl, h2⟩)
  obtain ⟨h1, h2, h4⟩ := this
  refine ⟨⟨h4, h2⟩, fun r hr => ?_⟩
  simp only [regsU, List.mem_flatten] at hr
  obtain ⟨rs, hrs, hr⟩ := hr
  exact h1 rs hrs r hr

/-- What an instruction emitted from the arguments' registers reads. -/
def ArgUses (args : List V) (m : MInst) : Prop := ∀ u ∈ useVregs m, ∃ cl, Reg.vreg u cl ∈ regsUL args

/-- `gen_call_args`: register uses from the arguments, stores of the stack arguments. -/
theorem callArgs_d {args : List V} {st : LState}
    (F : Array (Reg × Reg) × LState → (ArgLoc × Reg) × Nat → Array (Reg × Reg) × LState)
    (l : List ((ArgLoc × Reg) × Nat))
    (hF : ∀ a b, F a b = match b.1.1 with
      | .reg p => (a.1.push (b.1.2, p), a.2)
      | .stack off => (a.1, a.2.emit (.store (storeOpOfBytes b.2) b.1.2 (.spOffset off) trustedFlags)))
    (hl : ∀ b ∈ l, b.1.2 ∈ regsUL args) :
    (l.foldl F (#[], st)).2.nextVreg = st.nextVreg ∧ ∃ ms : List MInst,
      (l.foldl F (#[], st)).2.emitted = st.emitted ++ ms.toArray ∧ (∀ m ∈ ms, ArgUses args m) ∧
      (∀ r ∈ regsU (.op (.callArgs (l.foldl F (#[], st)).1.toList)), r ∈ regsUL args) ∧
      (V.op (.callArgs (l.foldl F (#[], st)).1.toList)).valsIn = [] ∧
      (V.op (.callArgs (l.foldl F (#[], st)).1.toList)).instsIn = [] := by
  have := foldl_inv (fun a : Array (Reg × Reg) × LState =>
      (∀ q ∈ a.1.toList, q.1 ∈ regsUL args) ∧ a.2.nextVreg = st.nextVreg ∧
      ∃ ms : List MInst, a.2.emitted = st.emitted ++ ms.toArray ∧ ∀ m ∈ ms, ArgUses args m)
    F l (#[], st) ⟨by simp, rfl, [], by simp, by simp⟩ (by
      intro b hb a ⟨h1, h2, ms, h4, h5⟩
      rw [hF]
      split
      · rename_i p hbp
        refine ⟨?_, h2, ms, h4, h5⟩
        intro q hq
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact h1 q hq
        · exact hl b hb
      · rename_i off _
        refine ⟨h1, by simp [LState.emit, h2],
          ms ++ [MInst.store (storeOpOfBytes b.2) b.1.2 (.spOffset off) trustedFlags],
          by simp [LState.emit, h4], ?_⟩
        intro m hm
        rcases List.mem_append.mp hm with hm | hm
        · exact h5 m hm
        · simp only [List.mem_singleton] at hm
          subst hm
          intro u hu
          obtain ⟨c, hc⟩ := useVregs_mem hu
          simp only [useRegsK, MInst.uses, AMode.regs, pairUses, List.append_nil,
            List.mem_singleton] at hc
          exact ⟨c, hc ▸ hl b hb⟩)
  obtain ⟨h1, h2, ms, h4, h5⟩ := this
  refine ⟨h2, ms, h4, h5, fun r hr => ?_, rfl, rfl⟩
  simp only [regsU, opRegsU, List.mem_map] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  exact h1 q hq

/-- `gen_return`: a `Rets` of the argument registers. -/
theorem rets_d {rss : List (List Reg)} {rs ps : List Reg} {st : LState}
    (h : rss.mapM (fun | [r] => some r | _ => none) = some rs) :
    (st.emit (.rets (rs.zip ps))).nextVreg = st.nextVreg ∧ ∃ ms : List MInst,
      (st.emit (.rets (rs.zip ps))).emitted = st.emitted ++ ms.toArray ∧
      (∀ m ∈ ms, ArgUses [.regsVec rss] m) ∧ (∀ r ∈ regsU (.op .unit), r ∈ regsUL [.regsVec rss]) ∧
      (V.op .unit).valsIn = [] ∧ (V.op .unit).instsIn = [] := by
  refine ⟨rfl, [.rets (rs.zip ps)], by simp [LState.emit], fun m hm => ?_,
    fun r hr => by simp [regsU, opRegsU] at hr, rfl, rfl⟩
  simp only [List.mem_singleton] at hm
  subst hm
  intro u hu
  obtain ⟨c, hc⟩ := useVregs_mem hu
  simp only [useRegsK, MInst.uses, pairUses, List.nil_append, List.mem_map] at hc
  obtain ⟨q, hq, hq1⟩ := hc
  obtain ⟨l, hl, hrl⟩ := single_mem h _ (List.of_mem_zip hq).1
  refine ⟨c, ?_⟩
  simp only [regsUL, regsU, List.append_nil, List.mem_flatten]
  exact ⟨l, hl, hq1 ▸ hrl⟩

theorem mapM_single_eq : ∀ {rss : List (List Reg)} {rs : List Reg},
    rss.mapM (fun | [r] => some r | _ => none) = some rs → rss = rs.map fun r => [r]
  | [], rs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; rfl
  | x :: xs, rs, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y0, h0, h⟩ := bind_some_ex h
    obtain ⟨ys, h1, h⟩ := bind_some_ex h
    simp only [pure, Option.some.injEq] at h
    subst h
    rw [mapM_single_eq h1]
    split at h0
    · cases h0; rfl
    · cases h0

theorem map_snd_zip_eq : ∀ {ps rs : List Reg}, rs.length ≤ ps.length → (ps.zip rs).map (·.2) = rs
  | _, [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: ps, r :: rs, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, true_and]
    exact map_snd_zip_eq (by simp at h; omega)

theorem flatten_map_single : ∀ rs : List Reg, (rs.map fun r => [r]).flatten = rs
  | [] => rfl
  | r :: rs => by
    show [r] ++ (rs.map fun r => [r]).flatten = r :: rs
    rw [flatten_map_single rs]
    rfl

/-- `gen_call_rets`: the call's defs are the argument registers. -/
theorem crets_d {rss : List (List Reg)} {rs ps : List Reg} (hp : retRegs rss.length = some ps)
    (h : rss.mapM (fun | [r] => some r | _ => none) = some rs) :
    (∀ r ∈ regsU (.regsVec rss), r ∈ (ps.zip rs).map (·.2)) ∧
      (∀ r ∈ (ps.zip rs).map (·.2), r ∈ regsU (.regsVec rss)) ∧
      (V.regsVec rss).valsIn = [] ∧ (V.regsVec rss).instsIn = [] := by
  have e := mapM_single_eq h
  have hl : ps.length = rss.length := by
    unfold retRegs at hp
    split at hp
    · cases hp; simp
    · cases hp
  have hz : (ps.zip rs).map (·.2) = rs := map_snd_zip_eq (by rw [hl, e]; simp)
  have hf : regsU (.regsVec rss) = rs := by
    rw [e]; exact flatten_map_single rs
  rw [hz, hf]
  exact ⟨fun _ h => h, fun _ h => h, rfl, rfl⟩

/-- `put_in_reg`/`put_in_regs`/`put_extended_in_reg`: the value register of an argument value. -/
theorem put_d {ctx : Ctx} {args : List V} {v : V} {x : Nat} {r : Reg} (hv : regsU v = [r])
    (hval : v.valsIn = []) (hins : v.instsIn = []) (hx : x ∈ valsInL args)
    (h : ctx.valueReg? x = some r) :
    (∀ r' ∈ regsU v, ∃ y ∈ valsInL args, ctx.valueReg? y = some r') ∧ v.valsIn = [] ∧
      v.instsIn = [] := by
  refine ⟨fun r' hr => ?_, hval, hins⟩
  rw [hv, List.mem_singleton] at hr
  subst hr
  exact ⟨x, hx, h⟩

/-- `put_in_regs_vec`: the value registers of the argument values. -/
theorem putVec_d {ctx : Ctx} {ns : List Nat} {rs : List Reg} (h : ns.mapM ctx.valueReg? = some rs) :
    (∀ r ∈ regsU (.regsVec (rs.map fun r => [r])), ∃ x ∈ valsInL [.values ns],
      ctx.valueReg? x = some r) ∧ (V.regsVec (rs.map fun r => [r])).valsIn = [] ∧
      (V.regsVec (rs.map fun r => [r])).instsIn = [] := by
  refine ⟨fun r hr => ?_, rfl, rfl⟩
  have e : regsU (.regsVec (rs.map fun r => [r])) = rs := flatten_map_single rs
  rw [e] at hr
  obtain ⟨x, hx, he⟩ := mapM_mem h r hr
  exact ⟨x, by simpa [valsInL, V.valsIn] using hx, he⟩

/-- **What an extern constructor does**, by term id (past the type predicates). -/
structure CtorD (ctx : Ctx) (id : TermId) (args : List V) (st : LState) (v : V) (st' : LState) :
    Prop where
  keep : id ≠ TId.emit → id ≠ TId.load_constant_full → id ≠ TId.gen_return →
    id ≠ TId.gen_call_args → st'.emitted = st.emitted ∧ st.nextVreg ≤ st'.nextVreg
  fresh : id = TId.temp_writable_reg ∨ id = TId.gen_call_output →
    ∀ r ∈ regsU v, ∃ n cl, r = .vreg n cl ∧ st.nextVreg ≤ n
  wrr : id = TId.writable_reg_to_reg → args = [v]
  vregs : id = TId.value_reg ∨ id = TId.value_regs → ∃ rs : List Reg, args = rs.map V.reg ∧ v = .regs rs
  zero : id = TId.zero_reg ∨ id = TId.writable_zero_reg → v = .reg .xzr
  emit : id = TId.emit → ∃ i m, args = [i] ∧ MInst.ofV i = some m ∧ v = .op .unit ∧ st' = st.emit m
  lc : id = TId.load_constant_full → ∃ r, v = .reg r ∧ LCD st r st'
  od : id = TId.opportunistic_def → v = .op .unit
  put : id = TId.put_in_reg ∨ id = TId.put_in_regs ∨ id = TId.put_in_regs_vec ∨
    id = TId.put_extended_in_reg →
    (∀ r ∈ regsU v, ∃ x ∈ valsInL args, ctx.valueReg? x = some r) ∧ v.valsIn = [] ∧ v.instsIn = []
  ssa : id = TId.abi_stackslot_addr → ∃ rd rest w, args = rd :: rest ∧
    v = .data tyMInst VIdx.MInst.LoadAddr [rd, w] ∧ w.regsIn = [] ∧ w.valsIn = [] ∧ w.instsIn = []
  crets : id = TId.gen_call_rets → ∃ a w ds, args = [a, w] ∧ v = .op (.callRets ds) ∧
    (∀ r ∈ regsU w, r ∈ ds.map (·.2)) ∧ (∀ r ∈ ds.map (·.2), r ∈ regsU w) ∧
    w.valsIn = [] ∧ w.instsIn = []
  trets : id = TId.gen_try_call_rets → ∃ ds, v = .op (.callRets ds) ∧
    ∀ r ∈ ds.map (·.2), r ∈ ctx.tryRegs.1 ∨ r ∈ ctx.tryRegs.2
  cinfo : id = TId.gen_call_info ∨ id = TId.gen_call_ind_info → ∃ a0 a1 us ds rest ci,
    args = a0 :: a1 :: .op (.callArgs us) :: .op (.callRets ds) :: rest ∧
    v = .op (.callInfo ci) ∧ ci.uses = us ∧ ci.defs = ds ∧
    ∀ r, ci.dest = .reg r → id = TId.gen_call_ind_info ∧ a1 = .reg r
  eargs : id = TId.gen_return ∨ id = TId.gen_call_args → st'.nextVreg = st.nextVreg ∧
    ∃ ms : List MInst, st'.emitted = st.emitted ++ ms.toArray ∧ (∀ m ∈ ms, ArgUses args m) ∧
      (∀ r ∈ regsU v, r ∈ regsUL args) ∧ v.valsIn = [] ∧ v.instsIn = []
  ret : id = TId.gen_return → v = .op .unit
  dyn : id ≠ TId.abi_dynamic_stackslot_addr
  gen : id ∉ ctorSpecials → (∀ r ∈ regsU v, r ∈ regsUL args) ∧ (∀ n ∈ v.valsIn, n ∈ valsInL args) ∧
    ∀ j ∈ v.instsIn, j ∈ instsInL args

/-- `CtorD` of every successful result, or a type predicate (state kept, a type returned). -/
def CtorDP (ctx : Ctx) (st : LState) (id : TermId) (args : List V) (r : ExtResult (V × LState)) :
    Prop :=
  ∀ v st', r = .ok (v, st') →
    ((tyPred id).isSome = true ∧ st' = st ∧ ∃ ty, v = .ty ty) ∨ CtorD ctx id args st v st'

/-- Close the generic field of a constructor keeping registers, values and instructions. -/
macro "gen_same" : tactic => `(tactic| (refine ⟨fun r hr => ?_, fun n hn => ?_, fun j hj => ?_⟩ <;>
  first
  | (simp_all [regsU, opRegsU, regsUL, V.valsIn, opVals, valsInL, V.instsIn, instsInL]; done)
  | (simp only [regsU, List.mem_singleton] at hr; subst hr
     simpa [regsUL, regsU] using List.mem_of_getElem? ‹_›)))

set_option maxHeartbeats 8000000 in
/-- **What every extern constructor does.** -/
theorem externCtor_d (ctx : Ctx) (t : Term) (args : List V) (st : LState) :
    CtorDP ctx st t.id args (externCtor ctx t args st) := by
  unfold externCtor
  split
  · intro v st' h
    split at h
    · cases h
      exact .inl ⟨by rw [‹tyPred _ = some _›]; rfl, rfl, _, rfl⟩
    · cases h
  · apply externCtor_split _ (CtorDP ctx st)
    all_goals
      intros
      unfold CtorDP
      intro v st' h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals try (rename_i heq; simp only [Option.map_eq_some_iff, Function.comp_apply] at heq
                   obtain ⟨_, _, rfl⟩ := heq)
    all_goals refine .inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (intro hx; exfalso; revert hx; decide)
      | (intro h1 h2 h3 h4; exfalso; first | exact h1 rfl | exact h2 rfl | exact h3 rfl |
          exact h4 rfl)
      | decide
      | skip
    all_goals intros
    all_goals first
      | exact ⟨rfl, Nat.le_refl _⟩
      | rfl
      | exact ⟨rfl, Nat.le_succ _⟩
      | (rename_i r hr; simp only [regsU, LState.fresh, List.mem_singleton] at hr
         exact ⟨_, _, hr, Nat.le_refl _⟩)
      | exact (callOutput_d _ _ (fun _ _ => rfl)).1
      | exact (callOutput_d _ _ (fun _ _ => rfl)).2 _ ‹_›
      | exact ⟨[_], rfl, rfl⟩
      | exact ⟨[_, _], rfl, rfl⟩
      | exact ⟨_, _, rfl, ‹_›, rfl, rfl⟩
      | exact ⟨_, rfl, loadConstantFull_d _ _ _ _ _⟩
      | (refine put_d rfl rfl rfl ?_ ‹_›
         simp [valsInL, V.valsIn, opVals])
      | exact putVec_d ‹_›
      | exact ⟨_, _, _, rfl, rfl, rfl, rfl, rfl⟩
      | exact ⟨_, _, _, rfl, rfl, crets_d ‹_› ‹_›⟩
      | (refine ⟨_, rfl, fun r hr => ?_⟩
         simp only [List.mem_map, List.mem_append, List.mem_filter] at hr
         obtain ⟨⟨a, b⟩, hq | ⟨hq, -⟩, rfl⟩ := hr
         · exact .inl (List.of_mem_zip hq).2
         · exact .inr (List.of_mem_zip hq).2)
      | (refine ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, fun r h => ?_⟩
         cases h <;> exact ⟨rfl, rfl⟩)
      | exact rets_d ‹_›
      | (refine callArgs_d _ _ (fun _ _ => rfl) ?_
         intro b hb
         have hz := List.of_mem_zip hb
         have hz1 := List.of_mem_zip hz.1
         obtain ⟨l, hl, hrl⟩ := single_mem ‹_› _ hz1.2
         simp only [regsUL, regsU, opRegsU, List.nil_append, List.append_nil, List.mem_flatten]
         exact ⟨l, hl, hrl⟩)
      | gen_same

/-! ## Extern constructors: failures and the environment -/

/-- A failing constructor is neither `emit` nor the unmodelled one. -/
def FailP (id : TermId) (r : ExtResult (V × LState)) : Prop :=
  r = .fail → id ≠ TId.emit ∧ id ≠ TId.abi_dynamic_stackslot_addr

set_option maxHeartbeats 4000000 in
theorem externCtor_fail (ctx : Ctx) (t : Term) (args : List V) (st : LState) :
    FailP t.id (externCtor ctx t args st) := by
  unfold externCtor
  split
  · intro h
    split at h
    · cases h
    · obtain ⟨p, hp⟩ : ∃ p, tyPred t.id = some p := ⟨_, ‹_›⟩
      constructor <;> intro he <;> rw [he] at hp <;> cases hp
  · apply externCtor_split _ (fun id _ r => FailP id r)
    all_goals
      intros
      unfold FailP
      intro h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals decide

theorem specials_noPred : ∀ t ∈ ctorSpecials, (tyPred t).isNone = true := by decide

theorem actor_gen {e : AEnv} {t : TermId} {as : List A} (h : t ∉ ctorSpecials) :
    actor e t as = some (genericCl e as, e) := by
  simp only [ctorSpecials, List.mem_cons, List.mem_nil_iff, or_false, not_or] at h
  unfold actor
  simp [h, unmodeledCtors]

/-- `actor` keeps the environment except for `emit` and the unmodelled constructor. -/
theorem actor_env {e e' : AEnv} {t : TermId} {as : List A} {a : A}
    (ha : actor e t as = some (a, e')) :
    e' = e ∨ t = TId.emit ∨ t = TId.abi_dynamic_stackslot_addr := by
  by_cases hs : t ∈ ctorSpecials
  · simp only [ctorSpecials, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | (right; left; rfl) | (right; right; rfl) | left
    all_goals simp (config := { decide := true }) only [actor, unmodeledCtors, ↓reduceIte,
      List.contains_cons, List.contains_nil] at ha
    all_goals (repeat' split at ha)
    all_goals first
      | (cases ha; done)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at ha; exact ha.2.symm)
  · rw [actor_gen hs] at ha
    simp only [Option.some.injEq, Prod.mk.injEq] at ha
    exact .inl ha.2.symm

/-! ## Extern constructors: soundness of `actor` -/

section Ctor
variable {ctx : Ctx} {c : SC} {s0 : LState}

theorem keep_finish {s s' : LState} {e : AEnv} {env : Isle.Interp.Env V} {a : A} {v : V}
    (hI : IsD ctx c s0 s) (hk : s'.emitted = s.emitted ∧ s.nextVreg ≤ s'.nextVreg)
    (he : EnvOK c (Dn ctx c s0 s) env e) (hγ : γ c a (Dn ctx c s0 s) env v) :
    IsD ctx c s0 s' ∧ RsD s s' ∧ EnvOK c (Dn ctx c s0 s') env e ∧
      γ c a (Dn ctx c s0 s') env v :=
  let ⟨h1, h2, h3⟩ := isD_keep hI hk.2 hk.1
  ⟨h1, h2, he.mono h3, γ_mono a h3 hγ⟩

theorem γ_genericCl {e : AEnv} {as : List A} {D : Nat → Prop} {env : Isle.Interp.Env V}
    {vs : List V} {v : V} (he : EnvOK c D env e) (hvs : γL c as D env vs)
    (hr : ∀ r ∈ regsU v, r ∈ regsUL vs) (hv : ∀ n ∈ v.valsIn, n ∈ valsInL vs)
    (hi : ∀ j ∈ v.instsIn, j ∈ instsInL vs) : γ c (genericCl e as) D env v := by
  unfold genericCl
  split
  · rename_i hf
    have hall := fitsClL_sound he F true true as hvs hf
    show Cl c _ _ D v
    refine ⟨fun r hr' => ?_, fun n hn => ?_, fun j hj => ?_⟩
    · obtain ⟨w, hw, hrw⟩ := mem_regsUL.mp (hr r hr')
      cases hz : fitsCl.fitsClL e F true false as
      · simp only [Bool.not_false]
        exact (hall w hw).1 r hrw
      · simp only [Bool.not_true]
        exact (fitsClL_sound he F true false as hvs hz w hw).1 r hrw
    · obtain ⟨w, hw, hn'⟩ := valsInL_mem' (hv n hn)
      exact (hall w hw).2.1 n hn'
    · obtain ⟨w, hw, hj'⟩ := instsInL_mem' (hi j hj)
      cases hb : fitsCl.fitsClL e F false true as
      · simp only [Bool.not_false]
        exact (hall w hw).2.2 j hj'
      · simp only [Bool.not_true]
        exact (fitsClL_sound he F false true as hvs hb w hw).2.2 j hj'
  · trivial

theorem RD_valueReg (hreg : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int)
    (hvr : ValRegK ctx) {s : LState} {x : Nat} {r : Reg} (hx : ctx.valueReg? x = some r)
    (hR : c.R x) : RD (Dn ctx c s0 s) false r := by
  have e := hreg x r hx
  subst e
  exact .inl ⟨hvr x _ hx x .int rfl, hR⟩

theorem Wv_vreg {D : Nat → Prop} {w : V} (h : Wv c false D w) :
    ∀ r ∈ regsU w, ∃ n cl, r = .vreg n cl ∧ (c.lo ≤ n ∨ D n) := by
  intro r hr
  have := h r hr
  cases r <;> first | exact ⟨_, _, rfl, this⟩ | exact absurd this.1 (by decide)

theorem Cl_unit {b z : Bool} {D : Nat → Prop} : Cl c b z D (.op .unit) :=
  Cl_of_atoms rfl (by simp [V.valsIn, opVals]) rfl

/-- An emission by `gen_return`/`gen_call_args` of clean argument registers. -/
theorem eargs_finish {s s' : LState} {vs : List V} {ms : List MInst}
    (hI : IsD ctx c s0 s) (hcl : ∀ w ∈ vs, Cl c true true (Dn ctx c s0 s) w)
    (hnv : s'.nextVreg = s.nextVreg) (he : s'.emitted = s.emitted ++ ms.toArray)
    (hmu : ∀ m ∈ ms, ArgUses vs m) :
    IsD ctx c s0 s' ∧ RsD s s' ∧ ∀ n, Dn ctx c s0 s n → Dn ctx c s0 s' n := by
  obtain ⟨h1, h2, h3, -⟩ := isD_emit hI (by omega) he (fun k m hk u hu => by
    obtain ⟨cl, hcu⟩ := hmu m (List.mem_of_getElem? hk) u hu
    obtain ⟨w, hw, hrw⟩ := mem_regsUL.mp hcu
    exact .inl ((hcl w hw).1 _ hrw))
  exact ⟨h1, h2, h3⟩

/-- `emit` of an instruction whose uses are defined. -/
theorem emit_finish {s : LState} {e : AEnv} {env : Isle.Interp.Env V} {a0 : A} {i : V}
    {m : MInst} (hI : IsD ctx c s0 s) (he : EnvOK c (Dn ctx c s0 s) env e)
    (hγ : γ c a0 (Dn ctx c s0 s) env i) (hfit : fitsMI e F a0 = true)
    (hm : MInst.ofV i = some m) :
    IsD ctx c s0 (s.emit m) ∧ RsD s (s.emit m) ∧
      EnvOK c (Dn ctx c s0 (s.emit m)) env (upg e F a0) ∧
      γ c (.cl false false) (Dn ctx c s0 (s.emit m)) env (.op .unit) := by
  have hmi := fitsMI_sound he hγ hfit m hm
  have hu : ∀ (k : Nat) m', [m][k]? = some m' → ∀ u ∈ useVregs m',
      DD c (Dn ctx c s0 s) ([m].take k) u := by
    intro k m' hk u hu
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      exact .inl (hmi.1 u hu)
    | succ k => simp at hk
  obtain ⟨h1, h2, h3, h4⟩ :=
    isD_emit (ms := [m]) (s' := s.emit m) hI (Nat.le_refl _) (by simp [LState.emit]) hu
  exact ⟨h1, h2, upg_sound F a0 h3 he hγ hm hmi.2 (h4 m (by simp)), Cl_unit⟩

set_option maxHeartbeats 4000000 in
/-- **The extern constructors meet `actor`.** -/
theorem ctor_ok (hreg : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int) (hvr : ValRegK ctx)
    (htry : ∀ r ∈ ctx.tryRegs.1 ++ ctx.tryRegs.2, ∃ n cl, r = .vreg n cl)
    {t : TermId} {term : Term} {as : List A} {e e' : AEnv} {a : A} {env : Isle.Interp.Env V}
    {vs : List V} {s s' : LState} {v : V}
    (ht : termOf program t = .ok term) (ha : actor e t as = some (a, e'))
    (hvs : γL c as (Dn ctx c s0 s) env vs) (he : EnvOK c (Dn ctx c s0 s) env e)
    (hI : IsD ctx c s0 s) (h : externCtor ctx term vs s = .ok (v, s')) :
    IsD ctx c s0 s' ∧ RsD s s' ∧ EnvOK c (Dn ctx c s0 s') env e' ∧
      γ c a (Dn ctx c s0 s') env v := by
  have hid := termOf_id_eq ht
  have hd0 := externCtor_d ctx term vs s v s' h
  rw [hid] at hd0
  by_cases hs : t ∈ ctorSpecials
  rotate_left
  · rw [actor_gen hs] at ha
    simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    rcases hd0 with ⟨-, rfl, ty, rfl⟩ | hd
    · exact keep_finish hI ⟨rfl, Nat.le_refl _⟩ he
        (γ_genericCl he hvs (by simp [regsU]) (by simp [V.valsIn]) (by simp [V.instsIn]))
    · have hne : ∀ x ∈ ctorSpecials, t ≠ x := fun x hx h' => hs (h' ▸ hx)
      have hg := hd.gen hs
      exact keep_finish hI (hd.keep (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide))
        (hne _ (by decide))) he (γ_genericCl he hvs hg.1 hg.2.1 hg.2.2)
  have hnp := specials_noPred t hs
  rcases hd0 with ⟨hp, -, -⟩ | hd
  · rw [Option.isNone_iff_eq_none.mp hnp] at hp
    cases hp
  have hlo := hI.2
  simp only [ctorSpecials, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (config := { decide := true }) only [actor, unmodeledCtors, ↓reduceIte,
    List.contains_cons, List.contains_nil] at ha
  -- temp_writable_reg, gen_call_output
  · simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    refine keep_finish hI (hd.keep (by decide) (by decide) (by decide) (by decide)) he ?_
    intro r hr
    obtain ⟨n, cl, rfl, hn⟩ := hd.fresh (by decide) r hr
    exact .inl (by omega)
  · simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    refine keep_finish hI (hd.keep (by decide) (by decide) (by decide) (by decide)) he ?_
    intro r hr
    obtain ⟨n, cl, rfl, hn⟩ := hd.fresh (by decide) r hr
    exact .inl (by omega)
  -- invalid_reg
  · simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    exact keep_finish hI (hd.keep (by decide) (by decide) (by decide) (by decide)) he trivial
  -- abi_dynamic_stackslot_addr
  · exact absurd rfl hd.dyn
  -- writable_reg_to_reg
  · simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain rfl := hd.wrr rfl
    cases as with
    | nil => simp [γL] at hvs
    | cons a0 as' =>
      exact keep_finish hI (hd.keep (by decide) (by decide) (by decide) (by decide)) he hvs.1
  -- value_reg, value_regs
  · simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨rs, rfl, rfl⟩ := hd.vregs (by decide)
    exact keep_finish hI (hd.keep (by decide) (by decide) (by decide) (by decide)) he ⟨rs, rfl, hvs⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨rs, rfl, rfl⟩ := hd.vregs (by decide)
    exact keep_finish hI (hd.keep (by decide) (by decide) (by decide) (by decide)) he ⟨rs, rfl, hvs⟩
  -- zero_reg, writable_zero_reg
  all_goals try (
    simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain rfl := hd.zero (by decide)
    refine keep_finish hI (hd.keep (by decide) (by decide) (by decide) (by decide)) he
      ⟨fun r hr => ?_, by simp [V.valsIn], by simp [V.instsIn]⟩
    simp only [regsU, List.mem_singleton] at hr
    subst hr
    exact ⟨rfl, by decide⟩)
  -- emit
  · obtain ⟨i, m, rfl, hm, rfl, rfl⟩ := hd.emit rfl
    cases as with
    | nil => simp [γL] at hvs
    | cons a0 as' =>
      have hγ : γ c a0 (Dn ctx c s0 s) env i := hvs.1
      simp only [List.headD_cons] at ha
      split at ha
      next τ k fs hres =>
        split at ha
        next hc =>
          exfalso
          simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hc
          obtain ⟨rfl, hk⟩ := hc
          have := res_sound he F a0 hγ
          rw [hres] at this
          obtain ⟨ws, rfl, -⟩ := this
          obtain ⟨ks, hks, -⟩ := ofV_fields hm
          rw [hk] at hks
          cases hks
        next =>
          by_cases hfit : fitsMI e F a0 = true
          · simp only [hfit, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at ha
            obtain ⟨rfl, rfl⟩ := ha
            exact emit_finish hI he hγ hfit hm
          · simp [hfit] at ha
      next =>
        by_cases hfit : fitsMI e F a0 = true
        · simp only [hfit, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at ha
          obtain ⟨rfl, rfl⟩ := ha
          exact emit_finish hI he hγ hfit hm
        · simp [hfit] at ha
  -- load_constant_full
  · simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨r, rfl, hle, ms, he', hms, n, cl, rfl, hn, m, hm, hdm⟩ := hd.lc rfl
    obtain ⟨hI', hR, hD, hdef⟩ := isD_emit hI hle he' (fun k m' hk u hu => by
      obtain ⟨h1, m'', hm'', h2⟩ := hms k m' hk u hu
      exact .inr ⟨by omega, m'', hm'', h2⟩)
    refine ⟨hI', hR, he.mono hD, fun r hr => ?_, by simp [V.valsIn], by simp [V.instsIn]⟩
    simp only [regsU, List.mem_singleton] at hr
    subst hr
    exact hdef m hm n hdm (by omega)
  -- opportunistic_def
  · simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain rfl := hd.od rfl
    exact keep_finish hI (hd.keep (by decide) (by decide) (by decide) (by decide)) he Cl_unit
  -- put_in_reg, put_in_regs, put_in_regs_vec, put_extended_in_reg
  iterate 4
    split at ha
    next hfit =>
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      have hcl := fitsClL_sound he F true true as hvs hfit
      obtain ⟨hp1, hp2, hp3⟩ := hd.put (by decide)
      refine keep_finish hI (hd.keep (by decide) (by decide) (by decide) (by decide)) he
        ⟨fun r hr => ?_, by simp [hp2], by simp [hp3]⟩
      obtain ⟨x, hx, hxr⟩ := hp1 r hr
      obtain ⟨w, hw, hxw⟩ := valsInL_mem' hx
      exact RD_valueReg hreg hvr hxr ((hcl w hw).2.1 x hxw)
    next =>
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      exact keep_finish hI (hd.keep (by decide) (by decide) (by decide) (by decide)) he trivial
  -- abi_stackslot_addr
  · simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨rd, rest, w, rfl, rfl, hw1, hw2, hw3⟩ := hd.ssa rfl
    cases as with
    | nil => simp [γL] at hvs
    | cons a0 as' =>
      exact keep_finish hI (hd.keep (by decide) (by decide) (by decide) (by decide)) he
        ⟨[rd, w], rfl, hvs.1, Cl_of_atoms hw1 (by simp [hw2]) hw3, trivial⟩
  -- gen_call_rets
  · obtain ⟨a0, w, ds, rfl, rfl, h1, h2, h3, h4⟩ := hd.crets rfl
    have hk := hd.keep (by decide) (by decide) (by decide) (by decide)
    split at ha
    next b0 x =>
      split at ha
      next hfit =>
        simp only [Option.some.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        have hx : env[x]? = some (some w) := hvs.2.1
        have hW := Wv_vreg (fitsWr_sound (a := .sym x) he hvs.2.1 hfit)
        refine keep_finish hI hk he ⟨ds, rfl, fun r hr => ?_, fun x' hx' => ?_⟩
        · obtain ⟨n, cl, rfl, -⟩ := hW r (h2 r hr)
          exact .inl ⟨n, cl, rfl⟩
        · simp only [List.mem_singleton] at hx'
          subst hx'
          exact ⟨w, hx, h3, h4, fun r hr => ⟨h1 r hr, hW r hr⟩⟩
      next =>
        simp only [Option.some.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        exact keep_finish hI hk he trivial
    next =>
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      exact keep_finish hI hk he trivial
  -- gen_try_call_rets
  · simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨ds, rfl, hds⟩ := hd.trets rfl
    refine keep_finish hI (hd.keep (by decide) (by decide) (by decide) (by decide)) he
      ⟨ds, rfl, fun r hr => ?_, fun x hx => by cases hx⟩
    obtain ⟨n, cl, rfl⟩ := htry r (List.mem_append.mpr (hds r hr))
    exact .inl ⟨n, cl, rfl⟩
  -- gen_call_info, gen_call_ind_info
  iterate 2
    obtain ⟨b0, b1, us, ds, rest, ci, rfl, rfl, hu, hdf, hdest⟩ := hd.cinfo (by decide)
    have hk := hd.keep (by decide) (by decide) (by decide) (by decide)
    split at ha
    next b a1 u r tl =>
      have hγ1 : γ c a1 (Dn ctx c s0 s) env b1 := hvs.2.1
      have hγu := hvs.2.2.1
      have hγr := hvs.2.2.2.1
      split at ha
      next hc =>
        simp only [Bool.and_eq_true] at hc
        obtain ⟨hc1, hcu⟩ := hc
        have hCu := fitsCl_sound he F true true u hγu hcu
        have huses : ∀ r' ∈ callUses ci, RD (Dn ctx c s0 s) true r' := by
          intro r' hr'
          unfold callUses at hr'
          rw [hu] at hr'
          rcases List.mem_append.mp hr' with hr' | hr'
          · split at hr'
            next r0 hdr =>
              simp only [List.mem_singleton] at hr'
              subst hr'
              obtain ⟨hid', rfl⟩ := hdest _ hdr
              simp only [Bool.or_eq_true] at hc1
              rcases hc1 with hc1 | hc1 <;> first
                | exact absurd hid' (by decide)
                | exact absurd hc1 (by decide)
                | exact (fitsCl_sound he F true true a1 hγ1 hc1).1 _ (by simp [regsU])
            next => cases hr'
          · exact hCu.1 r' hr'
        split at ha
        next xs hres =>
          simp only [Option.some.injEq, Prod.mk.injEq] at ha
          obtain ⟨rfl, rfl⟩ := ha
          have := res_sound he F r hγr
          rw [hres] at this
          obtain ⟨ds', hds', hok, hcd⟩ := this
          cases hds'
          refine keep_finish hI hk he ⟨ci, rfl, huses, ?_, ?_⟩
          · rw [hdf]; exact hok
          · rw [hdf]; exact hcd
        next =>
          split at ha
          next hfr =>
            simp only [Option.some.injEq, Prod.mk.injEq] at ha
            obtain ⟨rfl, rfl⟩ := ha
            have hCr := fitsCl_sound he F true true r hγr hfr
            refine keep_finish hI hk he ?_
            show PT c false _ TyId.«BoxCallInfo» _
            unfold PT
            rw [if_neg (show TyId.«BoxCallInfo» ≠ tyMInst by decide),
              if_pos (show TyId.«BoxCallInfo» ∈ ciTys by decide)]
            intro ci' hci'
            cases hci'
            refine ⟨huses, fun r' hr' => RD_okReg (hCr.1 r' ?_)⟩
            rw [hdf] at hr'
            exact hr'
          next => cases ha
      next => cases ha
    next => cases ha
  -- gen_return
  · split at ha
    next hfit =>
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      obtain ⟨hnv, ms, he', hmu, -, -, -⟩ := hd.eargs (by decide)
      obtain ⟨hI', hR, hD⟩ :=
        eargs_finish hI (fitsClL_sound he F true true as hvs hfit) hnv he' hmu
      obtain rfl := hd.ret rfl
      exact ⟨hI', hR, he.mono hD, Cl_unit⟩
    next => cases ha
  -- gen_call_args
  · split at ha
    next hfit =>
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      have hcl := fitsClL_sound he F true true as hvs hfit
      obtain ⟨hnv, ms, he', hmu, hr, hv, hi⟩ := hd.eargs (by decide)
      obtain ⟨hI', hR, hD⟩ := eargs_finish hI hcl hnv he' hmu
      refine ⟨hI', hR, he.mono hD, fun r hr' => ?_, by simp [hv], by simp [hi]⟩
      obtain ⟨w, hw, hrw⟩ := mem_regsUL.mp (hr r hr')
      exact RD_mono hD id ((hcl w hw).1 r hrw)
    next => cases ha

end Ctor

/-! ## The model -/

/-- **The model of the driver's semantics** for a context whose reached values and instructions
are closed under what the extractors read, whose value registers are the values' vregs, and
whose `try_call` registers are vregs. -/
theorem dModel {ctx : Ctx} {c : SC} {s0 : LState}
    (hreg : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int)
    (hvr : Kill.ValRegK ctx)
    (hroot : ∀ info, ctx.insts[c.root]? = some info → Flow.DataOk c.R info.data)
    (hinst : ∀ j info, c.I j → ctx.insts[j]? = some info →
      Flow.DataOk c.R info.data ∧ ∀ n ∈ info.results, c.R n)
    (hdefI : ∀ n j, c.R n → ctx.defInst? n = some j → c.I j)
    (hargs : ∀ n j info cl, c.R n → ctx.defInst? n = some j → ctx.insts[j]? = some info →
      info.clif = some cl → ∀ y ∈ Driver.instArgs cl, c.R y)
    (htry : ∀ r ∈ ctx.tryRegs.1 ++ ctx.tryRegs.2, ∃ n cl, r = .vreg n cl) :
    DModel program ctx c s0 where
  ext := extOK hroot hinst hdefI hargs
  ctor := fun _ _ _ _ _ _ _ _ _ _ _ ht ha hvs he hI h => ctor_ok hreg hvr htry ht ha hvs he hI h
  ctor_fail := fun _ term _ _ _ _ vs s ht ha h => by
    have hf := externCtor_fail ctx term vs s h
    rw [termOf_id_eq ht] at hf
    rcases actor_env ha with h' | rfl | rfl
    · exact h'
    · exact absurd rfl hf.1
    · exact absurd rfl hf.2
  oracle := dOracle
  wrap := dWrap

end Backend.Proof.DefGen
