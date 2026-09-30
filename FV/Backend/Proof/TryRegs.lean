import FV.Backend.Isel

/-!
# The return and payload vregs of a `try_call` (`tryRegsOf`)

For a callee convention whose exception payloads are x0 and x1 (`system_v`, the only one
`exnTableOpnd` accepts), with `n ≤ 8` ABI returns and `b` the first fresh vreg: the returns are
`vreg b, …, vreg (b + n - 1)` and the payloads `vreg b`, `vreg (b + 1)` (a payload in a return
register is that return's vreg, the others are fresh); `max n 2` vregs are allocated, and the
call's defs (`gen_try_call_rets`) are `x j ↦ vreg (b + j)` for `j < max n 2`.
-/

namespace Backend

theorem foldl_retFresh {α : Type} (L : List α) : ∀ (acc : Array Reg) (st : LState),
    ∃ st', L.foldl (fun (p : Array Reg × LState) (_ : α) =>
        (p.1.push (p.2.fresh .int).1, (p.2.fresh .int).2)) (acc, st) =
      (acc ++ ((List.range L.length).map fun j => Reg.vreg (st.nextVreg + j) .int).toArray, st') ∧
      st'.nextVreg = st.nextVreg + L.length ∧ st'.emitted = st.emitted := by
  induction L with
  | nil => intro acc st; exact ⟨st, by simp, by simp, rfl⟩
  | cons a L ih =>
    intro acc st
    obtain ⟨st', h1, h2, h3⟩ := ih (acc.push (Reg.vreg st.nextVreg .int)) (st.fresh .int).2
    refine ⟨st', ?_, ?_, ?_⟩
    · rw [List.foldl_cons]
      simp only [LState.fresh] at h1 ⊢
      rw [h1]
      simp only [List.length_cons, Prod.mk.injEq, and_true]
      rw [List.range_succ_eq_map]
      simp [Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
    · simp [h2, LState.fresh]; omega
    · rw [h3]; rfl

theorem zip_map_map {α β γ : Type} (f : α → β) (g : α → γ) :
    ∀ l : List α, (l.map f).zip (l.map g) = l.map fun a => (f a, g a)
  | [] => rfl
  | a :: l => by simp [zip_map_map f g l]

theorem retRegs_some {n : Nat} (h : n ≤ 8) : retRegs n = some ((List.range n).map Reg.x) := by
  simp [retRegs, h]

/-- **The vregs of a `try_call`** (payloads in x0/x1). -/
theorem tryRegsOf_eq {sig : Clif.Signature} {st : LState}
    (hcc : payloadRegs sig.callConv = [.x 0, .x 1]) (h8 : (sigRets sig).length ≤ 8) :
    ∃ st1, tryRegsOf sig st = some (((List.range (sigRets sig).length).map
        (fun j => Reg.vreg (st.nextVreg + j) .int),
        [.vreg st.nextVreg .int, .vreg (st.nextVreg + 1) .int]), st1) ∧
      st1.nextVreg = st.nextVreg + max (sigRets sig).length 2 ∧ st1.emitted = st.emitted := by
  have b00 : (Reg.x 0 == Reg.x 0) = true := by decide
  have b01 : (Reg.x 0 == Reg.x 1) = false := by decide
  have b10 : (Reg.x 1 == Reg.x 0) = false := by decide
  have b11 : (Reg.x 1 == Reg.x 1) = true := by decide
  generalize hn : (sigRets sig).length = n at h8
  obtain ⟨st', h1, h2, h3⟩ := foldl_retFresh ((List.range n).map Reg.x) #[] st
  simp only [List.length_map, List.length_range] at h1 h2
  unfold tryRegsOf
  rw [hn, retRegs_some h8]
  simp only [Option.bind_eq_bind, Option.bind_some, hcc]
  rw [h1]
  simp only [List.foldl_cons, List.foldl_nil]
  match n, h8 with
  | 0, _ =>
    refine ⟨((st'.fresh .int).2.fresh .int).2, ?_, ?_, ?_⟩
    · simp [LState.fresh, h2]
    · simp [LState.fresh, h2]
    · simp [LState.fresh, h3]
  | 1, _ =>
    refine ⟨(st'.fresh .int).2, ?_, ?_, ?_⟩
    · simp [LState.fresh, h2, List.idxOf?, List.findIdx?, List.findIdx?.go, b00, b10, b01]
    · simp [LState.fresh, h2]
    · simp [LState.fresh, h3]
  | k + 2, _ =>
    refine ⟨st', ?_, by rw [h2]; omega, h3⟩
    have hx0 : ((List.range (k + 2)).map Reg.x).idxOf? (Reg.x 0) = some 0 := by
      rw [List.range_succ_eq_map]; simp [List.idxOf?, List.findIdx?, List.findIdx?.go, b00]
    have hx1 : ((List.range (k + 2)).map Reg.x).idxOf? (Reg.x 1) = some 1 := by
      rw [List.range_succ_eq_map, List.range_succ_eq_map]
      simp [List.idxOf?, List.findIdx?, List.findIdx?.go, b01, b11]
    simp [hx0, hx1]

/-- `tryRegsOf`'s results, from any successful call (payloads in x0/x1). -/
theorem tryRegsOf_spec {sig : Clif.Signature} {st st1 : LState} {trs : List Reg × List Reg}
    (hcc : payloadRegs sig.callConv = [.x 0, .x 1]) (h : tryRegsOf sig st = some (trs, st1)) :
    (sigRets sig).length ≤ 8 ∧
    trs = ((List.range (sigRets sig).length).map (fun j => Reg.vreg (st.nextVreg + j) .int),
      [.vreg st.nextVreg .int, .vreg (st.nextVreg + 1) .int]) ∧
    st1.nextVreg = st.nextVreg + max (sigRets sig).length 2 ∧ st1.emitted = st.emitted := by
  have h8 : (sigRets sig).length ≤ 8 := by
    unfold tryRegsOf at h
    cases hr : retRegs (sigRets sig).length with
    | none => rw [hr] at h; cases h
    | some ps =>
      simp only [retRegs] at hr
      split at hr
      · assumption
      · cases hr
  obtain ⟨st1', h', h2, h3⟩ := tryRegsOf_eq (st := st) hcc h8
  rw [h'] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨h8, rfl, h2, h3⟩

/-- The call's defs `gen_try_call_rets` builds from `tryRegsOf`'s vregs: `x j ↦ vreg (b + j)`
for `j < max n 2`. -/
theorem tryDefs_eq (n b : Nat) (h8 : n ≤ 8) :
    ((List.range n).map Reg.x).zip ((List.range n).map (fun j => Reg.vreg (b + j) .int)) ++
      (([Reg.x 0, Reg.x 1].zip [Reg.vreg b .int, Reg.vreg (b + 1) .int]).filter
        fun (q : Reg × Reg) => !((List.range n).map Reg.x).contains q.1) =
    (List.range (max n 2)).map fun j => (Reg.x j, Reg.vreg (b + j) .int) := by
  match n, h8 with
  | 0, _ => simp [List.range_succ]
  | 1, _ =>
    have : (Reg.x 1 == Reg.x 0) = false := by decide
    have h00 : (Reg.x 0 == Reg.x 0) = true := by decide
    simp [List.range_succ, List.filter_cons, this, h00]
  | k + 2, _ =>
    have hmax : max (k + 2) 2 = k + 2 := by omega
    rw [hmax]
    have h0 : ((List.range (k + 2)).map Reg.x).contains (Reg.x 0) = true := by
      simp only [List.contains_iff_exists_mem_beq, List.mem_map, List.mem_range]
      exact ⟨.x 0, ⟨0, by omega, rfl⟩, by decide⟩
    have h1 : ((List.range (k + 2)).map Reg.x).contains (Reg.x 1) = true := by
      simp only [List.contains_iff_exists_mem_beq, List.mem_map, List.mem_range]
      exact ⟨.x 1, ⟨1, by omega, rfl⟩, by decide⟩
    simp only [List.zip_cons_cons, List.zip_nil_right, List.filter_cons, h0, h1, Bool.not_true,
      List.filter_nil, zip_map_map]
    simp

theorem tryInfoOf_spec {sig : Clif.Signature} {items : List (Option Nat)} {ls : List Label}
    {info : TryInfo} (h : tryInfoOf sig items ls = some info) :
    info.continuation = ls.getLastD 0 ∧ info.handlers.length + 1 = ls.length := by
  unfold tryInfoOf at h
  split at h
  · cases h
  · rename_i hl
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hl
    cases h
    refine ⟨rfl, ?_⟩
    simp only [List.length_map, List.length_zip]
    omega

theorem exnTableOpnd_cc {f : Clif.Function} {et : Clif.ExnTable} {sig : Clif.Signature}
    {items : List (Option Nat)} (h : exnTableOpnd f et = .ok (sig, items)) :
    payloadRegs sig.callConv = [.x 0, .x 1] := by
  unfold exnTableOpnd at h
  cases hs : f.sigDecls.lookup et.sig with
  | none => simp [hs] at h
  | some sig' =>
    simp only [hs] at h
    split at h
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    · rename_i hcc
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.or_eq_true, Option.isNone_iff_eq_none,
          beq_iff_eq] at hcc
        rcases hcc with h | h <;> simp [payloadRegs, h]

theorem tryCallData_spec {f : Clif.Function} {fn : Clif.FnRef} {args : List Clif.ValueId}
    {et : Clif.ExnTable} {data : V} (h : tryCallData f (.tryCall fn args et) = .ok data) :
    ∃ sig items ext, exnTableOpnd f et = .ok (sig, items) ∧ f.extern? fn = some ext ∧
      ext.sig = sig := by
  simp only [tryCallData] at h
  cases he : exnTableOpnd f et with
  | error e => simp [he, bind, Except.bind] at h
  | ok q =>
    obtain ⟨sig, items⟩ := q
    cases hx : f.extern? fn with
    | none => simp [he, hx, bind, Except.bind] at h
    | some ext =>
      by_cases hs : ext.sig = sig
      · exact ⟨sig, items, ext, rfl, rfl, hs⟩
      · simp [he, hx, hs, bind, Except.bind] at h

theorem tryFix_append (info : TryInfo) (pre : List MInst) (c : CallInfo) :
    tryFix info (pre ++ [.call c]) = pre ++ [.tryCall c info] := by
  simp [tryFix]

theorem returns_le_sigRets (sig : Clif.Signature) : sig.returns.length ≤ (sigRets sig).length := by
  unfold sigRets
  split
  · split
    · rename_i h; simp [List.isEmpty_iff.mp h]
    · exact Nat.le_refl _
  · exact Nat.le_refl _

set_option maxRecDepth 20000 in
theorem tryCallData_eq {f : Clif.Function} {fn : Clif.FnRef} {args : List Clif.ValueId}
    {et : Clif.ExnTable} {sig : Clif.Signature} {items : List (Option Nat)} {ext : Clif.ExtFunc}
    (he : exnTableOpnd f et = .ok (sig, items)) (hx : f.extern? fn = some ext) (hs : ext.sig = sig) :
    tryCallData f (.tryCall fn args et) = .ok (.data 152 27 [.data 151 13 [], .values args,
      .op (.funcRef fn), .op (.exnTable sig items)]) := by
  simp only [tryCallData, he, hx, hs, bind, Except.bind, bne_self_eq_false, Bool.false_eq_true,
    ite_false, pure, Except.pure]
  rfl

theorem tryCallIndData_spec {f : Clif.Function} {callee : Clif.ValueId}
    {args : List Clif.ValueId} {et : Clif.ExnTable} {data : V}
    (h : tryCallData f (.tryCallIndirect callee args et) = .ok data) :
    ∃ sig items, exnTableOpnd f et = .ok (sig, items) := by
  simp only [tryCallData] at h
  cases he : exnTableOpnd f et with
  | error e => simp [he, bind, Except.bind] at h
  | ok q => exact ⟨q.1, q.2, rfl⟩

set_option maxRecDepth 20000 in
theorem tryCallIndData_eq {f : Clif.Function} {callee : Clif.ValueId} {args : List Clif.ValueId}
    {et : Clif.ExnTable} {sig : Clif.Signature} {items : List (Option Nat)}
    (he : exnTableOpnd f et = .ok (sig, items)) :
    tryCallData f (.tryCallIndirect callee args et) = .ok (.data 152 28 [.data 151 14 [],
      .values (callee :: args), .op (.exnTable sig items)]) := by
  simp only [tryCallData, he, bind, Except.bind, pure, Except.pure]
  rfl

/-- The signature of an exception table is its `sigN` declaration. -/
theorem exnTableOpnd_sig {f : Clif.Function} {et : Clif.ExnTable} {sig : Clif.Signature}
    {items : List (Option Nat)} (h : exnTableOpnd f et = .ok (sig, items)) :
    f.sigDecls.lookup et.sig = some sig := by
  unfold exnTableOpnd at h
  cases hs : f.sigDecls.lookup et.sig with
  | none => simp [hs] at h
  | some sig' =>
    simp only [hs] at h
    split at h
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    · simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [h.1]

end Backend
