import FV.Backend.Proof.IselPrgCoverT
import FV.Backend.Proof.IselPrgCtxT

/-!
# Progress of the ISLE lowering over the typed scope: the terminator roots

`term_root`/`try_root` (`IselPrgCover`) over the typed scope (`PInvT`): `term_rootT`, a
non-`try_call` terminator's `lower`/`lower_branch` call in its context `termCtx` (a `return`'s
values are of the typed scope, `aVM`; a branch condition and a `br_table` index are in integer
positions, `PInvT.termIntOf`); `try_rootT`, a `try_call`'s `lower_branch` call in its context
`tryCtx`. Roots: `termRootsT`.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64

/-! ## `termRootsT` -/

/-- The roots after the `return`s are `termRoots`'s. -/
theorem termRoots_drop : termRoots.drop retCounts.length =
    [(TId.lower, [termInst VIdx.InstructionData.Trap [opc VIdx.Opcode.Trap, .op .trapCode none]]),
     (TId.lower_branch, [termInst VIdx.InstructionData.Jump [opc VIdx.Opcode.Jump, .blockCalls 1],
        .labels 1 (some 1)]),
     (TId.lower_branch, [termInst VIdx.InstructionData.Brif
        [opc VIdx.Opcode.Brif, aV, .blockCalls 2], .labels 2 (some 2)]),
     (TId.lower_branch, [termInst VIdx.InstructionData.BranchTable
        [opc VIdx.Opcode.BrTable, aV, .op .jumpTable none], .labels 1 none])] ++
    ((List.range (maxTryItems + 1)).map fun m => (TId.lower_branch,
      [termInst VIdx.InstructionData.TryCall [opc VIdx.Opcode.TryCall, .valsMin 0,
        .op .funcRefTry none, .op .exnTry (some m)], .labels (m + 1) (some (m + 1))])) ++
    ((List.range (maxTryItems + 1)).map fun m => (TId.lower_branch,
      [termInst VIdx.InstructionData.TryCallIndirect [opc VIdx.Opcode.TryCallIndirect, .valsMin 1,
        .op .exnTry (some m)], .labels (m + 1) (some (m + 1))])) := by
  unfold termRoots
  simp only [List.append_assoc]
  rw [show retCounts.length = (retCounts.map fun m => (TId.lower, [termInst
      VIdx.InstructionData.MultiAry [opc VIdx.Opcode.Return, .vals (List.replicate m aV)]])).length
      from (List.length_map ..).symm, List.drop_left]

theorem mem_termRootsT_mid {q : TermId × List PA}
    (h : q ∈ [(TId.lower, [termInst VIdx.InstructionData.Trap [opc VIdx.Opcode.Trap,
        .op .trapCode none]]),
     (TId.lower_branch, [termInst VIdx.InstructionData.Jump [opc VIdx.Opcode.Jump, .blockCalls 1],
        .labels 1 (some 1)]),
     (TId.lower_branch, [termInst VIdx.InstructionData.Brif
        [opc VIdx.Opcode.Brif, aV, .blockCalls 2], .labels 2 (some 2)]),
     (TId.lower_branch, [termInst VIdx.InstructionData.BranchTable
        [opc VIdx.Opcode.BrTable, aV, .op .jumpTable none], .labels 1 none])]) :
    q ∈ termRootsT := by
  unfold termRootsT; rw [termRoots_drop]
  apply List.mem_append_right; apply List.mem_append_left; apply List.mem_append_left; exact h

theorem mem_termRootsT_try {q : TermId × List PA}
    (h : q ∈ (List.range (maxTryItems + 1)).map fun m => (TId.lower_branch,
      [termInst VIdx.InstructionData.TryCall [opc VIdx.Opcode.TryCall, .valsMin 0,
        .op .funcRefTry none, .op .exnTry (some m)], .labels (m + 1) (some (m + 1))])) :
    q ∈ termRootsT := by
  unfold termRootsT; rw [termRoots_drop]
  apply List.mem_append_right; apply List.mem_append_left; apply List.mem_append_right; exact h

theorem mem_termRootsT_ind {q : TermId × List PA}
    (h : q ∈ (List.range (maxTryItems + 1)).map fun m => (TId.lower_branch,
      [termInst VIdx.InstructionData.TryCallIndirect [opc VIdx.Opcode.TryCallIndirect, .valsMin 1,
        .op .exnTry (some m)], .labels (m + 1) (some (m + 1))])) :
    q ∈ termRootsT := by
  unfold termRootsT; rw [termRoots_drop]
  apply List.mem_append_right; apply List.mem_append_right; exact h

section
variable {f : Clif.Function} {ctx : Ctx}

theorem γL_repT {xs : List Nat} (h : ∀ x ∈ xs, γ f ctx aVM (.value x)) :
    γL f ctx (List.replicate xs.length aVM) (xs.map .value) := by
  induction xs with
  | nil => exact γL_nil'
  | cons x xs ih =>
    exact γL_cons' (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

set_option maxRecDepth 100000 in
/-- **A terminator's root**: the driver's `lower`/`lower_branch` call on a non-`try_call`
terminator of `f` (at its placeholder slot, in its context `termCtx`, with one target per
successor) is a root of the table whose inputs describe its arguments. -/
theorem term_rootTB {ranges : Array (Nat × Nat)} {st0 : LState} (hP : PInvTB f ctx)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) (hdom : dominatedB f = true)
    (hin : iselInB f = true) (hdrv : driverInB f = true) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator}
    (ht : ∃ B ∈ f.blocks, B.term = t) {data : V} (hd : termData (abiTerm f t) = .ok data)
    {targets : List Label} (hlen : targets.length = (destsOf t).length) :
    ∃ q ∈ termRootsT, (∃ T : Term, program.termByName? (termCall t ti targets).1 = some T ∧
      T.id = q.1) ∧ γL f (termCtx ctx ti data) q.2 (termCall t ti targets).2 := by
  obtain ⟨B, hB, rfl⟩ := ht
  have hP' := pinv_termCtxTB hP hph data
  have hself := termCtx_insts_self hph data
  have hA : ∀ x ∈ termArgs (abiTerm f B.term), γ f (termCtx ctx ti data) aVM (.value x) :=
    fun x hx => γ_aVMTB hP' (termArgs_typed hb hdom hB hx)
  have hI : ∀ x ∈ termArgs (abiTerm f B.term), x ∈ Compile.termIntOperands B.term →
      γ f (termCtx ctx ti data) aV (.value x) :=
    fun x hx hi => γ_aVT (termArgs_typed hb hdom hB hx) (hP'.termIntOf B hB x hi)
  have hinst : ∀ k fs, γ f (termCtx ctx ti data) (idat k fs) data →
      γ f (termCtx ctx ti data) (termInst k fs) (.inst ti) :=
    fun k fs h => γ_inst hself (γ_ty_mem (by simp)) h (by simp)
  have hTI := termIsel_of hin hB
  generalize B.term = t at hA hI hTI hd hlen
  cases t with
  | ret vs =>
    simp only [abiTerm, termData, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    have hv : vs.length = f.sig.returns.length := by simpa [termIselB] using hTI
    have h8 : f.sig.returns.length ≤ 8 := by
      simp only [driverInB, Bool.and_eq_true, decide_eq_true_eq] at hdrv; exact hdrv.1.2
    have hm := ret_len hv h8
    refine ⟨(TId.lower, [termInst VIdx.InstructionData.MultiAry [opc VIdx.Opcode.Return,
      .vals (List.replicate (vs ++ sretRet f).length aVM)]]), ?_, ⟨_, program_termByName_lower, rfl⟩,
      γL_cons' (hinst _ _ (γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl))
        (γL_cons' (γ_vals (γL_repT fun x hx => hA x (by simpa [abiTerm, termArgs] using hx)))
          γL_nil')))) γL_nil'⟩
    unfold termRootsT; apply List.mem_append_left
    exact List.mem_map.2 ⟨_, List.mem_range.2 (by omega), rfl⟩
  | trap c =>
    simp only [abiTerm, termData, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    refine ⟨(TId.lower, [termInst VIdx.InstructionData.Trap [opc VIdx.Opcode.Trap, .op .trapCode none]]),
      ?_, ⟨_, program_termByName_lower, rfl⟩,
      γL_cons' (hinst _ _ (γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl))
        (γL_cons' (γ_op ⟨c, rfl⟩) γL_nil')))) γL_nil'⟩
    apply mem_termRootsT_mid
    exact List.mem_cons_self
  | jump bc =>
    simp only [abiTerm, termData, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    have hl : targets.length = 1 := by simpa [destsOf] using hlen
    refine ⟨(TId.lower_branch, [termInst VIdx.InstructionData.Jump
      [opc VIdx.Opcode.Jump, .blockCalls 1], .labels 1 (some 1)]), ?_,
      ⟨_, program_termByName_lower_branch, rfl⟩,
      γL_cons' (hinst _ _ (γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl))
        (γL_cons' (γ_blockCalls (bs := [0])) γL_nil'))))
        (γL_cons' (γ_labels (by omega) (.inr (by rw [hl]))) γL_nil')⟩
    apply mem_termRootsT_mid
    exact List.mem_cons_of_mem _ List.mem_cons_self
  | brif c th el =>
    simp only [abiTerm, termData, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    have hl : targets.length = 2 := by simpa [destsOf] using hlen
    refine ⟨(TId.lower_branch, [termInst VIdx.InstructionData.Brif
      [opc VIdx.Opcode.Brif, aV, .blockCalls 2], .labels 2 (some 2)]), ?_,
      ⟨_, program_termByName_lower_branch, rfl⟩,
      γL_cons' (hinst _ _ (γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl))
        (γL_cons' (hI c (by simp [abiTerm, termArgs]) (by simp [Compile.termIntOperands]))
          (γL_cons' (γ_blockCalls (bs := [0, 1])) γL_nil')))))
        (γL_cons' (γ_labels (by omega) (.inr (by rw [hl]))) γL_nil')⟩
    apply mem_termRootsT_mid
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  | brTable x dflt tbl =>
    simp only [abiTerm, termData, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    have hl : targets.length = tbl.length + 1 := by simpa [destsOf] using hlen
    refine ⟨(TId.lower_branch, [termInst VIdx.InstructionData.BranchTable
      [opc VIdx.Opcode.BrTable, aV, .op .jumpTable none], .labels 1 none]), ?_,
      ⟨_, program_termByName_lower_branch, rfl⟩,
      γL_cons' (hinst _ _ (γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl))
        (γL_cons' (hI x (by simp [abiTerm, termArgs]) (by simp [Compile.termIntOperands]))
          (γL_cons' (γ_op ⟨0, rfl⟩) γL_nil')))))
        (γL_cons' (γ_labels (by omega) (.inl rfl)) γL_nil')⟩
    apply mem_termRootsT_mid
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCallIndirect callee args et =>
    simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd

set_option maxRecDepth 100000 in
/-- **A `try_call`'s root**: the driver's `lower_branch` call on a `try_call`/`try_call_indirect`
of `f` (at its placeholder slot, in its context `tryCtx` with the return/payload vregs
`tryRegsOf` allocates, with one target per exception-table item plus the continuation) is a
root of the table whose inputs describe its arguments. -/
theorem try_rootTB {ranges : Array (Nat × Nat)} {st0 : LState} (hP : PInvTB f ctx)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) (hdom : dominatedB f = true)
    (hin : iselInB f = true) {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {t : Clif.Terminator} (ht : ∃ B ∈ f.blocks, B.term = t) {et : Clif.ExnTable}
    (het : exnOf t = some et) {data : V} (hd : tryCallData f t = .ok data) {sig : Clif.Signature}
    {items : List (Option Nat)} (hx : exnTableOpnd f et = .ok (sig, items))
    {trs : List Reg × List Reg} {st1 st2 : LState} (hr : tryRegsOf sig st1 = some (trs, st2))
    {targets : List Label} (hlen : targets.length = items.length + 1) :
    ∃ q ∈ termRootsT, q.1 = TId.lower_branch ∧
      γL f (tryCtx ctx ti data trs) q.2 [.inst ti, .labels targets] := by
  obtain ⟨B, hB, rfl⟩ := ht
  have hP' := pinv_tryCtxTB hP hph data trs
  have hself : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hA : ∀ x ∈ termArgs (abiTerm f B.term), (ctx.valueType? x).isSome :=
    fun x hx => termArgs_typed hb hdom hB hx
  have hTI := termIsel_of hin hB
  obtain ⟨hsig, hil⟩ := exnTableOpnd_inv hx
  generalize B.term = t at hA hTI het hd
  have hT : et.items.length ≤ maxTryItems ∧ SigOk sig := by
    cases t <;> simp only [exnOf, Option.some.injEq, reduceCtorEq] at het <;> subst het <;>
      simp only [termIselB, hsig, Bool.and_eq_true, decide_eq_true_eq] at hTI <;>
      exact ⟨hTI.1, sigOk_of hTI.2⟩
  have hS := hT.2
  have hinst : ∀ k fs, γ f (tryCtx ctx ti data trs) (idat k fs) data →
      γ f (tryCtx ctx ti data trs) (termInst k fs) (.inst ti) :=
    fun k fs h => γ_inst hself (γ_ty_mem (by simp)) h (by simp)
  have hrl : trs.1.length = sig.returns.length := by
    obtain ⟨rets, pays, st', h1, h2, -⟩ :=
      tryRegsOf_ok (s := sig) hS.2 st1
    rw [hr] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, -⟩ := h1
    exact h2
  have hm : items.length ≤ maxTryItems := hil ▸ hT.1
  have hmem : items.length ∈ List.range (maxTryItems + 1) := List.mem_range.2 (by omega)
  have hlab : γ f (tryCtx ctx ti data trs) (.labels (items.length + 1) (some (items.length + 1)))
      (.labels targets) := γ_labels (by omega) (.inr (by rw [hlen]))
  have hexn : γ f (tryCtx ctx ti data trs) (.op .exnTry (some items.length))
      (.op (.exnTable sig items)) := γ_op ⟨sig, items, rfl, hS, hrl, .inr rfl⟩
  cases t with
  | tryCall fn args et' =>
    simp only [exnOf, Option.some.injEq] at het
    subst het
    obtain ⟨ext, he, hes, hdat⟩ := tryCallData_call hd hx
    have hfr : γ f (tryCtx ctx ti data trs) (.op .funcRefTry none) (.op (.funcRef fn)) :=
      γ_op ⟨fn, ext, rfl, by show ctx.func.extern? fn = some ext; rw [hP.ctxInv.func]; exact he,
        hes ▸ hS, by rw [hes]; exact hrl⟩
    refine ⟨(TId.lower_branch, [termInst VIdx.InstructionData.TryCall [opc VIdx.Opcode.TryCall,
      .valsMin 0, .op .funcRefTry none, .op .exnTry (some items.length)],
      .labels (items.length + 1) (some (items.length + 1))]), ?_, rfl,
      γL_cons' (hinst _ _ ?_) (γL_cons' hlab γL_nil')⟩
    · apply mem_termRootsT_try
      exact List.mem_map.2 ⟨_, hmem, rfl⟩
    · subst hdat
      refine γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl)) ?_)
      refine γL_cons' (γ_valsMin (Nat.zero_le _) fun x hx' => hA x (by simp [abiTerm, termArgs, hx'])) ?_
      exact γL_cons' hfr (γL_cons' hexn γL_nil')
  | tryCallIndirect callee args et' =>
    simp only [exnOf, Option.some.injEq] at het
    subst het
    have hdat := tryCallData_ind hd hx
    refine ⟨(TId.lower_branch, [termInst VIdx.InstructionData.TryCallIndirect
      [opc VIdx.Opcode.TryCallIndirect, .valsMin 1, .op .exnTry (some items.length)],
      .labels (items.length + 1) (some (items.length + 1))]), ?_, rfl,
      γL_cons' (hinst _ _ ?_) (γL_cons' hlab γL_nil')⟩
    · apply mem_termRootsT_ind
      exact List.mem_map.2 ⟨_, hmem, rfl⟩
    · subst hdat
      refine γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl)) ?_)
      refine γL_cons' (γ_valsMin (by simp) fun x hx' => hA x ?_) (γL_cons' hexn γL_nil')
      simp only [List.mem_cons] at hx'
      rcases hx' with rfl | hx' <;> simp [abiTerm, termArgs, *]
  | _ => simp [exnOf] at het

/-- **A terminator's root** over the typed scope (`term_rootTB` under `PInvT`). -/
theorem term_rootT {ranges : Array (Nat × Nat)} {st0 : LState} (hP : PInvT f ctx)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) (hdom : dominatedB f = true)
    (hin : iselInB f = true) (hdrv : driverInB f = true) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator}
    (ht : ∃ B ∈ f.blocks, B.term = t) {data : V} (hd : termData (abiTerm f t) = .ok data)
    {targets : List Label} (hlen : targets.length = (destsOf t).length) :
    ∃ q ∈ termRootsT, (∃ T : Term, program.termByName? (termCall t ti targets).1 = some T ∧
      T.id = q.1) ∧ γL f (termCtx ctx ti data) q.2 (termCall t ti targets).2 :=
  term_rootTB hP.toB hb hdom hin hdrv hph ht hd hlen

/-- **A `try_call`'s root** over the typed scope (`try_rootTB` under `PInvT`). -/
theorem try_rootT {ranges : Array (Nat × Nat)} {st0 : LState} (hP : PInvT f ctx)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) (hdom : dominatedB f = true)
    (hin : iselInB f = true) {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {t : Clif.Terminator} (ht : ∃ B ∈ f.blocks, B.term = t) {et : Clif.ExnTable}
    (het : exnOf t = some et) {data : V} (hd : tryCallData f t = .ok data) {sig : Clif.Signature}
    {items : List (Option Nat)} (hx : exnTableOpnd f et = .ok (sig, items))
    {trs : List Reg × List Reg} {st1 st2 : LState} (hr : tryRegsOf sig st1 = some (trs, st2))
    {targets : List Label} (hlen : targets.length = items.length + 1) :
    ∃ q ∈ termRootsT, q.1 = TId.lower_branch ∧
      γL f (tryCtx ctx ti data trs) q.2 [.inst ti, .labels targets] :=
  try_rootTB hP.toB hb hdom hin hph ht het hd hx hr hlen

end

end Backend.Proof.Prg
