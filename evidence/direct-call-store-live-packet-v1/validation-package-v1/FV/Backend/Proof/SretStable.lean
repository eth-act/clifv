import FV.Backend.Proof.LowerSim

/-!
# The `sret` pointer is stable along a CLIF run (S7)

`lowerFunction` appends the entry block's `sret` parameter to every `return` (`sretRet`,
`abiTerm`), so the ABI return register x0 holds that value's CLIF value at the `return`. This
file shows that it is the `sret` argument the function was entered with:

* `sretStableB f` (decided per function; Cranelift's verifier guarantees it for every valid
  function: values are defined once, no branch targets the entry block): the `sretRet f` value
  is below `f.freshValue` (so no `try_call` result binds it), no statement result binds it, no
  block that a terminator may continue at (`runTargets`: branch targets, a `try_call`'s normal
  return) has it as a parameter, and the entry block's parameters are distinct;
* `StOk`: the invariant of every state reachable from the entry (one activation of `f`, no
  callers, at a block's statements or at a `try_call`'s pending normal-return jump, the `sretRet
  f` registers as at entry), `stOk_step`, `stOk_reach`;
* `sretArg f args`: the `sret` argument (empty unless `f` returns its struct pointer);
  `sret_reach`: in every reachable state, `sretRet f` reads `sretArg f args`.
-/

namespace Backend

/-- The `sret` argument of a call of `f` on `args` when `f` returns its struct pointer in x0
(`sigRets`: an `sret` parameter and no returns), else nothing: the ABI return values of `f`
after its CLIF return values, as `sretRet f` lists the corresponding entry-block parameter. -/
def sretArg (f : Clif.Function) (args : List Clif.Val) : List Clif.Val :=
  if sigRets f.sig != f.sig.returns then
    match f.sig.params.findIdx? (·.purpose == .sret) with
    | some i => args[i]?.toList
    | none => []
  else []

end Backend

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- The block ids at which a terminator continues in `Clif.run`: its branch targets, and a
`try_call`'s normal return (the only successor `Clif.run` takes). -/
def runTargets : Clif.Terminator → List Clif.BlockId
  | .tryCall _ _ et => [et.normal.block]
  | .tryCallIndirect _ _ et => [et.normal.block]
  | t => (dests t).map (·.block)

/-- **The `sret` value of `f` is bound once** (decided per function): `sretRet f`'s value is
below `f.freshValue`, no statement result and no parameter of a block a terminator continues at
(`runTargets`) is it, and the entry block's parameters are distinct. -/
def sretStableB (f : Clif.Function) : Bool :=
  (sretRet f).all fun x =>
    decide (x < f.freshValue) &&
    f.blocks.head?.all (fun b0 => decide (b0.params.map (·.1)).Nodup) &&
    f.blocks.all fun B =>
      B.body.all (fun st => !st.results.contains x) &&
      (runTargets B.term).all fun t =>
        (f.block? t).all fun B' => !(B'.params.map (·.1)).contains x

/-- `sretStableB` as a proposition. -/
structure SretStable (f : Clif.Function) : Prop where
  fresh : ∀ x ∈ sretRet f, x < f.freshValue
  entry : ∀ x ∈ sretRet f, ∀ b0, f.blocks.head? = some b0 → (b0.params.map (·.1)).Nodup
  results : ∀ x ∈ sretRet f, ∀ B ∈ f.blocks, ∀ st ∈ B.body, x ∉ st.results
  targets : ∀ x ∈ sretRet f, ∀ B ∈ f.blocks, ∀ t ∈ runTargets B.term, ∀ B',
    f.block? t = some B' → x ∉ B'.params.map (·.1)

theorem sretStable_of {f : Clif.Function} (h : sretStableB f = true) : SretStable f := by
  simp only [sretStableB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨fun x hx => (h x hx).1.1, fun x hx b0 hb0 => ?_, fun x hx B hB st hst hm => ?_,
    fun x hx B hB t ht B' hB' hm => ?_⟩
  · have := (h x hx).1.2
    rw [hb0] at this
    simpa using this
  · have := ((h x hx).2 B hB).1 st hst
    simp [hm] at this
  · have := ((h x hx).2 B hB).2 t ht
    rw [hB'] at this
    simp [hm] at this

theorem runTargets_of_dests {t : Clif.Terminator} {bc : Clif.BlockCall} (h : bc ∈ dests t) :
    bc.block ∈ runTargets t := by
  cases t <;> simp only [runTargets] <;> first | exact List.mem_map_of_mem h | simp [dests] at h

theorem runTargets_of_try {t : Clif.Terminator} {et : Clif.ExnTable} (h : IsTryWith t et) :
    et.normal.block ∈ runTargets t := by
  rcases h with ⟨fn, args, rfl⟩ | ⟨c, args, rfl⟩ <;> simp [runTargets]

/-- The invariant of the states reachable from the entry of `f` (registers `r0`): one
activation of `f` without callers, at statements of a block of `f` (and its terminator) or at a
`try_call`'s pending normal-return jump, with the `sretRet f` registers as in `r0`. -/
structure StOk (f : Clif.Function) (r0 : Clif.Regs) (s : Clif.State) : Prop where
  callers : s.callers = []
  func : s.frame.func = f
  regs : ∀ x ∈ sretRet f, s.frame.regs x = r0 x
  pos : ∃ B ∈ f.blocks, (s.frame.term = B.term ∧ ∀ st ∈ s.frame.body, st ∈ B.body) ∨
    (s.frame.body = [] ∧ ∃ et bc, IsTryWith B.term et ∧ Clif.tryNormal et f.freshValue = .ok bc ∧
      s.frame.term = .jump bc)

/-- Entering a block `f` may continue at keeps the invariant. -/
theorem stOk_enter {f : Clif.Function} {r0 : Clif.Regs} {s : Clif.State} (hS : SretStable f)
    (ho : StOk f r0 s) {B : Clif.Block} (hB : B ∈ f.blocks) {bc : Clif.BlockCall}
    (ht : bc.block ∈ runTargets B.term) {fr2 : Clif.Frame}
    (hent : Clif.enterBlock s.frame bc = .ok fr2) : StOk f r0 { s with frame := fr2 } := by
  obtain ⟨TB, args, regs, hblk, -, -, hset, rfl⟩ := enterBlock_spec hent
  rw [ho.func] at hblk
  have hTB : TB ∈ f.blocks := List.mem_of_find?_eq_some hblk
  refine ⟨ho.callers, ho.func, fun x hx => ?_, TB, hTB, .inl ⟨rfl, fun st hst => hst⟩⟩
  show regs x = r0 x
  rw [setMany_other hset (hS.targets x hx B hB _ ht TB hblk)]
  exact ho.regs x hx

/-- Binding a `try_call`'s results (at `f.freshValue` and above) keeps the `sretRet f`
registers. -/
theorem fresh_not_mem {f : Clif.Function} (hS : SretStable f) {x : Clif.ValueId}
    (hx : x ∈ sretRet f) (n : Nat) : x ∉ (List.range n).map (f.freshValue + ·) := by
  intro hm
  obtain ⟨i, -, hi⟩ := List.mem_map.1 hm
  have hi' : f.freshValue + i = x := hi
  have hlt := hS.fresh x hx
  rw [← hi'] at hlt
  exact Nat.not_lt.mpr (Nat.le_add_right _ _) hlt

/-- **One step keeps the invariant** (calls of `f` call externs, `hext`/`htry` and `RunPrem`'s
indirect-call clauses; no `return_call`, `hnt`). -/
theorem stOk_step {env : Clif.Env} {p : Clif.Program} {f : Clif.Function} {cs : Clif.State}
    (hext : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args, st.inst = .call fn args →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (htry : ∀ B ∈ f.blocks, ∀ fn args et, B.term = .tryCall fn args et →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (hnt : ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args)
    (hP : RunPrem env p f cs) (hS : SretStable f) {r0 : Clif.Regs} {s s' : Clif.State}
    (hr : Reach env p cs s) (ho : StOk f r0 s) (hs : Clif.step env p s = .next s') :
    StOk f r0 s' := by
  obtain ⟨hcall, hfunc, hregs, B, hB, hpos⟩ := ho
  have ho : StOk f r0 s := ⟨hcall, hfunc, hregs, B, hB, hpos⟩
  cases hbody : s.frame.body with
  | cons st rest =>
    obtain ⟨hterm, hbB⟩ : s.frame.term = B.term ∧ ∀ st ∈ s.frame.body, st ∈ B.body := by
      rcases hpos with h | ⟨hb0, -⟩
      · exact h
      · rw [hbody] at hb0; cases hb0
    have hst : st ∈ B.body := hbB st (by rw [hbody]; exact List.mem_cons_self)
    rw [step_stmt env p s st rest hbody
      (fun fn args hi e he => hext B hB st hst fn args hi e (hfunc ▸ he))
      (fun sig callee args hi => hP.indirect s st rest sig callee args hr hbody hi ⟨B, hB, hst⟩)] at hs
    cases hio : instOutcome env p s.frame s.mem st.inst with
    | ok r =>
      obtain ⟨vals, mem⟩ := r
      rw [hio] at hs
      simp only [Clif.StepResult.ofRes_ok, Clif.continueWith] at hs
      split at hs
      · rename_i regs hset
        simp only [Clif.StepResult.next.injEq] at hs
        subst hs
        refine ⟨hcall, hfunc, fun x hx => ?_, B, hB, .inl ⟨hterm, fun st' hst' => hbB st' ?_⟩⟩
        · show regs x = r0 x
          rw [setMany_other hset (hS.results x hx B hB st hst)]
          exact hregs x hx
        · rw [hbody]; exact List.mem_cons_of_mem _ hst'
      · cases hs
    | trap c => rw [hio] at hs; cases hs
    | stuck m => rw [hio] at hs; cases hs
  | nil =>
    rw [Clif.step_term env p s hbody] at hs
    rcases hpos with ⟨hterm, -⟩ | ⟨-, et, bc, hT, htn, hterm⟩
    · rw [hterm] at hs
      cases hT : B.term with
      | jump bc0 =>
        rw [hT] at hs
        obtain ⟨j, bc, fr2, -, hbc, hent, rfl⟩ := stepTerm_branch (by simp [dests]) hs
        exact stOk_enter hS ho hB (runTargets_of_dests (hT ▸ List.mem_of_getElem? hbc)) hent
      | brif c t e =>
        rw [hT] at hs
        obtain ⟨j, bc, fr2, -, hbc, hent, rfl⟩ := stepTerm_branch (by simp [dests]) hs
        exact stOk_enter hS ho hB (runTargets_of_dests (hT ▸ List.mem_of_getElem? hbc)) hent
      | brTable x d tbl =>
        rw [hT] at hs
        obtain ⟨j, bc, fr2, -, hbc, hent, rfl⟩ := stepTerm_branch (by simp [dests]) hs
        exact stOk_enter hS ho hB (runTargets_of_dests (hT ▸ List.mem_of_getElem? hbc)) hent
      | ret xs =>
        rw [hT] at hs
        exact absurd hs ((stepTerm_ret hcall).1 s')
      | returnCall fn args => exact absurd hT (hnt B hB fn args)
      | trap c => rw [hT] at hs; simp [Clif.stepTerm] at hs
      | tryCall fn args et =>
        rw [hT] at hs
        obtain ⟨ext, bc, rvals, cm', regs', -, htn, -, hset, rfl⟩ :=
          (stepTry_spec (fun e he => htry B hB fn args et hT e (hfunc ▸ he))).2 s' hs
        rw [hfunc] at htn hset
        refine ⟨hcall, hfunc, fun x hx => ?_, B, hB, .inr ⟨rfl, et, bc, .inl ⟨fn, args, hT⟩, htn, rfl⟩⟩
        show regs' x = r0 x
        rw [setMany_other hset (fresh_not_mem hS hx _)]
        exact hregs x hx
      | tryCallIndirect callee args et =>
        rw [hT] at hs
        obtain ⟨d, bc, rvals, cm', regs', -, htn, -, hset, rfl⟩ :=
          (stepTryInd_spec (fun cv hcv g hg => hP.tryIndirect s callee args et hr hbody
            (hterm.trans hT) ⟨B, hB, hT⟩ cv hcv g hg)).2 s' hs
        rw [hfunc] at htn hset
        refine ⟨hcall, hfunc, fun x hx => ?_, B, hB,
          .inr ⟨rfl, et, bc, .inr ⟨callee, args, hT⟩, htn, rfl⟩⟩
        show regs' x = r0 x
        rw [setMany_other hset (fresh_not_mem hS hx _)]
        exact hregs x hx
    · rw [hterm] at hs
      simp only [Clif.stepTerm] at hs
      cases hent : Clif.enterBlock s.frame bc with
      | ok fr2 =>
        rw [hent] at hs
        simp only [Clif.StepResult.ofRes_ok, Clif.StepResult.next.injEq] at hs
        subst hs
        have hbk : bc.block = et.normal.block := by rw [tryNormal_ok htn]
        exact stOk_enter hS ho hB (hbk ▸ runTargets_of_try hT) hent
      | trap c => rw [hent] at hs; cases hs
      | stuck m => rw [hent] at hs; cases hs

/-- **Every reachable state keeps the invariant.** -/
theorem stOk_reach {env : Clif.Env} {p : Clif.Program} {f : Clif.Function} {cs : Clif.State}
    (hext : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args, st.inst = .call fn args →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (htry : ∀ B ∈ f.blocks, ∀ fn args et, B.term = .tryCall fn args et →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (hnt : ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args)
    (hP : RunPrem env p f cs) (hS : SretStable f) {r0 : Clif.Regs} (h0 : StOk f r0 cs) :
    ∀ s, Reach env p cs s → StOk f r0 s := by
  suffices key : ∀ a b, Reach env p a b → Reach env p cs a → StOk f r0 a → StOk f r0 b from
    fun s h => key cs s h (.refl _) h0
  intro a b h
  induction h with
  | refl => exact fun _ h => h
  | step hs _ ih => exact fun hca hoa => ih (hca.snoc hs) (stOk_step hext htry hnt hP hS hca hoa hs)

/-- At the entry, `sretRet f` reads the `sret` argument. -/
theorem getMany_sretRet_entry {f : Clif.Function} (hS : SretStable f) {B0 : Clif.Block}
    (hB0 : f.blocks[0]? = some B0) {args : List Clif.Val} {fr : Clif.Frame}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some fr.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2)) :
    fr.getMany (sretRet f) = .ok (sretArg f args) := by
  have hhd : f.blocks.head? = some B0 := by rw [List.head?_eq_getElem?]; exact hB0
  have hlen : args.length = B0.params.length := by
    have := congrArg List.length hty
    simpa using this
  unfold sretArg
  by_cases hne : (sigRets f.sig != f.sig.returns) = true
  · rw [if_pos hne]
    cases hi : f.sig.params.findIdx? (·.purpose == .sret) with
    | none =>
      have hsr : sretRet f = [] := by unfold sretRet; rw [if_pos hne, hhd, hi]
      simp only [hsr]; rfl
    | some i =>
      simp only
      cases hp : B0.params[i]? with
      | none =>
        have hsr : sretRet f = [] := by unfold sretRet; rw [if_pos hne, hhd, hi]; simp [hp]
        have : args[i]? = none := by
          rw [List.getElem?_eq_none_iff]
          rw [List.getElem?_eq_none_iff] at hp
          omega
        simp [hsr, this, Clif.Frame.getMany]
      | some q =>
        have hsr : sretRet f = [q.1] := by unfold sretRet; rw [if_pos hne, hhd, hi]; simp [hp]
        have hlt : i < args.length := by
          rw [hlen]; exact (List.getElem?_eq_some_iff.mp hp).1
        obtain ⟨v, hv⟩ : ∃ v, args[i]? = some v := ⟨args[i], List.getElem?_eq_getElem hlt⟩
        have hnd := hS.entry q.1 (by rw [hsr]; exact List.mem_singleton_self _) B0 hhd
        have hx := setMany_nodup hregs hnd i q.1 v (by simp [hp]) hv
        simp [hsr, hv, Clif.Frame.getMany, Clif.Frame.get, hx]
  · have hsr : sretRet f = [] := by unfold sretRet; rw [if_neg hne]
    rw [if_neg hne, hsr]; rfl

/-- **In every state reachable from the entry, `sretRet f` reads the `sret` argument.** -/
theorem sret_reach {env : Clif.Env} {p : Clif.Program} {f : Clif.Function} {cs : Clif.State}
    (hext : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args, st.inst = .call fn args →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (htry : ∀ B ∈ f.blocks, ∀ fn args et, B.term = .tryCall fn args et →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (hnt : ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args)
    (hP : RunPrem env p f cs) (hS : sretStableB f = true) {B0 : Clif.Block}
    (hB0 : f.blocks[0]? = some B0) (hcall : cs.callers = []) (hfunc : cs.frame.func = f)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2)) :
    ∀ s sv, Reach env p cs s → s.frame.getMany (sretRet f) = .ok sv → sv = sretArg f args := by
  have hS' := sretStable_of hS
  have h0 : StOk f cs.frame.regs cs :=
    ⟨hcall, hfunc, fun _ _ => rfl, B0, List.mem_of_getElem? hB0,
      .inl ⟨hterm, fun st hst => hbody ▸ hst⟩⟩
  intro s sv hr hsv
  have ho := stOk_reach hext htry hnt hP hS' h0 s hr
  rw [getMany_congr ho.regs, getMany_sretRet_entry hS' hB0 hregs hty] at hsv
  exact (Clif.Res.ok.inj hsv).symm

/-- A returned run ends with a step that returns, from a reachable state. -/
theorem runLoop_returned_reach {env : Clif.Env} {p : Clif.Program} {vals : List Clif.Val}
    {cm : Clif.Mem} : ∀ fuel s, Clif.runLoop env p fuel s = .returned vals cm →
      ∃ s', Reach env p s s' ∧ Clif.step env p s' = .done vals cm
  | 0, _, h => by cases h
  | fuel + 1, s, h => by
    rw [Clif.runLoop_succ] at h
    cases hs : Clif.step env p s with
    | next s' =>
      rw [hs] at h
      obtain ⟨s'', hr, hd⟩ := runLoop_returned_reach fuel s' h
      exact ⟨s'', .step hs hr, hd⟩
    | done vals' cm' =>
      rw [hs] at h
      cases h
      exact ⟨s, .refl _, hs⟩
    | trapped c => rw [hs] at h; cases h
    | stuck m => rw [hs] at h; cases h

/-- A `return` returns values of the function's return types. -/
theorem stepTerm_ret_sigTys {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    {xs : List Clif.ValueId} {vals : List Clif.Val} {cm : Clif.Mem}
    (h : Clif.stepTerm env p s (.ret xs) = .done vals cm) :
    vals.map (·.ty) = Clif.AbiParam.tys s.frame.func.sig.returns := by
  simp only [Clif.stepTerm] at h
  cases hg : s.frame.getMany xs with
  | ok vs =>
    rw [hg] at h
    simp only [Clif.StepResult.ofRes_ok, Clif.returnValues] at h
    rcases checkTys_cases s!"return values of %{s.frame.func.name}" vs
      (Clif.AbiParam.tys s.frame.func.sig.returns) with ⟨hc, hty⟩ | ⟨m, hc⟩
    · rw [hc] at h
      simp only [Clif.StepResult.ofRes_ok] at h
      split at h
      · cases h; exact hty
      · split at h <;> cases h
    · rw [hc] at h; cases h
  | trap c => rw [hg] at h; cases h
  | stuck m => rw [hg] at h; cases h

/-- **A run of `f` from its entry returns values of `f`'s return types** (the run stays in
`f`'s activation, `StOk`). -/
theorem runLoop_returned_tys_entry {env : Clif.Env} {p : Clif.Program} {f : Clif.Function}
    {cs : Clif.State}
    (hext : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args, st.inst = .call fn args →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (htry : ∀ B ∈ f.blocks, ∀ fn args et, B.term = .tryCall fn args et →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (hnt : ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args)
    (hP : RunPrem env p f cs) (hS : SretStable f) {B0 : Clif.Block}
    (hB0 : f.blocks[0]? = some B0) (hcall : cs.callers = []) (hfunc : cs.frame.func = f)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term)
    {fuel : Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned vals cm) :
    vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns := by
  have h0 : StOk f cs.frame.regs cs :=
    ⟨hcall, hfunc, fun _ _ => rfl, B0, List.mem_of_getElem? hB0,
      .inl ⟨hterm, fun st hst => hbody ▸ hst⟩⟩
  obtain ⟨s, hr, hd⟩ := runLoop_returned_reach fuel cs hrun
  obtain ⟨hcall', hfunc', -, B, hB, hpos⟩ := stOk_reach hext htry hnt hP hS h0 s hr
  cases hbody' : s.frame.body with
  | cons st rest =>
    obtain ⟨-, hbB⟩ : s.frame.term = B.term ∧ ∀ st ∈ s.frame.body, st ∈ B.body := by
      rcases hpos with h | ⟨hb0, -⟩
      · exact h
      · rw [hbody'] at hb0; cases hb0
    have hst : st ∈ B.body := hbB st (by rw [hbody']; exact List.mem_cons_self)
    exact absurd hd (stmt_not_done hbody'
      (fun fn args hi e he => hext B hB st hst fn args hi e (hfunc' ▸ he))
      (fun sig callee args hi => hP.indirect s st rest sig callee args hr hbody' hi ⟨B, hB, hst⟩))
  | nil =>
    rw [Clif.step_term env p s hbody'] at hd
    rcases hpos with ⟨hterm', -⟩ | ⟨-, et, bc, -, -, hterm'⟩
    · rw [hterm'] at hd
      cases hT : B.term with
      | ret xs => rw [hT] at hd; rw [← hfunc']; exact stepTerm_ret_sigTys hd
      | jump bc0 =>
        rw [hT] at hd; exact absurd hd ((stepTerm_branch_ne (by simp [dests])).1 vals cm)
      | brif c t e =>
        rw [hT] at hd; exact absurd hd ((stepTerm_branch_ne (by simp [dests])).1 vals cm)
      | brTable x d tbl =>
        rw [hT] at hd; exact absurd hd ((stepTerm_branch_ne (by simp [dests])).1 vals cm)
      | returnCall fn args => exact absurd hT (hnt B hB fn args)
      | trap c => rw [hT] at hd; simp [Clif.stepTerm] at hd
      | tryCall fn args et =>
        rw [hT] at hd
        exact absurd hd ((stepTry_spec (fun e he => htry B hB fn args et hT e (hfunc' ▸ he))).1 vals cm)
      | tryCallIndirect callee args et =>
        rw [hT] at hd
        exact absurd hd ((stepTryInd_spec (fun cv hcv g hg => hP.tryIndirect s callee args et hr
          hbody' (hterm'.trans hT) ⟨B, hB, hT⟩ cv hcv g hg)).1 vals cm)
    · rw [hterm'] at hd
      exact absurd hd ((stepTerm_branch_ne (t := .jump bc) (by simp [dests])).1 vals cm)

end Backend.Proof.Driver
