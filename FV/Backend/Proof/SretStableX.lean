module

public import FV.Backend.Proof.SretStable
public import FV.Backend.Proof.LowerSimU

@[expose] public section

/-!
# The `sret` pointer is stable along a CLIF run with unwinding (S7)

`SretStable.lean`'s invariant for the runs with unwinding (`Clif.stepX`, `E2E.ReachX`). A caught
exception continues at a `try_call`'s handler block (`Clif.catchIn`: the payload bound at
`f.freshValue` and above, then the pending `jump` to the handler), which `sretStableB` does not
check (its `runTargets` are the successors `Clif.run` takes). Hence the stronger check:

* `exnTargets`: the handler blocks of a `try_call`/`try_call_indirect` terminator;
* `sretStableXB f` (decided per function; Cranelift's verifier guarantees it for every valid
  function): `sretStableB f`, and no handler block has the `sretRet f` value as a parameter;
* `StOkX`: the invariant of every state reachable with unwinding (one activation of `f`, no
  callers, at a block's statements or at a pending `jump` to a normal-return or handler block,
  the `sretRet f` registers as at entry), `stOkX_step` (a `Clif.step`), `stOkX_stepX` (a
  `Clif.stepX`, a caught exception included), `stOkX_reach`;
* `sret_reachX`: in every state reachable with unwinding, `sretRet f` reads `sretArg f args`;
* `runLoopX_returned_tys_entry`: a returned run with unwinding returns values of `f`'s return
  types.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- The handler blocks of a `try_call`/`try_call_indirect` terminator (the blocks a caught
exception continues at, `Clif.catchIn`). -/
def exnTargets : Clif.Terminator → List Clif.BlockId
  | .tryCall _ _ et => et.handlers.map (·.block)
  | .tryCallIndirect _ _ et => et.handlers.map (·.block)
  | _ => []

/-- **The `sret` value of `f` is bound once, also on the exceptional edges** (decided per
function): `sretStableB f`, and no handler block of a terminator (`exnTargets`) has the
`sretRet f` value as a parameter. -/
def sretStableXB (f : Clif.Function) : Bool :=
  sretStableB f && (sretRet f).all fun x =>
    f.blocks.all fun B =>
      (exnTargets B.term).all fun t =>
        (f.block? t).all fun B' => !(B'.params.map (·.1)).contains x

/-- `sretStableXB` as a proposition. -/
structure SretStableX (f : Clif.Function) : Prop where
  base : SretStable f
  exn : ∀ x ∈ sretRet f, ∀ B ∈ f.blocks, ∀ t ∈ exnTargets B.term, ∀ B',
    f.block? t = some B' → x ∉ B'.params.map (·.1)

theorem sretStableB_of_X {f : Clif.Function} (h : sretStableXB f = true) : sretStableB f = true := by
  simp only [sretStableXB, Bool.and_eq_true] at h
  exact h.1

theorem sretStableX_of {f : Clif.Function} (h : sretStableXB f = true) : SretStableX f := by
  refine ⟨sretStable_of (sretStableB_of_X h), fun x hx B hB t ht B' hB' hm => ?_⟩
  simp only [sretStableXB, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 x hx B hB t ht
  rw [hB'] at this
  simp [hm] at this

/-- The blocks a pending `jump` of the invariant may target: the successors `Clif.run` takes and
the handler blocks. -/
def runTargetsX (t : Clif.Terminator) : List Clif.BlockId := runTargets t ++ exnTargets t

/-- The invariant of the states reachable with unwinding from the entry of `f` (registers
`r0`): one activation of `f` without callers, at statements of a block of `f` (and its
terminator) or at a pending `jump` to a block a terminator of that block continues at
(`runTargetsX`: a `try_call`'s normal return or handler), with the `sretRet f` registers as in
`r0`. -/
structure StOkX (f : Clif.Function) (r0 : Clif.Regs) (s : Clif.State) : Prop where
  callers : s.callers = []
  func : s.frame.func = f
  regs : ∀ x ∈ sretRet f, s.frame.regs x = r0 x
  pos : ∃ B ∈ f.blocks, (s.frame.term = B.term ∧ ∀ st ∈ s.frame.body, st ∈ B.body) ∨
    (s.frame.body = [] ∧ ∃ bc, s.frame.term = .jump bc ∧ bc.block ∈ runTargetsX B.term)

/-- Entering a block `f` may continue at (with unwinding) keeps the invariant. -/
theorem stOkX_enter {f : Clif.Function} {r0 : Clif.Regs} {s : Clif.State} (hS : SretStableX f)
    (ho : StOkX f r0 s) {B : Clif.Block} (hB : B ∈ f.blocks) {bc : Clif.BlockCall}
    (ht : bc.block ∈ runTargetsX B.term) {fr2 : Clif.Frame}
    (hent : Clif.enterBlock s.frame bc = .ok fr2) : StOkX f r0 { s with frame := fr2 } := by
  obtain ⟨TB, args, regs, hblk, -, -, hset, rfl⟩ := enterBlock_spec hent
  rw [ho.func] at hblk
  have hTB : TB ∈ f.blocks := List.mem_of_find?_eq_some hblk
  refine ⟨ho.callers, ho.func, fun x hx => ?_, TB, hTB, .inl ⟨rfl, fun st hst => hst⟩⟩
  show regs x = r0 x
  have hnm : x ∉ TB.params.map (·.1) := by
    rcases List.mem_append.mp ht with h | h
    · exact hS.base.targets x hx B hB _ h TB hblk
    · exact hS.exn x hx B hB _ h TB hblk
  rw [setMany_other hset hnm]
  exact ho.regs x hx

/-- **One `Clif.step` keeps the invariant** (calls of `f` call externs, `hext`/`htry`; no
`return_call`, `hnt`; the indirect calls of the state call no function of `p`, `hind`/`htind`). -/
theorem stOkX_step {env : Clif.Env} {p : Clif.Program} {f : Clif.Function}
    (hext : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args, st.inst = .call fn args →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (htry : ∀ B ∈ f.blocks, ∀ fn args et, B.term = .tryCall fn args et →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (hnt : ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args)
    (hS : SretStableX f) {r0 : Clif.Regs} {s s' : Clif.State}
    (hind : ∀ st rest sig callee args, s.frame.body = st :: rest →
      st.inst = .callIndirect sig callee args → (∃ B ∈ f.blocks, st ∈ B.body) → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat)
    (htind : ∀ callee args et, s.frame.body = [] →
      s.frame.term = .tryCallIndirect callee args et →
      (∃ B ∈ f.blocks, B.term = .tryCallIndirect callee args et) → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat)
    (ho : StOkX f r0 s) (hs : Clif.step env p s = .next s') :
    StOkX f r0 s' := by
  obtain ⟨hcall, hfunc, hregs, B, hB, hpos⟩ := ho
  have ho : StOkX f r0 s := ⟨hcall, hfunc, hregs, B, hB, hpos⟩
  cases hbody : s.frame.body with
  | cons st rest =>
    obtain ⟨hterm, hbB⟩ : s.frame.term = B.term ∧ ∀ st ∈ s.frame.body, st ∈ B.body := by
      rcases hpos with h | ⟨hb0, -⟩
      · exact h
      · rw [hbody] at hb0; cases hb0
    have hst : st ∈ B.body := hbB st (by rw [hbody]; exact List.mem_cons_self)
    rw [step_stmt env p s st rest hbody
      (fun fn args hi e he => hext B hB st hst fn args hi e (hfunc ▸ he))
      (fun sig callee args hi => hind st rest sig callee args hbody hi ⟨B, hB, hst⟩)] at hs
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
          rw [setMany_other hset (hS.base.results x hx B hB st hst)]
          exact hregs x hx
        · rw [hbody]; exact List.mem_cons_of_mem _ hst'
      · cases hs
    | trap c => rw [hio] at hs; cases hs
    | stuck m => rw [hio] at hs; cases hs
  | nil =>
    rw [Clif.step_term env p s hbody] at hs
    rcases hpos with ⟨hterm, -⟩ | ⟨-, bc, hterm, hbc⟩
    · rw [hterm] at hs
      have hrt : ∀ {bc : Clif.BlockCall}, bc ∈ dests B.term → bc.block ∈ runTargetsX B.term :=
        fun h => List.mem_append_left _ (runTargets_of_dests h)
      cases hT : B.term with
      | jump bc0 =>
        rw [hT] at hs
        obtain ⟨j, bc, fr2, -, hbc, hent, rfl⟩ := stepTerm_branch (by simp [dests]) hs
        exact stOkX_enter hS ho hB (hrt (hT ▸ List.mem_of_getElem? hbc)) hent
      | brif c t e =>
        rw [hT] at hs
        obtain ⟨j, bc, fr2, -, hbc, hent, rfl⟩ := stepTerm_branch (by simp [dests]) hs
        exact stOkX_enter hS ho hB (hrt (hT ▸ List.mem_of_getElem? hbc)) hent
      | brTable x d tbl =>
        rw [hT] at hs
        obtain ⟨j, bc, fr2, -, hbc, hent, rfl⟩ := stepTerm_branch (by simp [dests]) hs
        exact stOkX_enter hS ho hB (hrt (hT ▸ List.mem_of_getElem? hbc)) hent
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
        have hbk : bc.block = et.normal.block := by rw [tryNormal_ok htn]
        refine ⟨hcall, hfunc, fun x hx => ?_, B, hB, .inr ⟨rfl, bc, rfl,
          List.mem_append_left _ (hbk ▸ runTargets_of_try (.inl ⟨fn, args, hT⟩))⟩⟩
        show regs' x = r0 x
        rw [setMany_other hset (fresh_not_mem hS.base hx _)]
        exact hregs x hx
      | tryCallIndirect callee args et =>
        rw [hT] at hs
        obtain ⟨d, bc, rvals, cm', regs', -, htn, -, hset, rfl⟩ :=
          (stepTryInd_spec (fun cv hcv g hg => htind callee args et hbody
            (hterm.trans hT) ⟨B, hB, hT⟩ cv hcv g hg)).2 s' hs
        rw [hfunc] at htn hset
        have hbk : bc.block = et.normal.block := by rw [tryNormal_ok htn]
        refine ⟨hcall, hfunc, fun x hx => ?_, B, hB, .inr ⟨rfl, bc, rfl,
          List.mem_append_left _ (hbk ▸ runTargets_of_try (.inr ⟨callee, args, hT⟩))⟩⟩
        show regs' x = r0 x
        rw [setMany_other hset (fresh_not_mem hS.base hx _)]
        exact hregs x hx
    · rw [hterm] at hs
      simp only [Clif.stepTerm] at hs
      cases hent : Clif.enterBlock s.frame bc with
      | ok fr2 =>
        rw [hent] at hs
        simp only [Clif.StepResult.ofRes_ok, Clif.StepResult.next.injEq] at hs
        subst hs
        exact stOkX_enter hS ho hB hbc hent
      | trap c => rw [hent] at hs; cases hs
      | stuck m => rw [hent] at hs; cases hs

/-- A handler block call's block is the handler's. -/
theorem tryHandler_block {d : Clif.TryDest} {base : Clif.ValueId} {bc : Clif.BlockCall}
    (h : Clif.tryHandler d base = .ok bc) : bc.block = d.block := by
  have key : ∀ r : Clif.Res (List Clif.ValueId),
      (r >>= fun args => (pure { block := d.block, args } : Clif.Res Clif.BlockCall)) = .ok bc →
      bc.block = d.block := by
    intro r hr
    cases r with
    | ok a => cases hr; rfl
    | trap c => cases hr
    | stuck m => cases hr
  exact key _ h

/-- A handler that catches `e` is one of the table's handlers. -/
theorem catch?_mem_handlers {et : Clif.ExnTable} {e : Clif.Exn} {d : Clif.TryDest}
    (h : et.catch? e = some d) : d ∈ et.handlers := by
  unfold Clif.ExnTable.catch? at h
  unfold Clif.ExnTable.handlers
  obtain ⟨a, ha, hfa⟩ := List.exists_of_findSome?_eq_some h
  rw [List.mem_filterMap]
  refine ⟨a, ha, ?_⟩
  cases a with
  | tag n d' =>
    simp only at hfa ⊢
    split at hfa
    · exact hfa
    · cases hfa
  | default d' => simpa using hfa
  | context v => simp at hfa

/-- **One `Clif.stepX` keeps the invariant**: a step of `Clif.step` (`stOkX_step`), or an
exception caught by the state's own `try_call` (the payload bound above `f.freshValue`, the
pending `jump` to a handler block); with no callers an uncaught exception does not continue. -/
theorem stOkX_stepX {env : Clif.XEnv} {p : Clif.Program} {f : Clif.Function}
    (hext : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args, st.inst = .call fn args →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (htry : ∀ B ∈ f.blocks, ∀ fn args et, B.term = .tryCall fn args et →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (hnt : ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args)
    (hS : SretStableX f) {r0 : Clif.Regs} {xs xs' : Clif.XState}
    (hind : ∀ st rest sig callee args, xs.s.frame.body = st :: rest →
      st.inst = .callIndirect sig callee args → (∃ B ∈ f.blocks, st ∈ B.body) → ∀ cv,
      xs.s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, xs.s.mem.symbols g.name ≠ some cv.toNat)
    (htind : ∀ callee args et, xs.s.frame.body = [] →
      xs.s.frame.term = .tryCallIndirect callee args et →
      (∃ B ∈ f.blocks, B.term = .tryCallIndirect callee args et) → ∀ cv,
      xs.s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, xs.s.mem.symbols g.name ≠ some cv.toNat)
    (ho : StOkX f r0 xs.s) (hs : Clif.stepX env p xs = .next xs') :
    StOkX f r0 xs'.s := by
  cases hra : Clif.raiseAt? env p xs.s with
  | none => exact stOkX_step hext htry hnt hS hind htind ho (stepX_next_inv hra hs)
  | some em =>
    obtain ⟨e, m⟩ := em
    simp only [Clif.stepX, hra, Clif.raiseIn] at hs
    cases hpend : Clif.pendingOf xs.s with
    | none =>
      simp [hpend, ho.callers, Clif.unwindFrom] at hs
    | some et =>
      cases hc : Clif.catchIn xs.s.frame et e with
      | none => simp [hpend, hc, ho.callers, Clif.unwindFrom] at hs
      | some r =>
        simp only [hpend, hc, Option.bind_some] at hs
        cases r with
        | trap c => cases hs
        | stuck msg => cases hs
        | ok fr =>
          simp only [Clif.XStepResult.ofRes, Clif.XStepResult.next.injEq] at hs
          subst hs
          -- the state is at its `try_call` with table `et`
          obtain ⟨hb0, hT⟩ : xs.s.frame.body = [] ∧ IsTryWith xs.s.frame.term et := by
            unfold Clif.pendingOf at hpend
            split at hpend
            · cases hpend; rename_i h1 h2; exact ⟨h1, .inl ⟨_, _, h2⟩⟩
            · cases hpend; rename_i h1 h2; exact ⟨h1, .inr ⟨_, _, h2⟩⟩
            · cases hpend
          obtain ⟨hcall, hfunc, hregs, B, hB, hpos⟩ := ho
          have hTB : IsTryWith B.term et := by
            rcases hpos with ⟨hterm, -⟩ | ⟨-, bc, hterm, -⟩
            · exact hterm ▸ hT
            · rcases hT with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [hterm] at h <;> cases h
          -- the caught frame
          unfold Clif.catchIn at hc
          cases hd : et.catch? e with
          | none => rw [hd] at hc; cases hc
          | some d =>
            rw [hd] at hc
            simp only [Option.map_some, Option.some.injEq] at hc
            cases hth : Clif.tryHandler d xs.s.frame.func.freshValue with
            | trap c => rw [hth] at hc; cases hc
            | stuck msg => rw [hth] at hc; cases hc
            | ok bc =>
              rw [hth] at hc
              cases hset : xs.s.frame.regs.setMany
                  ((List.range e.payload.length).map (xs.s.frame.func.freshValue + ·)) e.payload with
              | none => simp [hset, Clif.Res.ofOption] at hc
              | some regs =>
                simp only [hset, Clif.Res.ofOption, Clif.Res.ok_bind, Clif.Res.pure_eq,
                  Clif.Res.ok.injEq] at hc
                subst hc
                rw [hfunc] at hset
                have hbk : bc.block ∈ exnTargets B.term := by
                  rw [tryHandler_block hth]
                  rcases hTB with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] <;>
                    exact List.mem_map_of_mem (catch?_mem_handlers hd)
                refine ⟨hcall, hfunc, fun x hx => ?_, B, hB,
                  .inr ⟨rfl, bc, rfl, List.mem_append_right _ hbk⟩⟩
                show regs x = r0 x
                rw [setMany_other hset (fresh_not_mem hS.base hx _)]
                exact hregs x hx

/-- **Every state reachable with unwinding keeps the invariant** (the indirect-call premises of
`TrapsExplicitX`). -/
theorem stOkX_reach {env : Clif.XEnv} {p : Clif.Program} {f : Clif.Function} {cs : Clif.State}
    (hext : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args, st.inst = .call fn args →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (htry : ∀ B ∈ f.blocks, ∀ fn args et, B.term = .tryCall fn args et →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (hnt : ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args)
    (htr : E2E.TrapsExplicitX env p cs) (hcf : cs.frame.func = f) (hS : SretStableX f)
    {r0 : Clif.Regs} (h0 : StOkX f r0 cs) :
    ∀ xs, E2E.ReachX env p cs.toX xs → StOkX f r0 xs.s := by
  suffices key : ∀ a b, E2E.ReachX env p a b → E2E.ReachX env p cs.toX a → StOkX f r0 a.s →
      StOkX f r0 b.s from
    fun xs h => key cs.toX xs h (.refl _) h0
  intro a b h
  induction h with
  | refl => exact fun _ h => h
  | step hs _ ih =>
    exact fun hca hoa => ih (hca.snoc hs) (stOkX_stepX hext htry hnt hS
      (fun st rest sig callee args hb hi hB => htr.indirect _ st rest sig callee args hca hb hi
        (hcf ▸ hB))
      (fun callee args et hb ht hB => htr.tryIndirect _ callee args et hca hb ht (hcf ▸ hB))
      hoa hs)

/-- The entry state satisfies the invariant. -/
theorem stOkX_entry {f : Clif.Function} {cs : Clif.State} {B0 : Clif.Block}
    (hB0 : f.blocks[0]? = some B0) (hcall : cs.callers = []) (hfunc : cs.frame.func = f)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) :
    StOkX f cs.frame.regs cs :=
  ⟨hcall, hfunc, fun _ _ => rfl, B0, List.mem_of_getElem? hB0,
    .inl ⟨hterm, fun _ hst => hbody ▸ hst⟩⟩

/-- **In every state reachable with unwinding from the entry, `sretRet f` reads the `sret`
argument.** -/
theorem sret_reachX {env : Clif.XEnv} {p : Clif.Program} {f : Clif.Function} {cs : Clif.State}
    (hext : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args, st.inst = .call fn args →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (htry : ∀ B ∈ f.blocks, ∀ fn args et, B.term = .tryCall fn args et →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (hnt : ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args)
    (htr : E2E.TrapsExplicitX env p cs) (hS : sretStableXB f = true) {B0 : Clif.Block}
    (hB0 : f.blocks[0]? = some B0) (hcall : cs.callers = []) (hfunc : cs.frame.func = f)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2)) :
    ∀ xs sv, E2E.ReachX env p cs.toX xs → xs.s.frame.getMany (sretRet f) = .ok sv →
      sv = sretArg f args := by
  have hS' := sretStableX_of hS
  intro xs sv hr hsv
  have ho := stOkX_reach hext htry hnt htr hfunc hS' (stOkX_entry hB0 hcall hfunc hbody hterm) xs hr
  rw [getMany_congr ho.regs, getMany_sretRet_entry hS'.base hB0 hregs hty] at hsv
  exact (Clif.Res.ok.inj hsv).symm

/-- A returned run with unwinding ends with a step that returns, from a reachable state. -/
theorem runLoopX_returned_reach {env : Clif.XEnv} {p : Clif.Program} {vals : List Clif.Val}
    {cm : Clif.Mem} : ∀ fuel xs, Clif.runLoopX env p fuel xs = .returned vals cm →
      ∃ xs', E2E.ReachX env p xs xs' ∧ Clif.stepX env p xs' = .done vals cm
  | 0, _, h => by cases h
  | fuel + 1, xs, h => by
    cases hs : Clif.stepX env p xs with
    | next xs' =>
      rw [runLoopX_next hs] at h
      obtain ⟨xs'', hr, hd⟩ := runLoopX_returned_reach fuel xs' h
      exact ⟨xs'', .step hs hr, hd⟩
    | done vals' cm' =>
      rw [runLoopX_done hs] at h
      cases h
      exact ⟨xs, .refl _, hs⟩
    | unwound e cm' => rw [runLoopX_unwound hs] at h; cases h
    | trapped c => rw [runLoopX_trapped hs] at h; cases h
    | stuck m => rw [runLoopX_stuck hs] at h; cases h

/-- A step with unwinding that returns is a `Clif.step` that returns. -/
theorem stepX_done_inv {env : Clif.XEnv} {p : Clif.Program} {xs : Clif.XState}
    {vals : List Clif.Val} {cm : Clif.Mem} (hc : xs.s.callers = [])
    (h : Clif.stepX env p xs = .done vals cm) : Clif.step env.toEnv p xs.s = .done vals cm := by
  cases hra : Clif.raiseAt? env p xs.s with
  | none =>
    simp only [Clif.stepX, hra] at h
    cases hs : Clif.step env.toEnv p xs.s <;> rw [hs] at h <;> simp [Clif.liftStep] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | some em =>
    obtain ⟨e, m⟩ := em
    simp only [Clif.stepX, hra, Clif.raiseIn] at h
    cases hpend : (Clif.pendingOf xs.s).bind (Clif.catchIn xs.s.frame · e) with
    | none => simp [hpend, hc, Clif.unwindFrom] at h
    | some r =>
      rw [hpend] at h
      cases r <;> simp [Clif.XStepResult.ofRes] at h

/-- **A run with unwinding of `f` from its entry returns values of `f`'s return types**
(`runLoop_returned_tys_entry`'s counterpart; the run stays in `f`'s activation, `StOkX`). -/
theorem runLoopX_returned_tys_entry {env : Clif.XEnv} {p : Clif.Program} {f : Clif.Function}
    {cs : Clif.State}
    (hext : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args, st.inst = .call fn args →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (htry : ∀ B ∈ f.blocks, ∀ fn args et, B.term = .tryCall fn args et →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (hnt : ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args)
    (htr : E2E.TrapsExplicitX env p cs) (hS : SretStableX f) {B0 : Clif.Block}
    (hB0 : f.blocks[0]? = some B0) (hcall : cs.callers = []) (hfunc : cs.frame.func = f)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term)
    {fuel : Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoopX env p fuel cs.toX = .returned vals cm) :
    vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns := by
  obtain ⟨xs, hr, hdX⟩ := runLoopX_returned_reach fuel cs.toX hrun
  obtain ⟨hcall', hfunc', -, B, hB, hpos⟩ :=
    stOkX_reach hext htry hnt htr hfunc hS (stOkX_entry hB0 hcall hfunc hbody hterm) xs hr
  have hd := stepX_done_inv hcall' hdX
  cases hbody' : xs.s.frame.body with
  | cons st rest =>
    obtain ⟨-, hbB⟩ : xs.s.frame.term = B.term ∧ ∀ st ∈ xs.s.frame.body, st ∈ B.body := by
      rcases hpos with h | ⟨hb0, -⟩
      · exact h
      · rw [hbody'] at hb0; cases hb0
    have hst : st ∈ B.body := hbB st (by rw [hbody']; exact List.mem_cons_self)
    exact absurd hd (stmt_not_done hbody'
      (fun fn args hi e he => hext B hB st hst fn args hi e (hfunc' ▸ he))
      (fun sig callee args hi => htr.indirect xs st rest sig callee args hr hbody' hi
        ⟨B, hfunc ▸ hB, hst⟩))
  | nil =>
    rw [Clif.step_term env.toEnv p xs.s hbody'] at hd
    rcases hpos with ⟨hterm', -⟩ | ⟨-, bc, hterm', -⟩
    · rw [hterm'] at hd
      cases hT : B.term with
      | ret xs' => rw [hT] at hd; rw [← hfunc']; exact stepTerm_ret_sigTys hd
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
        exact absurd hd
          ((stepTry_spec (fun e he => htry B hB fn args et hT e (hfunc' ▸ he))).1 vals cm)
      | tryCallIndirect callee args et =>
        rw [hT] at hd
        exact absurd hd ((stepTryInd_spec (fun cv hcv g hg => htr.tryIndirect xs callee args et
          hr hbody' (hterm'.trans hT) ⟨B, hfunc ▸ hB, hT⟩ cv hcv g hg)).1 vals cm)
    · rw [hterm'] at hd
      exact absurd hd ((stepTerm_branch_ne (t := .jump bc) (by simp [dests])).1 vals cm)

end Backend.Proof.Driver
