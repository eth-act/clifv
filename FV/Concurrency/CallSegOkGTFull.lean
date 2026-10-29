import FV.Concurrency.CallSegOkGTWitness

/-!
# The caller of `atomic_load` through the generic call theorem (#473)

`CallSeg.WitnessC.realizes_call_full` derived again, from `realizes_linked_calls` (via
`CallSegOkGT.Witness.realizes_linked_calls_2`): one thread, the caller's root activation of
`link2` entered at its ABI entry `sC0` with a callee budget of `0x200` bytes (`RA5`: two frames of
`Mx2`), its CLIF entry state `csO` (`csC` with the slot-placement oracle at the caller's body `sp`),
in the environment without externs.

* `wf_RA5`, `codeIn_RA5`, `f5_ge`: the activation is well formed, keeps the linked code, and its
  addresses outside the world are at or above `0x6D10`;
* `CallShape`, `FamG`, `reach_invG`, `depthG`, `partsOkG`: the generic reachability argument for a
  caller at a call of a one-statement callee (shared with `WitnessRmw`);
* `Fam`, **`reach_inv`** (`shape_O`): the CLIF states reachable from `csO` (up to their bytes) are
  the caller at its call, `atomic_load` at its entry, `atomic_load` returning, the caller
  returning, or returned;
  **`partsOk_O`** (the one access is `atomic_load`'s 8 bytes at `0`, `LocO`), **`depth_O`**;
* **`ent_O`**: the activation's `Ent` (`Live`, and `ChainP` by `chainP_entry`);
* **`realizes_call_fullT`**: `realizes_linked_calls_2` with every premise discharged but the run.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallSegOkGT.WitnessFull

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver ArmAllocThread E2E
  LinkedMachine LinkedMachine.Link LinkedMachine.Witness CallComposeT CallSegOkG CallSegLive
  CallSegRun CallSegCall CallSeg.WitnessC RealizeCompiled.WitnessL ClifLift CallSegOkGT.Witness
  PrepThread

/-! ## The caller's root activation -/

/-- The caller in the link with a callee budget of `0x200` bytes. -/
abbrev RA5 : RL := link2.act callerF sC0 0x200 GL

theorem stack_RA5 : StackAvail 0x200 callerF.af sC0 := by
  have hs := spC
  have hfs : callerF.af.frameSize = 160 := hs.2.2.2.2.2.2.2.1
  refine ⟨⟨?_, fun a ha => ?_⟩, ArmAllocThread.Witness.probeBelow_le_small (by omega)⟩
  · show callerF.af.frameSize + 16 + 0x200 ≤ (E2E.spv RC.s0).toNat
    rw [spv_RC, hfs]; decide
  · obtain ⟨j, hj, hd⟩ := CallSeg.WitnessC.codeAddr_words program_RC ha
    show callerF.af.frameSize + 16 + 0x200 ≤
      (a - (E2E.spv RC.s0 - BitVec.ofNat 64 (callerF.af.frameSize + 16 + 0x200))).toNat
    rw [spv_RC, hfs]
    have hj' : j < 0x4000 := by have := hs.2.2.2.2.1; omega
    rw [show RC.base = 0x30000#64 from rfl] at hd
    generalize j = J at hj' hd
    bv_omega

theorem wf_RA5 : RA5.Wf where
  check := wfRC.check
  alloc := wfRC.alloc
  emit := wfRC.emit
  layout := wfRC.layout
  lm := wfRC.lm
  fit := wfRC.fit
  stack := stack_RA5
  psF := wfRC.psF
  prog0 := wfRC.prog0
  gfree := fun a hG ⟨h1, _⟩ => by
    have := gL_ge hG
    have e : (E2E.spv RA5.s0).toNat = 0x7000 := by rw [show E2E.spv RA5.s0 = 0x7000#64 from spv_RC]; rfl
    omega

theorem codeIn_RA5 : CodeIn link2 RA5 := fun n FB h => CallSegCall.Witness.codeIn_RA2 n FB h

/-- The addresses outside the activation's world are at or above `0x6D10`. -/
theorem f5_ge {a : BitVec 64} (h : RA5.F a) : 0x6D10 ≤ a.toNat := by
  have hs := spC
  have e : E2E.spv sC0 - BitVec.ofNat 64 (frameDrop callerF.af) = 0x6F50#64 := by
    rw [show E2E.spv sC0 = 0x7000#64 from spv_RC, show frameDrop callerF.af = 176 from hs.2.1]
    rfl
  have hsz : RC.fr.size ≤ 176 := hs.2.2.2.2.2.1
  have hfs : callerF.af.frameSize = 160 := hs.2.2.2.2.2.2.2.1
  change frameWG 0x200 RC.fr.intBase RC.fr.size callerF.af GL sC0 a at h
  unfold frameWG frameW frameF StackBelow at h
  rw [e, hfs, show frameDrop callerF.af = 176 from hs.2.1] at h
  rcases h with ((⟨h1, h2⟩ | ⟨h1, h2⟩ | hc) | ⟨h1, h2⟩) | hG
  · generalize RC.fr.size = n at hsz h2
    bv_omega
  · bv_omega
  · obtain ⟨j, hj, hd⟩ := CallSeg.WitnessC.codeAddr_words program_RC hc
    rw [show RC.base = 0x30000#64 from rfl] at hd
    have : j < 0x4000 := by have := hs.2.2.2.2.1; omega
    generalize j = J at this hd
    bv_omega
  · simp only [BitVec.toNat_ofNat] at h1 h2; omega
  · have := gL_ge hG; omega

/-! ## The CLIF entry state with the oracle -/

/-- The caller's CLIF memory with the slot-placement oracle at its body `sp`. -/
def memO : Clif.Mem := { memL with place := some ⟨[RA5.spB], fr2, none⟩ }

/-- **The caller's CLIF entry state** (`csC` with the oracle). -/
def csO : Clif.State := { csC with mem := memO }

/-- The thread's start: `csO` with no masked byte. -/
noncomputable def csT : TState := encT (fun _ => False) (.run csO)

theorem checksO : fC.blocks.isEmpty = false ∧
    (Clif.Regs.empty.setMany (B0C.params.map (·.1)) argsL).isSome = true ∧
    argsL.map (·.ty) = B0C.params.map (·.2) ∧ argsL.map (·.ty) = fC.sig.params.map (·.ty) ∧
    (match locsOf fC.sig with | [.reg (.x 0)] => true | _ => false) = true ∧
    B0L.body = [{ results := [1], inst := .atomicLoad .i64 {} 0 }] ∧ B0L.term = .ret [1] ∧
    B0C.term = .ret [1] ∧ (E2E.spv w₀C).toNat % 16 = 0 := by
  native_decide -- witness: native_decide

theorem b0C : fC.blocks[0]? = some B0C := by
  have h := checksO.1
  unfold B0C
  revert h
  cases fC.blocks with
  | nil => intro h; cases h
  | cons b bs => intro _; rfl

theorem regsC_eq : Clif.Regs.empty.setMany (B0C.params.map (·.1)) argsL = some regsC := by
  have h := checksO.2.1
  unfold regsC
  revert h
  cases Clif.Regs.empty.setMany (B0C.params.map (·.1)) argsL with
  | none => intro h; cases h
  | some r => intro _; rfl

theorem locsC : locsOf fC.sig = [.reg (.x 0)] := by
  have h := checksO.2.2.2.2.1
  revert h
  generalize locsOf fC.sig = l
  intro h
  match l, h with
  | [.reg (.x 0)], _ => rfl

theorem errW₀C : Arm.r .ERR w₀C = .None := by
  rw [E2E.r_bodyOf _ _ (by simp) (by simp)]
  exact abiRC.err

theorem relW_O : RelW ⟨RA5.F, fun _ => none, RA5.ctx.slotBase, 0⟩ fC (E2E.spv w₀C) [] memO
    w₀C := by
  refine ⟨⟨⟨fun a b _ hb => by simp [memO, memL] at hb, fun a n hv => ?_, rfl⟩,
      fun id b h => by simp at h, E2E.outRel_zero _ _ _⟩, rfl, errW₀C⟩
  simp only [Clif.Mem.valid, memO, memL, List.any_cons, List.any_nil, Bool.or_false,
    Clif.Alloc.contains] at hv
  have hv' : a + n ≤ 8 := by
    revert hv; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  refine ⟨by omega, fun k hk hF => ?_⟩
  have := f5_ge hF
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem argsAt_O : ArgsAtEntry RA5.F fC.sig argsL w₀C := by
  intro loc v h
  rw [locsC] at h
  simp only [argsL, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  show VHolds _ _
  rw [VHolds, E2E.regVal_bodyOf _ _ (by decide), x0C]
  rfl

theorem body_RA5 : BodyEntryW RA5.F RA5.vc.EntryArg RA5.af RA5.s0 w₀C :=
  (E2E.Binary.bodyEntry_bodyOf RA5.af RA5.s0).w RA5.F entryArgRC

theorem linv_O : Clif.LInv pCL csO :=
  ⟨⟨List.mem_cons_self .., .inl ⟨B0C, List.mem_of_getElem? b0C, List.suffix_refl _, rfl⟩⟩,
    fun _ h => nomatch h⟩

theorem func_f : pCL.func? "f" = some fC := by
  simp [Clif.Program.func?, pCL, name_fC]

/-! ## The reachable CLIF states, generically

A caller state `c0` whose block is one `call` of a program function entered at a frame `eF` that
runs one statement and returns (`CallShape`): the states reachable from `c0` (up to their bytes)
are the caller at its call, the callee at its entry, the callee returning, the caller returning
(`FamG`, `reach_invG`), with at most one caller (`depthG`) and, if the callee's statement
accesses 8 bytes of `memL`, every access on `LocO` (`partsOkG`). `csO` here and
`WitnessRmw.csO` are instances. -/

/-- The allocations of `memL`. -/
def AllocsIn (m : Clif.Mem) : Prop := ∀ x ∈ m.allocs, x ∈ memL.allocs

/-- The one location: the 8 bytes at `0` (`atomic_load`'s access). -/
def LocO : Nat → Nat → Prop := fun a n => a = 0 ∧ n = 8

theorem partDisj_O : PartDisj LocO := fun a n b m ha hb _ _ => by
  simp only [LocO] at ha hb; omega

theorem enterSlots_nil {f : Clif.Function} (hf : f.slots = []) (m : Clif.Mem) :
    (Clif.enterSlots f m).1 = [] ∧ (Clif.enterSlots f m).2.allocs = m.allocs := by
  unfold Clif.enterSlots
  split
  · simp [hf, Clif.bumpSlots]
  · split
    · simp [hf, Clif.placeSlots]
    · simp [hf, Clif.bumpSlots]

theorem res_some {r : Clif.StepResult} {t'' : TState} {B' : Bytes} (h : res r = some (t'', B')) :
    (∃ s', r = .next s' ∧ t'' = .run s') ∨ ∃ v, t'' = .ret v := by
  cases r with
  | next s' =>
    simp only [res, Option.some.injEq, Prod.mk.injEq] at h
    exact .inl ⟨s', rfl, h.1.symm⟩
  | done v m =>
    simp only [res, Option.some.injEq, Prod.mk.injEq] at h
    exact .inr ⟨v, h.1.symm⟩
  | trapped => cases h
  | stuck => cases h

/-- A `return` below a caller resumes it. -/
theorem stepTerm_ret_next {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    {xs : List Clif.ValueId} {c : Clif.Frame} {rs : List Clif.ValueId}
    {cs : List (Clif.Frame × List Clif.ValueId)} (hc : s.callers = (c, rs) :: cs) {s' : Clif.State}
    (h : Clif.stepTerm env p s (.ret xs) = .next s') :
    ∃ regs, s'.frame = { c with regs } ∧ s'.callers = cs := by
  simp only [Clif.stepTerm] at h
  revert h
  cases s.frame.getMany xs with
  | ok vals =>
    simp only [Clif.StepResult.ofRes, Clif.returnValues, hc]
    rcases checkTys_cases s!"return values of %{s.frame.func.name}" vals
      (Clif.AbiParam.tys s.frame.func.sig.returns) with ⟨hct, -⟩ | ⟨m, hct⟩
    · rw [hct]
      simp only
      split
      · intro h; cases h; exact ⟨_, rfl, rfl⟩
      · intro h; cases h
    · rw [hct]; intro h; cases h
  | trap c => intro h; cases h
  | stuck m => intro h; cases h

theorem evShape_congr {s s' : Clif.State} (h : s.frame.body = s'.frame.body) :
    evShape s = evShape s' := by
  unfold evShape; rw [h]

theorem evShape_nil {s : Clif.State} (h : s.frame.body = []) : evShape s = [[]] := by
  unfold evShape; rw [h]

/-- **A caller state at a call of a one-statement callee** in `p`: `c0` (no caller, allocations
of `memL`) calls, with its block's one statement, a function of `p` without slots, entered at
`eF` below the suspended caller `ext`; `eF`'s block is one statement other than a call, and both
blocks return. -/
structure CallShape (p : Clif.Program) (c0 : Clif.State) (eF : Clif.Frame)
    (ext : List (Clif.Frame × List Clif.ValueId)) : Prop where
  init : c0.callers = [] ∧ AllocsIn c0.mem
  call : ∃ (rs : List Clif.ValueId) (fn : Clif.FnRef) (args : List Clif.ValueId)
      (ex : Clif.ExtFunc) (vals : List Clif.Val) (b : Clif.Block) (regs : Clif.Regs),
    c0.frame.body = [{ results := rs, inst := .call fn args }] ∧
    ext = [({ c0.frame with body := [] }, rs)] ∧
    (do
      let ext ← Clif.Res.ofOption s!"unknown function reference fn{fn}" (c0.frame.func.extern? fn)
      let vals ← c0.frame.getMany args
      Clif.checkTys s!"arguments of call to %{ext.name}" vals (Clif.AbiParam.tys ext.sig.params)
      pure (ext, vals) : Clif.Res (Clif.ExtFunc × List Clif.Val)) = .ok (ex, vals) ∧
    p.func? ex.name = some eF.func ∧
    (Clif.AbiParam.tys eF.func.sig.params == Clif.AbiParam.tys ex.sig.params &&
      Clif.AbiParam.tys eF.func.sig.returns == Clif.AbiParam.tys ex.sig.returns) = true ∧
    eF.func.entry? = some b ∧ vals.map (·.ty) = Clif.AbiParam.tys eF.func.sig.params ∧
    vals.map (·.ty) = b.params.map (·.2) ∧
    Clif.Regs.empty.setMany (b.params.map (·.1)) vals = some regs ∧ eF.func.slots = [] ∧
    eF = ⟨eF.func, regs, [], b.body, b.term⟩
  body : ∃ st : Clif.Stmt, eF.body = [st] ∧ (∀ fn args, st.inst ≠ .call fn args) ∧
    ∀ sig callee args, st.inst ≠ .callIndirect sig callee args
  retE : ∃ xs, eF.term = .ret xs
  retC : ∃ ys, c0.frame.term = .ret ys

/-- **The CLIF states reachable from a `CallShape`'s caller** (at `cF`), up to their bytes. -/
def FamG (cF eF : Clif.Frame) (ext : List (Clif.Frame × List Clif.ValueId)) (s : Clif.State) :
    Prop :=
  (s.frame = cF ∧ s.callers = [] ∧ AllocsIn s.mem) ∨
  (s.frame = eF ∧ s.callers = ext ∧ AllocsIn s.mem) ∨
  (∃ r, s.frame = { eF with regs := r, body := [] } ∧ s.callers = ext) ∨
  (∃ r, s.frame = { cF with regs := r, body := [] } ∧ s.callers = [])

/-- The thread states running in `F` or returned. -/
def RInvG (F : Clif.State → Prop) : TState → Prop
  | .run s => F s
  | .ret _ => True

theorem famG_congr {cF eF : Clif.Frame} {ext : List (Clif.Frame × List Clif.ValueId)}
    {s s' : Clif.State} (h : withBytes s (fun _ => none) = withBytes s' (fun _ => none))
    (hs : FamG cF eF ext s) : FamG cF eF ext s' := by
  have e1 : s.frame = s'.frame := congrArg (·.frame) h
  have e2 : s.callers = s'.callers := congrArg (·.callers) h
  have e3 : s.mem.allocs = s'.mem.allocs := congrArg (·.mem.allocs) h
  unfold FamG AllocsIn at hs ⊢
  rw [← e1, ← e2, ← e3]
  exact hs

theorem rinvG_strip {F : Clif.State → Prop}
    (hF : ∀ s s', withBytes s (fun _ => none) = withBytes s' (fun _ => none) → F s → F s')
    {t t' : TState} (h : strip t = strip t') (ht : RInvG F t) : RInvG F t' :=
  match t, t', h, ht with
  | _, .ret _, _, _ => trivial
  | .ret _, .run _, h, _ => by cases h
  | .run s, .run s', h, ht => hF s s' (TState.run.inj h) ht

section
variable {p : Clif.Program} {c0 : Clif.State} {eF : Clif.Frame}
  {ext : List (Clif.Frame × List Clif.ValueId)}

/-- **A step from a reachable state to a running state stays reachable.** -/
theorem next_famG (H : CallShape p c0 eF ext) (env : Clif.Env) {s : Clif.State}
    (hs : FamG c0.frame eF ext s) (B : Bytes) {s' : Clif.State}
    (hst : Clif.step env p (withBytes s B) = .next s') : FamG c0.frame eF ext s' := by
  obtain ⟨rs, fn, args, ex, vals, b, regsE, hb, hext, hpre, hfn, hsig, hent, h1, h2, hr, hsl,
    heF⟩ := H.call
  obtain ⟨st, heb, hnc, hni⟩ := H.body
  obtain ⟨xs, hxs⟩ := H.retE
  obtain ⟨ys, hys⟩ := H.retC
  rcases hs with ⟨hf, hc, ha⟩ | ⟨hf, hc, ha⟩ | ⟨r, hf, hc⟩ | ⟨r, hf, hc⟩
  · -- the caller's call enters the callee
    have hbody : (withBytes s B).frame.body = [{ results := rs, inst := .call fn args }] := by
      show s.frame.body = _; rw [hf]; exact hb
    rw [Clif.step_call env p _ [] rs fn args hbody] at hst
    unfold Clif.stepCall at hst
    simp only [show (withBytes s B).frame = c0.frame from hf] at hst
    rw [hpre] at hst
    simp only [Clif.StepResult.ofRes_ok, hfn, hsig, ite_true] at hst
    rw [enterFunc_of' hent h1 h2 hr] at hst
    simp only [Clif.StepResult.ofRes_ok, Clif.StepResult.next.injEq] at hst
    subst hst
    obtain ⟨e1, e2⟩ := enterSlots_nil hsl (withBytes s B).mem
    refine .inr (.inl ⟨?_, ?_, ?_⟩)
    · show (⟨eF.func, regsE, (Clif.enterSlots eF.func (withBytes s B).mem).1, b.body, b.term⟩ :
        Clif.Frame) = eF
      rw [e1]; exact heF.symm
    · show _ :: s.callers = ext
      rw [hc, hext]
    · intro x hx
      exact ha x (e2 ▸ hx)
  · -- the callee's statement
    have hbody : (withBytes s B).frame.body = [st] := by
      show s.frame.body = _; rw [hf]; exact heb
    rw [Clif.step_inst env p _ _ [] hbody hnc hni] at hst
    unfold Clif.StepResult.ofRes at hst
    split at hst
    · rename_i a _
      obtain ⟨vs, m⟩ := a
      simp only [Clif.continueWith] at hst
      split at hst
      · rename_i regs _
        cases hst
        exact .inr (.inr (.inl ⟨regs, by show { s.frame with regs, body := [] } = _; rw [hf], hc⟩))
      · cases hst
    · cases hst
    · cases hst
  · -- the callee returns into the caller
    have hb' : (withBytes s B).frame.body = [] := by show s.frame.body = []; rw [hf]
    rw [Clif.step_term env p _ hb'] at hst
    have ht : (withBytes s B).frame.term = .ret xs := by
      show s.frame.term = _; rw [hf]; exact hxs
    rw [ht] at hst
    obtain ⟨regs, e1, e2⟩ := stepTerm_ret_next (s := withBytes s B)
      (c := { c0.frame with body := [] }) (rs := rs) (cs := []) (hc.trans hext) hst
    exact .inr (.inr (.inr ⟨regs, e1, e2⟩))
  · -- the caller returns: no next state
    have hb' : (withBytes s B).frame.body = [] := by show s.frame.body = []; rw [hf]
    rw [Clif.step_term env p _ hb'] at hst
    have ht : (withBytes s B).frame.term = .ret ys := by
      show s.frame.term = _; rw [hf]; exact hys
    rw [ht] at hst
    exact absurd hst ((stepTerm_ret (env := env) (p := p) (s := withBytes s B) (xs := ys) hc).1 s')

/-- **A step from a reachable state stays reachable.** -/
theorem step_famG (H : CallShape p c0 eF ext) (env : Clif.Env) {s : Clif.State}
    (hs : FamG c0.frame eF ext s) (B : Bytes) {t'' : TState} {B' : Bytes}
    (h : res (Clif.step env p (withBytes s B)) = some (t'', B')) :
    RInvG (FamG c0.frame eF ext) t'' := by
  rcases res_some h with ⟨s', hst, rfl⟩ | ⟨v, rfl⟩
  · exact next_famG H env hs B hst
  · trivial

/-- **The thread states reachable from a `CallShape`'s caller.** -/
theorem reach_invG (H : CallShape p c0 eF ext) {env : Clif.Env} {t : TState}
    (h : RReach env p (.run c0) t) : RInvG (FamG c0.frame eF ext) t := by
  induction h with
  | base => exact Or.inl ⟨rfl, H.init⟩
  | @step t evs t' _ hs ih =>
    cases t with
    | ret v => exact False.elim hs
    | run s =>
      obtain ⟨-, ⟨B, hB⟩, hf⟩ := hs
      obtain ⟨t'', h1, h2⟩ := hf B hB
      exact rinvG_strip (fun _ _ => famG_congr) h2 (step_famG H env ih B h1)
  | @stepS t evs t' _ hs ih =>
    cases t with
    | ret v => exact False.elim hs
    | run s =>
      obtain ⟨-, ⟨B, hB⟩, -, hf⟩ := hs
      obtain ⟨t'', h1, h2⟩ := hf B hB
      exact rinvG_strip (fun _ _ => famG_congr) h2 (step_famG H env ih _ h1)
  | strip _ he ih => exact rinvG_strip (fun _ _ => famG_congr) he ih

/-- **At most one caller** below every state reachable from a `CallShape`'s caller. -/
theorem depthG (H : CallShape p c0 eF ext) {env : Clif.Env} :
    ∀ S, RReach env p (.run c0) (.run S) → S.callers.length < 2 := by
  intro S h
  have hI : FamG c0.frame eF ext S := reach_invG H h
  obtain ⟨_, _, _, _, _, _, _, -, hext, -⟩ := H.call
  subst hext
  rcases hI with ⟨-, hc, -⟩ | ⟨-, hc, -⟩ | ⟨_, -, hc⟩ | ⟨_, -, hc⟩ <;> simp [hc]

/-- **The accesses from the states reachable from a `CallShape`'s caller lie on `LocO`**, if
the callee's statement (`evShape eS = [l]`, `eS` at `eF`) accesses 8 bytes. -/
theorem partsOkG (H : CallShape p c0 eF ext) {env : Clif.Env} {eS : Clif.State}
    {l : List (SKind × Nat)} (heS : eS.frame = eF) (hsh : evShape eS = [l])
    (hl : ∀ x ∈ l, x.2 = 8 ∧ x.1.dir ≠ .F) : PartsOk env p (.run c0) LocO := by
  intro t evs t' hR hs e he
  cases t with
  | ret v => exact False.elim hs
  | run s =>
  have hI : FamG c0.frame eF ext s := reach_invG H hR
  have hv0 := CallSegGeo.cstep_reads_valid hs
  obtain ⟨⟨hsh', hd⟩, -, -⟩ := hs
  have hnil : evShape s = [[]] → False := fun h => by
    rw [h, List.mem_singleton, List.map_eq_nil_iff] at hsh'
    subst hsh'; cases he
  obtain ⟨_, _, _, _, _, _, _, hb, -⟩ := H.call
  rcases hI with ⟨hf, -, -⟩ | ⟨hf, -, ha⟩ | ⟨r, hf, -⟩ | ⟨r, hf, -⟩
  · exact (hnil (by unfold evShape; rw [hf, hb])).elim
  · rw [(evShape_congr (s' := eS) (by rw [hf, heS])).trans hsh, List.mem_singleton] at hsh'
    have hm := List.mem_map_of_mem (f := fun e : Ev SKind BVal => (e.k, e.n)) he
    rw [hsh'] at hm
    have hn : e.n = 8 := (hl _ hm).1
    have hdir : e.dir ≠ .F := by rw [(hd e he).1]; exact (hl _ hm).2
    refine ⟨fun _ => ⟨?_, hn⟩, fun _ => by omega⟩
    have hv := hv0 e he hdir
    simp only [Clif.Mem.valid, List.any_eq_true] at hv
    obtain ⟨y, hy, hcy⟩ := hv
    have hy' := ha y hy
    simp only [memL, List.mem_singleton] at hy'
    subst hy'
    simp only [Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hcy
    omega
  · exact (hnil (evShape_nil (by rw [hf]))).elim
  · exact (hnil (evShape_nil (by rw [hf]))).elim

end

/-! ## The reachable CLIF states of `csO` -/

/-- `csO` calls `atomic_load`: a load, then both return. -/
theorem shape_O : CallShape pCL csO csL.frame extC := by
  obtain ⟨hb, hfn, hsig, hent, h1, h2, hsl⟩ := clifC
  exact ⟨⟨rfl, fun _ hx => hx⟩, ⟨[1], 0, [0], extF, argsL, B0L, regsL, hb, rfl, preC, hfn, hsig,
    hent, h1, h2, regsL_eq, hsl, rfl⟩, ⟨_, checksO.2.2.2.2.2.1, (fun _ _ h => by cases h),
    (fun _ _ _ h => by cases h)⟩, ⟨_, checksO.2.2.2.2.2.2.1⟩, ⟨_, checksO.2.2.2.2.2.2.2.1⟩⟩

/-- **The CLIF states reachable from `csO`**, up to their bytes (module doc). -/
def Fam (s : Clif.State) : Prop := FamG csC.frame csL.frame extC s

/-- The reachable thread states. -/
def RInv : TState → Prop := RInvG Fam

theorem fam_congr {s s' : Clif.State}
    (h : withBytes s (fun _ => none) = withBytes s' (fun _ => none)) (hs : Fam s) : Fam s' :=
  famG_congr h hs

theorem rinv_strip {t t' : TState} (h : strip t = strip t') (ht : RInv t) : RInv t' :=
  rinvG_strip (fun _ _ => fam_congr) h ht

/-- **A step from a reachable state to a running state stays reachable** (module doc). -/
theorem next_fam (env : Clif.Env) {s : Clif.State} (hs : Fam s) (B : Bytes) {s' : Clif.State}
    (hst : Clif.step env pCL (withBytes s B) = .next s') : Fam s' :=
  next_famG shape_O env hs B hst

/-- **A step from a reachable state stays reachable.** -/
theorem step_fam (env : Clif.Env) {s : Clif.State} (hs : Fam s) (B : Bytes) {t'' : TState}
    {B' : Bytes} (h : res (Clif.step env pCL (withBytes s B)) = some (t'', B')) : RInv t'' :=
  step_famG shape_O env hs B h

/-- **The thread states reachable from `csO`** (module doc). -/
theorem reach_inv {env : Clif.Env} {t : TState} (h : RReach env pCL (.run csO) t) : RInv t :=
  reach_invG shape_O h

/-- **At most one caller** below every reachable state. -/
theorem depth_O {env : Clif.Env} :
    ∀ S, RReach env pCL (.run csO) (.run S) → S.callers.length < 2 :=
  depthG shape_O

theorem evShape_csC : evShape csC = [[]] := by
  unfold evShape; rw [show csC.frame.body = B0C.body from rfl, clifC.1]

/-- **The accesses from the reachable states lie on `LocO`** (module doc). -/
theorem partsOk_O {env : Clif.Env} : PartsOk env pCL (.run csO) LocO :=
  partsOkG shape_O (eS := csL) rfl shapeL1 (by decide)

/-! ## The environment and the activation's entry -/

theorem keepsAllocs_E : Clif.EnvKeepsAllocs Clif.Env.empty := fun _ _ h => by
  simp [Clif.Env.empty] at h

theorem keepsPlace_E : Clif.EnvKeepsPlace Clif.Env.empty := fun _ _ h => by
  simp [Clif.Env.empty] at h

/-- **The caller's root activation entered at its ABI entry** (module doc). -/
theorem ent_O : ∃ g : Act, Ent link2 Clif.Env.empty pCL (PrivA RA5) (.run csO) LocO fr2 Mx2 2
    (fun _ => none) g (sC0, none) (csT, PrivA RA5) := by
  obtain ⟨-, -, -, vc, ctx, st0, R, gn, bl, A, Lp, ss, ss', cc, ins, a0, hF⟩ :=
    fnOk_C (env := Clif.Env.empty) rfl
  have hS := hF sC0 0x200 GL 0x4000#64 (E2E.spv w₀C) [] [] callerF [] (fun _ => False) [] wf_RA5
    abiRC checksO.2.2.2.2.2.2.2.2
  obtain ⟨-, hq, hA⟩ := q_init_lines wf_RA5 abiRC body_RA5
  refine ⟨⟨"f", callerF, sC0, 0x200, GL, 0x4000#64, fC, vc, ctx, st0, R, gn, bl, A,
    ⟨RA5.F, fun _ => none, RA5.ctx.slotBase, 0⟩, E2E.spv w₀C, Lp, ss, ss', cc, ins, a0, [], [],
    callerF, [], fun _ => False, []⟩, rfl, csO, fun _ => False, rfl, ?_, ?_, func_f⟩
  · exact {
      stat := hS
      syms := rfl
      code := codeIn_RA5
      bnd := fun _ h => h
      dirty := fun _ h => .inl h
      reach := RReach.base
      call := rfl
      ret := fun h => absurd rfl h
      linv := linv_O
      place := rfl
      nv := fun _ _ _ _ h => h
      ndead := fun _ h => h.elim
      opens := fun _ h => absurd h List.not_mem_nil
      budget := show (2 - 0) * 240 ≤ 512 by decide
      func := rfl }
  · exact chainP_entry hS b0C rfl rfl rfl rfl rfl regsC_eq checksO.2.2.1 checksO.2.2.2.1 relW_O
      argsAt_O hq hA

open ProgE2E PrivCohT Rel in
/-- **The caller of `atomic_load` through the call and back, from the generic theorem**
(`realizes_linked_calls_2` with one thread, the caller's root activation, every premise
discharged but the run): every execution of the realized prefix of a precise run of the linked
machine from the caller's ABI entry is realized by a `CStepS` thread of `pCL` from `csO`. -/
theorem realizes_call_fullT {ls : List Lab} {t' : CallCompose.AT}
    (hr : PRun Policy.arm link2.M (OkB (PrivA RA5)) (sC0, none) ls t') :
    ∃ k : Nat → Nat, (∀ i < 1, k i ≤ ls.length) ∧
      ∀ (PA : Traces ProgE2E.AState AKind BVal) (locsA locsC : List (Nat × Nat)) (MA0 MC0 : Bytes)
        (rfA coA rmwA : Concurrency.Rel PEv), PA.n = 1 →
        (∀ i < 1, PA.tr i = conv (evTr (ls.take (k i)))) →
        (PA.exec locsA rfA coA rmwA).Wf →
        Acyclic (union (PA.exec locsA rfA coA rmwA).poLoc (PA.exec locsA rfA coA rmwA).com) →
        InitFirst (PA.exec locsA rfA coA rmwA) →
        (∀ i < 1, ∀ a b, rmwA (.thr i a.1 a.2) (.thr i b.1 b.2) ↔
          MonPair (evTr (ls.take (k i))) a b) →
        locsC <+: locsA →
        (∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j < 1, PrivA RA5 (locsA[q]).1) →
        (∀ q (h : q < locsC.length),
          bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2) →
        StackDisjoint PA (fun _ l => PrivA RA5 l ∨ PrivA RA5 l) →
        ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧
          (∀ i < 1, PC.st i 0 = csT) ∧ PC.Runs (CStepS Clif.Env.empty pCL) ∧
          Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ (fun _ _ _ => True) := by
  obtain ⟨g, hg⟩ := ent_O
  exact realizes_linked_calls_2 (env := Clif.Env.empty) rfl (n := 1) (Bnd := fun _ => PrivA RA5)
    (c0 := fun _ => .run csO) (Loc := fun _ => LocO) (Dcap := fun _ => 2) (g := fun _ => g)
    (sA := fun _ => (sC0, none)) (cs := fun _ => csT) (D0 := fun _ => PrivA RA5)
    (fun _ _ => partsOk_O) (fun _ _ => partDisj_O) keepsAllocs_E keepsPlace_E
    (fun _ _ => depth_O) (fun _ _ => hg) (ls := fun _ => ls) (t' := fun _ => t') (fun _ _ => hr)

end Concurrency.CallSegOkGT.WitnessFull
