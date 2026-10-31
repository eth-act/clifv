import FV.E2E.ClifEnvOnly
import FV.E2E.LinkWorld
import FV.Backend.Proof.VCodeSemIDriver
import FV.E2E.CountedFam

/-!
# CLIF → counted VCode, with the callee contracts per step of the run (SEM1, `docs/plans/uninit.md` §5.9)

`iselSim_relW` (`FV/E2E/LinkWorld.lean`) runs the driver simulation (`driver_correct`) for
`csem F ctx X` with one `ExtSem` whose contract (`XCallsOk`) holds for every related state. The
counted VCode run (`csemI F ctx XI`: call number `n` with `XI.at n`) needs the contract of
`XI.at n` only for the actual `n`-th call of the run, with the environment restricted to that
call's invocation (`Clif.Env.only`, `Clif.Invoked`). The simulation is redone per step: each step
of the CLIF run instantiates the existing `DriverHyp` (unchanged rule-level contracts) and the
existing one-step lemmas, and the step's VCode run is lifted to `csemI`:

* a step without an extern call runs with the calls failing (`ExtSem.noCall`) and the
  environment answering nothing (its contracts are vacuous), so no VCode call is executed and
  the run lifts at the current counter (`csem_noCall_proj`);
* a `call`/`call_indirect` statement runs with `XI.at n` and the environment restricted to its
  invocation; its segment has exactly one VCode call (`InstCallsOne`, a property of the ISLE
  lowering taken as a premise), so it lifts to `csemI` from counter `n` to `n + 1`
  (`seqRun_csemI_le1`).

The counter of the CLIF run is `ReachN` (`callNum`: one per `call`, `call_indirect`, `try_call`,
`try_call_indirect` step). This file covers functions without `try_call` terminators
(`hnotry`); the `try_call` step is `IselSimITry.lean`'s.

* `ExtSem.noCall`, `csem_noCall_call`, `csem_noCall_proj`; `MRI`; `ReachN`, `callNum`;
* `xCallsOk_none`, `xCallsIndOk_none`: the contracts of the environment answering nothing;
* `driverHyp_relW`: `iselSim_relW`'s `DriverHyp`, for any contracts;
* `InstCallsOne`; `stmt_stepI_noCall`, `stmt_stepI_call`, `term_stepI`, `entry_stepI`;
* `sim_runI`, **`iselSim_relWI`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-! ## Failing calls, the counted relation, the CLIF call counter -/

/-- `X` whose calls fail. -/
def _root_.Backend.Proof.ExtSem.noCall (X : ExtSem) : ExtSem := { X with call := fun _ _ _ => none }

theorem csem_noCall_call {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    (h : i.isCallI = true) (uses : List CV) (w : Arm.ArmState) :
    csem F ctx X.noCall i uses w = none := by
  cases i <;> simp_all [MInst.isCallI, csem, ExtSem.noCall]

/-- **`csem` with failing calls projects into the counted semantics at any fixed counter.** -/
theorem csem_noCall_proj (F : BitVec 64 → Prop) (ctx : FnCtx) (XI : ExtSemI) (n : Nat) :
    ISem.ProjW (fun w => (w, n)) (csem F ctx (XI.at n).noCall) (csemI F ctx XI) := by
  intro i uses w outs w' ctl h
  cases hc : i.isCallI with
  | false =>
    have he : csem F ctx (XI.at n).noCall i = csem F ctx (XI.at n) i :=
      csem_call_congr F ctx (XI.at n) _ hc
    rw [he] at h
    rw [csemI_noncall F ctx XI hc uses w n n, h]
    rfl
  | true => rw [csem_noCall_call hc] at h; cases h

/-- The counted relation: `MR` on the Arm world. -/
def MRI (MR : MemRelT) : MemRelTW (Arm.ArmState × Nat) := fun sl cm w => MR sl cm w.1

theorem match_MRI {f : Clif.Function} {ctx : Ctx} {R : Reg → Reg} {gn : Nat → Nat}
    {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {MR : MemRelT}
    {slots : List (Clif.SlotId × Nat)} {s : Clif.State} {b k : Nat} {ρ : Nat → CV}
    {w : Arm.ArmState} {n : Nat} :
    Match f ctx R gn bl A (MRI MR) slots s ⟨b, k, ρ, (w, n)⟩ ↔
      Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩ := Iff.rfl

/-- A `call`/`call_indirect` statement. -/
def _root_.Clif.Inst.isCallLike : Clif.Inst → Bool
  | .call .. | .callIndirect .. => true
  | _ => false

/-- The extern calls a CLIF step from `s` makes (`call`, `call_indirect`, `try_call`,
`try_call_indirect`). -/
def callNum (s : Clif.State) : Nat :=
  match s.frame.body with
  | st :: _ => if st.inst.isCallLike then 1 else 0
  | [] => if s.frame.term.isTry then 1 else 0

/-- **`s` is reached from `cs` after `n` extern calls.** -/
inductive ReachN (env : Clif.Env) (p : Clif.Program) (cs : Clif.State) : Clif.State → Nat → Prop
  | refl : ReachN env p cs cs 0
  | snoc {s s' : Clif.State} {n : Nat} : ReachN env p cs s n → Clif.step env p s = .next s' →
      ReachN env p cs s' (n + callNum s)

theorem ReachN.reach {env : Clif.Env} {p : Clif.Program} {cs s : Clif.State} {n : Nat}
    (h : ReachN env p cs s n) : Reach env p cs s := by
  induction h with
  | refl => exact .refl _
  | snoc _ hs ih => exact ih.snoc hs

/-! ## The environment answering nothing -/

theorem xCallsOk_none (env : Clif.Env) (exts : List Clif.ExtFunc) (MR : MemRelT) (X : ExtSem) :
    XCallsOk (env.only fun _ _ _ => False) exts MR X := by
  intro ext _ g _ cm _ _ _ _ vals _ _ hg _ _ _ hret _
  obtain ⟨g0, -, rfl⟩ := Clif.Env.only_extern_eq hg
  rw [Clif.onlyFn_of_not (fun h => h)] at hret
  cases hret

theorem xCallsIndOk_none (env : Clif.Env) (sigs : List Clif.Signature) (MR : MemRelT)
    (X : ExtSem) : XCallsIndOk (env.only fun _ _ _ => False) sigs MR X := by
  intro _ _ n g _ cm _ _ _ vals _ _ hg _ _ _ _ hret _ _
  obtain ⟨g0, -, rfl⟩ := Clif.Env.only_extern_eq hg
  rw [Clif.onlyFn_of_not (fun h => h)] at hret
  cases hret

/-- A step without an extern call is the same in the environment answering nothing. -/
theorem step_none_of_callNum {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    (h : callNum s = 0) (hnr : ∀ fn args, s.frame.body = [] → s.frame.term ≠ .returnCall fn args) :
    Clif.step (env.only fun _ _ _ => False) p s = Clif.step env p s := by
  apply Clif.step_only
  intro n vals m ⟨_, hI⟩
  unfold callNum at h
  revert hI
  cases hb : s.frame.body with
  | cons st rest =>
    simp only [hb] at h
    cases hi : st.inst <;> simp_all [Clif.Inst.isCallLike]
  | nil =>
    simp only [hb] at h
    cases ht : s.frame.term with
    | returnCall fn args => exact absurd ht (hnr fn args hb)
    | _ => simp_all [Clif.Terminator.isTry]

/-! ## The driver hypotheses for any callee contracts -/

/-- **`iselSim_relW`'s driver hypotheses**, from the lowering obligations, for any callee
contracts `X` of an environment `env`. -/
theorem driverHyp_relW {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {ctx : Ctx} {st0 : LState} {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow}
    {A : Nat → Nat → List Clif.ValueId}
    (hshape : LowerShape f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff) :
    DriverHyp f vc ctx st0 R gn bl A (csem F ⟨fa.k, af.slotBase⟩ X)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) env p := by
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hRef : Refines F (csem F ⟨fa.k, af.slotBase⟩ X) := refines_csem _ _ X
  have hmem : MemRefines F slotOff syms (csem F ⟨fa.k, af.slotBase⟩ X) :=
    memRefines_csem _ _ X hslot hsym
  have hcalls := callsRefine_csem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hX
  have hicalls := indCallsRefine_csem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hXI hsym
    (fun _ _ _ h => h.1.1.symbols)
  have houtB := outgoing_le_intBase hc
  exact {
    shape := hshape
    cert := hcert
    dsem := (driverSem_csem F ⟨fa.k, af.slotBase⟩ X).toDriverSemG
    insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
      indRulesCorrect memRulesCorrect_program hRef (mrStable_relW Γ f c) hcalls hicalls hmem
      (outArgsOk_relW Γ f c) (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (indStack_mono (indStack_of_check hc.lowerOk) houtB) (memRelOk_relW Γ f c)
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef (mrStable_relW Γ f c)
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hc.lowerOk
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨_, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) hcalls, tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef (mrStable_relW Γ f c)
      hmem (outArgsOk_relW Γ f c) (indStack_mono (indStack_of_check hc.lowerOk) houtB) hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := cfg_of_prepare hc.prepare }

/-! ## Lifting runs into the counted semantics -/

theorem vTrapFrom_mapW {W₁ W₂ : Type} {π : W₂ → W₁} {vc : VCode} {sem₂ : ISem CV W₂}
    {sem₁ : ISem CV W₁} (hp : ISem.ProjW π sem₂ sem₁) {b k : Nat} {ρ : Nat → CV} {w : W₂}
    {c : Clif.TrapCode} (h : VTrapFrom vc sem₂ ⟨b, k, ρ, w⟩ c) :
    VTrapFrom vc sem₁ ⟨b, k, ρ, π w⟩ c := by
  obtain ⟨b', k', ρ', w', vb, i, ops, outs, w'', hs, hvb, hi, hops, hsem, htc⟩ := h
  exact ⟨b', k', ρ', π w', vb, i, ops, outs, π w'', vstar_mapW hp hs, hvb, hi, hops,
    hp _ _ _ _ _ _ hsem, htc⟩

theorem vRetFrom_mapW {W₁ W₂ : Type} {π : W₂ → W₁} {vc : VCode} {sem₂ : ISem CV W₂}
    {sem₁ : ISem CV W₁} (hp : ISem.ProjW π sem₂ sem₁) {b k : Nat} {ρ : Nat → CV} {w : W₂}
    {us : List (Reg × Reg)} {vals : List CV} {w' : W₂}
    (h : VRetFrom vc sem₂ ⟨b, k, ρ, w⟩ us vals w') :
    VRetFrom vc sem₁ ⟨b, k, ρ, π w⟩ us vals (π w') := by
  obtain ⟨b', k', ρ', w₁, vb, ops, outs, hs, hvb, hk, hops, hvals, hsem⟩ := h
  exact ⟨b', k', ρ', π w₁, vb, ops, outs, vstar_mapW hp hs, hvb, hk, hops, hvals,
    hp _ _ _ _ _ _ hsem⟩

theorem callsI_append (a b : List MInst) : callsI (a ++ b) = callsI a + callsI b := by
  unfold callsI; exact List.countP_append ..

theorem callsI_map_mapRegs (g : Reg → Reg) (ms : List MInst) :
    callsI (ms.map (·.mapRegs g)) = callsI ms := by
  unfold callsI
  rw [List.countP_map]
  congr 1
  funext i
  exact MInst.isCallI_mapRegs g i

theorem callsI_extraOf (results : List Nat) (rss : List (List Reg)) :
    callsI (extraOf results rss) = 0 := by
  unfold callsI extraOf
  rw [List.countP_eq_zero]
  intro i hi
  obtain ⟨⟨r, rs⟩, -, he⟩ := List.mem_filterMap.mp hi
  simp only at he
  split at he <;> cases he <;> simp [MInst.isCallI]

/-- **A `call`/`call_indirect` statement's lowering has exactly one VCode call** (a property of
the ISLE lowering: one `call` per CLIF call). Taken as a premise (`docs/plans/uninit.md` §5.9). -/
def InstCallsOne (f : Clif.Function) : Prop :=
  ∀ ctx ii info inst st rss st' tr, CtxInv f ctx →
    (∃ B ∈ f.blocks, ∃ stm ∈ B.body, stm.inst = inst) → Compile.functionE f = true →
    ctx.insts[ii]? = some info → info.clif = some inst → IndSigOk f (indSigs f) inst →
    st.emitted = #[] → ValsBelow ctx st →
    runTerm ctx "lower" [.inst ii] st = .ok (some (.regsVec rss), st', tr) →
    inst.isCallLike = true → callsI st'.emitted.toList = 1

section steps
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {W : Type}
  {F : BitVec 64 → Prop} {fctx : FnCtx} {XI : ExtSemI} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}

/-- The segment of a `call`/`call_indirect` statement has exactly one VCode call. -/
theorem segCalls_of {sem : ISem CV W} {MRW : MemRelTW W} {env' : Clif.Env}
    (H : DriverHyp f vc ctx st0 R gn bl A sem MRW env' p) (h1 : InstCallsOne f) {b : Nat}
    {B : Clif.Block} {j : Nat} {stm : Clif.Stmt} (hB : f.blocks[b]? = some B)
    (hstm : B.body[j]? = some stm) (hcl : stm.inst.isCallLike = true) :
    callsI (seg f R bl b j) = 1 := by
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨-, -, hsllen, hstmts, -, -, -, -, -, -, -⟩ := H.shape.blk b B L hB hL
  have hjlt : j < B.body.length := (List.getElem?_eq_some_iff.mp hstm).1
  obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
    ⟨L.sl[j]'(by omega), List.getElem?_eq_getElem _⟩
  obtain ⟨⟨info, hinfo, hclif, -⟩, hemp, hst0, ⟨tr, hrun⟩, -⟩ := hstmts j stm sl hstm hsl
  have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
  have hstmmem : stm ∈ B.body := List.mem_of_getElem? hstm
  have h := h1 ctx (L.start + j) info stm.inst sl.st sl.rss sl.st' tr H.shape.ctxInv
    ⟨B, hBmem, stm, hstmmem, rfl⟩ H.subE hinfo hclif (H.indSig B hBmem stm hstmmem) hemp
    (fun x r h => Nat.lt_of_lt_of_le (H.shape.valsBelow x r h) hst0) hrun hcl
  rw [seg_eq hB hL hstm hsl, callsI_map_mapRegs, callsI_append, h, callsI_extraOf]

/-! ### For any family with index-independent non-calls (`CountedFam.lean`) -/

section fam
variable {sem semB : Nat → ISem CV W} {MRW : MemRelTW W}

/-- **A statement without an extern call, counted, for a family** `sem` with a probe `semB`
(`ProbeOf`: `sem` on non-calls, failing calls): no VCode call runs. -/
theorem stmt_stepG_noCall (hB : ProbeOf semB sem) {n : Nat}
    (Hb : DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MRW slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hnc : stm.inst.isCallLike = false)
    (hind : ∀ sig callee args, stm.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ b' k' ρ' w', Star (VStep vc (ISem.counted sem)) (.run ⟨b, k, ρ, (w, n)⟩)
        (.run ⟨b', k', ρ', (w', n)⟩) ∧ Match f ctx R gn bl A MRW slots s' ⟨b', k', ρ', w'⟩) ∧
    (∀ c, Clif.step env p s = .trapped c → explicitTrapInst stm.inst = true →
      VTrapFrom vc (ISem.counted sem) ⟨b, k, ρ, (w, n)⟩ c) := by
  have hstep : Clif.step (env.only fun _ _ _ => False) p s = Clif.step env p s :=
    step_none_of_callNum (by simp [callNum, hbody, hnc]) (fun _ _ h => by rw [hbody] at h; cases h)
  obtain ⟨S1, S2⟩ := stmt_step Hb hm hbody hind
  have hp := counted_probe_proj hB n
  refine ⟨fun s' hs => ?_, fun c hs hexp => vTrapFrom_mapW hp (S2 c (hstep.trans hs) hexp)⟩
  obtain ⟨⟨b', k', ρ', w'⟩, hstar, hM⟩ := S1 s' (hstep.trans hs)
  exact ⟨b', k', ρ', w', vstar_mapW hp hstar, hM⟩

/-- **A `call`/`call_indirect` statement, counted, for a family** (`stmt_stepI_call` for `sem`). -/
theorem stmt_stepG_call (hni : NoncallIndep sem) {n : Nat} {s : Clif.State}
    (Hs : DriverHyp f vc ctx st0 R gn bl A (sem n) MRW (env.only (Clif.Invoked env p s)) p)
    (hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1)
    {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MRW slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hcl : stm.inst.isCallLike = true)
    (hind : ∀ sig callee args, stm.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ b' k' ρ' w', Star (VStep vc (ISem.counted sem)) (.run ⟨b, k, ρ, (w, n)⟩)
        (.run ⟨b', k', ρ', (w', n + 1)⟩) ∧ Match f ctx R gn bl A MRW slots s' ⟨b', k', ρ', w'⟩) ∧
    (∀ c, Clif.step env p s = .trapped c → explicitTrapInst stm.inst = true →
      VTrapFrom vc (ISem.counted sem) ⟨b, k, ρ, (w, n)⟩ c) := by
  have hstep : Clif.step (env.only (Clif.Invoked env p s)) p s = Clif.step env p s :=
    Clif.step_only fun _ _ _ h => h
  obtain ⟨B, j, hB, -, hjlt, hstm, rfl, hnext, htrap⟩ := stmt_run Hs hm hbody hind
  obtain ⟨L, hL⟩ := Hs.blow hB
  obtain ⟨vb, hvb, -, -, -, -, -, -, hcode, htne, -⟩ := Hs.shape.blk b B L hB hL
  obtain ⟨hsegat, hlt⟩ := seg_at hcode htne hjlt
  have h1 := hseg b B j stm hB hstm hcl
  have hle : callsI (seg f R bl b j) ≤ 1 := by omega
  refine ⟨fun s' hs => ?_, fun c hs hexp => ?_⟩
  · obtain ⟨ρ', w', hsr, hM⟩ := hnext s' (hstep.trans hs)
    have hsrI : seqRun (ISem.counted sem) (seg f R bl b j) ρ (w, n) =
        some (.fall ρ' (w', n + 1)) := by
      rw [seqRun_counted_le1 hni hle ρ w n, hsr]
      simp [SeqEnd.liftW, h1]
    rw [pos_succ] at hlt hM
    exact ⟨_, _, ρ', w', seqRun_fall_star hvb hsegat hlt hsrI, hM⟩
  · obtain ⟨k', i, ops, ρ₁, w₁, outs, w₂, hsr, htc⟩ := htrap c (hstep.trans hs) hexp
    have hsrI := seqRun_counted_le1 hni hle ρ w n
    rw [hsr] at hsrI
    obtain ⟨hstar, -, hi, hops, hsem, -, -⟩ := seqRun_stop_star hvb hsegat hsrI
    exact ⟨b, _, ρ₁, _, vb, i, ops, outs, _, hstar, hvb, hi, hops, hsem, htc⟩

/-- **A terminator other than `try_call`, counted, for a family** (the probe: no VCode call). -/
theorem term_stepG (hB : ProbeOf semB sem) {n : Nat}
    (Hb : DriverHyp f vc ctx st0 R gn bl A (semB n) MRW (env.only fun _ _ _ => False) p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MRW slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    (hnt : s.frame.term.isTry = false) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ b' k' ρ' w', Star (VStep vc (ISem.counted sem)) (.run ⟨b, k, ρ, (w, n)⟩)
        (.run ⟨b', k', ρ', (w', n)⟩) ∧ Match f ctx R gn bl A MRW slots s' ⟨b', k', ρ', w'⟩) ∧
    (∀ vals cm, Clif.step env p s = .done vals cm →
      ∃ us outs w' sv, VRetFrom vc (ISem.counted sem) ⟨b, k, ρ, (w, n)⟩ us outs (w', n) ∧
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        s.frame.getMany (sretRet f) = .ok sv ∧ AllHold (vals ++ sv) outs ∧
        MRW slots s.mem w' ∧ cm = (s.mem.free (slots.map (·.2))).leave) ∧
    (∀ c, Clif.step env p s = .trapped c →
      VTrapFrom vc (ISem.counted sem) ⟨b, k, ρ, (w, n)⟩ c) := by
  have hnr : ∀ fn args, s.frame.body = [] → s.frame.term ≠ .returnCall fn args := by
    intro fn args _ h
    obtain ⟨-, -, -, -, B, j, hB, hterm, -⟩ := hm
    exact Hb.noTail B (List.mem_of_getElem? hB) fn args (hterm.symm.trans h)
  have hstep : Clif.step (env.only fun _ _ _ => False) p s = Clif.step env p s :=
    step_none_of_callNum (by simp [callNum, hbody, hnt]) hnr
  obtain ⟨T1, T2, T3⟩ := term_step_abi Hb hm hbody hnt
  have hp := counted_probe_proj hB n
  refine ⟨fun s' hs => ?_, fun vals cm hs => ?_,
    fun c hs => vTrapFrom_mapW hp (T3 c (hstep.trans hs))⟩
  · obtain ⟨⟨b', k', ρ', w'⟩, hstar, hM⟩ := T1 s' (hstep.trans hs)
    exact ⟨b', k', ρ', w', vstar_mapW hp hstar, hM⟩
  · obtain ⟨us, outs, w', sv, hret, h1, h2, h3, h4, h5, h6⟩ := T2 vals cm (hstep.trans hs)
    exact ⟨us, outs, w', sv, vRetFrom_mapW hp hret, h1, h2, h3, h4, h5, h6⟩

end fam

/-- **A statement without an extern call, counted**: the probe (`noCall`, the environment
answering nothing) runs its segment, which therefore executes no VCode call. -/
theorem stmt_stepI_noCall {n : Nat}
    (Hb : DriverHyp f vc ctx st0 R gn bl A (csem F fctx (XI.at n).noCall) MR
      (env.only fun _ _ _ => False) p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : Arm.ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hnc : stm.inst.isCallLike = false)
    (hind : ∀ sig callee args, stm.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ b' k' ρ' w', Star (VStep vc (csemI F fctx XI)) (.run ⟨b, k, ρ, (w, n)⟩)
        (.run ⟨b', k', ρ', (w', n)⟩) ∧ Match f ctx R gn bl A MR slots s' ⟨b', k', ρ', w'⟩) ∧
    (∀ c, Clif.step env p s = .trapped c → explicitTrapInst stm.inst = true →
      VTrapFrom vc (csemI F fctx XI) ⟨b, k, ρ, (w, n)⟩ c) := by
  exact stmt_stepG_noCall (probeOf_csem F fctx XI) Hb hm hbody hnc hind

/-- **A `call`/`call_indirect` statement, counted**: its segment runs with `XI.at n` in the
environment restricted to its invocation, and has one VCode call: the counter goes to `n + 1`. -/
theorem stmt_stepI_call {n : Nat} {s : Clif.State}
    (Hs : DriverHyp f vc ctx st0 R gn bl A (csem F fctx (XI.at n)) MR
      (env.only (Clif.Invoked env p s)) p)
    (hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1)
    {b k : Nat} {ρ : Nat → CV} {w : Arm.ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hcl : stm.inst.isCallLike = true)
    (hind : ∀ sig callee args, stm.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ b' k' ρ' w', Star (VStep vc (csemI F fctx XI)) (.run ⟨b, k, ρ, (w, n)⟩)
        (.run ⟨b', k', ρ', (w', n + 1)⟩) ∧ Match f ctx R gn bl A MR slots s' ⟨b', k', ρ', w'⟩) ∧
    (∀ c, Clif.step env p s = .trapped c → explicitTrapInst stm.inst = true →
      VTrapFrom vc (csemI F fctx XI) ⟨b, k, ρ, (w, n)⟩ c) := by
  exact stmt_stepG_call (noncallIndep_csem F fctx XI) Hs hseg hm hbody hcl hind

/-- **A terminator other than `try_call`, counted** (the probe: no VCode call). -/
theorem term_stepI {n : Nat}
    (Hb : DriverHyp f vc ctx st0 R gn bl A (csem F fctx (XI.at n).noCall) MR
      (env.only fun _ _ _ => False) p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : Arm.ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    (hnt : s.frame.term.isTry = false) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ b' k' ρ' w', Star (VStep vc (csemI F fctx XI)) (.run ⟨b, k, ρ, (w, n)⟩)
        (.run ⟨b', k', ρ', (w', n)⟩) ∧ Match f ctx R gn bl A MR slots s' ⟨b', k', ρ', w'⟩) ∧
    (∀ vals cm, Clif.step env p s = .done vals cm →
      ∃ us outs w' sv, VRetFrom vc (csemI F fctx XI) ⟨b, k, ρ, (w, n)⟩ us outs (w', n) ∧
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        s.frame.getMany (sretRet f) = .ok sv ∧ AllHold (vals ++ sv) outs ∧
        MR slots s.mem w' ∧ cm = (s.mem.free (slots.map (·.2))).leave) ∧
    (∀ c, Clif.step env p s = .trapped c → VTrapFrom vc (csemI F fctx XI) ⟨b, k, ρ, (w, n)⟩ c) := by
  exact term_stepG (probeOf_csem F fctx XI) Hb hm hbody hnt

end steps

end E2E
