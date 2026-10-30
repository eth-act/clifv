import FV.Concurrency.CallCalleeRet
import FV.Concurrency.CallRetPremises
import FV.E2E.RegLevelU

/-!
# The caller's pause at a call, at every layer (#473, step (3))

`CallRetsN.arm_isel_refinesCRN` ends a run at a call with the three relations (layer 2's
`Match` at a CLIF call statement, `prepare`'s `PMatch`, the checker's `MatchRun`) and the
register-level relation `RelQ` at a pause (`Pause`: done, at a call or at a `rets` item).

* `setTargets_call`, `sameInst_call`: `prepare` keeps a `call` instruction;
* `pmatch_call_fwd`: at a `call` of the original VCode, `prepare`'s relation is the block
  correspondence to the same `call` in the prepared code;
* **`atCall_of_pause`**: at that end, the allocated configuration is at the `call` item: the
  item `.op k allocs`, with the prepared code's `call` at `k`, the checker's configuration at
  `k` (the pause is neither a `rets` item nor done elsewhere: a `move` steps, the block does not
  end before its `call`).
-/

namespace Concurrency.CallResumeAll

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck ThreadRefine IselCall IselCallRet ArmAllocThread E2E

theorem setTargets_call (info : CallInfo) (ls : List Label) :
    (MInst.call info).setTargets ls = none := by
  simp [MInst.setTargets]

/-- `prepare` keeps a `call` instruction. -/
theorem sameInst_call {info : CallInfo} {i' : MInst} (h : SameInst (.call info) i') :
    i' = .call info := by
  rcases h with h | h
  · exact h
  · rw [setTargets_call] at h; cases h

/-- **At a `call` of the original VCode, `prepare`'s relation is the block correspondence** to
the same `call` of the prepared code. -/
theorem pmatch_call_fwd {vc vcp : VCode} {L : Nat → Prop} {ss ss' : Array (Array Nat)}
    (H : PrepFacts vc vcp L ss ss') {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (hX0 : NoCall X) {ev : MInst → List CV → ArmState → List Ev} {b k : Nat} {ρ : Nat → CV}
    {w : ArmState} {vP : VConf CV ArmState}
    (hm : PMatch vc vcp (csem F fc X) ev L ss' (.run ⟨b, k, ρ, w⟩) vP) {vb : VBlock}
    {info : CallInfo} (hvb : vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.call info)) :
    ∃ b' vb', vP = .run ⟨b', k, ρ, w⟩ ∧ vcp.blocks[b']? = some vb' ∧
      vb'.insts[k]? = some (.call info) ∧ L b ∧ sigmaOf vc vcp b = some b' := by
  cases hm with
  | blk hLb hσ =>
    obtain ⟨vb0, vb1, hvb0, hvb1, -, -, -, hins, -⟩ := (H.kept _ _ hLb hσ).blocks
    rw [hvb] at hvb0; cases hvb0
    obtain ⟨i'', hi'', hs⟩ := hins k _ hi
    exact ⟨_, vb1, rfl, hvb1, by rw [hi'', sameInst_call hs], hLb, hσ⟩
  | pend _ _ hvb' hi' _ hsem =>
    rw [hvb] at hvb'; cases hvb'
    rw [hi] at hi'; cases hi'
    simp only [csem] at hsem
    rw [hX0] at hsem
    simp at hsem

/-- **At the call end of `arm_isel_refinesCRN` the allocated configuration is at the `call`
item** (module doc). -/
theorem atCall_of_pause {RA : RL} (hX0 : NoCall RA.X) {f : Clif.Function} {vc : VCode}
    {ctx : Ctx} {st0 : LState} {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow}
    {A : Nat → Nat → List Clif.ValueId} {MR : MemRelT} {env : Clif.Env} {p : Clif.Program}
    {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) MR env p)
    (hchk : threadCheckBlC f bl = true) {L : Nat → Prop} {ss ss' : Array (Array Nat)}
    (H3 : PrepFacts vc RA.vc L ss ss') {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV} {s' : Clif.State}
    {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState} (hP : Pause RA (.run cM'))
    (hat : AtCallS s') (hm2 : Match f ctx R gn bl A MR slots s' vV')
    (hm3 : PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP'))
    (hm4 : MatchRun cc ins ckeep r₀ cM' vP') :
    ∃ b k allocs its m w vb info, cM' = ⟨b, .op k allocs :: its, m, w⟩ ∧
      vP' = ⟨b, k, vP'.ρ, w⟩ ∧ RA.vc.blocks[b]? = some vb ∧ vb.insts[k]? = some (.call info) ∧
      ∃ b0, vV' = ⟨b0, k, vP'.ρ, w⟩ ∧ L b0 ∧ sigmaOf vc RA.vc b0 = some b := by
  obtain ⟨vb0, n, us, ds, hvb0, hi0⟩ := match_atCall H hchk hm2 hat
  obtain ⟨b0, k0, ρ0, w0⟩ := vV'
  obtain ⟨b', vb', e, hvb', hi', hL, hσ⟩ := pmatch_call_fwd H3 hX0 hm3 hvb0 hi0
  cases e
  obtain ⟨cb, cits, cm, cw⟩ := cM'
  obtain ⟨hb, hw, vb, a, out, hvb, hrun, -, -⟩ := hm4
  simp only at hb hw hvb hrun
  subst hb hw
  rw [hc.vc_eq, hvb'] at hvb
  cases hvb
  cases cits with
  | nil =>
    have := (runItems_nil hrun).1
    have := (Array.getElem?_eq_some_iff.mp hi').1
    omega
  | cons it its =>
    cases it with
    | move src dst =>
      exfalso
      rcases hP with (⟨_, _, _, e⟩ | ⟨_, e⟩ | hD) | ⟨_, _, _, _, _, _, _, _, e, -⟩ |
          ⟨_, _, _, _, _, _, _, _, e, -⟩
      · cases e
      · cases e
      · exact hD [] _ .move
      · cases e
      · cases e
    | op k allocs =>
      obtain ⟨-, rfl, -⟩ := runItems_op hrun
      exact ⟨_, k, allocs, its, cm, _, vb', _, rfl, rfl, hvb', hi', b0, rfl, hL, hσ⟩

open CallRetResume CallResumeL IselResume in
/-- **The caller resumed at every layer after its callee's return, from the return's ABI facts**
(module doc): from the call end of `arm_isel_refinesCRN` and a state `y` after the callee's
return at the address after the `bl` (no error, `sp`, the callee-saved registers up to `ckeep`
and the caller's `RA.FK` memory as at the call, the caller's program; its returned values `ysB`
in the registers `usB`, which are the call's def registers; a memory relation `MemRel FB` of the
callee's CLIF memory agreeing with `y` outside `FB`), the CLIF thread after the call and `y` are
related by all the relations at the item after the call. `resume_allP` derives these facts from
a compiled callee's `RetC`; an external callee's event contract states them. -/
theorem resume_allX {RA : RL} (hRA : RA.Wf) (hgv : RA.gv = fun _ _ => False)
    (hX0 : NoCall RA.X) {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {Γ : E2E.Rel} {c : BitVec 64} {env : Clif.Env} {p : Clif.Program}
    {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) (RelW Γ f c) env p)
    (hchk : threadCheckBlC f bl = true) (hlow : lowerCheck f vc = true) (hind : indSigs f = [])
    (hv : verifiable f = true) (hnt : f.blocks.all (fun B => !B.term.isTry) = true)
    (hout0 : vc.outgoing = 0) (hΓF : Γ.F = RA.F) (hslot : RA.ctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → RA.X.sym n 0 = BitVec.ofNat 64 b)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV}
    (hvdef : ∀ (b : Nat) (vb : VBlock) (k : Nat) (info : CallInfo),
      RA.vc.blocks[b]? = some vb → vb.insts[k]? = some (.call info) →
      ∀ d ∈ info.defs, ∃ (n : Nat) (c : RegClass), d.2 = .vreg n c)
    {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState}
    (hq : Q RA x (.run cM')) (hA : AInv RA (.run cM')) (hP : Pause RA (.run cM'))
    (hat : AtCallS s') (hm2 : Match f ctx R gn bl A (RelW Γ f c) slots s' vV')
    (hm3 : PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP'))
    (hm4 : MatchRun cc ins ckeep r₀ cM' vP') {y : ArmState}
    (hpc : Arm.r .PC y = Arm.r .PC x + 4#64) (herr : Arm.r .ERR y = .None)
    (hsp : spOf y = spOf x) (hmem : ∀ a, RA.FK a → y.mem a = x.mem a)
    (hcs : ∀ r ∈ calleeSaved, ckeep r (regVal y r) = ckeep r (regVal x r))
    (hprog : y.program = x.program) (hfp : xreg 29 y = xreg 29 x)
    {usB : List (Reg × Reg)} {ysB : List CV} {rvals : List Clif.Val}
    (hus : ∀ (j : Nat) (v q : Reg) (u : CV), usB[j]? = some (v, q) → ysB[j]? = some u →
      regVal y q = u)
    (hpreB : PrefixHold rvals ysB)
    {FB : BitVec 64 → Prop} {cmB : Clif.Mem} {wB : ArmState} {bases : List Nat}
    (hB : MemRel FB Γ.syms cmB wB)
    (hval : ∀ a n, ((cmB.free bases).leave).valid a n = true → s'.mem.valid a n = true)
    (hmemB : ∀ a, ¬ FB a → y.mem a = wB.mem a)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s'.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hcl : stm.inst = .call fn args)
    {ext : Clif.ExtFunc} (hext : s'.frame.func.extern? fn = some ext)
    (huniq : ∀ e ∈ f.externs, e.2.name = ext.name → e.2 = ext)
    {vals : List Clif.Val} (hvals : s'.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params)
    (hrty : rvals.map (·.ty) = Clif.AbiParam.tys ext.sig.returns)
    {regs' : Clif.Regs} (hregs : s'.frame.regs.setMany stm.results rvals = some regs')
    (habi : ∀ (vb : VBlock) (info : CallInfo),
      RA.vc.blocks[vP'.b]? = some vb → vb.insts[vP'.k]? = some (.call info) →
      (∀ (j : Nat) (d : Reg × Reg), info.defs[j]? = some d → ∃ v, usB[j]? = some (v, d.1)) ∧
      rvals.length ≤ info.defs.length ∧ info.defs.length = (sigRets ext.sig).length) :
    ∃ vV'' vP'' cM'',
      Match f ctx R gn bl A (RelW Γ f c) slots { s' with
          frame := { s'.frame with regs := regs', body := rest }, mem := (cmB.free bases).leave }
        vV'' ∧
      PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV'') (.run vP'') ∧
      MatchRun cc ins ckeep r₀ cM'' vP'' ∧ Q RA y (.run cM'') ∧ AInv RA (.run cM'') := by
  obtain ⟨b, k, allocs, its, m, w, vb, info, rfl, hvP, hvb, hi, b0, hvV, hL, hσ⟩ :=
    atCall_of_pause hX0 H hchk H3 hc hP hat hm2 hm3 hm4
  obtain ⟨pb, pk, ρ, pw⟩ := vP'
  simp only at hvP hvV
  cases hvP
  subst hvV
  have hst := q_stRel hq
  obtain ⟨-, -, -, regs2, -, -, -, -, -, -, -, -, -, cc2, wh, ops, hal2, -, -, -, -, hops, hstat,
    -⟩ := q_op hq hvb hi
  obtain ⟨regs, hal, hsz, -, -⟩ := q_regs hq hvb hi hops
  have hsz' : allocs.size = ops.size := by rw [hal, Array.size_map, hsz]
  have hv' := hvdef b vb k info hvb hi
  have hdef := hdef_of_q hq hvb hi hv' hops
  obtain ⟨hreg, hlenv, hlen⟩ := habi vb info hvb hi
  have hstat' : cc2.checkStatic wh ops allocs (MInst.call info).clobbers = .ok () := by
    rw [hal2]; exact hstat
  -- the return's facts give the resume premises
  have hpres := hpresR_of_callee hRA hst hdef hcs hsp hmem
  have hkeep : ∀ c ∈ (MInst.call info).clobbers, c ∈ calleeSaved →
      ckeep c (regVal y c) = ckeep c (regVal x c) := hkeep_of_callee hcs
  -- layer 2
  have hpre : PrefixHold rvals ((defPairs ops allocs).map fun q => locVal RA.fr y q.2) :=
    prefixHold_outs hv' hops hstat' RA.fr hpreB hus hreg hlenv
  have hlenO : ((defPairs ops allocs).map fun q => locVal RA.fr y q.2).length =
      (sigRets ext.sig).length := by
    have := congrArg List.length (defPairs_locs hv' hops hstat')
    simp only [List.length_map] at this ⊢
    rw [this, hlen]
  have hmrw : RelW Γ f c slots s'.mem w := hm2.2.2.2.1
  have hspw : spv y = spv w := by
    have e := hst.world.1 (.GPR 31#5) (by simp [Masked])
    exact hsp.trans e
  have hrel : RelW Γ f c slots ((cmB.free bases).leave) y :=
    relW_after_callee hmrw hB hval hmemB hspw herr
  obtain ⟨ρ2, hv2, hm2'⟩ := isel_resumeC (fctx := RA.ctx) (X := RA.X) H.shape H.cert H.brIdx
    hchk hlow hind hv hnt H.cfg hout0 hslot hsym hm2 hbody hcl hext huniq hvals htys hrty hregs
    hlenO hpre hrel
  -- layers 3–4b
  have hk : k + 1 < vb.insts.size := by
    obtain ⟨vb0, vb1, hvb0, hvb1, -, -, hsz0, -, -⟩ := (H3.kept b0 _ hL hσ).blocks
    rw [hvb] at hvb1; cases hvb1
    have h0 : k + 1 < vb0.insts.size := by
      cases hv2 with
      | step hvb2 _ _ _ _ hnext =>
        rw [hvb0] at hvb2; cases hvb2
        cases hnext
        assumption
    omega
  obtain ⟨m', hms, hst'⟩ := mstep_callR hq hvb hi hk hops hsz' hpres hkeep RA.X y
  obtain ⟨ρ', hv4, hA'⟩ := alloc_call_vstep hc hm4 hvb hi (fun u w0 r h => by
    simp only [csem, xcallX, Option.map_some, Option.some.injEq] at h
    subst h; rfl) hms
  have hv3 := prep_vstep_next H3 (driverSem_csem _ _ _).toDriverSemG hL hσ hv4
  rw [hΓF] at hv2
  obtain rfl : ρ2 = ρ' := by
    have := vstep_det hv2 hv3
    simp only [VConf.run.injEq, VState.mk.injEq] at this
    simpa using this
  refine ⟨_, _, _, hm2', .blk hL hσ, hA', CallSeg.resumeQW hRA hq hvb hi hpc herr hsp hmem hprog hfp
    hst' (SameWorld.refl _ _), aInv_stepS hRA hq hA hms⟩

open CallRetResume CallResumeL IselResume in
/-- **The caller resumed at every layer after a compiled callee's return** (module doc): from
the call end of `arm_isel_refinesCRN` (the CLIF thread at a call statement, the three relations,
`Q`/`AInv` at the pause) and a callee `RB` entered at the call (its ABI entry state the caller's
state but in the pc and `x30`, its kept addresses containing `RA.FK`) that returned to `y`
(`RetC`; the linked machine back on the caller's program; its returned values `ysB` in its `rets`
registers `usB`, which are the call's def registers; its memory relation `MemRel FB` at its
`rets` agreeing with `y` outside `FB`), the CLIF thread after the call (the callee's values and
memory) and `y` are related by all the relations at the item after the call: the premises of
`arm_isel_refinesCRN` for the caller's next segment. `habi` is asked only at the paused call
instruction (`vP'`'s); `resume_all` asks it at every call. -/
theorem resume_allP {RA RB : RL} (hRA : RA.Wf) (hRB : RB.Wf) (hgv : RA.gv = fun _ _ => False)
    (hX0 : NoCall RA.X) {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {Γ : E2E.Rel} {c : BitVec 64} {env : Clif.Env} {p : Clif.Program}
    {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) (RelW Γ f c) env p)
    (hchk : threadCheckBlC f bl = true) (hlow : lowerCheck f vc = true) (hind : indSigs f = [])
    (hv : verifiable f = true) (hnt : f.blocks.all (fun B => !B.term.isTry) = true)
    (hout0 : vc.outgoing = 0) (hΓF : Γ.F = RA.F) (hslot : RA.ctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → RA.X.sym n 0 = BitVec.ofNat 64 b)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV}
    (hvdef : ∀ (b : Nat) (vb : VBlock) (k : Nat) (info : CallInfo),
      RA.vc.blocks[b]? = some vb → vb.insts[k]? = some (.call info) →
      ∀ d ∈ info.defs, ∃ (n : Nat) (c : RegClass), d.2 = .vreg n c)
    {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState}
    (hq : Q RA x (.run cM')) (hA : AInv RA (.run cM')) (hP : Pause RA (.run cM'))
    (hat : AtCallS s') (hm2 : Match f ctx R gn bl A (RelW Γ f c) slots s' vV')
    (hm3 : PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP'))
    (hm4 : MatchRun cc ins ckeep r₀ cM' vP')
    {ra : BitVec 64} (hent : AbiCall RB.fb RB.base ra RB.s0) {r₀B : Reg → CV} {y : ArmState}
    (hy : RetC RB ra r₀B y)
    (hfx : ∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f RB.s0 = Arm.r f x)
    (hlr : xreg 30 RB.s0 = Arm.r .PC x + 4#64)
    (hm0 : ∀ a, RA.FK a → RB.s0.mem a = x.mem a) (hG : ∀ a, RA.FK a → RB.G a)
    (hr₀B : ∀ r ∈ calleeSaved, ckeep r (r₀B r) =
      ckeep r (locVal RB.fr (iterN RB.step (prologueLines RB.af.saves RB.af.frameSize).length RB.s0) (.reg r)))
    (hprog : y.program = x.program)
    {usB : List (Reg × Reg)} {ysB : List CV} {rvals : List Clif.Val}
    (hus : ∀ (j : Nat) (v q : Reg) (u : CV), usB[j]? = some (v, q) → ysB[j]? = some u →
      regVal y q = u)
    (hpreB : PrefixHold rvals ysB)
    {FB : BitVec 64 → Prop} {cmB : Clif.Mem} {wB : ArmState} {bases : List Nat}
    (hB : MemRel FB Γ.syms cmB wB)
    (hval : ∀ a n, ((cmB.free bases).leave).valid a n = true → s'.mem.valid a n = true)
    (hmemB : ∀ a, ¬ FB a → y.mem a = wB.mem a)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s'.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hcl : stm.inst = .call fn args)
    {ext : Clif.ExtFunc} (hext : s'.frame.func.extern? fn = some ext)
    (huniq : ∀ e ∈ f.externs, e.2.name = ext.name → e.2 = ext)
    {vals : List Clif.Val} (hvals : s'.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params)
    (hrty : rvals.map (·.ty) = Clif.AbiParam.tys ext.sig.returns)
    {regs' : Clif.Regs} (hregs : s'.frame.regs.setMany stm.results rvals = some regs')
    (habi : ∀ (vb : VBlock) (info : CallInfo),
      RA.vc.blocks[vP'.b]? = some vb → vb.insts[vP'.k]? = some (.call info) →
      (∀ (j : Nat) (d : Reg × Reg), info.defs[j]? = some d → ∃ v, usB[j]? = some (v, d.1)) ∧
      rvals.length ≤ info.defs.length ∧ info.defs.length = (sigRets ext.sig).length) :
    ∃ vV'' vP'' cM'',
      Match f ctx R gn bl A (RelW Γ f c) slots { s' with
          frame := { s'.frame with regs := regs', body := rest }, mem := (cmB.free bases).leave }
        vV'' ∧
      PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV'') (.run vP'') ∧
      MatchRun cc ins ckeep r₀ cM'' vP'' ∧ Q RA y (.run cM'') ∧ AInv RA (.run cM'') := by
  obtain ⟨hpc, herr, hsp, hmem, hx29, hcs⟩ := hy
  obtain ⟨he, hsp0, hra⟩ := entry_premises hRB hent hfx hlr
  exact resume_allX hRA hgv hX0 H hchk hlow hind hv hnt hout0 hΓF hslot hsym H3 hc hvdef hq hA hP
    hat hm2 hm3 hm4 (hpc.trans hra) herr (hsp.trans hsp0)
    (fun a ha => (hmem a (hG a ha)).trans (hm0 a ha))
    (fun r hr => (hcs r hr).trans ((hr₀B r hr).trans (he r hr))) hprog
    (hx29.trans (hfx (.GPR 29#5) (by simp) (by simp))) hus hpreB hB hval hmemB
    hbody hcl hext huniq hvals htys hrty hregs habi

open CallRetResume CallResumeL IselResume in
/-- **The caller resumed at every layer after a compiled callee's return** (module doc):
`resume_allP` with `habi` at every call instruction. -/
theorem resume_all {RA RB : RL} (hRA : RA.Wf) (hRB : RB.Wf) (hgv : RA.gv = fun _ _ => False)
    (hX0 : NoCall RA.X) {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {Γ : E2E.Rel} {c : BitVec 64} {env : Clif.Env} {p : Clif.Program}
    {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) (RelW Γ f c) env p)
    (hchk : threadCheckBlC f bl = true) (hlow : lowerCheck f vc = true) (hind : indSigs f = [])
    (hv : verifiable f = true) (hnt : f.blocks.all (fun B => !B.term.isTry) = true)
    (hout0 : vc.outgoing = 0) (hΓF : Γ.F = RA.F) (hslot : RA.ctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → RA.X.sym n 0 = BitVec.ofNat 64 b)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV}
    (hvdef : ∀ (b : Nat) (vb : VBlock) (k : Nat) (info : CallInfo),
      RA.vc.blocks[b]? = some vb → vb.insts[k]? = some (.call info) →
      ∀ d ∈ info.defs, ∃ (n : Nat) (c : RegClass), d.2 = .vreg n c)
    {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState}
    (hq : Q RA x (.run cM')) (hA : AInv RA (.run cM')) (hP : Pause RA (.run cM'))
    (hat : AtCallS s') (hm2 : Match f ctx R gn bl A (RelW Γ f c) slots s' vV')
    (hm3 : PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP'))
    (hm4 : MatchRun cc ins ckeep r₀ cM' vP')
    {ra : BitVec 64} (hent : AbiCall RB.fb RB.base ra RB.s0) {r₀B : Reg → CV} {y : ArmState}
    (hy : RetC RB ra r₀B y)
    (hfx : ∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f RB.s0 = Arm.r f x)
    (hlr : xreg 30 RB.s0 = Arm.r .PC x + 4#64)
    (hm0 : ∀ a, RA.FK a → RB.s0.mem a = x.mem a) (hG : ∀ a, RA.FK a → RB.G a)
    (hr₀B : ∀ r ∈ calleeSaved, ckeep r (r₀B r) =
      ckeep r (locVal RB.fr (iterN RB.step (prologueLines RB.af.saves RB.af.frameSize).length RB.s0) (.reg r)))
    (hprog : y.program = x.program)
    {usB : List (Reg × Reg)} {ysB : List CV} {rvals : List Clif.Val}
    (hus : ∀ (j : Nat) (v q : Reg) (u : CV), usB[j]? = some (v, q) → ysB[j]? = some u →
      regVal y q = u)
    (hpreB : PrefixHold rvals ysB)
    {FB : BitVec 64 → Prop} {cmB : Clif.Mem} {wB : ArmState} {bases : List Nat}
    (hB : MemRel FB Γ.syms cmB wB)
    (hval : ∀ a n, ((cmB.free bases).leave).valid a n = true → s'.mem.valid a n = true)
    (hmemB : ∀ a, ¬ FB a → y.mem a = wB.mem a)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s'.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hcl : stm.inst = .call fn args)
    {ext : Clif.ExtFunc} (hext : s'.frame.func.extern? fn = some ext)
    (huniq : ∀ e ∈ f.externs, e.2.name = ext.name → e.2 = ext)
    {vals : List Clif.Val} (hvals : s'.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params)
    (hrty : rvals.map (·.ty) = Clif.AbiParam.tys ext.sig.returns)
    {regs' : Clif.Regs} (hregs : s'.frame.regs.setMany stm.results rvals = some regs')
    (habi : ∀ (b : Nat) (vb : VBlock) (k : Nat) (info : CallInfo),
      RA.vc.blocks[b]? = some vb → vb.insts[k]? = some (.call info) →
      (∀ (j : Nat) (d : Reg × Reg), info.defs[j]? = some d → ∃ v, usB[j]? = some (v, d.1)) ∧
      rvals.length ≤ info.defs.length ∧ info.defs.length = (sigRets ext.sig).length) :
    ∃ vV'' vP'' cM'',
      Match f ctx R gn bl A (RelW Γ f c) slots { s' with
          frame := { s'.frame with regs := regs', body := rest }, mem := (cmB.free bases).leave }
        vV'' ∧
      PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV'') (.run vP'') ∧
      MatchRun cc ins ckeep r₀ cM'' vP'' ∧ Q RA y (.run cM'') ∧ AInv RA (.run cM'') :=
  resume_allP hRA hRB hgv hX0 H hchk hlow hind hv hnt hout0 hΓF hslot hsym H3 hc hvdef hq hA hP
    hat hm2 hm3 hm4 hent hy hfx hlr hm0 hG hr₀B hprog hus hpreB hB hval hmemB hbody hcl hext
    huniq hvals htys hrty hregs (fun vb info => habi _ vb _ info)

end Concurrency.CallResumeAll
