import FV.Concurrency.CallLayers
import FV.Concurrency.CallRets
import FV.Concurrency.CallRetsAlloc

/-!
# All layers pausing at calls and returns, with the return's contract (#473, (1))

**`arm_isel_refinesCR`**: `CallLayers.arm_isel_refinesC` with layers 2–4a pausing at done
`return`s too (`CallRets.isel_alloc_refinesCR`, through `CallLayers.arm_isel_refinesG2`). Where
layer 4b pauses at the `rets` item of the return, **the activation's return contract** holds
(`CallRetsAlloc.ret_link`, `rets_alloc`): the CLIF `return` is done with values `vals` and
memory `cm`; the epilogue and `ret` of the activation's own step (`RA.step`), from the Arm state
at the pause, reach the return address with `sp` as at entry, the memory unchanged, every
callee-saved register holding (up to `ckeep`) the allocation checker's entry value `r₀`, and the
`rets`' values — which hold `vals` (`PrefixHold`) — in their fixed registers; the CLIF memory
before the return is related by `MR` to the VCode world, which `Q` relates to the Arm state.
-/

namespace Concurrency.CallRetsEnd

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine
  ThreadCompose IselCall IselCallRet CallRets CallRetsAlloc ArmAllocThread E2E

/-- **The return contract at a `rets` pause** (module doc). The relation at the `rets` is `QA`
(in a return tail the store differs from the machine's at the restored registers). -/
def RetEnd (RA : RL) (ra : BitVec 64) (env : Clif.Env) (p : Clif.Program) (MR : MemRelT)
    (slots : List (Clif.SlotId × Nat)) (r₀ : Reg → CV) (x : ArmState) (s' : Clif.State) : Prop :=
  ∃ b k allocs its m w vb us ops ρ vals cm n,
    QA RA x (.run ⟨b, .op k allocs :: its, m, w⟩) ∧ RA.vc.blocks[b]? = some vb ∧
    vb.insts[k]? = some (.rets us) ∧ (MInst.rets us).operands = .ok ops ∧
    Clif.step env p s' = .done vals cm ∧ PrefixHold vals (vuses ops ρ) ∧ MR slots s'.mem w ∧
    cm = (s'.mem.free (slots.map (·.2))).leave ∧
    (∀ i < n, RA.GoodX (iterN RA.step i x)) ∧
    Arm.r .PC (iterN RA.step n x) = ra ∧ Arm.r .ERR (iterN RA.step n x) = .None ∧
    spv (iterN RA.step n x) = spv RA.s0 ∧ (iterN RA.step n x).mem = x.mem ∧
    ((iterN RA.step n x).program = x.program ∧ xreg 29 (iterN RA.step n x) = xreg 29 RA.s0) ∧
    (∀ r ∈ calleeSaved, ckeep r (regVal (iterN RA.step n x) r) = ckeep r (r₀ r)) ∧
    ∀ (j : Nat) (v q : Reg) (y : CV), us[j]? = some (v, q) → (vuses ops ρ)[j]? = some y →
      regVal (iterN RA.step n x) q = y

/-- **All layers from a segment's start, layers 2–4a given, pausing at calls and at returns
with their contract** (`arm_isel_refinesCR`, `arm_isel_refines_entryCR`). -/
theorem arm_isel_refinesCRG {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {ra : BitVec 64} (hent : AbiCall RA.fb RA.base ra RA.s0)
    {f : Clif.Function} {vc : VCode} {ctx : Ctx} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {MR : MemRelT}
    {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
    (hX : TlsMemFree RA.X) (hX0 : NoCall RA.X)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV}
    (hr₀ : ∀ r ∈ RA.af.saves, ckeep r (r₀ r) = ckeep r (regVal RA.s0 r))
    {s : Clif.State} {cM : MState CV ArmState} {x : ArmState}
    {mon : Mon}
    (hLA : ∀ {trM : List (List Ev)} {cE : MConf CV ArmState},
      MTRun RA.vc RA.rf (csem RA.F RA.ctx RA.X) ckeep (cEvs RA.F RA.ctx) (.run cM) trM cE →
      ∃ m trS t ψ, m ≤ trM.length ∧ CRun env p (.run s) trS t ∧
        Refines Maps (fun _ => False) (StepPair (conv (trM.take m))) trS (conv (trM.take m)) ψ ∧
        ((((m = trM.length ∧ ∃ cM', MStep RA.vc (csem RA.F RA.ctx RA.X) ckeep RA.rf cE cM') ∨
            Stop env p t) ∧
            ∀ v, t = .ret v → m = trM.length) ∨
          (m = trM.length ∧ ∃ s' vV' vP' cM', t = .run s' ∧ AtCallS s' ∧ cE = .run cM' ∧
            Match f ctx R gn bl A MR slots s' vV' ∧
            PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
            MatchRun cc ins ckeep r₀ cM' vP') ∨
          (m = trM.length ∧ ∃ s' vR trR vV' vP' vals cm, t = .run s' ∧ AtRetS s' ∧
            Match f ctx R gn bl A MR slots s' vR ∧
            VTRun vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) (.run vR) trR vV' ∧
            (∀ e ∈ trR, e = []) ∧
            PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' vV' vP' ∧
            Backend.Proof.Match cc ins ckeep r₀ cE vP' ∧ Clif.step env p s' = .done vals cm ∧
            ∃ us outs w', VRetFrom vc (csem RA.F RA.ctx RA.X) vR us outs w' ∧
              us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
              PrefixHold vals outs ∧ MR slots s'.mem w' ∧
              cm = (s'.mem.free (slots.map (·.2))).leave)))
    (hq : Q RA x (.run cM)) (hA : AInv RA (.run cM))
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (x, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CRun env p (.run s) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE cE, PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ RelQ RA tE cE ∧
          AtRets RA cE) ∨
        (∃ tE s' vV' vP' cM', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧
          RelQ RA tE (.run cM') ∧ Pause RA (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
          Match f ctx R gn bl A MR slots s' vV' ∧
          PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
          MatchRun cc ins ckeep r₀ cM' vP') ∨
        (∃ tE s', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ t = .run s' ∧
          AtRetS s' ∧ (RetEnd RA ra env p MR slots r₀ tE.1 s' ∨
            ∃ cE, RelQ RA tE cE ∧ (Done RA cE ∨ AtCall RA cE)))) := by
  -- the pause relation: a call with the three relations, or a done return with its facts
  let RelR : Clif.State → MConf CV ArmState → Prop := fun s' cE =>
    (∃ cM' vV' vP', AtCallS s' ∧ cE = .run cM' ∧ Match f ctx R gn bl A MR slots s' vV' ∧
      PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
      MatchRun cc ins ckeep r₀ cM' vP') ∨
    (AtRetS s' ∧ ∃ vR trR vV' vP' vals cm, Match f ctx R gn bl A MR slots s' vR ∧
      VTRun vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) (.run vR) trR vV' ∧
      (∀ e ∈ trR, e = []) ∧
      PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' vV' vP' ∧
      Backend.Proof.Match cc ins ckeep r₀ cE vP' ∧ Clif.step env p s' = .done vals cm ∧
      ∃ us outs w', VRetFrom vc (csem RA.F RA.ctx RA.X) vR us outs w' ∧
        PrefixHold vals outs ∧ MR slots s'.mem w' ∧
        cm = (s'.mem.free (slots.map (·.2))).leave)
  obtain ⟨k, trS, t, ψ, hk, hrun, href, hend⟩ := CallLayers.arm_isel_refinesG2 hR hsc hgv hg hX
    hX0 (Rel := RelR) (fun hM => by
      obtain ⟨m, trS, t, ψ, hm, hrun, href, hendm⟩ :=
        hLA hM
      refine ⟨m, trS, t, ψ, hm, hrun, href, ?_⟩
      rcases hendm with h | ⟨h1, s', vV', vP', cM', ht, hat, hcE, h5, h6, h7⟩ |
        ⟨h1, s', vR, trR, vV', vP', vals, cm, ht, hat, h5, h6, h7, h8, h9, h10, us, outs, w', h11,
          -, -, h12, h13, h14⟩
      · exact .inl h
      · exact .inr ⟨h1, s', ht, .inl ⟨cM', vV', vP', hat, hcE, h5, h6, h7⟩⟩
      · exact .inr ⟨h1, s', ht, .inr ⟨hat, vR, trR, vV', vP', vals, cm, h5, h6, h7, h8, h9, h10,
          us, outs, w', h11, h12, h13, h14⟩⟩) hq hA hr
  refine ⟨k, trS, t, ψ, hk, hrun, href, ?_⟩
  rcases hend with h | h | h | ⟨tE, s', cE, hpre, hrq, hP, ht, hrel⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  rcases hrel with ⟨cM', vV', vP', hat, rfl, h5, h6, h7⟩ |
    ⟨hat, vR, trR, vV', vP', vals, cm, h5, h6, h7, h8, h9, h10, us0, outs, w', h11, h12, h13, h14⟩
  · exact .inr (.inr (.inr (.inl ⟨tE, s', vV', vP', cM', hpre, hrq, hP, ht, hat, h5, h6, h7⟩)))
  refine .inr (.inr (.inr (.inr ⟨tE, s', hpre, ht, hat, ?_⟩)))
  rcases hP with hD | hcall | ⟨b, kk, allocs, its, m, w, vb, us, rfl, hvb, hi⟩
  · exact .inr ⟨cE, hrq, .inl hD⟩
  · exact .inr ⟨cE, hrq, .inr hcall⟩
  left
  -- the prepared code's configuration is at the `rets`
  cases vP' with
  | ret => exact h9.elim
  | halt => exact h9.elim
  | run vs =>
    obtain ⟨b', k', ρ, w''⟩ := vs
    have h9' := h9
    obtain ⟨hb, hw, vb', a, out, hvb', hrunI, -, -⟩ := h9'
    simp only at hb hw hvb' hrunI
    subst hb hw
    obtain ⟨-, hk', -⟩ := runItems_op hrunI
    subst hk'
    obtain ⟨ops, hops, rfl, rfl, rfl⟩ := ret_link H3 h6 h7 h8 hvb hi h11
    obtain ⟨n, ops2, hops2, hgood, hpc, herr, hsp, hmem, hprog, hcs, hres⟩ :=
      rets_alloc hR hent hc hr₀ hrq h9 hvb hi
    rw [hops] at hops2; cases hops2
    exact ⟨b, kk, allocs, its, m, _, vb, _, ops, ρ, vals, cm, n, hrq, hvb, hi, hops, h10, h12,
      h13, h14, hgood, hpc, herr, hsp, hmem, hprog, hcs, hres⟩


/-- **All layers from related configurations, pausing at calls and at returns with their
contract** (module doc). -/
theorem arm_isel_refinesCR {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {ra : BitVec 64} (hent : AbiCall RA.fb RA.base ra RA.s0)
    {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {MR : MemRelT}
    {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat}
    {syms : String → Option Nat}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk RA.F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree RA.X) (hX0 : NoCall RA.X)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV}
    (hr₀ : ∀ r ∈ RA.af.saves, ckeep r (r₀ r) = ckeep r (regVal RA.s0 r))
    {s : Clif.State} {vV vP : VState CV ArmState} {cM : MState CV ArmState} {x : ArmState}
    {mon : Mon}
    (hm2 : Match f ctx R gn bl A MR slots s vV)
    (hm3 : PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV) (.run vP))
    (hm4 : MatchRun cc ins ckeep r₀ cM vP) (hq : Q RA x (.run cM)) (hA : AInv RA (.run cM))
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (x, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CRun env p (.run s) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE cE, PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ RelQ RA tE cE ∧
          AtRets RA cE) ∨
        (∃ tE s' vV' vP' cM', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧
          RelQ RA tE (.run cM') ∧ Pause RA (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
          Match f ctx R gn bl A MR slots s' vV' ∧
          PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
          MatchRun cc ins ckeep r₀ cM' vP') ∨
        (∃ tE s', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ t = .run s' ∧
          AtRetS s' ∧ (RetEnd RA ra env p MR slots r₀ tE.1 s' ∨
            ∃ cE, RelQ RA tE cE ∧ (Done RA cE ∨ AtCall RA cE)))) := by
  exact arm_isel_refinesCRG hR hsc hgv hg hent hX hX0 H3 hc hr₀
    (fun hM => isel_alloc_refinesCR H hchk hMR hMRw hX hX0 H3 hc hm2 hm3 hm4 hM) hq hA hr

/-- **All layers from the activation's entry configuration, pausing at calls and at returns
with their contract** (`arm_isel_refinesCRG` with `CallRets.isel_alloc_refines_entryCR`; as
`CallLayers.arm_isel_refines_entryC`). -/
theorem arm_isel_refines_entryCR {RA : RL} (hR : RA.Wf) (hsc : MemScopeLSC RA)
    (hgv : RA.gv = fun _ _ => False) {g : ArmState → ArmState} (hg : AgreesAt RA g)
    {ra : BitVec 64} (hent : AbiCall RA.fb RA.base ra RA.s0)
    {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {MR : MemRelT}
    {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat}
    {syms : String → Option Nat}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hMR : MemRelOk RA.F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree RA.X) (hX0 : NoCall RA.X)
    (hMem : MemRefines RA.F sb syms (csem RA.F RA.ctx RA.X)) (hMRs : MRStable RA.F MR)
    (hreg : ∀ off, ArgLoc.stack off ∉ locsOf f.sig)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    (hm3 : ∀ (ρ₀ : Nat → CV) (w₀ : ArmState), PMatch vc RA.vc (csem RA.F RA.ctx RA.X)
      (cEvs RA.F RA.ctx) L ss' (VConf.init ρ₀ w₀) (VConf.init ρ₀ w₀))
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0)
    (hm4 : ∀ (m₀ : Loc → CV) (ρ₀ : Nat → CV) (w₀ : ArmState),
      Backend.Proof.Match cc ins ckeep (fun r => m₀ (.reg r)) (MConf.init RA.rf m₀ w₀)
        (VConf.init ρ₀ w₀))
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {m₀ : Loc → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hr₀ : ∀ r ∈ RA.af.saves, ckeep r (m₀ (.reg r)) = ckeep r (regVal RA.s0 r))
    (hargs : ArgsAtEntry RA.F f.sig args w₀) {x : ArmState} {mon : Mon}
    (hq : Q RA x (MConf.init RA.rf m₀ w₀)) (hA : AInv RA (MConf.init RA.rf m₀ w₀))
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv RA) (x, mon) ls t') :
    ∃ k trS t ψ, k ≤ ls.length ∧ CRun env p (.run cs) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨
        (∃ tE cE, PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ RelQ RA tE cE ∧
          AtRets RA cE) ∨
        (∃ tE s' vV' vP' cM', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧
          RelQ RA tE (.run cM') ∧ Pause RA (.run cM') ∧ t = .run s' ∧ AtCallS s' ∧
          Match f ctx R gn bl A MR slots s' vV' ∧
          PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP') ∧
          MatchRun cc ins ckeep (fun r => m₀ (.reg r)) cM' vP') ∨
        (∃ tE s', PRun Policy.arm g (OkPriv RA) (x, mon) (ls.take k) tE ∧ t = .run s' ∧
          AtRetS s' ∧ (RetEnd RA ra env p MR slots (fun r => m₀ (.reg r)) tE.1 s' ∨
            ∃ cE, RelQ RA tE cE ∧ (Done RA cE ∨ AtCall RA cE)))) :=
  arm_isel_refinesCRG hR hsc hgv hg hent hX hX0 H3 hc hr₀ (s := cs)
    (cM := ⟨0, RA.rf.blocks[0]!.toList, m₀, w₀⟩)
    (fun hM => isel_alloc_refines_entryCR (ρ₀ := fun _ => 0) H hchk hMR hMRw hX hX0 hMem hMRs
      hreg hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs H3 hc (hm3 _ _)
      (hm4 m₀ (fun _ => 0) w₀) hM) hq hA hr

end Concurrency.CallRetsEnd
