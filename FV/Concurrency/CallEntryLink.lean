import FV.Concurrency.CallEnterArm
import FV.Concurrency.CallArgsEntry

/-!
# The call end of a caller's segment on the linked machine (#473, step (4))

At the call end of a caller's segment (the CLIF thread at a direct call of `ext`, the three
relations and `Q` at the paused `call` item), with the callee `nB = ext.name` a function of the
link:

* **`Link.call_end`**: the machine's step is the `bl` into `nB` (`step_call`: no events, plain);
  the callee's activation `L.act FB (enter FB x) KB GB` is `Wf`, its ABI entry an `AbiCall`
  returning after the `bl`, its state the caller's but in the pc and `x30` with the caller's
  memory, `Q`/`AInv` at its initial configuration after the prologue (`enter_call`), and the
  call's arguments are where its entry code reads them (`ArgsAtEntry` of its body-entry world,
  `CallArgsEntry.callee_argsAtEntry_sig`, for a callee of signature `ext.sig`);
* `obligations_of_checksA`, **`driverHypT_ofA`**: `IselResume.driverHypT_of` with the arity and
  use-register checks on the driver's lowering `bl` it builds (`callArityC`, `callUseRegsC`), the
  premises `resume_allA` and `call_end` ask of `bl`.
-/

namespace Concurrency.LinkedMachine.Link

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck ThreadRefine IselCall IselCallRet ArmAllocThread E2E SegShape
  CallResumeAll CallResumeChecks CallRetResume CallResumeL IselResume CallArity CallArgsAt
  CallArgsL2 CallArgsEntry ArmFoot ArmInstFoot

variable {L : Link}

/-- **`IselCheck.obligations_of_threadCheckC` with the call checks on its lowering.** -/
theorem _root_.Concurrency.IselCheck.obligations_of_checksA {f : Clif.Function} {vc : VCode}
    (h : lowerCheck f vc = true) (ht : threadCheckC f = true) (ha : callArityC f = true)
    (hu : callUseRegsC f = true) :
    ∃ ctx st0 R gn bl A, LowerShape f vc ctx st0 R gn bl ∧ Cert f ctx st0 gn bl A ∧
      (∀ B ∈ f.blocks, BrIdxTyped ctx B.term) ∧ threadCheckBlC f bl = true ∧
      callArityBl f bl = true ∧ callUseRegsBl f bl = true := by
  have h0 := h
  unfold lowerCheck at h
  unfold threadCheckC at ht
  split at h
  · cases h
  · rename_i ctx ranges st0 hb
    rw [hb] at ht
    simp only at ht
    split at h
    · cases h
    · rename_i bl hl
      rw [hl] at ht
      simp only [Bool.and_eq_true] at h
      have hS := lowerShape_of_ok (gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))) hb hl
        (fun n hn => gnAt_temp hn) h.1.1.1.1
      exact ⟨ctx, st0, _, _, bl, _, hS, cert_of_ok hS.len h.1.1.1.2, brIdx_of_ok h.1.1.2, ht,
        callArityBl_of_C ha hb hl, callUseRegsBl_of_C hu hb hl⟩

/-- **`driverHypT_of` with the call checks on the driver's lowering** (module doc). -/
theorem _root_.Concurrency.IselResume.driverHypT_ofA {f : Clif.Function} {vc : VCode}
    {Γ : E2E.Rel} {fctx : FnCtx} {X : ExtSem} {c : BitVec 64} {env : Clif.Env} {p : Clif.Program}
    (hlow : lowerCheck f vc = true) (hthr : threadCheckC f = true) (har : callArityC f = true)
    (hcu : callUseRegsC f = true)
    (hext : ∀ e ∈ f.externs, env.extern e.2.name = none) (hind : indSigs f = [])
    (hv : verifiable f = true) (hnt : f.blocks.all (fun B => !B.term.isTry) = true)
    (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps)) (hout0 : vc.outgoing = 0)
    (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    ∃ ctx st0 R gn bl A, DriverHypT f vc ctx st0 R gn bl A (csem Γ.F fctx X) (RelW Γ f c) env p ∧
      threadCheckBlC f bl = true ∧ callArityBl f bl = true ∧ callUseRegsBl f bl = true := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hbl, ha, hu⟩ :=
    obligations_of_checksA hlow hthr har hcu
  refine ⟨ctx, st0, R, gn, bl, A, driverHypT_mk hshape hcert hbr hlow hind hv hnt hcfg hout0
    hslot hsym (mrStable_relW Γ f c) (outArgsOk_relW Γ f c) (memRelOk_relW Γ f c) ?_, hbl, ha, hu⟩
  intro ext hmem g _ _ _ _ _ _ _ _ _ hg
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
  rw [hext e he] at hg; cases hg

/-- **The call end on the linked machine** (module doc). -/
theorem call_end (hL : L.Ok) {nA : String} {FA : LFn} (hA : (nA, FA) ∈ L.fns) {s0 : ArmState}
    {K : Nat} {G : BitVec 64 → Prop} (hRA : (L.act FA s0 K G).Wf)
    {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {Γ : E2E.Rel}
    {c : BitVec 64} {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A
      (csem (L.act FA s0 K G).F (L.act FA s0 K G).ctx (L.act FA s0 K G).X) (RelW Γ f c) env p)
    (hchk : threadCheckBlC f bl = true) (hres : callResLenB f = true)
    (hcu : callUseRegsBl f bl = true)
    (hlow : lowerCheck f vc = true) (hind : indSigs f = []) (hv : verifiable f = true)
    (hnt : f.blocks.all (fun B => !B.term.isTry) = true) (hout0 : vc.outgoing = 0)
    (hslot : (L.act FA s0 K G).ctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → (L.act FA s0 K G).X.sym n 0 = BitVec.ofNat 64 b)
    (hX0 : NoCall (L.act FA s0 K G).X)
    {Lp : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc (L.act FA s0 K G).vc Lp ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt (L.act FA s0 K G).vc (L.act FA s0 K G).rf cc ins a0) {r₀ : Reg → CV}
    (huv : CallUsesVirt (L.act FA s0 K G).vc) (hdv : CallDefsVirt (L.act FA s0 K G).vc)
    {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState}
    (hq : Q (L.act FA s0 K G) x (.run cM')) (hP : Pause (L.act FA s0 K G) (.run cM'))
    (hm2 : Match f ctx R gn bl A (RelW Γ f c) slots s' vV')
    (hm3 : PMatch vc (L.act FA s0 K G).vc
      (csem (L.act FA s0 K G).F (L.act FA s0 K G).ctx (L.act FA s0 K G).X)
      (cEvs (L.act FA s0 K G).F (L.act FA s0 K G).ctx) Lp ss' (.run vV') (.run vP'))
    (hm4 : MatchRun cc ins ckeep r₀ cM' vP')
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s'.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hcl : stm.inst = .call fn args)
    {ext : Clif.ExtFunc} (hext : s'.frame.func.extern? fn = some ext)
    (huniq : ∀ e ∈ f.externs, e.2.name = ext.name → e.2 = ext)
    {vals : List Clif.Val} (hvals : s'.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params)
    {FB : LFn} (hB : (ext.name, FB) ∈ L.fns) (hFB : FB.Static)
    (hcode : ∀ k w, FB.fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (FB.base + BitVec.ofNat 64 (4 * k)) x = w)
    {KB : Nat} {GB : BitVec 64 → Prop} (hstB : StackAvail KB FB.af (enter FB x))
    (hgB : ∀ a, GB a → ¬ StackBelow (frameDrop FB.af + KB) (spv (enter FB x)) a)
    {fB : Clif.Function} (hsig : fB.sig = ext.sig) :
    L.M x = enter FB x ∧ stepEvs x = [] ∧ cls x = .plain ∧
      (L.act FB (enter FB x) KB GB).Wf ∧
      AbiCall FB.fb FB.base (Arm.r .PC x + 4#64) (enter FB x) ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f (enter FB x) = Arm.r f x) ∧
      xreg 30 (enter FB x) = Arm.r .PC x + 4#64 ∧ (enter FB x).mem = x.mem ∧
      Q (L.act FB (enter FB x) KB GB)
        (iterN (L.act FB (enter FB x) KB GB).step (prologueLines FB.af.saves FB.af.frameSize).length
          (enter FB x))
        (MConf.init FB.rf (locVal (L.act FB (enter FB x) KB GB).fr
          (iterN (L.act FB (enter FB x) KB GB).step (prologueLines FB.af.saves FB.af.frameSize).length
            (enter FB x))) (bodyOf FB.af (enter FB x))) ∧
      AInv (L.act FB (enter FB x) KB GB)
        (MConf.init FB.rf (locVal (L.act FB (enter FB x) KB GB).fr
          (iterN (L.act FB (enter FB x) KB GB).step (prologueLines FB.af.saves FB.af.frameSize).length
            (enter FB x))) (bodyOf FB.af (enter FB x))) ∧
      ArgsAtEntry (L.act FB (enter FB x) KB GB).F fB.sig vals (bodyOf FB.af (enter FB x)) := by
  have hextf : f.extern? fn = some ext := by rw [← hm2.2.1]; exact hext
  -- the paused `call` item of the allocated code
  obtain ⟨vb, us, ds, ops, hvb, hi, -, -⟩ := isel_argsAt H hchk hres hlow hind hv hnt hout0
    hslot hsym hm2 hbody hcl hext huniq hvals htys
  obtain ⟨b0, k0, ρ0, w0⟩ := vV'
  obtain ⟨b', vb', e, hvb', hi', -, -⟩ := pmatch_call_fwd H3 hX0 hm3 hvb hi
  cases e
  obtain ⟨b2, k2, allocs, its, m, w2, vb2, info2, rfl, e2, -, -, -⟩ :=
    atCall_of_pause hX0 H hchk H3 hc hP ⟨stm, rest, fn, args, hbody, hcl⟩ hm2 hm3 hm4
  simp only [VState.mk.injEq] at e2
  obtain ⟨rfl, rfl, -, rfl⟩ := e2
  obtain ⟨hstep, hev, hcls⟩ := step_call hL hA hB hRA hq hvb' hi' rfl
  have hst := q_stRel hq
  obtain ⟨hRB, hent, hfx, hlr, hmem, hqB, hAB⟩ :=
    enter_call hL hB hFB hst.err hst.align hcode hstB hgB
  exact ⟨hstep, hev, hcls, hRB, hent, hfx, hlr, hmem, hqB, hAB,
    callee_argsAtEntry_sig hX0 H hchk hres hcu hlow hind hv hnt hout0 hslot hsym H3 hc huv hdv hq
      hP hm2 hm3 hm4 hbody hcl hext huniq hvals htys FB _ hsig⟩

end Concurrency.LinkedMachine.Link
