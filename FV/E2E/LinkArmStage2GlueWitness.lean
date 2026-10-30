import FV.E2E.LinkArmThmPRBRLAll
import FV.E2E.LinkArmThmPRBRZeroWitness
import FV.E2E.LinkPlaceBReachWitness
import FV.E2E.LinkArmProphThmWitness

/-!
# Witnesses for the stage-2 glue (SEM1 #537, #680 (3): `LinkArmStage2ZS`, `LinkArmCallDecode`,
`LinkArmInvokedStep`, `LinkArmProgInst`, `LinkArmCountStep`, `LinkArmStage2Count`,
`LinkArmStage2PRBZSOf`, `LinkArmThmPRBRLAll`)

On the slotted test system `LinkSlotSysWitness.Lsl` (`NeedSlots`, budget `K`):

* **`thmPRBRL_ofZS_zero_Lsl`**: `thmPRBRL_ofZS` at depth `0`, every premise discharged;
* **`stage2PRBZS_one_Lsl`**: `stage2PRBZS_of` at depth `1` (the depth-`0` statement
  `thmPRBRL_zero_Lsl`, `RetOkPRB` by `retOkPRB_Lsl`; `DetPRB 0` and `DetTabPRB 1` remain);
* **`thmPRBRL_every_Lsl`**: `thmPRBRL_all` with the scope conditions discharged (`baseRetOk_Lsl`,
  `retCount_Lsl`); `DetPRB`, `DetTabPRB`, `CountPRB` remain;
* `*_Lsl`: the other glue theorems instantiated on `Lsl` (`Ok`, budget and `NeedSlots`
  discharged);
* concrete runs: `reachN_call_at_sP` (`LinkPlaceBReachWitness.sP` steps to `sP1` after its call:
  the calling state of count `0`), `invoked_step_sP` (`sP`'s invocation answers `sP1`'s memory),
  `callIdx_unique_u0` (the stuck call run of `LinkArmProphThmWitness`: one step per count).
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof Backend.Proof.Driver

theorem thmPRBRL_ofZS_zero_Lsl : Lsl.ThmPRBRL (fun M _ => Lsl.K M) 0 :=
  Lsl.thmPRBRL_ofZS Lsl_ok (Lsl.budget_K Lsl_ok) (fun h => absurd h (Nat.lt_irrefl 0))
    (fun h => absurd h (Nat.lt_irrefl 0)) (retOkPRB_Lsl 0) (Lsl.stage2PRBZS_zero Lsl_ok)
    countPRB_zero_Lsl

/-- **Stage 2 at the call sites at depth `1` on the slotted system.** -/
theorem stage2PRBZS_one_Lsl (hdet : Lsl.DetPRB (fun M _ => Lsl.K M) 0)
    (hdt : Lsl.DetTabPRB (fun M _ => Lsl.K M) 1) : Lsl.Stage2PRBZS (fun M _ => Lsl.K M) 1 :=
  Lsl.stage2PRBZS_of Lsl_ok (Lsl.budget_K Lsl_ok) needSlots thmPRBRL_zero_Lsl hdet hdt
    (retOkPRB_Lsl 1)

/-- **`ThmPRBRL` at every depth on the slotted system** from `DetPRB`, `DetTabPRB`, `CountPRB`. -/
theorem thmPRBRL_every_Lsl (hdet : ∀ M, Lsl.DetPRB (fun M _ => Lsl.K M) M)
    (hdt : ∀ M, Lsl.DetTabPRB (fun M _ => Lsl.K M) M)
    (hcnt : ∀ M, Lsl.CountPRB (fun M _ => Lsl.K M) M) (M : Nat) :
    Lsl.ThmPRBRL (fun M _ => Lsl.K M) M :=
  Lsl.thmPRBRL_all Lsl_ok (Lsl.budget_K Lsl_ok) baseRetOk_Lsl retCount_Lsl hdet hdt hcnt M

theorem reachN_call_at_sP : ∃ tj tj1, ReachN CallPostExistsWitness.envE
    InvokedNWitness.PE.bare LinkPlaceBReachWitness.sP tj 0 ∧ callNum tj = 1 ∧
    Clif.step CallPostExistsWitness.envE InvokedNWitness.PE.bare tj = .next tj1 ∧
    ReachN CallPostExistsWitness.envE InvokedNWitness.PE.bare LinkPlaceBReachWitness.sP
      tj1 1 :=
  reachN_call_at LinkPlaceBReachWitness.nextAdv_sP1.1 0 (Nat.zero_lt_one)

theorem invoked_step_sP (nm : String) (vals : List Clif.Val) (m : Clif.Mem)
    (h : Clif.Invoked CallPostExistsWitness.envE InvokedNWitness.PE.bare
      LinkPlaceBReachWitness.sP nm vals m) :
    ∃ G rv, CallPostExistsWitness.envE.extern nm = some G ∧
      G vals m = .returned rv LinkPlaceBReachWitness.sP1.mem :=
  invoked_step LinkPlaceBReachWitness.linkFreeE LinkPlaceBReachWitness.linv_sP h
    LinkPlaceBReachWitness.step_sP rfl

theorem callIdx_unique_u0 (i j : Nat)
    (h : callsBefore id LinkArmProphThmWitness.faC 0x1000#64 LinkArmProphThmWitness.u0 i =
      callsBefore id LinkArmProphThmWitness.faC 0x1000#64 LinkArmProphThmWitness.u0 j) : i = j :=
  callIdx_unique (LinkArmProphThmWitness.callPc_u0 i) (LinkArmProphThmWitness.callPc_u0 j) h

theorem calleeOkXPBTGZS_Lsl
    {M : Nat}
    (ih : 0 < M → Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M - 1))
    (hdet : 0 < M → Lsl.DetPRB (fun M _ => Lsl.K M) (M - 1))
    {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    {F G : BitVec 64 → Prop}
    {ra : BitVec 64}
    {s w₀ : Arm.ArmState}
    (he : Lsl.MachEntry (fun M _ => Lsl.K M) M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8}
    {R : Nat → Arm.ArmState}
    {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow ((fun M _ => Lsl.K M) M g) (spv t) a → t.mem a = P n a)
    {env : Clif.Env}
    {cs : Clif.State}
    {c : BitVec 64}
    (h2 : Lsl.Stage2ZS (fun M _ => Lsl.K M) M g F P R env cs c Q n) :
    CalleeOkGP Q F ((fun M _ => Lsl.K M) M g) G s (CallAt (Lsl.A g).fa (Lsl.A g).base)
      ((Lsl.XPBTGY (fun M _ => Lsl.K M) M g F P R env cs c).at n) (Lsl.hooks M)
      (Lsl.A g).vcp.CallSite (GotV (Lsl.A g).vcp) :=
  Lsl.calleeOkXPBTGZS Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet hg he hQ h2

theorem thmPRBRL_ofZS_Lsl
    {M : Nat}
    (ih : 0 < M → Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M - 1))
    (hdet : 0 < M → Lsl.DetPRB (fun M _ => Lsl.K M) (M - 1))
    (hret : Lsl.RetOkPRB (fun M _ => Lsl.K M) M)
    (h2 : Lsl.Stage2PRBZS (fun M _ => Lsl.K M) M)
    (hcnt : Lsl.CountPRB (fun M _ => Lsl.K M) M) :
    Lsl.ThmPRBRL (fun M _ => Lsl.K M) M :=
  Lsl.thmPRBRL_ofZS Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet hret h2 hcnt

theorem callDecode_Lsl
    {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    {u : Arm.ArmState}
    {i : MInst}
    {info : CallInfo}
    (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti)
    (hS : (Lsl.A g).vcp.CallSite info)
    {ops : Array Operand}
    {regs : Array Reg}
    {i' : MInst}
    (hops : i.operands = .ok ops)
    {cc : CheckCtx}
    {wh : String}
    (hst : cc.checkStatic wh ops (regs.map .reg) i.clobbers = .ok ())
    (hasg : i.assign regs = .ok i')
    (hpi : CallAt (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC u) i')
    (himgU : ∀ a, Lsl.Img a → u.mem a = Lsl.imgMem a)
    (hgd : gotGuard (GotV (Lsl.A g).vcp) Lsl.Xb info (useVals ops regs u))
    {h : Clif.Function}
    (hh : h ∈ Lsl.P.funcs)
    {args : List CV}
    (hd : callDest info = some h.name ∧ useVals ops regs u = args ∨
      callDest info = none ∧ Lsl.IndTo g h ∧
        ∃ u0, useVals ops regs u = u0 :: args ∧ lo64 u0 = Lsl.Xb.sym h.name 0)
    (hlen : args.length = (regLocs h.sig).length) :
    ∃ Lu : List (Nat × Reg), Lu.map (·.2) = regLocs h.sig ∧
      args = Lu.map (fun q => regVal u q.2) ∧ Lsl.CallsTo g u h ∧ RaOk (Lsl.A h) (Arm.r .PC u) :=
  Lsl.callDecode Lsl_ok hg hi hS hops hst hasg hpi himgU hgd hh hd hlen

theorem nv_cases_Lsl
    {M : Nat}
    {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    {F : BitVec 64 → Prop}
    {c : BitVec 64}
    (hdead : ∀ a, StackBelow ((fun M _ => Lsl.K M) M g) c a → F a ∧ ¬ Lsl.Img a)
    (P : Nat → BitVec 64 → BitVec 8)
    (R : Nat → Arm.ArmState)
    (cs : Clif.State)
    (n : Nat)
    {d : Option String}
    {uses : List CV}
    {w : Arm.ArmState}
    (hnv : ¬ ∀ r, CallPost ((Lsl.envOfB M g c).only (InvokedN (Lsl.envOfB M g c) Lsl.P.bare cs n))
      (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, Lsl.syms, (Lsl.A g).af.slotBase, (RAFrame.compute (Lsl.A g).vcp (Lsl.A g).rf).intBase⟩ g c)
      Lsl.Xb.sym d uses w r) :
    (∃ h ∈ Lsl.P.funcs, ∃ args vals cm cs' rvals cm',
      Lsl.ProgInst (fun M _ => Lsl.K M) M g F P R c cs n d uses w h args vals cm cs' rvals cm') ∨
    (∃ nm vals cm, InvokedN (Lsl.envOfB M g c) Lsl.P.bare cs n nm vals cm ∧ Lsl.P.func? nm = none ∧
      (d = some nm ∧ (∃ args, uses = args) ∨
        d = none ∧ ∃ u args, uses = u :: args ∧ lo64 u = Lsl.Xb.sym nm 0)) :=
  Lsl.nv_cases Lsl_ok (Lsl.budget_K Lsl_ok) hg hdead P R cs n hnv

theorem callDecodeBase_Lsl
    {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    {u : Arm.ArmState}
    {i : MInst}
    {info : CallInfo}
    (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti)
    (hS : (Lsl.A g).vcp.CallSite info)
    {ops : Array Operand}
    {regs : Array Reg}
    {i' : MInst}
    (hops : i.operands = .ok ops)
    {cc : CheckCtx}
    {wh : String}
    (hst : cc.checkStatic wh ops (regs.map .reg) i.clobbers = .ok ())
    (hasg : i.assign regs = .ok i')
    (hpi : CallAt (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC u) i')
    (himgU : ∀ a, Lsl.Img a → u.mem a = Lsl.imgMem a)
    {nm : String}
    (hnm : Lsl.P.func? nm = none)
    (hd : callDest info = some nm ∨
      callDest info = none ∧ ∃ u0 args, useVals ops regs u = u0 :: args ∧ lo64 u0 = Lsl.Xb.sym nm 0) :
    ∀ h, ¬ Lsl.CallsTo g u h :=
  Lsl.callDecodeBase Lsl_ok hg hi hS hops hst hasg hpi himgU hnm hd

theorem adv_base_Lsl
    {M : Nat}
    {g : Clif.Function}
    (hgf : Clif.LinkFree g)
    {c : BitVec 64}
    {t t1 : Clif.State}
    (hI : Clif.LInv (Lsl.P.only g) t)
    (hc : t.callers = [])
    {nm : String}
    {vals : List Clif.Val}
    {cm : Clif.Mem}
    (hinv : Clif.Invoked (Lsl.envOfB M g c) Lsl.P.bare t nm vals cm)
    (hpf : Lsl.P.func? nm = none)
    (hst : Clif.step (Lsl.envOfB M g c) Lsl.P.bare t = .next t1) : Clif.NextAdv t.mem t1.mem 0 :=
  Lsl.adv_base Lsl_ok needSlots hgf hI hc hinv hpf hst

theorem adv_prog_Lsl
    {M : Nat}
    {g : Clif.Function}
    (hgf : Clif.LinkFree g)
    {c : BitVec 64}
    {t t1 : Clif.State}
    (hI : Clif.LInv (Lsl.P.only g) t)
    (hc : t.callers = [])
    {h : Clif.Function}
    {vals : List Clif.Val}
    {cm : Clif.Mem}
    (hinv : Clif.Invoked (Lsl.envOfB M g c) Lsl.P.bare t h.name vals cm)
    (hpf : Lsl.P.func? h.name = some h)
    {cs' : Clif.State}
    {rvals : List Clif.Val}
    {cm' : Clif.Mem}
    (hinit : Clif.initState Lsl.P h.name vals cm = .ok cs')
    (hrun : Lsl.crun M cs' = .returned rvals cm')
    (hst : Clif.step (Lsl.envOfB M g c) Lsl.P.bare t = .next t1) : t1.mem = cm' :=
  Lsl.adv_prog hgf hI hc hinv hpf hinit hrun hst

theorem oracleAt_at_Lsl
    {M' : Nat}
    (hdt : Lsl.DetTabPRB (fun M _ => Lsl.K M) (M' + 1))
    {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    {F : BitVec 64 → Prop}
    {vals : List Clif.Val}
    {cs : Clif.State}
    {w₀ : Arm.ArmState}
    {ini : Clif.SlotInit}
    {G : BitVec 64 → Prop}
    {ra : BitVec 64}
    {s : Arm.ArmState}
    (hWE : Lsl.WorldEntryB (fun M _ => Lsl.K M) (M' + 1) g F vals cs w₀ ini)
    (hME : Lsl.MachEntryPR (fun M _ => Lsl.K M) (M' + 1) g F G ra s w₀ (Lsl.BP (M' + 1) g s) (Lsl.RP (M' + 1) g s))
    (hra : RaOk (Lsl.A g) (ra - 4))
    (htab : Lsl.TableOf (M' + 1) g s ini)
    {i : Nat}
    (htr : ∀ j < i, ¬ PostCall (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC (runX (Lsl.mach (M' + 1) g) j s)) ∨
      spOf (runX (Lsl.mach (M' + 1) g) j s) = spv s - BitVec.ofNat 64 (frameDrop (Lsl.A g).af))
    (hsp : spOf (runX (Lsl.mach (M' + 1) g) i s) = spv s - BitVec.ofNat 64 (frameDrop (Lsl.A g).af))
    {ins : MInst}
    {info : CallInfo}
    (hi : ins = .call info ∨ ∃ ti, ins = .tryCall info ti)
    (hS : (Lsl.A g).vcp.CallSite info)
    {ops : Array Operand}
    {regs : Array Reg}
    {i' : MInst}
    (hops : ins.operands = .ok ops)
    {cc : CheckCtx}
    {wh : String}
    (hst : cc.checkStatic wh ops (regs.map .reg) ins.clobbers = .ok ())
    (hasg : ins.assign regs = .ok i')
    (hpi : CallAt (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC (runX (Lsl.mach (M' + 1) g) i s)) i')
    (herr : Arm.r .ERR (runX (Lsl.mach (M' + 1) g) i s) = .None)
    (hgd : gotGuard (GotV (Lsl.A g).vcp) Lsl.Xb info (useVals ops regs (runX (Lsl.mach (M' + 1) g) i s)))
    (hGu : ∀ a, G a → (runX (Lsl.mach (M' + 1) g) i s).mem a = s.mem a)
    {w : Arm.ArmState}
    (hsw : SameWorld F (runX (Lsl.mach (M' + 1) g) i s) w)
    {h : Clif.Function}
    (hh : h ∈ Lsl.P.funcs)
    {args : List CV}
    (hd : callDest info = some h.name ∧ useVals ops regs (runX (Lsl.mach (M' + 1) g) i s) = args ∨
      callDest info = none ∧ Lsl.IndTo g h ∧ ∃ u0,
        useVals ops regs (runX (Lsl.mach (M' + 1) g) i s) = u0 :: args ∧ lo64 u0 = Lsl.Xb.sym h.name 0)
    (hcal : Lsl.Callee g h)
    {vals' : List Clif.Val}
    {cm : Clif.Mem}
    {cs' : Clif.State}
    {rvals' : List Clif.Val}
    {cm'' : Clif.Mem}
    (hmrW : MemRel F Lsl.syms cm (Lsl.worldPR (fun M _ => Lsl.K M) (M' + 1) h
      (Lsl.BP (M' + 1) g s (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
      (Lsl.RP (M' + 1) g s (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) w))
    (hargsW : ArgsAt h.sig vals' args (Lsl.worldPR (fun M _ => Lsl.K M) (M' + 1) h
      (Lsl.BP (M' + 1) g s (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
      (Lsl.RP (M' + 1) g s (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) w))
    (hsavW : StackArgsAvoid F h.sig vals' (Lsl.worldPR (fun M _ => Lsl.K M) (M' + 1) h
      (Lsl.BP (M' + 1) g s (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
      (Lsl.RP (M' + 1) g s (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) w))
    (hspw : spv w = spv w₀)
    (hinit : Clif.initState Lsl.P h.name vals' cm = .ok cs')
    (hrun : Lsl.crun (M' + 1) cs' = .returned rvals' cm'')
    {x : Nat}
    (hpl : Lsl.NeedSlots → Lsl.PlaceAtB cm (spv w₀) (ini.adv x))
    (hcnt : ∀ e, Lsl.TabUpTo (M' + 1) g s ini.bytes ini.next i e → e = x) :
    ∃ Lu : List (Nat × Reg), Lu.map (·.2) = regLocs h.sig ∧
      args = Lu.map (fun q => regVal (runX (Lsl.mach (M' + 1) g) i s) q.2) ∧
      Lsl.CallsTo g (runX (Lsl.mach (M' + 1) g) i s) h ∧
      RaOk (Lsl.A h) (Arm.r .PC (runX (Lsl.mach (M' + 1) g) i s)) ∧
      Lsl.OracleAt (fun M _ => Lsl.K M) (M' + 1) h (spv w₀) cm args (Lsl.worldPR (fun M _ => Lsl.K M) (M' + 1) h
        (Lsl.BP (M' + 1) g s (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
        (Lsl.RP (M' + 1) g s (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) w) :=
  Lsl.oracleAt_at Lsl_ok (Lsl.budget_K Lsl_ok) hdt hg hWE hME hra htab htr hsp hi hS hops hst hasg hpi herr hgd hGu hsw hh hd hcal hmrW hargsW hsavW hspw hinit hrun hpl hcnt

theorem countStep_prog_Lsl
    {M' : Nat}
    (ih : Lsl.ThmPRBRL (fun M _ => Lsl.K M) M')
    (hdet : Lsl.DetPRB (fun M _ => Lsl.K M) M')
    (hdt : Lsl.DetTabPRB (fun M _ => Lsl.K M) (M' + 1))
    {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    {F : BitVec 64 → Prop}
    {vals : List Clif.Val}
    {cs : Clif.State}
    {w₀ : Arm.ArmState}
    {ini : Clif.SlotInit}
    {G : BitVec 64 → Prop}
    {ra : BitVec 64}
    {s : Arm.ArmState}
    (hWE : Lsl.WorldEntryB (fun M _ => Lsl.K M) (M' + 1) g F vals cs w₀ ini)
    (hME : Lsl.MachEntryPR (fun M _ => Lsl.K M) (M' + 1) g F G ra s w₀ (Lsl.BP (M' + 1) g s) (Lsl.RP (M' + 1) g s))
    (hra : RaOk (Lsl.A g) (ra - 4))
    (htab : Lsl.TableOf (M' + 1) g s ini)
    {i : Nat}
    (htr : ∀ j < i, ¬ PostCall (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC (runX (Lsl.mach (M' + 1) g) j s)) ∨
      spOf (runX (Lsl.mach (M' + 1) g) j s) = spv s - BitVec.ofNat 64 (frameDrop (Lsl.A g).af))
    (hsp : spOf (runX (Lsl.mach (M' + 1) g) i s) = spv s - BitVec.ofNat 64 (frameDrop (Lsl.A g).af))
    {ins : MInst}
    {info : CallInfo}
    (hi : ins = .call info ∨ ∃ ti, ins = .tryCall info ti)
    (hS : (Lsl.A g).vcp.CallSite info)
    {ops : Array Operand}
    {regs : Array Reg}
    {i' : MInst}
    (hops : ins.operands = .ok ops)
    {cc : CheckCtx}
    {wh : String}
    (hst : cc.checkStatic wh ops (regs.map .reg) ins.clobbers = .ok ())
    (hasg : ins.assign regs = .ok i')
    (hpi : CallAt (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC (runX (Lsl.mach (M' + 1) g) i s)) i')
    (herr : Arm.r .ERR (runX (Lsl.mach (M' + 1) g) i s) = .None)
    (hgd : gotGuard (GotV (Lsl.A g).vcp) Lsl.Xb info (useVals ops regs (runX (Lsl.mach (M' + 1) g) i s)))
    (hGu : ∀ a, G a → (runX (Lsl.mach (M' + 1) g) i s).mem a = s.mem a)
    {w : Arm.ArmState}
    (hsw : SameWorld F (runX (Lsl.mach (M' + 1) g) i s) w)
    {h : Clif.Function}
    (hh : h ∈ Lsl.P.funcs)
    {args : List CV}
    (hd : callDest info = some h.name ∧ useVals ops regs (runX (Lsl.mach (M' + 1) g) i s) = args ∨
      callDest info = none ∧ Lsl.IndTo g h ∧ ∃ u0,
        useVals ops regs (runX (Lsl.mach (M' + 1) g) i s) = u0 :: args ∧ lo64 u0 = Lsl.Xb.sym h.name 0)
    (hcal : Lsl.Callee g h)
    {vals' : List Clif.Val}
    {cm : Clif.Mem}
    {cs' : Clif.State}
    {rvals' : List Clif.Val}
    {cm'' : Clif.Mem}
    (hmrW : MemRel F Lsl.syms cm (Lsl.worldPR (fun M _ => Lsl.K M) (M' + 1) h
      (Lsl.BP (M' + 1) g s (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
      (Lsl.RP (M' + 1) g s (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) w))
    (hargsW : ArgsAt h.sig vals' args (Lsl.worldPR (fun M _ => Lsl.K M) (M' + 1) h
      (Lsl.BP (M' + 1) g s (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
      (Lsl.RP (M' + 1) g s (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) w))
    (hsavW : StackArgsAvoid F h.sig vals' (Lsl.worldPR (fun M _ => Lsl.K M) (M' + 1) h
      (Lsl.BP (M' + 1) g s (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
      (Lsl.RP (M' + 1) g s (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) w))
    (hspw : spv w = spv w₀)
    (hinit : Clif.initState Lsl.P h.name vals' cm = .ok cs')
    (hrun : Lsl.crun (M' + 1) cs' = .returned rvals' cm'')
    {tj tj1 : Clif.State}
    (hrtj : ReachN (Lsl.envOfB (M' + 1) g (spv w₀)) Lsl.P.bare cs tj
      (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
    (hcnj : callNum tj = 1)
    (hstj : Clif.step (Lsl.envOfB (M' + 1) g (spv w₀)) Lsl.P.bare tj = .next tj1)
    (hinvj : Clif.Invoked (Lsl.envOfB (M' + 1) g (spv w₀)) Lsl.P.bare tj h.name vals' cm)
    (hItj : Clif.LInv (Lsl.P.only g) tj)
    (hctj : tj.callers = [])
    (hptj : Lsl.PlaceAtB tj.mem (spv w₀) (ini.adv (Clif.sumTo
      (advAt (Lsl.envOfB (M' + 1) g (spv w₀)) Lsl.P.bare cs)
      (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))))
    (hcnt : ∀ e, Lsl.TabUpTo (M' + 1) g s ini.bytes ini.next i e →
      e = Clif.sumTo (advAt (Lsl.envOfB (M' + 1) g (spv w₀)) Lsl.P.bare cs)
        (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) :
    ∀ e', Lsl.TabUpTo (M' + 1) g s ini.bytes ini.next (i + 1) e' →
      e' = Clif.sumTo (advAt (Lsl.envOfB (M' + 1) g (spv w₀)) Lsl.P.bare cs)
        (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s (i + 1)) :=
  Lsl.countStep_prog Lsl_ok (Lsl.budget_K Lsl_ok) needSlots ih hdet hdt hg hWE hME hra htab htr hsp hi hS hops hst hasg hpi herr hgd hGu hsw hh hd hcal hmrW hargsW hsavW hspw hinit hrun hrtj hcnj hstj hinvj hItj hctj hptj hcnt

theorem countStep_base_Lsl
    {M' : Nat}
    {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    {cs : Clif.State}
    {c : BitVec 64}
    {s : Arm.ArmState}
    {ini : Clif.SlotInit}
    {i : Nat}
    (hcp : CallPc (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC (runX (Lsl.mach (M' + 1) g) i s)))
    (hn : ∀ h, ¬ Lsl.CallsTo g (runX (Lsl.mach (M' + 1) g) i s) h)
    {tj tj1 : Clif.State}
    (hrtj : ReachN (Lsl.envOfB (M' + 1) g c) Lsl.P.bare cs tj
      (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
    (hcnj : callNum tj = 1)
    (hstj : Clif.step (Lsl.envOfB (M' + 1) g c) Lsl.P.bare tj = .next tj1)
    {nm : String}
    {vals' : List Clif.Val}
    {cm : Clif.Mem}
    (hinvj : Clif.Invoked (Lsl.envOfB (M' + 1) g c) Lsl.P.bare tj nm vals' cm)
    (hpf : Lsl.P.func? nm = none)
    (hItj : Clif.LInv (Lsl.P.only g) tj)
    (hctj : tj.callers = [])
    {ini' : Clif.SlotInit}
    (hptj : Lsl.PlaceAtB tj.mem c ini')
    (hcnt : ∀ e, Lsl.TabUpTo (M' + 1) g s ini.bytes ini.next i e →
      e = Clif.sumTo (advAt (Lsl.envOfB (M' + 1) g c) Lsl.P.bare cs)
        (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) :
    ∀ e', Lsl.TabUpTo (M' + 1) g s ini.bytes ini.next (i + 1) e' →
      e' = Clif.sumTo (advAt (Lsl.envOfB (M' + 1) g c) Lsl.P.bare cs)
        (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s (i + 1)) :=
  Lsl.countStep_base Lsl_ok needSlots hg hcp hn hrtj hcnj hstj hinvj hpf hItj hctj hptj hcnt

theorem stage2PRBZS_of_Lsl
    {M' : Nat}
    (ih : Lsl.ThmPRBRL (fun M _ => Lsl.K M) M')
    (hdet : Lsl.DetPRB (fun M _ => Lsl.K M) M')
    (hdt : Lsl.DetTabPRB (fun M _ => Lsl.K M) (M' + 1))
    (hret : Lsl.RetOkPRB (fun M _ => Lsl.K M) (M' + 1)) : Lsl.Stage2PRBZS (fun M _ => Lsl.K M) (M' + 1) :=
  Lsl.stage2PRBZS_of Lsl_ok (Lsl.budget_K Lsl_ok) needSlots ih hdet hdt hret

theorem thmPRBRL_succS_Lsl
    {M' : Nat}
    (ih : Lsl.ThmPRBRL (fun M _ => Lsl.K M) M')
    (hdet : Lsl.DetPRB (fun M _ => Lsl.K M) M')
    (hdt : Lsl.DetTabPRB (fun M _ => Lsl.K M) (M' + 1))
    (hret : Lsl.RetOkPRB (fun M _ => Lsl.K M) (M' + 1))
    (hcnt : Lsl.CountPRB (fun M _ => Lsl.K M) (M' + 1)) : Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M' + 1) :=
  Lsl.thmPRBRL_succS Lsl_ok (Lsl.budget_K Lsl_ok) needSlots ih hdet hdt hret hcnt

theorem thmPRBRL_all_Lsl
    (hB : Lsl.BaseRetOk)
    (hC : ∀ g ∈ Lsl.P.funcs, Lsl.RetCount g)
    (hdet : ∀ M, Lsl.DetPRB (fun M _ => Lsl.K M) M)
    (hdt : ∀ M, Lsl.DetTabPRB (fun M _ => Lsl.K M) M)
    (hcnt : ∀ M, Lsl.CountPRB (fun M _ => Lsl.K M) M)
    (M : Nat) : Lsl.ThmPRBRL (fun M _ => Lsl.K M) M :=
  Lsl.thmPRBRL_all Lsl_ok (Lsl.budget_K Lsl_ok) hB hC hdet hdt hcnt M

end E2E.LinkSlotSysWitness
