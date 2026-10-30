import FV.E2E.LinkArmStage2Base
import FV.E2E.LinkArmCallCount
import FV.E2E.BackendPrefixAtCleanup
import FV.E2E.IselCallsOneAll
import FV.E2E.LinkArmThmPRBRZeroWitness

/-!
# Witnesses for the stage-2 glue modules (SEM1 #537, #680 (3))

On the slotted test system `LinkSlotSysWitness.Lsl` (`NeedSlots`; `f` calls the slotted `h`):

* **`thmPRBRL_ofZ_zero_Lsl`**: `thmPRBRL_ofZ` at depth `0` with every premise discharged
  (`stage2PRBZ_zero`, `countPRB_zero_Lsl`, `retOkPRB_Lsl`);
* `slotted_fH`, `calleeIni_fH`: `h`'s entry takes one slot of the oracle (`calleeIni_next`);
* `prefix_relatedPRI_atE_f`: `prefix_relatedPRI_atE` (`BackendPrefixAtCleanup`, through
  `prefix_relatedPRI_at` / `prefix_related_cleanupPRI_at`, `backend_prefix*PRI_at`,
  `regLevel_prefixPRSG`, `regLevel_value_prefixPRSG`) applies to `f`'s artifact;
* `*_Lsl`: the stage-2 glue theorems (`LinkArmStage2Z`, `LinkArmStage2Base`, `LinkArmProgResultBT`,
  `LinkArmStage2Prog`, `LinkArmCallTab`, `LinkArmOracleAt`, `LinkArmProgCallPRBRLT`,
  `LinkArmCallCount`) instantiated on `Lsl` with its budget `K` (`Lsl_ok`, `budget_K`
  discharged; the per-activation premises remain).
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof Backend.Proof.Driver
open LinkSys (slotted calleeIni)

theorem fF_mem : fF ∈ Lsl.P.funcs := by rw [funcs_eq]; simp

theorem fH_mem : fH ∈ Lsl.P.funcs := by rw [funcs_eq]; simp

/-- **`thmPRBRL_ofZ` at depth `0` on the slotted test system**, every premise discharged. -/
theorem thmPRBRL_ofZ_zero_Lsl : Lsl.ThmPRBRL (fun M _ => Lsl.K M) 0 :=
  Lsl.thmPRBRL_ofZ Lsl_ok (Lsl.budget_K Lsl_ok) (fun h => absurd h (Nat.lt_irrefl 0))
    (fun h => absurd h (Nat.lt_irrefl 0)) (retOkPRB_Lsl 0) (Lsl.stage2PRBZ_zero Lsl_ok)
    countPRB_zero_Lsl

theorem stage2PRBZ_zero_Lsl : Lsl.Stage2PRBZ (fun M _ => Lsl.K M) 0 := Lsl.stage2PRBZ_zero Lsl_ok

theorem slotted_fH : LinkSys.slotted fH = 1 := by
  have h := fH_slots
  unfold LinkSys.slotted
  cases hs : fH.slots with
  | nil => exact absurd hs h
  | cons _ _ => rfl

theorem calleeIni_fH : (LinkSys.calleeIni fH iniT).next = iniT.next + 1 ∧
    (LinkSys.calleeIni fH iniT).bytes = iniT.bytes := by
  rw [LinkSys.calleeIni_next, slotted_fH, LinkSys.calleeIni_bytes]; exact ⟨rfl, rfl⟩

/-- **`prefix_relatedPRI_atE` applies to `f` of the slotted system** (its artifact from `Lsl_ok`,
`InstCallsOne`/`TryCallsOne` by `instCallsOne_all`/`tryCallsOne_all`). -/
theorem prefix_relatedPRI_atE_f
    {XI : ExtSemI}
    {syms : String → Option Nat}
    {env : Clif.Env}
    {K : Nat}
    {F : BitVec 64 → Prop}
    {c : BitVec 64}
    {w₀ : Arm.ArmState}
    {args : List Clif.Val}
    {cs : Clif.State}
    (hnrc : NoRetCall env Lsl.P.bare cs)
    (hX : ∀ s n, ReachN env Lsl.P.bare cs s n →
      XCallsOk (env.only (Clif.Invoked env Lsl.P.bare s)) (fF.externs.map (·.2))
        (RelW ⟨F, syms, (Lsl.A fF).af.slotBase, (RAFrame.compute (Lsl.A fF).vcp (Lsl.A fF).rf).intBase⟩ fF c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env Lsl.P.bare s)) (indSigs fF)
        (RelW ⟨F, syms, (Lsl.A fF).af.slotBase, (RAFrame.compute (Lsl.A fF).vcp (Lsl.A fF).rf).intBase⟩ fF c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hcs : ClifEntry fF args cs)
    (hrel : RelW ⟨F, syms, (Lsl.A fF).af.slotBase, (RAFrame.compute (Lsl.A fF).vcp (Lsl.A fF).rf).intBase⟩ fF c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fF.sig args w₀)
    (htr : TrapsExplicit env Lsl.P.bare cs)
    {fuel : Nat}
    {v : List Clif.Val}
    {m : Clif.Mem}
    (hrun : Clif.runLoop env Lsl.P.bare fuel cs = .returned v m)
    {N : Nat}
    {H : ArmHooks}
    {G : BitVec 64 → Prop}
    {base ra : BitVec 64}
    {Kp : Nat}
    {cc : BitVec 64}
    {P : Nat → BitVec 64 → BitVec 8}
    {R : Nat → Arm.ArmState}
    {s : Arm.ArmState}
    (he : ActEntryPRN (Lsl.A fF).vcp (Lsl.A fF).rf (Lsl.A fF).af (Lsl.A fF).fa (Lsl.A fF).fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State}
    (hr : ReachN env Lsl.P.bare cs t N)
    (hcn : callNum t = 1) :
    ∀ j ≤ N, ∃ u i info uses w r, OnCallG (ArmStepX (XI.at 0) H (Lsl.A fF).fa) (Lsl.A fF).fa base s
        (fun t => ¬ PostCall (Lsl.A fF).fa base (Arm.r .PC t) ∨
          spOf t = spv s - BitVec.ofNat 64 (frameDrop (Lsl.A fF).af)) j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop (Lsl.A fF).af) ∧ CallSiteAt F K G s (Lsl.A fF).fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ (Lsl.A fF).vcp.CallSite info ∧
      gotGuard (GotV (Lsl.A fF).vcp) (XI.at 0) info uses ∧
      (XI.at j).call (callDest info) uses w = some r ∧
      RelatedN env Lsl.P.bare cs (fF.externs.map (·.2)) (indSigs fF)
        (RelW ⟨F, syms, (Lsl.A fF).af.slotBase, (RAFrame.compute (Lsl.A fF).vcp (Lsl.A fF).rf).intBase⟩ fF c) XI.sym j (callDest info) uses w :=
  prefix_relatedPRI_atE (Lsl_ok.subset fF fF_mem) (Lsl_ok.compiled fF fF_mem) (instCallsOne_all fF)
    (tryCallsOne_all fF) (Lsl_ok.covered fF fF_mem) hnrc hX hsym rfl hcs hrel hargs htr hrun he hr hcn

theorem XPBTGY_subZ_Lsl
    {M : Nat}
    {g : Clif.Function}
    {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8}
    {R : Nat → Arm.ArmState}
    {env : Clif.Env}
    {cs : Clif.State}
    {c : BitVec 64}
    {Q : Arm.ArmState → Prop}
    {n : Nat}
    (h2 : Lsl.Stage2Z (fun M _ => Lsl.K M) M g F P R env cs c Q n) :
    ∀ s w, Q s → SameWorld F s w → ∀ (i : MInst) (info : CallInfo),
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) → ∀ (ops : Array Operand) (regs : Array Reg)
      (i' : MInst), i.operands = .ok ops → ∀ (cc : CheckCtx) (wh : String),
      cc.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () → i.assign regs = .ok i' →
      CallAt (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC s) i' → Arm.CheckSPAlignment s →
      Arm.r .ERR s = .None →
      ∀ r, ((Lsl.XPBTGY (fun M _ => Lsl.K M) M g F P R env cs c).at n).call (callDest info) (useVals ops regs s) w =
          some r →
        (Lsl.XPRBT (fun M _ => Lsl.K M) M g F P R n).call (callDest info) (useVals ops regs s) w = some r :=
  Lsl.XPBTGY_subZ Lsl_ok h2

theorem calleeOkXPBTGZ_Lsl
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
    (h2 : Lsl.Stage2Z (fun M _ => Lsl.K M) M g F P R env cs c Q n) :
    CalleeOkGP Q F ((fun M _ => Lsl.K M) M g) G s (CallAt (Lsl.A g).fa (Lsl.A g).base)
      ((Lsl.XPBTGY (fun M _ => Lsl.K M) M g F P R env cs c).at n) (Lsl.hooks M)
      (Lsl.A g).vcp.CallSite (GotV (Lsl.A g).vcp) :=
  Lsl.calleeOkXPBTGZ Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet hg he hQ h2

theorem calleeTryOkXPBTGZ_Lsl
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
    (h2 : Lsl.Stage2Z (fun M _ => Lsl.K M) M g F P R env cs c Q n) :
    CalleeTryOkGP Q F ((fun M _ => Lsl.K M) M g) G s (CallAt (Lsl.A g).fa (Lsl.A g).base)
      ((Lsl.XPBTGY (fun M _ => Lsl.K M) M g F P R env cs c).at n) (Lsl.hooks M)
      (Lsl.A g).vcp.TrySite (GotV (Lsl.A g).vcp) :=
  Lsl.calleeTryOkXPBTGZ Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet hg he hQ h2

theorem thmPRBRL_ofZ_Lsl
    {M : Nat}
    (ih : 0 < M → Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M - 1))
    (hdet : 0 < M → Lsl.DetPRB (fun M _ => Lsl.K M) (M - 1))
    (hret : Lsl.RetOkPRB (fun M _ => Lsl.K M) M)
    (h2 : Lsl.Stage2PRBZ (fun M _ => Lsl.K M) M)
    (hcnt : Lsl.CountPRB (fun M _ => Lsl.K M) M) :
    Lsl.ThmPRBRL (fun M _ => Lsl.K M) M :=
  Lsl.thmPRBRL_ofZ Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet hret h2 hcnt

theorem stage2Z_base_Lsl
    {M : Nat}
    {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    (F : BitVec 64 → Prop)
    (P : Nat → BitVec 64 → BitVec 8)
    (R : Nat → Arm.ArmState)
    (c' : BitVec 64)
    (cs : Clif.State)
    (c : BitVec 64)
    (Q : Arm.ArmState → Prop)
    (n : Nat)
    (hb : ∀ nm vals m, InvokedN (Lsl.envOfB M g c') Lsl.P.bare cs n nm vals m → Lsl.P.func? nm = none) :
    Lsl.Stage2Z (fun M _ => Lsl.K M) M g F P R (Lsl.envOfB M g c') cs c Q n :=
  Lsl.stage2Z_base Lsl_ok hg F P R c' cs c Q n hb

theorem progResultBT_Lsl
    {M : Nat}
    (ih : 0 < M → Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M - 1))
    (hdet : 0 < M → Lsl.DetPRB (fun M _ => Lsl.K M) (M - 1))
    {g h : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    (hh : h ∈ Lsl.P.funcs)
    (hcallee : Lsl.Callee g h)
    {F : BitVec 64 → Prop}
    (himgF : ∀ a, Lsl.Img a → F a)
    {c : BitVec 64}
    (hroom : (fun M _ => Lsl.K M) M g ≤ c.toNat)
    (hdead : ∀ a, StackBelow ((fun M _ => Lsl.K M) M g) c a → F a ∧ ¬ Lsl.Img a)
    (halign : c.toNat % 16 = 0)
    {sl : List (Clif.SlotId × Nat)}
    {cm : Clif.Mem}
    {w : Arm.ArmState}
    {args : List CV}
    {vals rvals : List Clif.Val}
    {cm' : Clif.Mem}
    {cs : Clif.State}
    {ini : Clif.SlotInit}
    (hargs : ArgsAt h.sig vals args w)
    (hsav : StackArgsAvoid F h.sig vals w)
    (hmr : RelW ⟨F, Lsl.syms, (Lsl.A g).af.slotBase, (RAFrame.compute (Lsl.A g).vcp (Lsl.A g).rf).intBase⟩
      g c sl cm w)
    (hpl : Lsl.NeedSlots → Lsl.PlaceAtB cm c ini)
    (hslotb : Lsl.NeedSlots → ∀ a, Lsl.SlotByte h c a →
      ini.bytes (ini.next + 1) a = w.mem (BitVec.ofNat 64 a))
    (htab : Lsl.TableOf (M - 1) h (enterAt (Lsl.A h) (Lsl.canon h args w)) (calleeIni h ini))
    (hinit : Clif.initState Lsl.P h.name vals cm = .ok cs)
    (hret : Lsl.crun M cs = .returned rvals cm') :
    ∃ outs w', Lsl.progXBT (fun M _ => Lsl.K M) M F h args w = some (outs, w') ∧ outs.length = (sigRets h.sig).length ∧
      PrefixHold rvals outs ∧
      RelW ⟨F, Lsl.syms, (Lsl.A g).af.slotBase, (RAFrame.compute (Lsl.A g).vcp (Lsl.A g).rf).intBase⟩
        g c sl cm' w' :=
  Lsl.progResultBT Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet hg hh hcallee himgF hroom hdead halign hargs hsav hmr hpl hslotb htab hinit hret

theorem stage2_answerF_Lsl
    {M : Nat}
    (ih : 0 < M → Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M - 1))
    (hdet : 0 < M → Lsl.DetPRB (fun M _ => Lsl.K M) (M - 1))
    {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    {F : BitVec 64 → Prop}
    (himgF : ∀ a, Lsl.Img a → F a)
    {c : BitVec 64}
    (hroom : (fun M _ => Lsl.K M) M g ≤ c.toNat)
    (hdead : ∀ a, StackBelow ((fun M _ => Lsl.K M) M g) c a → F a ∧ ¬ Lsl.Img a)
    (halign : c.toNat % 16 = 0)
    (P : Nat → BitVec 64 → BitVec 8)
    (R : Nat → Arm.ArmState)
    (cs : Clif.State)
    (n : Nat)
    {d : Option String}
    {uses : List CV}
    {w : Arm.ArmState}
    (hor : ∀ h ∈ Lsl.P.funcs, ∀ (args : List CV) (vals : List Clif.Val) (cm : Clif.Mem)
      (cs' : Clif.State) (rvals : List Clif.Val) (cm' : Clif.Mem),
      (d = some h.name ∧ uses = args ∨
        d = none ∧ Lsl.IndTo g h ∧ ∃ u, uses = u :: args ∧ lo64 u = Lsl.Xb.sym h.name 0) →
      InvokedN (Lsl.envOfB M g c) Lsl.P.bare cs n h.name vals cm →
      Lsl.Callee g h → 0 < M →
      MemRel F Lsl.syms cm (Lsl.worldPR (fun M _ => Lsl.K M) M h (P n) (R n) w) →
      ArgsAt h.sig vals args (Lsl.worldPR (fun M _ => Lsl.K M) M h (P n) (R n) w) →
      StackArgsAvoid F h.sig vals (Lsl.worldPR (fun M _ => Lsl.K M) M h (P n) (R n) w) →
      SameWorld F w (Lsl.worldPR (fun M _ => Lsl.K M) M h (P n) (R n) w) → spv w = c →
      Clif.initState Lsl.P h.name vals cm = .ok cs' → Lsl.crun M cs' = .returned rvals cm' →
      Lsl.OracleAt (fun M _ => Lsl.K M) M h c cm args (Lsl.worldPR (fun M _ => Lsl.K M) M h (P n) (R n) w))
    (hnv : ¬ ∀ r, CallPost ((Lsl.envOfB M g c).only (InvokedN (Lsl.envOfB M g c) Lsl.P.bare cs n))
      (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, Lsl.syms, (Lsl.A g).af.slotBase, (RAFrame.compute (Lsl.A g).vcp (Lsl.A g).rf).intBase⟩ g c)
      Lsl.Xb.sym d uses w r) :
    ∃ x, (Lsl.XPRBT (fun M _ => Lsl.K M) M g F P R n).call d uses w = some x ∧
      CallPost ((Lsl.envOfB M g c).only (InvokedN (Lsl.envOfB M g c) Lsl.P.bare cs n))
        (g.externs.map (·.2)) (indSigs g)
        (RelW ⟨F, Lsl.syms, (Lsl.A g).af.slotBase, (RAFrame.compute (Lsl.A g).vcp (Lsl.A g).rf).intBase⟩ g c)
        Lsl.Xb.sym d uses w x :=
  Lsl.stage2_answerF Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet hg himgF hroom hdead halign P R cs n hor hnv

theorem stage2_answer_Lsl
    {M : Nat}
    (ih : 0 < M → Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M - 1))
    (hdet : 0 < M → Lsl.DetPRB (fun M _ => Lsl.K M) (M - 1))
    {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    {F : BitVec 64 → Prop}
    (himgF : ∀ a, Lsl.Img a → F a)
    {c : BitVec 64}
    (hroom : (fun M _ => Lsl.K M) M g ≤ c.toNat)
    (hdead : ∀ a, StackBelow ((fun M _ => Lsl.K M) M g) c a → F a ∧ ¬ Lsl.Img a)
    (halign : c.toNat % 16 = 0)
    (P : Nat → BitVec 64 → BitVec 8)
    (R : Nat → Arm.ArmState)
    (cs : Clif.State)
    (n : Nat)
    {d : Option String}
    {uses : List CV}
    {w : Arm.ArmState}
    (hor : ∀ h ∈ Lsl.P.funcs, ∀ (args : List CV) (vals : List Clif.Val) (cm : Clif.Mem),
      (d = some h.name ∧ uses = args ∨ d = none ∧ ∃ u, uses = u :: args) →
      InvokedN (Lsl.envOfB M g c) Lsl.P.bare cs n h.name vals cm →
      Lsl.OracleAt (fun M _ => Lsl.K M) M h c cm args (Lsl.worldPR (fun M _ => Lsl.K M) M h (P n) (R n) w))
    (hnv : ¬ ∀ r, CallPost ((Lsl.envOfB M g c).only (InvokedN (Lsl.envOfB M g c) Lsl.P.bare cs n))
      (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, Lsl.syms, (Lsl.A g).af.slotBase, (RAFrame.compute (Lsl.A g).vcp (Lsl.A g).rf).intBase⟩ g c)
      Lsl.Xb.sym d uses w r) :
    ∃ x, (Lsl.XPRBT (fun M _ => Lsl.K M) M g F P R n).call d uses w = some x ∧
      CallPost ((Lsl.envOfB M g c).only (InvokedN (Lsl.envOfB M g c) Lsl.P.bare cs n))
        (g.externs.map (·.2)) (indSigs g)
        (RelW ⟨F, Lsl.syms, (Lsl.A g).af.slotBase, (RAFrame.compute (Lsl.A g).vcp (Lsl.A g).rf).intBase⟩ g c)
        Lsl.Xb.sym d uses w x :=
  Lsl.stage2_answer Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet hg himgF hroom hdead halign P R cs n hor hnv

theorem retAt_enterAt_iff_Lsl
    {h : Clif.Function}
    {t x : Arm.ArmState} :
    Lsl.RetAt h (enterAt (Lsl.A h) t) x ↔ RetOf (Lsl.A h) t x :=
  Lsl.retAt_enterAt_iff 

theorem noRetAt_upTo_Lsl
    {M : Nat}
    {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    {F G : BitVec 64 → Prop}
    {ra : BitVec 64}
    {s w₀ : Arm.ArmState}
    (hME : Lsl.MachEntry (fun M _ => Lsl.K M) M g F G ra s w₀)
    (hra : RaOk (Lsl.A g) (ra - 4))
    {i : Nat}
    (htr : ∀ j < i, ¬ PostCall (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC (runX (Lsl.mach M g) j s)) ∨
      spOf (runX (Lsl.mach M g) j s) = spv s - BitVec.ofNat 64 (frameDrop (Lsl.A g).af))
    (hsp : spOf (runX (Lsl.mach M g) i s) = spv s - BitVec.ofNat 64 (frameDrop (Lsl.A g).af))
    (herr : Arm.r .ERR (runX (Lsl.mach M g) i s) = .None) :
    ∀ j < i + 1, ¬ Lsl.RetAt g s (runX (Lsl.mach M g) j s) :=
  Lsl.noRetAt_upTo Lsl_ok hg hME hra htr hsp herr

theorem tabUpTo_call_at_Lsl
    {M : Nat}
    {g : Clif.Function}
    {s : Arm.ArmState}
    {ini : Clif.SlotInit}
    (htab : Lsl.TableOf (M + 1) g s ini)
    {i : Nat}
    (hnr : ∀ j < i + 1, ¬ Lsl.RetAt g s (runX (Lsl.mach (M + 1) g) j s))
    (hcp : CallPc (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC (runX (Lsl.mach (M + 1) g) i s)))
    {h : Clif.Function}
    (hct : Lsl.CallsTo g (runX (Lsl.mach (M + 1) g) i s) h) :
    ∃ E : Nat → Nat,
      (∀ e, Lsl.TabUpTo (M + 1) g s ini.bytes ini.next i e →
        e = Clif.sumTo E (callsBefore (Lsl.mach (M + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) ∧
      (slotted h = 1 → ∀ a, Lsl.SlotByte h (spv (runX (Lsl.mach (M + 1) g) i s)) a →
        ini.bytes (ini.next + Clif.sumTo E
          (callsBefore (Lsl.mach (M + 1) g) (Lsl.A g).fa (Lsl.A g).base s i) + 1) a =
          (runX (Lsl.mach (M + 1) g) i s).mem (BitVec.ofNat 64 a)) ∧
      slotted h ≤ E (callsBefore (Lsl.mach (M + 1) g) (Lsl.A g).fa (Lsl.A g).base s i) ∧
      ∃ N', RetOf (Lsl.A h) (runX (Lsl.mach (M + 1) g) i s)
          (runX (Lsl.mach M h) N' (enterAt (Lsl.A h) (runX (Lsl.mach (M + 1) g) i s))) ∧
        (∀ N'' < N', ¬ RetOf (Lsl.A h) (runX (Lsl.mach (M + 1) g) i s)
          (runX (Lsl.mach M h) N'' (enterAt (Lsl.A h) (runX (Lsl.mach (M + 1) g) i s)))) ∧
        Lsl.TabUpTo M h (enterAt (Lsl.A h) (runX (Lsl.mach (M + 1) g) i s)) ini.bytes
          (ini.next + Clif.sumTo E (callsBefore (Lsl.mach (M + 1) g) (Lsl.A g).fa (Lsl.A g).base s i) +
            slotted h) N'
          (E (callsBefore (Lsl.mach (M + 1) g) (Lsl.A g).fa (Lsl.A g).base s i) - slotted h) :=
  Lsl.tabUpTo_call_at htab hnr hcp hct

theorem tableOf_callee_Lsl
    {M : Nat}
    {h : Clif.Function}
    {t : Arm.ArmState}
    {ini' : Clif.SlotInit}
    {N' e : Nat}
    (hret : RetOf (Lsl.A h) t (runX (Lsl.mach M h) N' (enterAt (Lsl.A h) t)))
    (htab : Lsl.TabUpTo M h (enterAt (Lsl.A h) t) ini'.bytes ini'.next N' e) :
    Lsl.TableOf M h (enterAt (Lsl.A h) t) ini' :=
  Lsl.tableOf_callee hret htab

theorem slotByte_below_Lsl
    {g h : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    (hcal : Lsl.Callee g h)
    {c : BitVec 64}
    (hroom : frameDrop (Lsl.A h).af ≤ c.toNat)
    {a : Nat}
    (ha : Lsl.SlotByte h c a) :
    StackBelow (frameDrop (Lsl.A h).af) c (BitVec.ofNat 64 a) ∧ (BitVec.ofNat 64 a).toNat = a :=
  Lsl.slotByte_below Lsl_ok hg hcal hroom ha

theorem callerFacts_Lsl
    {M : Nat}
    (hM : 0 < M)
    {g h : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    (hh : h ∈ Lsl.P.funcs)
    (hcal : Lsl.Callee g h)
    {F : BitVec 64 → Prop}
    (himgF : ∀ a, Lsl.Img a → F a)
    {Lu : List (Nat × Reg)}
    (hLu : Lu.map (·.2) = regLocs h.sig)
    {t w : Arm.ArmState}
    (hsw : SameWorld F t w)
    (himgT : ∀ a, Lsl.Img a → t.mem a = Lsl.imgMem a)
    (hra : RaOk (Lsl.A h) (Arm.r .PC t))
    {P : Nat → BitVec 64 → BitVec 8}
    {R : Nat → Arm.ArmState}
    {n : Nat}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n))
    (hrgnQ : ∀ a, StackBelow ((fun M _ => Lsl.K M) M g) (spv t) a → t.mem a = P n a)
    (hdeadW : ∀ a, StackBelow (frameDrop (Lsl.A h).af + (fun M _ => Lsl.K M) (M - 1) h) (spv w) a → F a ∧ ¬ Lsl.Img a) :
    Lsl.CallerOk F h (Lu.map (fun q => regVal t q.2)) (Lsl.worldPR (fun M _ => Lsl.K M) M h (P n) (R n) w) t ∧
    (∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 →
      Arm.r f t = Arm.r f (Lsl.canon h (Lu.map (fun q => regVal t q.2)) (Lsl.worldPR (fun M _ => Lsl.K M) M h (P n) (R n) w))) ∧
    (∀ a, StackBelow (frameDrop (Lsl.A h).af + (fun M _ => Lsl.K M) (M - 1) h) (spv (Lsl.worldPR (fun M _ => Lsl.K M) M h (P n) (R n) w)) a →
      t.mem a = (Lsl.canon h (Lu.map (fun q => regVal t q.2)) (Lsl.worldPR (fun M _ => Lsl.K M) M h (P n) (R n) w)).mem a) ∧
    SameWorld F t (Lsl.worldPR (fun M _ => Lsl.K M) M h (P n) (R n) w) :=
  Lsl.callerFacts Lsl_ok (Lsl.budget_K Lsl_ok) hM hg hh hcal himgF hLu hsw himgT hra hmskQ hrgnQ hdeadW

theorem oracleAt_of_call_Lsl
    {M' : Nat}
    (hdt : Lsl.DetTabPRB (fun M _ => Lsl.K M) (M' + 1))
    {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    {F G : BitVec 64 → Prop}
    {ra : BitVec 64}
    {s w₀ : Arm.ArmState}
    (hME : Lsl.MachEntry (fun M _ => Lsl.K M) (M' + 1) g F G ra s w₀)
    (hra : RaOk (Lsl.A g) (ra - 4))
    {ini : Clif.SlotInit}
    (htab : Lsl.TableOf (M' + 1) g s ini)
    (himgF : ∀ a, Lsl.Img a → F a)
    {c : BitVec 64}
    (hroom : (fun M _ => Lsl.K M) (M' + 1) g ≤ c.toNat)
    (hdead : ∀ a, StackBelow ((fun M _ => Lsl.K M) (M' + 1) g) c a → F a ∧ ¬ Lsl.Img a)
    (halign : c.toNat % 16 = 0)
    {i : Nat}
    (htr : ∀ j < i, ¬ PostCall (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC (runX (Lsl.mach (M' + 1) g) j s)) ∨
      spOf (runX (Lsl.mach (M' + 1) g) j s) = spv s - BitVec.ofNat 64 (frameDrop (Lsl.A g).af))
    (hsp : spOf (runX (Lsl.mach (M' + 1) g) i s) = spv s - BitVec.ofNat 64 (frameDrop (Lsl.A g).af))
    (herr : Arm.r .ERR (runX (Lsl.mach (M' + 1) g) i s) = .None)
    (hcp : CallPc (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC (runX (Lsl.mach (M' + 1) g) i s)))
    {h : Clif.Function}
    (hpf : Lsl.P.func? h.name = some h)
    (hcal : Lsl.Callee g h)
    (hct : Lsl.CallsTo g (runX (Lsl.mach (M' + 1) g) i s) h)
    {P : Nat → BitVec 64 → BitVec 8}
    {R : Nat → Arm.ArmState}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f (runX (Lsl.mach (M' + 1) g) i s) =
      Arm.r f (R (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)))
    (hrgnQ : ∀ a, StackBelow ((fun M _ => Lsl.K M) (M' + 1) g) (spv (runX (Lsl.mach (M' + 1) g) i s)) a →
      (runX (Lsl.mach (M' + 1) g) i s).mem a =
        P (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i) a)
    {Lu : List (Nat × Reg)}
    (hLu : Lu.map (·.2) = regLocs h.sig)
    {w : Arm.ArmState}
    (hsw : SameWorld F (runX (Lsl.mach (M' + 1) g) i s) w)
    (hspw : spv w = c)
    (himgT : ∀ a, Lsl.Img a → (runX (Lsl.mach (M' + 1) g) i s).mem a = Lsl.imgMem a)
    (hrah : RaOk (Lsl.A h) (Arm.r .PC (runX (Lsl.mach (M' + 1) g) i s)))
    {vals : List Clif.Val}
    {cm : Clif.Mem}
    {cs : Clif.State}
    {rvals : List Clif.Val}
    {cm' : Clif.Mem}
    (hmrW : MemRel F Lsl.syms cm (Lsl.worldPR (fun M _ => Lsl.K M) (M' + 1) h
      (P (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
      (R (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) w))
    (hargsW : ArgsAt h.sig vals (Lu.map (fun q => regVal (runX (Lsl.mach (M' + 1) g) i s) q.2))
      (Lsl.worldPR (fun M _ => Lsl.K M) (M' + 1) h (P (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
        (R (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) w))
    (hsavW : StackArgsAvoid F h.sig vals
      (Lsl.worldPR (fun M _ => Lsl.K M) (M' + 1) h (P (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
        (R (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) w))
    {x : Nat}
    (hpl : Lsl.NeedSlots → Lsl.PlaceAtB cm c (ini.adv x))
    (hcnt : ∀ e, Lsl.TabUpTo (M' + 1) g s ini.bytes ini.next i e → e = x)
    (hinit : Clif.initState Lsl.P h.name vals cm = .ok cs)
    (hrun : Lsl.crun (M' + 1) cs = .returned rvals cm') :
    Lsl.OracleAt (fun M _ => Lsl.K M) (M' + 1) h c cm (Lu.map (fun q => regVal (runX (Lsl.mach (M' + 1) g) i s) q.2))
      (Lsl.worldPR (fun M _ => Lsl.K M) (M' + 1) h (P (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
        (R (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) w) :=
  Lsl.oracleAt_of_call Lsl_ok (Lsl.budget_K Lsl_ok) hdt hg hME hra htab himgF hroom hdead halign htr hsp herr hcp hpf hcal hct hmskQ hrgnQ hLu hsw hspw himgT hrah hmrW hargsW hsavW hpl hcnt hinit hrun

theorem progCallPRBRLT_Lsl
    {M : Nat}
    (hM : 0 < M)
    (ih : Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M - 1))
    (hdet : Lsl.DetPRB (fun M _ => Lsl.K M) (M - 1))
    {n : String}
    {h : Clif.Function}
    (hpf : Lsl.P.func? n = some h)
    (hcal : ∃ g ∈ Lsl.P.funcs, Lsl.Callee g h)
    {F : BitVec 64 → Prop}
    (himgF : ∀ a, Lsl.Img a → F a)
    {uses : List CV}
    {w : Arm.ArmState}
    (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (Lsl.A h).af + (fun M _ => Lsl.K M) (M - 1) h ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (Lsl.A h).af + (fun M _ => Lsl.K M) (M - 1) h) (spv w) a → F a ∧ ¬ Lsl.Img a)
    {vals : List Clif.Val}
    {cm : Clif.Mem}
    {cs : Clif.State}
    {rvals : List Clif.Val}
    {cm' : Clif.Mem}
    {ini : Clif.SlotInit}
    (hmr : MemRel F Lsl.syms cm w)
    (hargs : ArgsAt h.sig vals uses w)
    (hsav : StackArgsAvoid F h.sig vals w)
    (hpl : Lsl.NeedSlots → Lsl.PlaceAtB cm (spv w) ini)
    (hslotb : Lsl.NeedSlots → ∀ a, Lsl.SlotByte h (spv w) a →
      ini.bytes (ini.next + 1) a = w.mem (BitVec.ofNat 64 a))
    (htab : Lsl.TableOf (M - 1) h (enterAt (Lsl.A h) (Lsl.canon h uses w)) (calleeIni h ini))
    (hinit : Clif.initState Lsl.P n vals cm = .ok cs)
    (hrun : Lsl.crun M cs = .returned rvals cm') :
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState) (e : Nat),
      us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel F Lsl.syms cm' wf ∧ (Lsl.A h).vc.RetsSite us ∧
      (Lsl.NeedSlots → Clif.NextAdv cs.mem.leave cm' e) ∧
      (∀ t, Lsl.CallerOk F h uses w t →
        (∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f t = Arm.r f (Lsl.canon h uses w)) →
        (∀ a, StackBelow (frameDrop (Lsl.A h).af + (fun M _ => Lsl.K M) (M - 1) h) (spv w) a →
          t.mem a = (Lsl.canon h uses w).mem a) → ∃ k,
        Lsl.pcall M h t =
          Arm.set_program (runX (Lsl.mach (M - 1) h) k (enterAt (Lsl.A h) t)) t.program ∧
        ActRet (Arm.r .PC t + 4) F
          (fun a => F a ∧ ¬ StackBelow (frameDrop (Lsl.A h).af + (fun M _ => Lsl.K M) (M - 1) h) (spv w) a)
          us outs wf (enterAt (Lsl.A h) t) (runX (Lsl.mach (M - 1) h) k (enterAt (Lsl.A h) t)) ∧
        Lsl.TabUpTo (M - 1) h (enterAt (Lsl.A h) t) (calleeIni h ini).bytes (calleeIni h ini).next k
          e ∧ PostTrace (Lsl.A h).fa (Lsl.A h).af (Lsl.A h).base (Lsl.mach (M - 1) h) (enterAt (Lsl.A h) t) k) :=
  Lsl.progCallPRBRLT Lsl_ok hM ih hdet hpf hcal himgF herr hal hroom hdead hmr hargs hsav hpl hslotb htab hinit hrun

theorem callCount_Lsl
    {M' : Nat}
    (ih : Lsl.ThmPRBRL (fun M _ => Lsl.K M) M')
    (hdet : Lsl.DetPRB (fun M _ => Lsl.K M) M')
    {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs)
    {F G : BitVec 64 → Prop}
    {ra : BitVec 64}
    {s w₀ : Arm.ArmState}
    (hME : Lsl.MachEntry (fun M _ => Lsl.K M) (M' + 1) g F G ra s w₀)
    (hra : RaOk (Lsl.A g) (ra - 4))
    {ini : Clif.SlotInit}
    (htab : Lsl.TableOf (M' + 1) g s ini)
    (himgF : ∀ a, Lsl.Img a → F a)
    {c : BitVec 64}
    (hroom : (fun M _ => Lsl.K M) (M' + 1) g ≤ c.toNat)
    (hdead : ∀ a, StackBelow ((fun M _ => Lsl.K M) (M' + 1) g) c a → F a ∧ ¬ Lsl.Img a)
    (halign : c.toNat % 16 = 0)
    {i : Nat}
    (htr : ∀ j < i, ¬ PostCall (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC (runX (Lsl.mach (M' + 1) g) j s)) ∨
      spOf (runX (Lsl.mach (M' + 1) g) j s) = spv s - BitVec.ofNat 64 (frameDrop (Lsl.A g).af))
    (hsp : spOf (runX (Lsl.mach (M' + 1) g) i s) = spv s - BitVec.ofNat 64 (frameDrop (Lsl.A g).af))
    (herr : Arm.r .ERR (runX (Lsl.mach (M' + 1) g) i s) = .None)
    (hcp : CallPc (Lsl.A g).fa (Lsl.A g).base (Arm.r .PC (runX (Lsl.mach (M' + 1) g) i s)))
    {h : Clif.Function}
    (hpf : Lsl.P.func? h.name = some h)
    (hcal : Lsl.Callee g h)
    (hct : Lsl.CallsTo g (runX (Lsl.mach (M' + 1) g) i s) h)
    {P : Nat → BitVec 64 → BitVec 8}
    {R : Nat → Arm.ArmState}
    (hmskQ : ∀ f, MaskedReg f → Arm.r f (runX (Lsl.mach (M' + 1) g) i s) =
      Arm.r f (R (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)))
    (hrgnQ : ∀ a, StackBelow ((fun M _ => Lsl.K M) (M' + 1) g) (spv (runX (Lsl.mach (M' + 1) g) i s)) a →
      (runX (Lsl.mach (M' + 1) g) i s).mem a =
        P (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i) a)
    {Lu : List (Nat × Reg)}
    (hLu : Lu.map (·.2) = regLocs h.sig)
    {w : Arm.ArmState}
    (hsw : SameWorld F (runX (Lsl.mach (M' + 1) g) i s) w)
    (hspw : spv w = c)
    (himgT : ∀ a, Lsl.Img a → (runX (Lsl.mach (M' + 1) g) i s).mem a = Lsl.imgMem a)
    (hrah : RaOk (Lsl.A h) (Arm.r .PC (runX (Lsl.mach (M' + 1) g) i s)))
    {vals : List Clif.Val}
    {cm : Clif.Mem}
    {cs : Clif.State}
    {rvals : List Clif.Val}
    {cm' : Clif.Mem}
    (hmrW : MemRel F Lsl.syms cm (Lsl.worldPR (fun M _ => Lsl.K M) (M' + 1) h
      (P (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
      (R (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) w))
    (hargsW : ArgsAt h.sig vals (Lu.map (fun q => regVal (runX (Lsl.mach (M' + 1) g) i s) q.2))
      (Lsl.worldPR (fun M _ => Lsl.K M) (M' + 1) h (P (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
        (R (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) w))
    (hsavW : StackArgsAvoid F h.sig vals
      (Lsl.worldPR (fun M _ => Lsl.K M) (M' + 1) h (P (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
        (R (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) w))
    (hor : Lsl.OracleAt (fun M _ => Lsl.K M) (M' + 1) h c cm (Lu.map (fun q => regVal (runX (Lsl.mach (M' + 1) g) i s) q.2))
      (Lsl.worldPR (fun M _ => Lsl.K M) (M' + 1) h (P (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i))
        (R (callsBefore (Lsl.mach (M' + 1) g) (Lsl.A g).fa (Lsl.A g).base s i)) w))
    (hinit : Clif.initState Lsl.P h.name vals cm = .ok cs)
    (hrun : Lsl.crun (M' + 1) cs = .returned rvals cm') :
    ∃ d, (Lsl.NeedSlots → Clif.NextAdv cm cm' d) ∧
      ∀ e e', Lsl.TabUpTo (M' + 1) g s ini.bytes ini.next i e →
        Lsl.TabUpTo (M' + 1) g s ini.bytes ini.next (i + 1) e' → e' = e + d :=
  Lsl.callCount Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet hg hME hra htab himgF hroom hdead halign htr hsp herr hcp hpf hcal hct hmskQ hrgnQ hLu hsw hspw himgT hrah hmrW hargsW hsavW hor hinit hrun

end E2E.LinkSlotSysWitness
