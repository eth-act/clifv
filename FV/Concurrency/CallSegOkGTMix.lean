import FV.Concurrency.CallSegOkGTExtWitness

/-!
# Witness: a compiled caller of a compiled callee and an external, end to end (#649)

One link in which a compiled caller makes two calls, the first to a compiled callee, the second
to an external:

* `fM`: the CLIF `%f(i64) -> i64 { v1 = call fn0(v0); v2 = call fn1(v1); return v2 }` with
  `fn0 = colocated %ld` (the compiled `atomic_load`, `ldF` at `0x20000`) and `fn1 = colocated %xt`
  (an external), compiled by the pipeline (`callerM` at `0x30000`);
* `idT`: the external's Arm code, one `ret` at `0x28000`; `fT`: its CLIF specification
  `v1 = bor v0, v0; return v1`; `pM = [fM, fL, fT]`, `linkM = [ld, xt, f]`;
* `sM0`: the caller's ABI entry state (sp `0x7000`, the three functions' code in memory), `RCM`
  its activation with the kept addresses `GM` (the callee's and the external's code);
* **`fnOk_M`**, **`fnOk_LM`** (both compiled functions `FnOk` in `linkM`), **`linkOkM`**
  (`LinkOkX`), `placeOkM`, `linkFreeM`, **`extM`** (the external's contract, proven by
  `WitnessExt.ext_ret`);
* **`CallShape2`**, `Fam2`, **`reach_inv2`**, `depth2`, `partsOk2`: the generic reachability
  argument for a caller whose block is two calls, each of a one-statement callee;
* `shape_M`, **`partsOk_M`** (the one access is `atomic_load`'s 8 bytes at `0`), **`depth_M`**;
* **`ent_M`**: the caller's root activation's `Ent`;
* **`realizes_calls_mixT`**: `realizes_linked_calls_ext` on `linkM`/`pM` with one thread, every
  premise discharged but the run.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallSegOkGT.WitnessMix

open Arm ArmFoot ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck ThreadRefine IselCall IselCallRet ArmAllocThread E2E
  LinkedMachine LinkedMachine.Link LinkedMachine.Witness CallComposeT CallSegOkG CallSegLive
  CallSegPc CallSegRun CallResumeChecks CallEntryRel CallSeg.WitnessC RealizeCompiled.WitnessL
  IselResume CallArity CallArgsEntry CallArgsL2 CallArgsAt CallSegExt CallSegOkGT.Witness
  CallSegOkGT.WitnessFull CallSegOkGT.WitnessExt ClifLift
open ArmAllocThread.Witness renaming act → actW
open ArmAllocThread.Witness (entryAt codeMem ok_getD)

/-! ## The caller, the external and the link -/

/-- The caller: a call of the compiled `atomic_load`, then of the external `xt`. -/
def srcM : String := "function %f(i64) -> i64 {
    fn0 = colocated %ld(i64) -> i64
    fn1 = colocated %xt(i64) -> i64

block0(v0: i64):
    v1 = call fn0(v0)
    v2 = call fn1(v1)
    return v2
}
"

def fM : Clif.Function :=
  match Clif.parse srcM with
  | .ok p => p.funcs.headD default
  | .error _ => default

def vcM : VCode := match lowerFunction fM with
  | .ok vc => vc
  | .error _ => default

def vcpM : VCode := match Backend.prepare vcM with
  | .ok vcp => vcp
  | .error _ => default

def rfM : RFunc := spillAlloc vcpM

/-- The external's CLIF specification: it returns its argument. -/
def srcT : String := "function %xt(i64) -> i64 {
block0(v0: i64):
    v1 = bor v0, v0
    return v1
}
"

def fT : Clif.Function :=
  match Clif.parse srcT with
  | .ok p => p.funcs.headD default
  | .error _ => default

/-- The specification's entry block. -/
def BT : Clif.Block := fT.blocks.headD default

/-- The program: the caller, `atomic_load` and the external's specification. -/
def pM : Clif.Program := { funcs := [fM, fL, fT] }

/-- The caller's externs `fn0` (`ld`) and `fn1` (`xt`). -/
def extL : Clif.ExtFunc := (fM.extern? 0).getD default

def extT : Clif.ExtFunc := (fM.extern? 1).getD default

/-- **The compiled caller at `0x30000`.** -/
def callerM : LFn := { LFn.of (actW vcpM rfM) with base := 0x30000#64 }

/-- **The external's code**: one `ret` at `0x28000`. -/
def idT : LFn := { idF with base := 0x28000#64 }

/-- **The link of `atomic_load`, the external and the caller.** -/
def linkM : Link := ⟨[("ld", ldF), ("xt", idT), ("f", callerM)]⟩

/-! ## The caller's activation -/

/-- The external's code addresses. -/
def GX (a : BitVec 64) : Prop := (a - 0x28000#64).toNat < 4

instance (a : BitVec 64) : Decidable (GX a) := by unfold GX; infer_instance

/-- The caller's kept addresses: the callee's and the external's code. -/
def GM (a : BitVec 64) : Prop := GL a ∨ GX a

instance (a : BitVec 64) : Decidable (GM a) := by unfold GM; infer_instance

/-- The three functions' code in memory. -/
def memM : Memory := fun a =>
  if GL a then RAL.s0.mem a
  else if GX a then codeMem retFb 0x28000#64 a
  else codeMem (actW vcpM rfM).fb 0x30000#64 a

/-- The caller's ABI entry state: sp `0x7000`, its code at `0x30000`, the others' in memory. -/
def sM0 : ArmState := setMem memM (entryAt 0x7000#64 (actW vcpM rfM).fb 0x30000#64)

/-- **The caller's activation** (no callee budget). -/
def RCM : RL := { actW vcpM rfM with base := 0x30000#64, s0 := sM0, H := linkM.H, G := GM }

theorem factsM : (checkAlloc vcpM rfM).isOk = true ∧ (lowerRFunc vcpM rfM).toBool = true ∧
    (emitFunc 0 (actW vcpM rfM).af).toBool = true ∧ (actW vcpM rfM).fa.k = 0 ∧
    (actW vcpM rfM).fa.layout.toBool = true ∧
    (labelOffsets (actW vcpM rfM).fa.lines).toBool = true ∧
    4 * (actW vcpM rfM).fb.words.size ≤ 2 ^ 64 ∧
    (emitPlan (actW vcpM rfM).fa.k (actW vcpM rfM).af).toBool = true := by
  native_decide -- witness: native_decide

theorem allocM : checkAlloc vcpM rfM = .ok () := by
  have h := factsM.1
  revert h
  cases checkAlloc vcpM rfM with
  | ok u => intro _; rfl
  | error e => intro h; cases h

theorem spM : E2E.spv RCM.s0 = 0x7000#64 ∧ frameDrop RCM.af = 192 ∧
    RCM.fb.words.size ≤ 0x4000 ∧ RCM.fr.size ≤ 240 ∧ RCM.af.frameSize = 176 ∧
    (actW vcpL rfL).fb.words.size = 29 ∧ 0 < RCM.fb.words.size := by
  native_decide -- witness: native_decide

theorem codeRCM : ∀ k < RCM.fb.words.size,
    Arm.read_mem_bytes 4 (0x30000#64 + BitVec.ofNat 64 (4 * k)) RCM.s0 = RCM.fb.words[k]! := by
  native_decide -- witness: native_decide

theorem retM : Arm.read_mem_bytes 4 (0x28000#64 + BitVec.ofNat 64 (4 * 0)) sM0 = 0xd65f03c0#32 := by
  native_decide -- witness: native_decide

/-- The entry `args` of the caller reads argument registers only. -/
theorem entryArgRCM : ∀ r, RCM.vc.EntryArg r → r.isArgReg = true := by
  rintro r ⟨vb, ds, h1, h2, v, hv⟩
  have h : entryArgsB vcpM = true := by native_decide -- witness: native_decide
  simp only [entryArgsB, show vcpM = RCM.vc from rfl, h1, h2, List.all_eq_true] at h
  exact h _ hv

/-- The caller's ABI entry: `x0` is `0`. -/
theorem x0M : regVal RCM.s0 (.x 0) = 0 := by native_decide -- witness: native_decide

theorem spv_RCM : E2E.spv RCM.s0 = 0x7000#64 := spM.1

theorem program_RCM : RCM.s0.program = RCM.fb.program RCM.base := by
  show (setMem memM _).program = _
  rw [setMem_program, ArmAllocThread.Witness.entryAt_program]
  rfl

theorem gM_ge {a : BitVec 64} (h : GM a) : 0x20000 ≤ a.toNat ∧ a.toNat < 0x30000 := by
  have hs := spM.2.2.2.2.2.1
  rcases h with h | h
  · unfold GL at h
    rw [hs] at h
    bv_omega
  · unfold GX at h
    bv_omega

theorem stackRCM : StackAvail 0 (actW vcpM rfM).af RCM.s0 := by
  have hs := spM
  refine ⟨?_, fun a ha => ?_⟩
  · rw [spv_RCM]; show (actW vcpM rfM).af.frameSize + 16 + 0 ≤ _
    have : (actW vcpM rfM).af.frameSize = 176 := hs.2.2.2.2.1
    simp only [BitVec.toNat_ofNat]; omega
  · obtain ⟨j, hj, hd⟩ := codeAddr_words program_RCM ha
    rw [spv_RCM]
    have : (actW vcpM rfM).af.frameSize = 176 := hs.2.2.2.2.1
    show (actW vcpM rfM).af.frameSize + 16 + 0 ≤ _
    rw [this]
    have hj' : j < 0x4000 := by have := hs.2.2.1; omega
    rw [show RCM.base = 0x30000#64 from rfl] at hd
    generalize j = J at hj' hd
    bv_omega

theorem wfRCM : RCM.Wf := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h9⟩ := factsM
  refine wf_gen allocM h1 h2 h3 h4 h5 h6 h9 stackRCM program_RCM fun a hG ⟨h1, _⟩ => ?_
  have := gM_ge hG
  rw [show E2E.spv sM0 = 0x7000#64 from spv_RCM] at h1
  simp only [BitVec.toNat_ofNat] at h1
  omega

theorem abiRCM : AbiCall RCM.fb RCM.base 0x4000#64 RCM.s0 where
  program := program_RCM
  code k w hk := by
    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hk
    rw [show RCM.base = 0x30000#64 from rfl, codeRCM k hlt]
    simp [hlt]
  pc := by
    show Arm.r .PC (setMem memM _) = _
    rw [show RCM.base = 0x30000#64 from rfl]
    simp [ArmFoot.r_setMem, ArmAllocThread.Witness.entryAt, Arm.r_of_w_same]
  err := by
    show Arm.r .ERR (setMem memM _) = _
    simp only [ArmAllocThread.Witness.entryAt, ArmFoot.r_setMem,
      Arm.r_of_w_different (show StateField.ERR ≠ .PC by simp),
      Arm.r_of_w_different (show StateField.ERR ≠ .GPR 31#5 by simp),
      Arm.r_of_w_different (show StateField.ERR ≠ .GPR 30#5 by simp)]
    simp [set_program, ArmState.default, Arm.r, read_base_error]
  lr := by
    show Arm.r (.GPR 30#5) (setMem memM _) = _
    simp [ArmAllocThread.Witness.entryAt, ArmFoot.r_setMem, Arm.r_of_w_different,
      Arm.r_of_w_same]
  spAligned := by rw [spv_RCM]; decide
  fits := by
    have := spM.2.2.1
    rw [show RCM.base = 0x30000#64 from rfl]
    simp only [BitVec.toNat_ofNat]; omega

/-- The caller's body-entry world. -/
abbrev w₀M : ArmState := E2E.bodyOf RCM.af RCM.s0

/-! ## The link is well formed -/

theorem laidCM : callerM.LaidOut where
  layout := ok_getD factsM.2.2.2.2.1
  lm := ok_getD factsM.2.2.2.2.2.1
  pos := spM.2.2.2.2.2.2
  fit := by
    show (0x30000#64 : BitVec 64).toNat + 4 * (actW vcpM rfM).fb.words.size ≤ 2 ^ 64
    have := spM.2.2.1
    simp only [BitVec.toNat_ofNat]
    have : (actW vcpM rfM).fb.words.size ≤ 0x4000 := this
    omega

theorem laidT : idT.LaidOut where
  layout := laidX.layout
  lm := laidX.lm
  pos := laidX.pos
  fit := by
    show (0x28000#64 : BitVec 64).toNat + 4 * retFb.words.size ≤ 2 ^ 64
    rw [checksX.2.2.1]; decide

theorem sepM : linkM.fns.Pairwise Sep := by native_decide -- witness: native_decide

/-- **The link is well formed.** -/
theorem okM : linkM.Ok where
  sep := sepM
  laid := by
    intro p hp
    simp only [linkM, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact laidL
    · exact laidT
    · exact laidCM

theorem mem_ldM : ("ld", ldF) ∈ linkM.fns := .head _

theorem mem_xtM : ("xt", idT) ∈ linkM.fns := .tail _ (.head _)

theorem mem_callerM : ("f", callerM) ∈ linkM.fns := .tail _ (.tail _ (.head _))

theorem mem_linkM {n : String} {F : LFn} (h : (n, F) ∈ linkM.fns) :
    (n = "ld" ∧ F = ldF) ∨ (n = "xt" ∧ F = idT) ∨ (n = "f" ∧ F = callerM) := by
  simpa [linkM] using h

/-! ## Checks -/

theorem checksCM : lowerCheck fM vcM = true ∧ threadCheckC fM = true ∧ callArityC fM = true ∧
    callUseRegsC fM = true ∧ fM.externs.map (·.2.name) = ["ld", "xt"] ∧
    (indSigs fM).isEmpty = true ∧ verifiable fM = true ∧
    fM.blocks.all (fun B => !B.term.isTry) = true ∧ IselThread.Witness.isOkB vcM.cfg = true ∧
    vcM.outgoing = 0 ∧
    (locsOf fM.sig).all (fun l => match l with | .stack _ => false | _ => true) = true ∧
    fM.externs = [(0, extL), (1, extT)] ∧ callResLenB fM = true ∧ callUsesVirtB vcpM = true ∧
    callDefsVirtB vcpM = true ∧ callDefsRetB vcpM [.x 0] = true ∧ prepCheck vcM vcpM = true ∧
    vcpM.blocks.all (·.insts.all callerFormB) = true ∧ extL.name = "ld" ∧ extT.name = "xt" ∧
    fL.sig = extL.sig ∧ fT.sig = extT.sig := by
  native_decide -- witness: native_decide

theorem checksPM : fM.name = "f" ∧ fT.name = "xt" ∧ fM.slots = [] ∧ fT.slots = [] ∧
    pM.funcs.all (fun f => f.externs.all (·.2.name != f.name)) = true ∧
    pM.funcs.all (fun g => g.blocks.all fun b => match b.term with
      | .returnCall .. => false
      | _ => true) = true ∧
    callsInsideB callerM = true ∧ callsInsideB idT = true ∧ retsX0B vcpM = true ∧
    frameDrop callerM.af = 192 ∧ callerM.af.frameSize = 176 := by
  native_decide -- witness: native_decide

theorem name_fM : fM.name = "f" := checksPM.1

theorem name_fT : fT.name = "xt" := checksPM.2.1

theorem slots_fM : fM.slots = [] := checksPM.2.2.1

theorem slots_fT : fT.slots = [] := checksPM.2.2.2.1

theorem drop_M : frameDrop callerM.af = 192 := checksPM.2.2.2.2.2.2.2.2.2.1

theorem fs_M : callerM.af.frameSize = 176 := checksPM.2.2.2.2.2.2.2.2.2.2

theorem cfgM : ∃ ss ps, vcM.cfg = .ok (ss, ps) := by
  have h := checksCM.2.2.2.2.2.2.2.2.1
  revert h
  cases vcM.cfg with
  | ok r => intro _; exact ⟨r.1, r.2, rfl⟩
  | error e => intro h; cases h

/-- `pM` has no `return_call`. -/
theorem linkFreeM : ∀ f : Clif.Function, f ∈ Clif.Program.funcs pM → Clif.LinkFree f := by
  intro g hg b hb fn args he
  have h := List.all_eq_true.mp checksPM.2.2.2.2.2.1 g hg
  have := List.all_eq_true.mp h b hb
  rw [he] at this
  cases this

/-! ## The two compiled functions -/

/-- Every activation of the caller is in the scope with calls. -/
theorem scope_M {R : RL} (hR : R.vc = vcpM) : MemScopeLSC R := by
  intro b vb k i hb hi
  rw [hR] at hb
  obtain ⟨hb', rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨hk', rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  have h1 := (Array.all_eq_true.mp checksCM.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) b hb'
  have h2 : callerFormB vcpM.blocks[b].insts[k] = true := (Array.all_eq_true.mp h1) k hk'
  revert h2
  generalize vcpM.blocks[b].insts[k] = i
  intro h2
  cases i with
  | args ds => exact .inl (.inl (.inl (.inr (.inl ⟨ds, rfl⟩))))
  | rets us => exact .inl (.inl (.inl (.inr (.inr (.inl ⟨us, rfl⟩)))))
  | call info => exact .inr (.inr (.inr ⟨info, rfl⟩))
  | _ => simp [callerFormB] at h2

theorem static_M : callerM.Static :=
  ⟨wfRCM.check, wfRCM.alloc, wfRCM.emit, wfRCM.layout, wfRCM.lm, wfRCM.fit, wfRCM.psF,
    entryArgRCM⟩

/-- **The caller is compiled in `linkM`.** -/
theorem fnOk_M {env : Clif.Env} (henvL : env.extern "ld" = none) (henvT : env.extern "xt" = none) :
    FnOk linkM env pM (fun _ => none) "f" callerM fM := by
  obtain ⟨hlow, hthr, har0, hcu0, hnames, hind, hv, hnt, -, hout0, hlocs, hexts, hres, huv, hdv,
    -, hprep, -, hnL, hnT, hsigL, hsigT⟩ := checksCM
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hbl, har, hcu⟩ :=
    obligations_of_checksA hlow hthr har0 hcu0
  obtain ⟨Lp, ss, ss', H3, hm3⟩ := CallLayers.prep_init (vc := vcM) (vcp := callerM.vc) hprep
  obtain ⟨cc, ins, a0, hat, hm4⟩ :=
    CallLayers.alloc_init (vc := callerM.vc) (rf := callerM.rf) allocM ckeep
  have hext : ∀ e ∈ fM.externs, env.extern e.2.name = none := by
    intro e he
    have : e.2.name ∈ fM.externs.map (·.2.name) := List.mem_map_of_mem he
    rw [hnames] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h <;> rw [h]
    · exact henvL
    · exact henvT
  refine ⟨static_M, by rw [fs_M], fun q hq => (by rw [slots_fM] at hq; cases hq), vcM, ctx, st0,
    R, gn, bl, A, Lp, ss, ss', cc, ins, a0,
    fun s0 K G ra c slots ext caller opens N sps hwf habi hc => ?_⟩
  exact {
    mem := mem_callerM
    wf := hwf
    scope := scope_M rfl
    abi := habi
    H := driverHypT_mk (Γ := ⟨(linkM.act callerM s0 K G).F, fun _ => none,
        (linkM.act callerM s0 K G).ctx.slotBase, 0⟩) (fctx := (linkM.act callerM s0 K G).ctx)
      (X := callerM.X) hshape hcert hbr hlow (List.isEmpty_iff.mp hind) hv hnt cfgM hout0 rfl
      (fun _ _ h => by cases h) (mrStable_relW _ fM c) (outArgsOk_relW _ fM c)
      (memRelOk_relW _ fM c) (by
        intro e0 hmem g _ _ _ _ _ _ _ _ _ hg
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
        rw [hext e he] at hg; cases hg)
    chk := hbl
    ΓF := rfl
    align := hc
    tls := VCodeThread.Witness.X0_tls
    noCall := fun _ _ _ => rfl
    H3 := H3
    checked := hat
    ok := okM
    slot := rfl
    sym := fun _ _ h => by cases h
    reg := fun off h => by
      have := List.all_eq_true.mp hlocs _ h
      simp at this
    pinit := hm3 _ _
    minit := hm4
    res := hres
    cu := hcu
    ar := har
    low := hlow
    ind := List.isEmpty_iff.mp hind
    ver := hv
    nt := hnt
    out0 := hout0
    uv := (callUsesVirtB_iff _).1 huv
    dv := (callDefsVirtB_iff _).1 hdv
    uniq := fun e he e' he' hn => by
      rw [hexts] at he he'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he he'
      rcases he with rfl | rfl <;> rcases he' with rfl | rfl
      · rfl
      · exact absurd (hnL.symm.trans (hn.trans hnT)) (by decide)
      · exact absurd (hnT.symm.trans (hn.trans hnL)) (by decide)
      · rfl
    envx := hext
    sigs := fun e he callee hp => by
      rw [hexts] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · have : pM.func? "ld" = some fL := by native_decide -- witness: native_decide
        rw [hnL, this] at hp; cases hp
        exact hsigL
      · have : pM.func? "xt" = some fT := by native_decide -- witness: native_decide
        rw [hnT, this] at hp; cases hp
        exact hsigT }

/-- Every activation of `atomic_load` in `linkM` is in the scope with calls. -/
theorem scope_ldM (s0 : ArmState) (K : Nat) (G : BitVec 64 → Prop) :
    MemScopeLSC (linkM.act ldF s0 K G) :=
  scope_ld s0 K G

/-- **`atomic_load` is compiled in `linkM`** (no extern, for every environment). -/
theorem fnOk_LM {env : Clif.Env} : FnOk linkM env pM (fun _ => none) "ld" ldF fL := by
  obtain ⟨hlow, -, hexn, hind, hv, -, hout0, hprep, -, -, -⟩ := checksL
  obtain ⟨hthr, har0, hcu0, hres, hnt, huv, hdv, -⟩ := checks2
  have hnil : fL.externs = [] := List.isEmpty_iff.mp hexn
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hbl, har, hcu⟩ :=
    obligations_of_checksA hlow hthr har0 hcu0
  obtain ⟨Lp, ss, ss', H3, hm3⟩ := CallLayers.prep_init (vc := vcL) (vcp := ldF.vc) hprep
  obtain ⟨cc, ins, a0, hat, hm4⟩ :=
    CallLayers.alloc_init (vc := ldF.vc) (rf := ldF.rf) allocL ckeep
  have hext : ∀ e ∈ fL.externs, env.extern e.2.name = none := by
    intro e he; rw [hnil] at he; cases he
  refine ⟨static_ld, by rw [fs_ld],
    fun q hq => (by rw [CallEntryRel.Witness.slots_fL] at hq; cases hq), vcL, ctx, st0,
    R, gn, bl, A, Lp, ss, ss', cc, ins, a0,
    fun s0 K G ra c slots ext caller opens N sps hwf habi hc => ?_⟩
  exact {
    mem := mem_ldM
    wf := hwf
    scope := scope_ldM s0 K G
    abi := habi
    H := driverHypT_mk (Γ := ⟨(linkM.act ldF s0 K G).F, fun _ => none,
        (linkM.act ldF s0 K G).ctx.slotBase, 0⟩) (fctx := (linkM.act ldF s0 K G).ctx)
      (X := ldF.X) hshape hcert hbr hlow (List.isEmpty_iff.mp hind) hv hnt cfgL hout0 rfl
      (fun _ _ h => by cases h) (mrStable_relW _ fL c) (outArgsOk_relW _ fL c)
      (memRelOk_relW _ fL c) (by
        intro e0 hmem g _ _ _ _ _ _ _ _ _ hg
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
        rw [hext e he] at hg; cases hg)
    chk := hbl
    ΓF := rfl
    align := hc
    tls := VCodeThread.Witness.X0_tls
    noCall := fun _ _ _ => rfl
    H3 := H3
    checked := hat
    ok := okM
    slot := rfl
    sym := fun _ _ h => by cases h
    reg := fun off h => by rw [locsL] at h; simp at h
    pinit := hm3 _ _
    minit := hm4
    res := hres
    cu := hcu
    ar := har
    low := hlow
    ind := List.isEmpty_iff.mp hind
    ver := hv
    nt := hnt
    out0 := hout0
    uv := (callUsesVirtB_iff _).1 huv
    dv := (callDefsVirtB_iff _).1 hdv
    uniq := fun e he => by rw [hnil] at he; cases he
    envx := hext
    sigs := fun e he => by rw [hnil] at he; cases he }

/-! ## The static premises of the link and the external's contract -/

/-- **The oracle's frames**: the caller's, `atomic_load`'s, and an empty frame for the
external's slot-free specification. -/
def frM (n : String) : Option (Nat × (Clif.SlotId → Nat)) :=
  if n = "f" then some (frameDrop callerM.af, slotOffs callerM.af fM)
  else if n = "ld" then some (frameDrop ldF.af, slotOffs ldF.af fL)
  else if n = "xt" then some (0, fun _ => 0)
  else none

/-- **The frame bound**: the caller's frame, 176 bytes and the frame record (bound 256). -/
def MxM : Nat := 256

theorem frM_f : frM "f" = some (frameDrop callerM.af, slotOffs callerM.af fM) := by simp [frM]

theorem frM_ld : frM "ld" = some (frameDrop ldF.af, slotOffs ldF.af fL) := by simp [frM]

theorem frM_xt : frM "xt" = some (0, fun _ => 0) := by simp [frM]

theorem func_pM {n : String} {f : Clif.Function} (hf : pM.func? n = some f) :
    (n = "f" ∧ f = fM) ∨ (n = "ld" ∧ f = fL) ∨ (n = "xt" ∧ f = fT) := by
  obtain ⟨hm, rfl⟩ := Clif.Program.func?_some hf
  simp only [pM, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact .inl ⟨name_fM, rfl⟩
  · exact .inr (.inl ⟨name_fL, rfl⟩)
  · exact .inr (.inr ⟨name_fT, rfl⟩)

/-- **The static premises of `linkM` on `pM`**: `f` and `ld` compiled, `xt` the external with
its specification, `x0` the return register. -/
theorem linkOkM {env : Clif.Env} (henvL : env.extern "ld" = none)
    (henvT : env.extern "xt" = none) :
    LinkOkX linkM env pM (fun _ => none) frM MxM (· = "xt") (fun _ => [.x 0]) where
  fn := by
    intro n f hf hn
    rcases func_pM hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, -⟩
    · exact ⟨callerM, mem_callerM, fnOk_M henvL henvT, frM_f, by rw [fs_M]; decide⟩
    · exact ⟨ldF, mem_ldM, fnOk_LM, frM_ld, by rw [fs_ld]; decide⟩
    · exact absurd rfl hn
  xfn := by
    intro n f hf hn
    rcases func_pM hf with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, rfl⟩
    · exact absurd hn (by decide)
    · exact absurd hn (by decide)
    · exact ⟨⟨idT, mem_xtM⟩, slots_fT⟩
  inside := by
    intro n F h
    rcases mem_linkM h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact inside_ld
    · exact callsInside_of checksPM.2.2.2.2.2.2.2.1
    · exact callsInside_of checksPM.2.2.2.2.2.2.1
  noSelf := by
    intro n f hf e he
    obtain ⟨hm, rfl⟩ := Clif.Program.func?_some hf
    have h := List.all_eq_true.mp checksPM.2.2.2.2.1 f hm
    simpa using List.all_eq_true.mp h e he
  defsRet := by
    intro nA FA nB FB hA hB b vb us hb hk
    have hus : us.map (·.2) = [.x 0] := by
      rcases mem_linkM hB with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact CallSegCall.Witness.rets_ld hb hk
      · exact CallSegCall.Witness.rets_ld hb hk
      · exact rets_x0 checksPM.2.2.2.2.2.2.2.2.1 hb hk
    rw [hus]
    rcases mem_linkM hA with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact defsRet_L
    · exact defsRet_L
    · exact (callDefsRetB_iff _ _).1 checksCM.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  defsRetX := by
    intro nA FA n hA _
    rcases mem_linkM hA with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact defsRet_L
    · exact defsRet_L
    · exact (callDefsRetB_iff _ _).1 checksCM.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **The oracle's frames of `pM`** hold its slots within `MxM` bytes. -/
theorem placeOkM : PlaceOk pM frM MxM := by
  intro g hg
  simp only [pM, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · refine ⟨_, _, by rw [name_fM]; exact frM_f, by rw [drop_M]; decide, fun q hq => ?_⟩
    rw [slots_fM] at hq; cases hq
  · refine ⟨_, _, by rw [name_fL]; exact frM_ld, by rw [drop_ld]; decide, fun q hq => ?_⟩
    rw [CallEntryRel.Witness.slots_fL] at hq; cases hq
  · refine ⟨_, _, by rw [name_fT]; exact frM_xt, by decide, fun q hq => ?_⟩
    rw [slots_fT] at hq; cases hq

theorem b0T : fT.blocks[0]? = some BT := by native_decide -- witness: native_decide

theorem params_BT : BT.params = [(0, .i64)] := by native_decide -- witness: native_decide

theorem body_BT : BT.body = [{ results := [1], inst := .binary .bor .i64 0 0 }] := by
  native_decide -- witness: native_decide

theorem term_BT : BT.term = .ret [1] := by native_decide -- witness: native_decide

theorem sig_fT_fC : fT.sig = fC.sig := by native_decide -- witness: native_decide

theorem func_xtM : pM.func? "xt" = some fT := by native_decide -- witness: native_decide

/-- `fT` returns its argument. -/
theorem specT : RetSpec fT BT :=
  ⟨b0T, params_BT, body_BT, term_BT, slots_fT, by rw [sig_fT_fC]; exact WitnessFull.locsC⟩

/-- **The external's event contract holds** (`ext_ret`: its code is one `ret`). -/
theorem extM {env : Clif.Env} :
    ExtEvContractT linkM env pM (fun _ => none) (· = "xt") (fun _ => [.x 0]) :=
  ext_ret okM mem_xtM (fun F hF => by
    rcases mem_linkM hF with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨h, -⟩
    · exact absurd h (by decide)
    · rfl
    · exact absurd h (by decide)) laidT rfl func_xtM specT

/-! ## The caller's root activation -/

/-- The caller in the link with a callee budget of `0x200` bytes (two frames of `MxM`). -/
abbrev RAM : RL := linkM.act callerM sM0 0x200 GM

theorem stack_RAM : StackAvail 0x200 callerM.af sM0 := by
  have hs := spM
  have hfs : callerM.af.frameSize = 176 := fs_M
  refine ⟨?_, fun a ha => ?_⟩
  · show callerM.af.frameSize + 16 + 0x200 ≤ (E2E.spv RCM.s0).toNat
    rw [spv_RCM, hfs]; decide
  · obtain ⟨j, hj, hd⟩ := codeAddr_words program_RCM ha
    show callerM.af.frameSize + 16 + 0x200 ≤
      (a - (E2E.spv RCM.s0 - BitVec.ofNat 64 (callerM.af.frameSize + 16 + 0x200))).toNat
    rw [spv_RCM, hfs]
    have hj' : j < 0x4000 := by have := hs.2.2.1; omega
    rw [show RCM.base = 0x30000#64 from rfl] at hd
    generalize j = J at hj' hd
    bv_omega

theorem wf_RAM : RAM.Wf where
  check := wfRCM.check
  alloc := wfRCM.alloc
  emit := wfRCM.emit
  layout := wfRCM.layout
  lm := wfRCM.lm
  fit := wfRCM.fit
  stack := stack_RAM
  psF := wfRCM.psF
  prog0 := wfRCM.prog0
  gfree := fun a hG ⟨h1, _⟩ => by
    have := gM_ge hG
    have e : (E2E.spv RAM.s0).toNat = 0x7000 := by
      rw [show E2E.spv RAM.s0 = 0x7000#64 from spv_RCM]; rfl
    omega

/-- **The linked code is kept by the caller**: its own code, `atomic_load`'s and the external's
words in its kept addresses `GM`, in memory at its entry. -/
theorem codeIn_RAM : CallSegCall.CodeIn linkM RAM := by
  intro n FB hB
  rcases mem_linkM hB with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · refine .inr fun k wd hk => ?_
    have hk' : (actW vcpL rfL).fb.words[k]? = some wd := hk
    obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hk'
    have hG : ∀ i < 4, GL (0x20000#64 + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 i) :=
      fun i hi => by
        unfold GL
        have : (actW vcpL rfL).fb.words.size = 29 := spM.2.2.2.2.2.1
        rw [this] at hlt ⊢
        bv_omega
    refine ⟨fun i hi => .inl (hG i hi), ?_⟩
    have hR : Arm.read_mem_bytes 4 (0x20000#64 + BitVec.ofNat 64 (4 * k)) RAL.s0 = wd :=
      abiRL.code k wd hk'
    show Arm.read_mem_bytes 4 (0x20000#64 + BitVec.ofNat 64 (4 * k)) sM0 = wd
    rw [← hR]
    refine read_mem_bytes_congr 4 _ fun i hi => ?_
    show memM _ = _
    simp only [memM, hG i hi, ↓reduceIte]
  · refine .inr fun k wd hk => ?_
    have hk' : retFb.words[k]? = some wd := hk
    rw [checksX.2.2.1] at hk'
    obtain ⟨rfl, rfl⟩ : k = 0 ∧ 0xd65f03c0#32 = wd := by
      cases k with
      | zero => simpa using hk'
      | succ k => simp at hk'
    refine ⟨fun i hi => .inr ?_, retM⟩
    show ((0x28000#64 + BitVec.ofNat 64 (4 * 0) + BitVec.ofNat 64 i) - 0x28000#64).toNat < 4
    bv_omega
  · exact .inl ⟨rfl, rfl⟩

/-- The addresses outside the activation's world are at or above `0x6D00`. -/
theorem fM_ge {a : BitVec 64} (h : RAM.F a) : 0x6D00 ≤ a.toNat := by
  have hs := spM
  have e : E2E.spv sM0 - BitVec.ofNat 64 (frameDrop callerM.af) = 0x6F40#64 := by
    rw [show E2E.spv sM0 = 0x7000#64 from spv_RCM, drop_M]
    rfl
  have hsz : RCM.fr.size ≤ 240 := hs.2.2.2.1
  have hfs : callerM.af.frameSize = 176 := fs_M
  change frameWG 0x200 RCM.fr.intBase RCM.fr.size callerM.af GM sM0 a at h
  unfold frameWG frameW frameF StackBelow at h
  rw [e, hfs, drop_M] at h
  rcases h with ((⟨h1, h2⟩ | ⟨h1, h2⟩ | hc) | ⟨h1, h2⟩) | hG
  · generalize RCM.fr.size = n at hsz h2
    bv_omega
  · bv_omega
  · obtain ⟨j, hj, hd⟩ := codeAddr_words program_RCM hc
    rw [show RCM.base = 0x30000#64 from rfl] at hd
    have : j < 0x4000 := by have := hs.2.2.1; omega
    generalize j = J at this hd
    bv_omega
  · simp only [BitVec.toNat_ofNat] at h1 h2; omega
  · have := gM_ge hG; omega

/-! ## The CLIF entry state with the oracle -/

/-- The caller's entry block. -/
def B0M : Clif.Block := fM.blocks.headD default

/-- The caller's entry registers: `v0 = 0`. -/
def regsM : Clif.Regs :=
  (Clif.Regs.empty.setMany (B0M.params.map (·.1)) argsL).getD Clif.Regs.empty

/-- The caller's CLIF memory with the slot-placement oracle at its body `sp`. -/
def memOM : Clif.Mem := { memL with place := some ⟨[RAM.spB], frM, none⟩ }

/-- **The caller's CLIF entry state**: block 0, `v0 = 0`, no slots, `memL` with the oracle. -/
def csOM : Clif.State :=
  { frame := { func := fM, regs := regsM, slots := [], body := B0M.body, term := B0M.term }
    callers := []
    mem := memOM }

/-- The thread's start: `csOM` with no masked byte. -/
noncomputable def csTM : TState := encT (fun _ => False) (.run csOM)

theorem checksOM : fM.blocks.isEmpty = false ∧
    (Clif.Regs.empty.setMany (B0M.params.map (·.1)) argsL).isSome = true ∧
    argsL.map (·.ty) = B0M.params.map (·.2) ∧ argsL.map (·.ty) = fM.sig.params.map (·.ty) ∧
    (match locsOf fM.sig with | [.reg (.x 0)] => true | _ => false) = true ∧
    B0M.body = [{ results := [1], inst := .call 0 [0] }, { results := [2], inst := .call 1 [1] }] ∧
    B0M.term = .ret [2] ∧ fM.extern? 0 = some extL ∧ fM.extern? 1 = some extT ∧
    pM.func? extL.name = some fL ∧ pM.func? extT.name = some fT ∧
    (E2E.spv w₀M).toNat % 16 = 0 := by
  native_decide -- witness: native_decide

theorem b0M : fM.blocks[0]? = some B0M := by
  have h := checksOM.1
  unfold B0M
  revert h
  cases fM.blocks with
  | nil => intro h; cases h
  | cons b bs => intro _; rfl

theorem regsM_eq : Clif.Regs.empty.setMany (B0M.params.map (·.1)) argsL = some regsM := by
  have h := checksOM.2.1
  unfold regsM
  revert h
  cases Clif.Regs.empty.setMany (B0M.params.map (·.1)) argsL with
  | none => intro h; cases h
  | some r => intro _; rfl

theorem locsM : locsOf fM.sig = [.reg (.x 0)] := by
  have h := checksOM.2.2.2.2.1
  revert h
  generalize locsOf fM.sig = l
  intro h
  match l, h with
  | [.reg (.x 0)], _ => rfl

theorem errW₀M : Arm.r .ERR w₀M = .None := by
  rw [E2E.r_bodyOf _ _ (by simp) (by simp)]
  exact abiRCM.err

theorem relW_M : RelW ⟨RAM.F, fun _ => none, RAM.ctx.slotBase, 0⟩ fM (E2E.spv w₀M) [] memOM
    w₀M := by
  refine ⟨⟨⟨fun a b _ hb => by simp [memOM, memL] at hb, fun a n hv => ?_, rfl⟩,
      fun id b h => by simp at h, E2E.outRel_zero _ _ _⟩, rfl, errW₀M⟩
  simp only [Clif.Mem.valid, memOM, memL, List.any_cons, List.any_nil, Bool.or_false,
    Clif.Alloc.contains] at hv
  have hv' : a + n ≤ 8 := by
    revert hv; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  refine ⟨by omega, fun k hk hF => ?_⟩
  have := fM_ge hF
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem argsAt_M : ArgsAtEntry RAM.F fM.sig argsL w₀M := by
  intro loc v h
  rw [locsM] at h
  simp only [argsL, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  show VHolds _ _
  rw [VHolds, E2E.regVal_bodyOf _ _ (by decide), x0M]
  rfl

theorem body_RAM : BodyEntryW RAM.F RAM.vc.EntryArg RAM.af RAM.s0 w₀M :=
  (E2E.Binary.bodyEntry_bodyOf RAM.af RAM.s0).w RAM.F entryArgRCM

theorem linv_M : Clif.LInv pM csOM :=
  ⟨⟨List.mem_cons_self .., .inl ⟨B0M, List.mem_of_getElem? b0M, List.suffix_refl _, rfl⟩⟩,
    fun _ h => nomatch h⟩

theorem func_fM : pM.func? "f" = some fM := by
  simp [Clif.Program.func?, pM, name_fM]

/-! ## The reachable CLIF states of a caller of two calls, generically

A caller state `c0` whose block is two `call`s of program functions, each entered at a block of
one statement other than a call, all three blocks returning (`CallShape2`): the states reachable
from `c0` (up to their bytes) are the caller at its first call, the first callee at its entry
and returning, the caller at its second call, the second callee at its entry and returning, and
the caller returning (`Fam2`, `reach_inv2`), with at most one caller (`depth2`) and, if the first
callee's statement accesses 8 bytes of `memL` and the second's none, every access on `LocO`
(`partsOk2`). -/

/-- **A caller state at two calls of one-statement callees** in `p` (section doc): `st2` is the
second call; the first callee has no stack slots. -/
structure CallShape2 (p : Clif.Program) (c0 : Clif.State) (st2 : Clif.Stmt) (B1 B2 : Clif.Block) :
    Prop where
  init : c0.callers = [] ∧ AllocsIn c0.mem
  call1 : ∃ (rs : List Clif.ValueId) (fn : Clif.FnRef) (args : List Clif.ValueId)
      (ex : Clif.ExtFunc) (f1 : Clif.Function),
    c0.frame.body = [{ results := rs, inst := .call fn args }, st2] ∧
    c0.frame.func.extern? fn = some ex ∧ p.func? ex.name = some f1 ∧ f1.blocks[0]? = some B1 ∧
    f1.slots = []
  call2 : ∃ (rs : List Clif.ValueId) (fn : Clif.FnRef) (args : List Clif.ValueId)
      (ex : Clif.ExtFunc) (f2 : Clif.Function),
    st2 = { results := rs, inst := .call fn args } ∧
    c0.frame.func.extern? fn = some ex ∧ p.func? ex.name = some f2 ∧ f2.blocks[0]? = some B2
  body1 : ∃ st : Clif.Stmt, B1.body = [st] ∧ (∀ fn args, st.inst ≠ .call fn args) ∧
    ∀ sig callee args, st.inst ≠ .callIndirect sig callee args
  body2 : ∃ st : Clif.Stmt, B2.body = [st] ∧ (∀ fn args, st.inst ≠ .call fn args) ∧
    ∀ sig callee args, st.inst ≠ .callIndirect sig callee args
  ret1 : ∃ xs, B1.term = .ret xs
  ret2 : ∃ xs, B2.term = .ret xs
  retC : ∃ ys, c0.frame.term = .ret ys

/-- A frame of the caller `cF` with the body `b`. -/
def Sus (cF : Clif.Frame) (b : List Clif.Stmt) (c : Clif.Frame) : Prop :=
  c.body = b ∧ c.func = cF.func ∧ c.term = cF.term

/-- **The CLIF states reachable from a `CallShape2`'s caller** (at `cF`), up to their bytes. -/
def Fam2 (cF : Clif.Frame) (st2 : Clif.Stmt) (B1 B2 : Clif.Block) (s : Clif.State) : Prop :=
  (s.frame = cF ∧ s.callers = [] ∧ AllocsIn s.mem) ∨
  (s.frame.body = B1.body ∧ s.frame.term = B1.term ∧
    (∃ c rs, s.callers = [(c, rs)] ∧ Sus cF [st2] c) ∧ AllocsIn s.mem) ∨
  (s.frame.body = [] ∧ s.frame.term = B1.term ∧ ∃ c rs, s.callers = [(c, rs)] ∧ Sus cF [st2] c) ∨
  (Sus cF [st2] s.frame ∧ s.callers = []) ∨
  (s.frame.body = B2.body ∧ s.frame.term = B2.term ∧ ∃ c rs, s.callers = [(c, rs)] ∧ Sus cF [] c) ∨
  (s.frame.body = [] ∧ s.frame.term = B2.term ∧ ∃ c rs, s.callers = [(c, rs)] ∧ Sus cF [] c) ∨
  (Sus cF [] s.frame ∧ s.callers = [])

theorem fam2_congr {cF : Clif.Frame} {st2 : Clif.Stmt} {B1 B2 : Clif.Block}
    {s s' : Clif.State} (h : withBytes s (fun _ => none) = withBytes s' (fun _ => none))
    (hs : Fam2 cF st2 B1 B2 s) : Fam2 cF st2 B1 B2 s' := by
  have e1 : s.frame = s'.frame := congrArg (·.frame) h
  have e2 : s.callers = s'.callers := congrArg (·.callers) h
  have e3 : s.mem.allocs = s'.mem.allocs := congrArg (·.mem.allocs) h
  unfold Fam2 AllocsIn at hs ⊢
  rw [← e1, ← e2, ← e3]
  exact hs

section
variable {p : Clif.Program} {c0 : Clif.State} {st2 : Clif.Stmt} {B1 B2 : Clif.Block}

/-- A one-statement block's step: the statement done, the term and the callers kept. -/
theorem next_one {env : Clif.Env} {s : Clif.State} {B : Bytes} {s' : Clif.State}
    {st : Clif.Stmt} (hb : s.frame.body = [st]) (hnc : ∀ fn args, st.inst ≠ .call fn args)
    (hni : ∀ sig callee args, st.inst ≠ .callIndirect sig callee args)
    (hst : Clif.step env p (withBytes s B) = .next s') :
    s'.frame.body = [] ∧ s'.frame.term = s.frame.term ∧ s'.callers = s.callers := by
  have hbody : (withBytes s B).frame.body = [st] := hb
  rw [Clif.step_inst env p _ _ [] hbody hnc hni] at hst
  unfold Clif.StepResult.ofRes at hst
  split at hst
  · rename_i a _
    obtain ⟨vs, m⟩ := a
    simp only [Clif.continueWith] at hst
    split at hst
    · cases hst
      exact ⟨rfl, rfl, rfl⟩
    · cases hst
  · cases hst
  · cases hst

/-- A direct call's step: the callee at its entry block below the caller with the call's rest. -/
theorem next_call {env : Clif.Env} {s : Clif.State} {B : Bytes} {s' : Clif.State}
    {rs : List Clif.ValueId} {fn : Clif.FnRef} {args : List Clif.ValueId}
    {rest : List Clif.Stmt} {ex : Clif.ExtFunc} {f : Clif.Function} {Bf : Clif.Block}
    (hb : s.frame.body = { results := rs, inst := .call fn args } :: rest)
    (he : s.frame.func.extern? fn = some ex) (hfn : p.func? ex.name = some f)
    (hB : f.blocks[0]? = some Bf) (hc : s.callers = [])
    (hst : Clif.step env p (withBytes s B) = .next s') :
    s'.frame.body = Bf.body ∧ s'.frame.term = Bf.term ∧
      s'.callers = [({ s.frame with body := rest }, rs)] ∧
      (f.slots = [] → s'.mem.allocs = s.mem.allocs) := by
  obtain ⟨vals, B0, cs, -, hB0, rfl, hcc, -, -, hmem, hbody, hterm, -⟩ :=
    CallEnterClif.step_call_entry (s := withBytes s B) hb he hfn hst
  rw [hB] at hB0
  cases hB0
  refine ⟨hbody, hterm, ?_, fun hsl => ?_⟩
  · show cs.callers ++ _ = _
    rw [hcc, show (withBytes s B).callers = [] from hc]
    rfl
  · show cs.mem.allocs = _
    rw [hmem]
    exact (WitnessFull.enterSlots_nil hsl _).2

/-- A `return` below one caller resumes it. -/
theorem next_ret {env : Clif.Env} {s : Clif.State} {B : Bytes} {s' : Clif.State}
    {xs : List Clif.ValueId} {c : Clif.Frame} {rs : List Clif.ValueId}
    (hb : s.frame.body = []) (ht : s.frame.term = .ret xs) (hc : s.callers = [(c, rs)])
    (hst : Clif.step env p (withBytes s B) = .next s') :
    s'.frame.body = c.body ∧ s'.frame.func = c.func ∧ s'.frame.term = c.term ∧ s'.callers = [] := by
  have hb' : (withBytes s B).frame.body = [] := hb
  rw [Clif.step_term env p _ hb'] at hst
  have ht' : (withBytes s B).frame.term = .ret xs := ht
  rw [ht'] at hst
  obtain ⟨regs, e1, e2⟩ := stepTerm_ret_next (s := withBytes s B) (c := c) (rs := rs) (cs := [])
    hc hst
  rw [e1]
  exact ⟨rfl, rfl, rfl, e2⟩

/-- **A step from a reachable state to a running state stays reachable.** -/
theorem next_fam2 (H : CallShape2 p c0 st2 B1 B2) (env : Clif.Env) {s : Clif.State}
    (hs : Fam2 c0.frame st2 B1 B2 s) (B : Bytes) {s' : Clif.State}
    (hst : Clif.step env p (withBytes s B) = .next s') : Fam2 c0.frame st2 B1 B2 s' := by
  obtain ⟨rs1, fn1, args1, ex1, f1, hb, he1, hf1, hB1, hsl1⟩ := H.call1
  obtain ⟨rs2, fn2, args2, ex2, f2, hst2, he2, hf2, hB2⟩ := H.call2
  obtain ⟨st1', hb1, hnc1, hni1⟩ := H.body1
  obtain ⟨st2', hb2, hnc2, hni2⟩ := H.body2
  obtain ⟨xs1, hx1⟩ := H.ret1
  obtain ⟨xs2, hx2⟩ := H.ret2
  obtain ⟨ys, hys⟩ := H.retC
  rcases hs with ⟨hf, hc, ha⟩ | ⟨hfb, hft, ⟨c, rs, hc, hsus⟩, -⟩ | ⟨hfb, hft, c, rs, hc, hsus⟩ |
    ⟨⟨hfb, hfu, hft⟩, hc⟩ | ⟨hfb, hft, c, rs, hc, hsus⟩ | ⟨hfb, hft, c, rs, hc, hsus⟩ |
    ⟨⟨hfb, -, hft⟩, hc⟩
  · -- the first call enters the first callee
    obtain ⟨e1, e2, e3, e4⟩ := next_call (s := s) (by rw [hf]; exact hb) (by rw [hf]; exact he1)
      hf1 hB1 hc hst
    refine .inr (.inl ⟨e1, e2, ⟨_, rs1, e3, rfl, by rw [hf], by rw [hf]⟩, fun x hx => ?_⟩)
    exact ha x (by rw [← e4 hsl1]; exact hx)
  · -- the first callee's statement
    obtain ⟨e1, e2, e3⟩ := next_one (hfb.trans hb1) hnc1 hni1 hst
    exact .inr (.inr (.inl ⟨e1, e2.trans hft, c, rs, e3.trans hc, hsus⟩))
  · -- the first callee returns into the caller
    obtain ⟨e1, e2, e3, e4⟩ := next_ret hfb (hft.trans hx1) hc hst
    exact .inr (.inr (.inr (.inl ⟨⟨e1.trans hsus.1, e2.trans hsus.2.1, e3.trans hsus.2.2⟩, e4⟩)))
  · -- the second call enters the second callee
    obtain ⟨e1, e2, e3, -⟩ := next_call (s := s) (rest := []) (by rw [hfb, hst2])
      (by rw [hfu]; exact he2) hf2 hB2 hc hst
    exact .inr (.inr (.inr (.inr (.inl ⟨e1, e2, _, rs2, e3, rfl, hfu, hft⟩))))
  · -- the second callee's statement
    obtain ⟨e1, e2, e3⟩ := next_one (hfb.trans hb2) hnc2 hni2 hst
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨e1, e2.trans hft, c, rs, e3.trans hc, hsus⟩)))))
  · -- the second callee returns into the caller
    obtain ⟨e1, e2, e3, e4⟩ := next_ret hfb (hft.trans hx2) hc hst
    exact .inr (.inr (.inr (.inr (.inr (.inr
      ⟨⟨e1.trans hsus.1, e2.trans hsus.2.1, e3.trans hsus.2.2⟩, e4⟩)))))
  · -- the caller returns: no next state
    have hb' : (withBytes s B).frame.body = [] := hfb
    rw [Clif.step_term env p _ hb'] at hst
    have ht : (withBytes s B).frame.term = .ret ys := hft.trans hys
    rw [ht] at hst
    exact absurd hst ((stepTerm_ret (env := env) (p := p) (s := withBytes s B) (xs := ys) hc).1 s')

/-- **A step from a reachable state stays reachable.** -/
theorem step_fam2 (H : CallShape2 p c0 st2 B1 B2) (env : Clif.Env) {s : Clif.State}
    (hs : Fam2 c0.frame st2 B1 B2 s) (B : Bytes) {t'' : TState} {B' : Bytes}
    (h : res (Clif.step env p (withBytes s B)) = some (t'', B')) :
    RInvG (Fam2 c0.frame st2 B1 B2) t'' := by
  rcases res_some h with ⟨s', hst, rfl⟩ | ⟨v, rfl⟩
  · exact next_fam2 H env hs B hst
  · trivial

/-- **The thread states reachable from a `CallShape2`'s caller.** -/
theorem reach_inv2 (H : CallShape2 p c0 st2 B1 B2) {env : Clif.Env} {t : TState}
    (h : RReach env p (.run c0) t) : RInvG (Fam2 c0.frame st2 B1 B2) t := by
  induction h with
  | base => exact Or.inl ⟨rfl, H.init⟩
  | @step t evs t' _ hs ih =>
    cases t with
    | ret v => exact False.elim hs
    | run s =>
      obtain ⟨-, ⟨B, hB⟩, hf⟩ := hs
      obtain ⟨t'', h1, h2⟩ := hf B hB
      exact rinvG_strip (fun _ _ => fam2_congr) h2 (step_fam2 H env ih B h1)
  | @stepS t evs t' _ hs ih =>
    cases t with
    | ret v => exact False.elim hs
    | run s =>
      obtain ⟨-, ⟨B, hB⟩, -, hf⟩ := hs
      obtain ⟨t'', h1, h2⟩ := hf B hB
      exact rinvG_strip (fun _ _ => fam2_congr) h2 (step_fam2 H env ih _ h1)
  | strip _ he ih => exact rinvG_strip (fun _ _ => fam2_congr) he ih

/-- **At most one caller** below every state reachable from a `CallShape2`'s caller. -/
theorem depth2 (H : CallShape2 p c0 st2 B1 B2) {env : Clif.Env} :
    ∀ S, RReach env p (.run c0) (.run S) → S.callers.length < 2 := by
  intro S h
  have hI : Fam2 c0.frame st2 B1 B2 S := reach_inv2 H h
  rcases hI with ⟨-, hc, -⟩ | ⟨-, -, ⟨_, _, hc, -⟩, -⟩ | ⟨-, -, _, _, hc, -⟩ | ⟨-, hc⟩ |
    ⟨-, -, _, _, hc, -⟩ | ⟨-, -, _, _, hc, -⟩ | ⟨-, hc⟩ <;> simp [hc]

/-- **The accesses from the states reachable from a `CallShape2`'s caller lie on `LocO`**, if
the first callee's statement accesses 8 bytes and the second's none. -/
theorem partsOk2 (H : CallShape2 p c0 st2 B1 B2) {env : Clif.Env} {l : List (SKind × Nat)}
    (hsh1 : ∀ s : Clif.State, s.frame.body = B1.body → evShape s = [l])
    (hsh2 : ∀ s : Clif.State, s.frame.body = B2.body → evShape s = [[]])
    (hl : ∀ x ∈ l, x.2 = 8 ∧ x.1.dir ≠ .F) : PartsOk env p (.run c0) LocO := by
  intro t evs t' hR hs e he
  cases t with
  | ret v => exact False.elim hs
  | run s =>
  have hI : Fam2 c0.frame st2 B1 B2 s := reach_inv2 H hR
  have hv0 := CallSegGeo.cstep_reads_valid hs
  obtain ⟨⟨hsh', hd⟩, -, -⟩ := hs
  have hnil : evShape s = [[]] → False := fun h => by
    rw [h, List.mem_singleton, List.map_eq_nil_iff] at hsh'
    subst hsh'; cases he
  obtain ⟨_, _, _, _, _, hb, -⟩ := H.call1
  obtain ⟨_, _, _, _, _, hst2, -⟩ := H.call2
  rcases hI with ⟨hf, -, -⟩ | ⟨hfb, -, -, ha⟩ | ⟨hfb, -⟩ | ⟨⟨hfb, -⟩, -⟩ | ⟨hfb, -⟩ | ⟨hfb, -⟩ |
    ⟨⟨hfb, -⟩, -⟩
  · exact (hnil (by unfold evShape; rw [hf, hb])).elim
  · rw [hsh1 s hfb, List.mem_singleton] at hsh'
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
  · exact (hnil (evShape_nil hfb)).elim
  · exact (hnil (by unfold evShape; rw [hfb, hst2])).elim
  · exact (hnil (hsh2 s hfb)).elim
  · exact (hnil (evShape_nil hfb)).elim
  · exact (hnil (evShape_nil hfb)).elim

end

/-! ## The reachable CLIF states of `csOM` -/

/-- `csOM` calls `atomic_load`, then the external's specification. -/
theorem shape_M : CallShape2 pM csOM { results := [2], inst := .call 1 [1] } B0L BT := by
  obtain ⟨-, -, -, -, -, hb, ht, he0, he1, hf0, hf1, -⟩ := checksOM
  obtain ⟨-, -, -, hent, -, -, hsl⟩ := clifC
  have hB0L : fL.blocks[0]? = some B0L := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  exact ⟨⟨rfl, fun _ hx => hx⟩, ⟨[1], 0, [0], extL, fL, hb, he0, hf0, hB0L, hsl⟩,
    ⟨[2], 1, [1], extT, fT, rfl, he1, hf1, b0T⟩,
    ⟨_, checksO.2.2.2.2.2.1, (fun _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩,
    ⟨_, body_BT, (fun _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩,
    ⟨_, checksO.2.2.2.2.2.2.1⟩, ⟨_, term_BT⟩, ⟨_, ht⟩⟩

/-- **The accesses from the states reachable from `csOM` lie on `LocO`** (`atomic_load`'s 8
bytes at `0`; the external's specification has none). -/
theorem partsOk_M {env : Clif.Env} : PartsOk env pM (.run csOM) LocO :=
  partsOk2 shape_M (l := [(.scR, 8)])
    (fun s hs => (evShape_congr (s' := csL) (by rw [hs]; rfl)).trans shapeL1)
    (fun s hs => by unfold evShape; rw [hs, body_BT])
    (by decide)

/-- **At most one caller** below every state reachable from `csOM`. -/
theorem depth_M {env : Clif.Env} :
    ∀ S, RReach env pM (.run csOM) (.run S) → S.callers.length < 2 :=
  depth2 shape_M

/-! ## The activation's entry and the program-level statement -/

/-- **The caller's root activation in `linkM` entered at its ABI entry.** -/
theorem ent_M : ∃ g : Act, Ent linkM Clif.Env.empty pM (PrivA RAM) (.run csOM) LocO frM MxM 2
    (fun _ => none) g (sM0, none) (csTM, PrivA RAM) := by
  obtain ⟨-, -, -, vc, ctx, st0, R, gn, bl, A, Lp, ss, ss', cc, ins, a0, hF⟩ :=
    fnOk_M (env := Clif.Env.empty) rfl rfl
  have hS := hF sM0 0x200 GM 0x4000#64 (E2E.spv w₀M) [] [] callerM [] (fun _ => False) []
    wf_RAM abiRCM checksOM.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, hq, hA⟩ := q_init_lines wf_RAM abiRCM body_RAM
  refine ⟨⟨"f", callerM, sM0, 0x200, GM, 0x4000#64, fM, vc, ctx, st0, R, gn, bl, A,
    ⟨RAM.F, fun _ => none, RAM.ctx.slotBase, 0⟩, E2E.spv w₀M, Lp, ss, ss', cc, ins, a0, [], [],
    callerM, [], fun _ => False, []⟩, rfl, csOM, fun _ => False, rfl, ?_, ?_, func_fM⟩
  · exact {
      stat := hS
      syms := rfl
      code := codeIn_RAM
      bnd := fun _ h => h
      dirty := fun _ h => .inl h
      reach := RReach.base
      call := rfl
      ret := fun h => absurd rfl h
      linv := linv_M
      place := rfl
      nv := fun _ _ _ _ h => h
      ndead := fun _ h => h.elim
      opens := fun _ h => absurd h List.not_mem_nil
      budget := show (2 - 0) * 256 ≤ 512 by decide
      func := rfl }
  · exact chainP_entry hS b0M rfl rfl rfl rfl rfl regsM_eq checksOM.2.2.1 checksOM.2.2.2.1 relW_M
      argsAt_M hq hA

open ProgE2E PrivCohT Rel in
/-- **A compiled caller of a compiled callee and of an external, through both calls and back,
from the generic theorem** (`realizes_linked_calls_ext` on `linkM`/`pM` with one thread, the
caller's root activation, the external under its contract `extM`, every premise discharged but
the run): every execution of the realized prefix of a precise run of the linked machine from the
caller's ABI entry is realized by a `CStepS` thread of `pM` from `csOM`. -/
theorem realizes_calls_mixT {ls : List Lab} {t' : CallCompose.AT}
    (hr : PRun Policy.arm linkM.M (OkB (PrivA RAM)) (sM0, none) ls t') :
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
        (∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j < 1, PrivA RAM (locsA[q]).1) →
        (∀ q (h : q < locsC.length),
          bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2) →
        StackDisjoint PA (fun _ l => PrivA RAM l ∨ PrivA RAM l) →
        ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧
          (∀ i < 1, PC.st i 0 = csTM) ∧ PC.Runs (CStepS Clif.Env.empty pM) ∧
          Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ (fun _ _ _ => True) := by
  obtain ⟨g, hg⟩ := ent_M
  exact realizes_linked_calls_ext (env := Clif.Env.empty) (n := 1) (Bnd := fun _ => PrivA RAM)
    (c0 := fun _ => .run csOM) (Loc := fun _ => LocO) (Dcap := fun _ => 2) (g := fun _ => g)
    (sA := fun _ => (sM0, none)) (cs := fun _ => csTM) (D0 := fun _ => PrivA RAM)
    (fun _ _ => partsOk_M) (fun _ _ => partDisj_O) linkFreeM keepsAllocs_E keepsPlace_E placeOkM
    (fun _ _ => depth_M) (linkOkM rfl rfl) extM (fun _ _ => hg) (ls := fun _ => ls)
    (t' := fun _ => t') (fun _ _ => hr)

end Concurrency.CallSegOkGT.WitnessMix
