import FV.Concurrency.CallSegOkGTExtFull

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
    (blocksLinesE (actW vcpM rfM).ctx (actW vcpM rfM).af (actW vcpM rfM).af.blocks.toList
      {}).toBool = true := by
  native_decide -- witness: native_decide

theorem allocM : checkAlloc vcpM rfM = .ok () := by
  have h := factsM.1
  revert h
  cases checkAlloc vcpM rfM with
  | ok u => intro _; rfl
  | error e => intro h; cases h

theorem spM : E2E.spv RCM.s0 = 0x7000#64 ∧ frameDrop RCM.af = 256 ∧
    RCM.fb.words.size ≤ 0x4000 ∧ RCM.fr.size ≤ 240 ∧ RCM.af.frameSize = 240 ∧
    (actW vcpL rfL).fb.words.size = 47 ∧ 0 < RCM.fb.words.size := by
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
    have : (actW vcpM rfM).af.frameSize = 240 := hs.2.2.2.2.1
    simp only [BitVec.toNat_ofNat]; omega
  · obtain ⟨j, hj, hd⟩ := codeAddr_words program_RCM ha
    rw [spv_RCM]
    have : (actW vcpM rfM).af.frameSize = 240 := hs.2.2.2.2.1
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
    frameDrop callerM.af = 256 ∧ callerM.af.frameSize = 240 := by
  native_decide -- witness: native_decide

theorem name_fM : fM.name = "f" := checksPM.1

theorem name_fT : fT.name = "xt" := checksPM.2.1

theorem slots_fM : fM.slots = [] := checksPM.2.2.1

theorem slots_fT : fT.slots = [] := checksPM.2.2.2.1

theorem drop_M : frameDrop callerM.af = 256 := checksPM.2.2.2.2.2.2.2.2.2.1

theorem fs_M : callerM.af.frameSize = 240 := checksPM.2.2.2.2.2.2.2.2.2.2

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
  refine ⟨static_ld, by rw [fs_ld], fun q hq => (by rw [CallEntryRel.Witness.slots_fL] at hq; cases hq), vcL, ctx, st0,
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

/-- **The frame bound**: the caller's frame, 240 bytes and the frame record. -/
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

end Concurrency.CallSegOkGT.WitnessMix
