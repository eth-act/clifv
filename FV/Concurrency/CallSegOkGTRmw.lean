import FV.Concurrency.CallSegOkGTFull
import FV.Concurrency.CallRmwWitness

/-!
# The caller of `atomic_rmw` through the generic call theorem (#473)

`CallSeg.WitnessCR.realizes_call` derived again, from `CallSegOkGT.realizes_linked_calls`: the
compiled caller of `CallRmwData` (`fC`, `v2 = call fn0(v0, v1)`) and the compiled `atomic_rmw`
(`RealizeCompiled.WitnessR.fR`, its LL/SC loop) linked as `linkR` (`rmw` at `0x20000`, `f` at
`0x30000`), the program `pCR`:

* `okR`, **`fnOk_CR`**, **`fnOk_R`**, `frR`/`MxR`, **`linkOk_R`**, `placeOk_R`, `linkFree_CR`: the
  static premises of the link (as `CallSegOkGT.Witness` for `link2`);
* `RAc`: the caller's root activation with a callee budget of `0x240` bytes (two frames of `MxR`);
  `csO`: its CLIF entry state with the slot-placement oracle at its body `sp`;
* `Fam`, **`reach_inv`**: the CLIF states reachable from `csO` (up to their bytes), an instance
  (`shape_O`) of `WitnessFull.CallShape`;
  **`partsOk_O`** (the `atomic_rmw`'s read and write: the 8 bytes at `0`, `LocO`), `depth_O`;
* **`ent_O`**: the activation's `Ent`;
* **`realizes_call_rmwT`**: `realizes_linked_calls` with one thread, every premise discharged
  but the run.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallSegOkGT.WitnessRmw

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver ArmAllocThread E2E
  LinkedMachine LinkedMachine.Link CallComposeT CallSegOkG CallSegLive CallSegRun CallSegPc
  CallResumeChecks CallEntryRel IselCheck IselResume CallArity CallArgsEntry CallArgsL2 CallArgsAt
  PrepThread VCodeThread CallSeg.WitnessCR RealizeCompiled.WitnessR RealizeCompiled.WitnessL
  ClifLift
open ArmAllocThread.Witness renaming act → actW

/-! ## The link -/

/-- The compiled `atomic_rmw` at `0x20000`. -/
def rmwF : LFn := { LFn.of (actW vcpR rfR) with base := 0x20000#64 }

/-- The compiled caller at `0x30000`. -/
def callerRF : LFn := { LFn.of (actW vcpC rfC) with base := 0x30000#64 }

/-- **The link of the two functions.** -/
def linkR : Link := ⟨[("rmw", rmwF), ("f", callerRF)]⟩

theorem factsLR : (actW vcpR rfR).fa.layout.toBool = true ∧
    (labelOffsets (actW vcpR rfR).fa.lines).toBool = true ∧
    (actW vcpC rfC).fa.layout.toBool = true ∧
    (labelOffsets (actW vcpC rfC).fa.lines).toBool = true ∧
    0 < (actW vcpR rfR).fb.words.size ∧ 0 < (actW vcpC rfC).fb.words.size ∧
    0x20000 + 4 * (actW vcpR rfR).fb.words.size ≤ 0x30000 ∧
    0x30000 + 4 * (actW vcpC rfC).fb.words.size ≤ 2 ^ 64 := by
  native_decide -- witness: native_decide

theorem laidR : rmwF.LaidOut where
  layout := ArmAllocThread.Witness.ok_getD factsLR.1
  lm := ArmAllocThread.Witness.ok_getD factsLR.2.1
  pos := factsLR.2.2.2.2.1
  fit := by
    show (0x20000#64 : BitVec 64).toNat + 4 * (actW vcpR rfR).fb.words.size ≤ 2 ^ 64
    have := factsLR.2.2.2.2.2.2.1
    simp only [BitVec.toNat_ofNat]
    omega

theorem laidC : callerRF.LaidOut where
  layout := ArmAllocThread.Witness.ok_getD factsLR.2.2.1
  lm := ArmAllocThread.Witness.ok_getD factsLR.2.2.2.1
  pos := factsLR.2.2.2.2.2.1
  fit := by
    show (0x30000#64 : BitVec 64).toNat + 4 * (actW vcpC rfC).fb.words.size ≤ 2 ^ 64
    have := factsLR.2.2.2.2.2.2.2
    simp only [BitVec.toNat_ofNat]
    omega

theorem mem_rmw : ("rmw", rmwF) ∈ linkR.fns := .head _

theorem mem_callerR : ("f", callerRF) ∈ linkR.fns := .tail _ (.head _)

/-- **The link is well formed.** -/
theorem okR : linkR.Ok where
  sep := by
    refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    refine ⟨by decide, .inl ?_⟩
    show (0x20000#64 : BitVec 64).toNat + 4 * (actW vcpR rfR).fb.words.size ≤
      (0x30000#64 : BitVec 64).toNat
    have := factsLR.2.2.2.2.2.2.1
    simp only [BitVec.toNat_ofNat]
    omega
  laid := by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact laidR
    · rw [List.mem_singleton] at hp
      subst hp
      exact laidC

theorem mem_linkR {n : String} {F : LFn} (h : (n, F) ∈ linkR.fns) :
    (n = "rmw" ∧ F = rmwF) ∨ (n = "f" ∧ F = callerRF) := by
  simpa [linkR] using h

/-! ## Checks -/

theorem checksCR : lowerCheck fC vcC = true ∧ threadCheckC fC = true ∧ callArityC fC = true ∧
    callUseRegsC fC = true ∧ fC.externs.map (·.2.name) = ["rmw"] ∧ (indSigs fC).isEmpty = true ∧
    verifiable fC = true ∧ fC.blocks.all (fun B => !B.term.isTry) = true ∧
    IselThread.Witness.isOkB vcC.cfg = true ∧ vcC.outgoing = 0 ∧
    (locsOf fC.sig).all (fun l => match l with | .stack _ => false | _ => true) = true ∧
    fC.externs = [(0, extF)] ∧ callResLenB fC = true ∧ callUsesVirtB vcpC = true ∧
    callDefsVirtB vcpC = true ∧ callDefsRetB vcpC [.x 0] = true ∧ prepCheck vcC vcpC = true ∧
    vcpC.blocks.all (·.insts.all CallSeg.WitnessC.callerFormB) = true ∧ fR.sig = extF.sig := by
  native_decide -- witness: native_decide

theorem checksRR : threadCheckC fR = true ∧ callArityC fR = true ∧ callUseRegsC fR = true ∧
    callResLenB fR = true ∧ fR.blocks.all (fun B => !B.term.isTry) = true ∧
    callUsesVirtB vcpR = true ∧ callDefsVirtB vcpR = true ∧ callDefsRetB vcpR [.x 0] = true ∧
    Witness.retsX0B vcpR = true ∧ Witness.retsX0B vcpC = true := by
  native_decide -- witness: native_decide

theorem checksLR : fC.name = "f" ∧ fR.name = "rmw" ∧ fC.slots = [] ∧
    pCR.funcs.all (fun f => f.externs.all (·.2.name != f.name)) = true ∧
    pCR.funcs.all (fun g => g.blocks.all fun b => match b.term with
      | .returnCall .. => false
      | _ => true) = true ∧
    Witness.callsInsideB rmwF = true ∧ Witness.callsInsideB callerRF = true := by
  native_decide -- witness: native_decide

theorem name_fC : fC.name = "f" := checksLR.1

theorem name_fR : fR.name = "rmw" := checksLR.2.1

theorem slots_fC : fC.slots = [] := checksLR.2.2.1

theorem slots_fR : fR.slots = [] := clifC.2.2.2.2.2.2

theorem cfgFC : ∃ ss ps, vcC.cfg = .ok (ss, ps) := by
  have h := checksCR.2.2.2.2.2.2.2.2.1
  revert h
  cases vcC.cfg with
  | ok r => intro _; exact ⟨r.1, r.2, rfl⟩
  | error e => intro h; cases h

theorem fs_C : callerRF.af.frameSize = 176 := spC.2.2.2.2.2.2.2.1

theorem fs_R : rmwF.af.frameSize = 192 := spC.2.2.2.2.2.2.2.2

theorem drop_C : frameDrop callerRF.af = 192 := spC.2.1

theorem drop_R : frameDrop rmwF.af = 208 := spC.2.2.1

/-- `pCR` has no `return_call`. -/
theorem linkFree_CR : ∀ f : Clif.Function, f ∈ Clif.Program.funcs pCR → Clif.LinkFree f := by
  intro g hg b hb fn args he
  have h := List.all_eq_true.mp checksLR.2.2.2.2.1 g hg
  have := List.all_eq_true.mp h b hb
  rw [he] at this
  cases this

/-! ## The scopes and the static checks of the two functions -/

/-- Every activation of the caller is in the scope with calls. -/
theorem scope_CR {R : RL} (hR : R.vc = vcpC) : MemScopeLSC R := by
  intro b vb k i hb hi
  rw [hR] at hb
  obtain ⟨hb', rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨hk', rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  have h1 := (Array.all_eq_true.mp checksCR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) b hb'
  have h2 : CallSeg.WitnessC.callerFormB vcpC.blocks[b].insts[k] = true :=
    (Array.all_eq_true.mp h1) k hk'
  revert h2
  generalize vcpC.blocks[b].insts[k] = i
  intro h2
  cases i with
  | args ds => exact .inl (.inl (.inl (.inr (.inl ⟨ds, rfl⟩))))
  | rets us => exact .inl (.inl (.inl (.inr (.inr (.inl ⟨us, rfl⟩)))))
  | call info => exact .inr (.inr (.inr ⟨info, rfl⟩))
  | _ => simp [CallSeg.WitnessC.callerFormB] at h2

/-- Every activation of `atomic_rmw` in the link is in the scope with calls (as `scopeX`). -/
theorem scope_R (s0 : ArmState) (K : Nat) (G : BitVec 64 → Prop) :
    MemScopeLSC (linkR.act rmwF s0 K G) := by
  refine memScopeLSC_of_ls (memScopeLS_of_memScopeB (memScopeB_of_memScopeL ?_))
  have h : (linkR.act rmwF s0 K G).vc.blocks.all
      (·.insts.all (formRB (linkR.act rmwF s0 K G).ctx)) = true := scopeLR
  intro b vb k i hb hi
  obtain ⟨hb', rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨hk', rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  have h1 := (Array.all_eq_true.mp h) b hb'
  have h2 := (Array.all_eq_true.mp h1) k hk'
  revert h2
  generalize (linkR.act rmwF s0 K G).vc.blocks[b].insts[k] = i
  intro h2
  cases i with
  | fence => exact .inl (.inr (.inl rfl))
  | args ds => exact .inl (.inl (.inr (.inl ⟨ds, rfl⟩)))
  | rets us => exact .inl (.inl (.inr (.inr (.inl ⟨us, rfl⟩))))
  | loadAcquire ty rt rn fl => exact .inl (.inr (.inr (.inl ⟨ty, rt, rn, fl, rfl, h2⟩)))
  | atomicRmwLoop => exact .inr (.inl ⟨_, _, _, _, _, _, _, _, rfl⟩)
  | _ => simp [formRB] at h2

theorem static_CR : callerRF.Static :=
  ⟨wfRC.check, wfRC.alloc, wfRC.emit, wfRC.layout, wfRC.lm, wfRC.fit, wfRC.psF, entryArgRC⟩

theorem static_R : rmwF.Static :=
  ⟨wfRR.check, wfRR.alloc, wfRR.emit, wfRR.layout, wfRR.lm, wfRR.fit, wfRR.psF, entryArgRR⟩

/-! ## The two functions compiled -/

/-- **The caller is compiled.** -/
theorem fnOk_CR {env : Clif.Env} (henv : env.extern "rmw" = none) :
    FnOk linkR env pCR (fun _ => none) "f" callerRF fC := by
  obtain ⟨hlow, hthr, har0, hcu0, hnames, hind, hv, hnt, -, hout0, hlocs, hexts, hres, huv, hdv,
    -, hprep, -, hsigF⟩ := checksCR
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hbl, har, hcu⟩ :=
    obligations_of_checksA hlow hthr har0 hcu0
  obtain ⟨Lp, ss, ss', H3, hm3⟩ := CallLayers.prep_init (vc := vcC) (vcp := callerRF.vc) hprep
  obtain ⟨cc, ins, a0, hat, hm4⟩ :=
    CallLayers.alloc_init (vc := callerRF.vc) (rf := callerRF.rf) allocC ckeep
  have hext : ∀ e ∈ fC.externs, env.extern e.2.name = none := by
    intro e he
    have : e.2.name ∈ fC.externs.map (·.2.name) := List.mem_map_of_mem he
    rw [hnames, List.mem_singleton] at this
    rw [this]; exact henv
  refine ⟨static_CR, by rw [fs_C], fun q hq => (by rw [slots_fC] at hq; cases hq), vcC, ctx, st0,
    R, gn, bl, A, Lp, ss, ss', cc, ins, a0,
    fun s0 K G ra c slots ext caller opens N sps hwf habi hc => ?_⟩
  exact {
    mem := mem_callerR
    wf := hwf
    scope := scope_CR rfl
    abi := habi
    H := driverHypT_mk (Γ := ⟨(linkR.act callerRF s0 K G).F, fun _ => none,
        (linkR.act callerRF s0 K G).ctx.slotBase, 0⟩) (fctx := (linkR.act callerRF s0 K G).ctx)
      (X := callerRF.X) hshape hcert hbr hlow (List.isEmpty_iff.mp hind) hv hnt cfgFC hout0 rfl
      (fun _ _ h => by cases h) (mrStable_relW _ fC c) (outArgsOk_relW _ fC c)
      (memRelOk_relW _ fC c) (by
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
    ok := okR
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
    uniq := fun e he e' he' _ => by
      rw [hexts, List.mem_singleton] at he he'; rw [he, he']
    envx := hext
    sigs := fun e he callee hp => by
      rw [hexts, List.mem_singleton] at he
      subst he
      obtain ⟨-, hf, -⟩ := clifC
      rw [hf] at hp; cases hp
      exact hsigF
    probe := ArmAllocThread.ProbeF.of_small
      (show callerRF.af.frameSize + 16 < 4096 by rw [fs_C]; decide) }

/-- **`atomic_rmw` is compiled** (no extern, for every environment). -/
theorem fnOk_R {env : Clif.Env} : FnOk linkR env pCR (fun _ => none) "rmw" rmwF fR := by
  obtain ⟨hlow, -, hexn, hind, hv, -, hout0, hprep, -, -, -⟩ := checksR
  obtain ⟨hthr, har0, hcu0, hres, hnt, huv, hdv, -⟩ := checksRR
  have hnil : fR.externs = [] := List.isEmpty_iff.mp hexn
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hbl, har, hcu⟩ :=
    obligations_of_checksA hlow hthr har0 hcu0
  obtain ⟨Lp, ss, ss', H3, hm3⟩ := CallLayers.prep_init (vc := vcR) (vcp := rmwF.vc) hprep
  obtain ⟨cc, ins, a0, hat, hm4⟩ :=
    CallLayers.alloc_init (vc := rmwF.vc) (rf := rmwF.rf) allocR ckeep
  have hext : ∀ e ∈ fR.externs, env.extern e.2.name = none := by
    intro e he; rw [hnil] at he; cases he
  refine ⟨static_R, by rw [fs_R], fun q hq => (by rw [slots_fR] at hq; cases hq), vcR, ctx, st0,
    R, gn, bl, A, Lp, ss, ss', cc, ins, a0,
    fun s0 K G ra c slots ext caller opens N sps hwf habi hc => ?_⟩
  exact {
    mem := mem_rmw
    wf := hwf
    scope := scope_R s0 K G
    abi := habi
    H := driverHypT_mk (Γ := ⟨(linkR.act rmwF s0 K G).F, fun _ => none,
        (linkR.act rmwF s0 K G).ctx.slotBase, 0⟩) (fctx := (linkR.act rmwF s0 K G).ctx)
      (X := rmwF.X) hshape hcert hbr hlow (List.isEmpty_iff.mp hind) hv hnt cfgR hout0 rfl
      (fun _ _ h => by cases h) (mrStable_relW _ fR c) (outArgsOk_relW _ fR c)
      (memRelOk_relW _ fR c) (by
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
    ok := okR
    slot := rfl
    sym := fun _ _ h => by cases h
    reg := fun off h => by rw [locsR] at h; simp at h
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
    sigs := fun e he => by rw [hnil] at he; cases he
    probe := ArmAllocThread.ProbeF.of_small (show rmwF.af.frameSize + 16 < 4096 by rw [fs_R]; decide) }

/-! ## The static premises of the link -/

/-- **The oracle's frames.** -/
def frR (n : String) : Option (Nat × (Clif.SlotId → Nat)) :=
  if n = "f" then some (frameDrop callerRF.af, slotOffs callerRF.af fC)
  else if n = "rmw" then some (frameDrop rmwF.af, slotOffs rmwF.af fR)
  else none

/-- **The frame bound**: `atomic_rmw`'s frame, 192 bytes and the frame record (bound 272). -/
def MxR : Nat := 272

theorem frR_f : frR "f" = some (frameDrop callerRF.af, slotOffs callerRF.af fC) := by simp [frR]

theorem frR_rmw : frR "rmw" = some (frameDrop rmwF.af, slotOffs rmwF.af fR) := by simp [frR]

/-- **The static premises of `linkR` on `pCR`.** -/
theorem linkOk_R {env : Clif.Env} (henv : env.extern "rmw" = none) :
    LinkOk linkR env pCR (fun _ => none) frR MxR where
  fn := by
    intro n f hf
    obtain ⟨hm, rfl⟩ := Clif.Program.func?_some hf
    simp only [pCR, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · rw [name_fC]
      exact ⟨callerRF, mem_callerR, fnOk_CR henv, frR_f, by
        rw [ArmAllocThread.Witness.probeBelow_small (af := callerRF.af) (by rw [fs_C]; decide), fs_C]
        decide⟩
    · rw [name_fR]
      exact ⟨rmwF, mem_rmw, fnOk_R, frR_rmw, by
        rw [ArmAllocThread.Witness.probeBelow_small (af := rmwF.af) (by rw [fs_R]; decide), fs_R]
        decide⟩
  inside := by
    intro n F h
    rcases mem_linkR h with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Witness.callsInside_of checksLR.2.2.2.2.2.1
    · exact Witness.callsInside_of checksLR.2.2.2.2.2.2
  noSelf := by
    intro n f hf e he
    obtain ⟨hm, rfl⟩ := Clif.Program.func?_some hf
    have h := List.all_eq_true.mp checksLR.2.2.2.1 f hm
    simpa using List.all_eq_true.mp h e he
  defsRet := by
    intro nA FA nB FB hA hB b vb us hb hk
    have hus : us.map (·.2) = [.x 0] := by
      rcases mem_linkR hB with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Witness.rets_x0 checksRR.2.2.2.2.2.2.2.2.1 hb hk
      · exact Witness.rets_x0 checksRR.2.2.2.2.2.2.2.2.2 hb hk
    rw [hus]
    rcases mem_linkR hA with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact (callDefsRetB_iff _ _).1 checksRR.2.2.2.2.2.2.2.1
    · exact (callDefsRetB_iff _ _).1 checksCR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **The oracle's frames of `pCR`** hold its slots within `MxR` bytes. -/
theorem placeOk_R : PlaceOk pCR frR MxR := by
  intro g hg
  simp only [pCR, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · refine ⟨_, _, by rw [name_fC]; exact frR_f, by rw [drop_C]; decide, fun q hq => ?_⟩
    rw [slots_fC] at hq; cases hq
  · refine ⟨_, _, by rw [name_fR]; exact frR_rmw, by rw [drop_R]; decide, fun q hq => ?_⟩
    rw [slots_fR] at hq; cases hq

/-! ## The caller's root activation -/

/-- The caller in the link with a callee budget of `0x240` bytes. -/
abbrev RAc : RL := linkR.act callerRF sC0 0x240 GL

theorem stack_RAc : StackAvail 0x240 callerRF.af sC0 := by
  have hs := spC
  have hfs : callerRF.af.frameSize = 176 := hs.2.2.2.2.2.2.2.1
  refine ⟨⟨?_, fun a ha => ?_⟩, ArmAllocThread.Witness.probeBelow_le_small (by omega)⟩
  · show callerRF.af.frameSize + 16 + 0x240 ≤ (E2E.spv RC.s0).toNat
    rw [spv_RC, hfs]; decide
  · obtain ⟨j, hj, hd⟩ := CallSeg.WitnessCR.codeAddr_words program_RC ha
    show callerRF.af.frameSize + 16 + 0x240 ≤
      (a - (E2E.spv RC.s0 - BitVec.ofNat 64 (callerRF.af.frameSize + 16 + 0x240))).toNat
    rw [spv_RC, hfs]
    have hj' : j < 0x4000 := by have := hs.2.2.2.2.1; omega
    rw [show RC.base = 0x30000#64 from rfl] at hd
    generalize j = J at hj' hd
    bv_omega

theorem wf_RAc : RAc.Wf where
  check := wfRC.check
  alloc := wfRC.alloc
  emit := wfRC.emit
  layout := wfRC.layout
  lm := wfRC.lm
  fit := wfRC.fit
  stack := stack_RAc
  psF := wfRC.psF
  prog0 := wfRC.prog0
  gfree := fun a hG ⟨h1, _⟩ => by
    have := gR_ge hG
    have e : (E2E.spv RAc.s0).toNat = 0x7000 := by
      rw [show E2E.spv RAc.s0 = 0x7000#64 from spv_RC]; rfl
    omega

/-- **The linked code is kept by the caller.** -/
theorem codeIn_RAc : CallSegCall.CodeIn linkR RAc := by
  intro n FB hB
  rcases mem_linkR hB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine .inr fun k wd hk => ?_
    have hk' : (actW vcpR rfR).fb.words[k]? = some wd := hk
    obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hk'
    have hG : ∀ i < 4, GL (0x20000#64 + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 i) :=
      fun i hi => by
        unfold GL
        have : (actW vcpR rfR).fb.words.size ≤ 0x4000 := spC.2.2.2.1
        generalize (actW vcpR rfR).fb.words.size = n at this hlt
        bv_omega
    refine ⟨hG, ?_⟩
    have hR : Arm.read_mem_bytes 4 (0x20000#64 + BitVec.ofNat 64 (4 * k)) RAR.s0 = wd :=
      Concurrency.CallThread.Witness.abiRR.code k wd hk'
    show Arm.read_mem_bytes 4 (0x20000#64 + BitVec.ofNat 64 (4 * k)) sC0 = wd
    rw [← hR]
    refine read_mem_bytes_congr 4 _ fun i hi => ?_
    show memC _ = _
    simp only [memC, hG i hi, ↓reduceIte]
  · exact .inl ⟨rfl, rfl⟩

/-- The addresses outside the activation's world are at or above `0x6CC0`. -/
theorem fc_ge {a : BitVec 64} (h : RAc.F a) : 0x6CC0 ≤ a.toNat := by
  have hs := spC
  have e : E2E.spv sC0 - BitVec.ofNat 64 (frameDrop callerRF.af) = 0x6F40#64 := by
    rw [show E2E.spv sC0 = 0x7000#64 from spv_RC, show frameDrop callerRF.af = 192 from hs.2.1]
    rfl
  have hsz : RC.fr.size ≤ 176 := hs.2.2.2.2.2.1
  have hfs : callerRF.af.frameSize = 176 := hs.2.2.2.2.2.2.2.1
  change frameWG 0x240 RC.fr.intBase RC.fr.size callerRF.af GL sC0 a at h
  unfold frameWG frameW frameF StackBelow at h
  rw [e, hfs, show frameDrop callerRF.af = 192 from hs.2.1] at h
  rcases h with ((⟨h1, h2⟩ | ⟨h1, h2⟩ | hc) | ⟨h1, h2⟩) | hG
  · generalize RC.fr.size = n at hsz h2
    bv_omega
  · bv_omega
  · obtain ⟨j, hj, hd⟩ := CallSeg.WitnessCR.codeAddr_words program_RC hc
    rw [show RC.base = 0x30000#64 from rfl] at hd
    have : j < 0x4000 := by have := hs.2.2.2.2.1; omega
    generalize j = J at this hd
    bv_omega
  · simp only [BitVec.toNat_ofNat] at h1 h2; omega
  · have := gR_ge hG; omega

/-! ## The CLIF entry state with the oracle -/

/-- The caller's CLIF memory with the slot-placement oracle at its body `sp`. -/
def memO : Clif.Mem := { memL with place := some ⟨[RAc.spB], frR, none⟩ }

/-- **The caller's CLIF entry state** (`csC` with the oracle). -/
def csO : Clif.State := { csC with mem := memO }

/-- The thread's start: `csO` with no masked byte. -/
noncomputable def csT : TState := encT (fun _ => False) (.run csO)

theorem checksO : fC.blocks.isEmpty = false ∧
    (Clif.Regs.empty.setMany (B0C.params.map (·.1)) argsR).isSome = true ∧
    argsR.map (·.ty) = B0C.params.map (·.2) ∧ argsR.map (·.ty) = fC.sig.params.map (·.ty) ∧
    (match locsOf fC.sig with | [.reg (.x 0), .reg (.x 1)] => true | _ => false) = true ∧
    B0R.body = [{ results := [2], inst := .atomicRmw .add .i64 {} 0 1 }] ∧ B0R.term = .ret [2] ∧
    B0C.term = .ret [2] ∧ (E2E.spv w₀C).toNat % 16 = 0 := by
  native_decide -- witness: native_decide

theorem b0C : fC.blocks[0]? = some B0C := by
  have h := checksO.1
  unfold B0C
  revert h
  cases fC.blocks with
  | nil => intro h; cases h
  | cons b bs => intro _; rfl

theorem regsC_eq : Clif.Regs.empty.setMany (B0C.params.map (·.1)) argsR = some regsC := by
  have h := checksO.2.1
  unfold regsC
  revert h
  cases Clif.Regs.empty.setMany (B0C.params.map (·.1)) argsR with
  | none => intro h; cases h
  | some r => intro _; rfl

theorem locsC : locsOf fC.sig = [.reg (.x 0), .reg (.x 1)] := by
  have h := checksO.2.2.2.2.1
  revert h
  generalize locsOf fC.sig = l
  intro h
  match l, h with
  | [.reg (.x 0), .reg (.x 1)], _ => rfl

theorem errW₀C : Arm.r .ERR w₀C = .None := by
  rw [E2E.r_bodyOf _ _ (by simp) (by simp)]
  exact abiRC.err

theorem relW_O : RelW ⟨RAc.F, fun _ => none, RAc.ctx.slotBase, 0⟩ fC (E2E.spv w₀C) [] memO
    w₀C := by
  refine ⟨⟨⟨fun a b _ hb => by simp [memO, memL] at hb, fun a n hv => ?_, rfl⟩,
      fun id b h => by simp at h, E2E.outRel_zero _ _ _⟩, rfl, errW₀C⟩
  simp only [Clif.Mem.valid, memO, memL, List.any_cons, List.any_nil, Bool.or_false,
    Clif.Alloc.contains] at hv
  have hv' : a + n ≤ 8 := by
    revert hv; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  refine ⟨by omega, fun k hk hF => ?_⟩
  have := fc_ge hF
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem argsAt_O : ArgsAtEntry RAc.F fC.sig argsR w₀C := by
  intro loc v h
  rw [locsC] at h
  simp only [argsR, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
    Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show VHolds _ _
    rw [VHolds, E2E.regVal_bodyOf _ _ (by decide), x0C.1]
    rfl
  · show VHolds _ _
    rw [VHolds, E2E.regVal_bodyOf _ _ (by decide), x0C.2]
    rfl

theorem body_RAc : BodyEntryW RAc.F RAc.vc.EntryArg RAc.af RAc.s0 w₀C :=
  (E2E.Binary.bodyEntry_bodyOf RAc.af RAc.s0).w RAc.F entryArgRC

theorem linv_O : Clif.LInv pCR csO :=
  ⟨⟨List.mem_cons_self .., .inl ⟨B0C, List.mem_of_getElem? b0C, List.suffix_refl _, rfl⟩⟩,
    fun _ h => nomatch h⟩

theorem func_f : pCR.func? "f" = some fC := by
  simp [Clif.Program.func?, pCR, name_fC]

/-! ## The reachable CLIF states (`WitnessFull.CallShape`) -/

/-- The allocations of `memL`. -/
def AllocsIn (m : Clif.Mem) : Prop := ∀ x ∈ m.allocs, x ∈ memL.allocs

/-- `csO` calls `atomic_rmw`: a read-modify-write, then both return. -/
theorem shape_O : WitnessFull.CallShape pCR csO csR.frame extC := by
  obtain ⟨hb, hfn, hsig, hent, h1, h2, hsl⟩ := clifC
  exact ⟨⟨rfl, fun _ hx => hx⟩, ⟨[2], 0, [0, 1], extF, argsR, B0R, regsR, hb, rfl, preC, hfn,
    hsig, hent, h1, h2, regsR_eq, hsl, rfl⟩, ⟨_, checksO.2.2.2.2.2.1, (fun _ _ h => by cases h),
    (fun _ _ _ h => by cases h)⟩, ⟨_, checksO.2.2.2.2.2.2.1⟩, ⟨_, checksO.2.2.2.2.2.2.2.1⟩⟩

/-- **The CLIF states reachable from `csO`**, up to their bytes: the caller at its call,
`atomic_rmw` at its entry, `atomic_rmw` returning, the caller returning. -/
def Fam (s : Clif.State) : Prop := WitnessFull.FamG csC.frame csR.frame extC s

/-- The reachable thread states. -/
def RInv : TState → Prop := WitnessFull.RInvG Fam

theorem fam_congr {s s' : Clif.State}
    (h : withBytes s (fun _ => none) = withBytes s' (fun _ => none)) (hs : Fam s) : Fam s' :=
  WitnessFull.famG_congr h hs

theorem rinv_strip {t t' : TState} (h : strip t = strip t') (ht : RInv t) : RInv t' :=
  WitnessFull.rinvG_strip (fun _ _ => fam_congr) h ht

/-- **A step from a reachable state to a running state stays reachable.** -/
theorem next_fam (env : Clif.Env) {s : Clif.State} (hs : Fam s) (B : Bytes) {s' : Clif.State}
    (hst : Clif.step env pCR (withBytes s B) = .next s') : Fam s' :=
  WitnessFull.next_famG shape_O env hs B hst

/-- **A step from a reachable state stays reachable.** -/
theorem step_fam (env : Clif.Env) {s : Clif.State} (hs : Fam s) (B : Bytes) {t'' : TState}
    {B' : Bytes} (h : res (Clif.step env pCR (withBytes s B)) = some (t'', B')) : RInv t'' :=
  WitnessFull.step_famG shape_O env hs B h

/-- **The thread states reachable from `csO`.** -/
theorem reach_inv {env : Clif.Env} {t : TState} (h : RReach env pCR (.run csO) t) : RInv t :=
  WitnessFull.reach_invG shape_O h

/-- **At most one caller** below every reachable state. -/
theorem depth_O {env : Clif.Env} :
    ∀ S, RReach env pCR (.run csO) (.run S) → S.callers.length < 2 :=
  WitnessFull.depthG shape_O

/-- The accesses: `atomic_rmw`'s read and write of the 8 bytes at `0`. -/
def LocO : Nat → Nat → Prop := fun a n => a = 0 ∧ n = 8

theorem partDisj_O : PartDisj LocO := fun a n b m ha hb _ _ => by
  simp only [LocO] at ha hb; omega

theorem evShape_csC : evShape csC = [[]] := by
  unfold evShape; rw [show csC.frame.body = B0C.body from rfl, clifC.1]

/-- **The accesses from the reachable states lie on `LocO`.** -/
theorem partsOk_O {env : Clif.Env} : PartsOk env pCR (.run csO) LocO :=
  WitnessFull.partsOkG shape_O (eS := csR) rfl shapeR1 (by decide)

/-! ## The activation's entry and the thread -/

/-- **The caller's root activation entered at its ABI entry.** -/
theorem ent_O : ∃ g : Act, Ent linkR Clif.Env.empty pCR (PrivA RAc) (.run csO) LocO frR MxR 2
    (fun _ => none) g (sC0, none) (csT, PrivA RAc) := by
  obtain ⟨-, -, -, vc, ctx, st0, R, gn, bl, A, Lp, ss, ss', cc, ins, a0, hF⟩ :=
    fnOk_CR (env := Clif.Env.empty) rfl
  have hS := hF sC0 0x240 GL 0x4000#64 (E2E.spv w₀C) [] [] callerRF [] (fun _ => False) [] wf_RAc
    abiRC checksO.2.2.2.2.2.2.2.2
  obtain ⟨-, hq, hA⟩ := q_init_lines wf_RAc abiRC body_RAc
  refine ⟨⟨"f", callerRF, sC0, 0x240, GL, 0x4000#64, fC, vc, ctx, st0, R, gn, bl, A,
    ⟨RAc.F, fun _ => none, RAc.ctx.slotBase, 0⟩, E2E.spv w₀C, Lp, ss, ss', cc, ins, a0, [], [],
    callerRF, [], fun _ => False, []⟩, rfl, csO, fun _ => False, rfl, ?_, ?_, func_f⟩
  · exact {
      stat := hS
      syms := rfl
      code := codeIn_RAc
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
      budget := show (2 - 0) * 272 ≤ 576 by decide
      func := rfl }
  · exact chainP_entry hS b0C rfl rfl rfl rfl rfl regsC_eq checksO.2.2.1 checksO.2.2.2.1 relW_O
      argsAt_O hq hA

open ProgE2E PrivCohT Rel in
/-- **The caller of `atomic_rmw` through the call and back, from the generic theorem**
(`realizes_linked_calls` on `linkR`/`pCR` with one thread, the caller's root activation, every
premise discharged but the run): every execution of the realized prefix of a precise run of the
linked machine from the caller's ABI entry is realized by a `CStepS` thread of `pCR` from `csO`. -/
theorem realizes_call_rmwT {ls : List Lab} {t' : CallCompose.AT}
    (hr : PRun Policy.arm linkR.M (OkB (PrivA RAc)) (sC0, none) ls t') :
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
        (∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j < 1, PrivA RAc (locsA[q]).1) →
        (∀ q (h : q < locsC.length),
          bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2) →
        StackDisjoint PA (fun _ l => PrivA RAc l ∨ PrivA RAc l) →
        ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧
          (∀ i < 1, PC.st i 0 = csT) ∧ PC.Runs (CStepS Clif.Env.empty pCR) ∧
          Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ (fun _ _ _ => True) := by
  obtain ⟨g, hg⟩ := ent_O
  exact realizes_linked_calls (n := 1) (L := linkR) (env := Clif.Env.empty) (p := pCR)
    (Bnd := fun _ => PrivA RAc) (c0 := fun _ => .run csO) (Loc := fun _ => LocO) (fr := frR)
    (Mx := MxR) (Dcap := fun _ => 2) (syms := fun _ => none) (g := fun _ => g)
    (sA := fun _ => (sC0, none)) (cs := fun _ => csT) (D0 := fun _ => PrivA RAc)
    (fun _ _ => partsOk_O) (fun _ _ => partDisj_O) linkFree_CR WitnessFull.keepsAllocs_E
    WitnessFull.keepsPlace_E placeOk_R (fun _ _ => depth_O) (linkOk_R rfl) (fun _ _ => hg)
    (ls := fun _ => ls) (t' := fun _ => t') (fun _ _ => hr)

end Concurrency.CallSegOkGT.WitnessRmw
