import FV.Concurrency.CallSegOkGT
import FV.Concurrency.CallSegCallWitness
import FV.Concurrency.CallEntryRelWitness

/-!
# Witness: the static premises of the link of the caller and `atomic_load` (#473, steps 3 and 4)

On the link `LinkedMachine.Witness.link2` (`ld` the compiled `atomic_load` `ldF` of `fL`, `f` the
compiled caller `callerF` of `fC`) and the program `pCL = [fC, fL]`:

* **`fnOk_C`**, **`fnOk_L`**: both functions are compiled (`FnOk`): every activation of them
  (well formed, entered at an ABI call, its memory relation base 16-aligned) has its `StatOk`
  (the lowering, prep and allocation data fixed before the activation; `DriverHypT` by
  `IselResume.driverHypT_mk` on the activation's private set);
* `fr2`, `Mx2`: the oracle's frames of both functions and the frame bound (240 bytes);
* **`linkOk_2`**: `LinkOk` (every call line followed by a word, `callsInside_of` on a check; no
  self-call; the callees' `rets` registers `x0` `CallDefsRet` of both functions);
* `placeOk_2`: `CallSegRun.PlaceOk`; `linkFree_CL`: no `return_call` in `pCL`;
* **`funRealT_link_2`**: `funRealT_link` on `link2`/`pCL` with the static premises discharged.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallSegOkGT.Witness

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck ThreadRefine IselCall IselCallRet ArmAllocThread E2E
  LinkedMachine LinkedMachine.Link LinkedMachine.Witness CallComposeT CallSegOkG CallSegPc
  CallSegRun CallResumeChecks CallEntryRel CallSeg.WitnessC CallEntry.Witness CallResumeL.Witness
  RealizeCompiled.WitnessL IselResume CallArity CallArgsEntry CallArgsL2 CallArgsAt
  IselCall.Witness CallEntryRel.Witness

/-! ## Checks -/

/-- Every `bl`/`blr` line of `F` is followed by a word (as a check). -/
def callsInsideB (F : LFn) : Bool :=
  (List.range F.fa.lines.toList.length).all fun j =>
    match F.fa.lines.toList[j]? with
    | some (.ins (.bl _) _) | some (.ins (.blr _) _) =>
      decide (lineOffset F.fa.lines.toList j + 4 < 4 * F.fb.words.size)
    | _ => true

theorem callsInside_of {F : LFn} (h : callsInsideB F = true) : CallsInside F := by
  intro j i t hj hi
  have hlt : j < F.fa.lines.toList.length := (List.getElem?_eq_some_iff.mp hj).1
  have h1 := List.all_eq_true.mp h j (List.mem_range.mpr hlt)
  rw [hj] at h1
  rcases hi with ⟨n, rfl⟩ | ⟨r, rfl⟩ <;> simpa using h1

/-- Every `rets` of `vc` reads `x0` (as a check). -/
def retsX0B (vc : VCode) : Bool :=
  vc.blocks.all fun vb => vb.insts.all fun i => match i with
    | .rets us => us.map (·.2) == [.x 0]
    | _ => true

theorem rets_x0 {vc : VCode} (h : retsX0B vc = true) {b : Nat} {vb : VBlock}
    {us : List (Reg × Reg)} (hb : vc.blocks[b]? = some vb)
    (hk : ∃ k : Nat, vb.insts[k]? = some (MInst.rets us)) : us.map (·.2) = [.x 0] := by
  obtain ⟨k, hk⟩ := hk
  simp only [retsX0B, Array.all_eq_true] at h
  obtain ⟨hb1, rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨hk1, e⟩ := Array.getElem?_eq_some_iff.mp hk
  have h2 := h b hb1 k hk1
  rw [e] at h2
  simpa using h2

theorem checks2 : threadCheckC fL = true ∧ callArityC fL = true ∧ callUseRegsC fL = true ∧
    callResLenB fL = true ∧ fL.blocks.all (fun B => !B.term.isTry) = true ∧
    callUsesVirtB vcpL = true ∧ callDefsVirtB vcpL = true ∧ callDefsRetB vcpL [.x 0] = true ∧
    fC.name = "f" ∧ fL.name = "ld" ∧ fC.slots = [] ∧
    pCL.funcs.all (fun f => f.externs.all (·.2.name != f.name)) = true ∧
    pCL.funcs.all (fun g => g.blocks.all fun b => match b.term with
      | .returnCall .. => false
      | _ => true) = true ∧
    callsInsideB ldF = true ∧ callsInsideB callerF = true ∧ retsX0B vcpC = true := by
  native_decide -- witness: native_decide

theorem name_fC : fC.name = "f" := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := checks2; exact h

theorem name_fL : fL.name = "ld" := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := checks2; exact h

theorem slots_fC : fC.slots = [] := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := checks2; exact h

theorem noSelfB : pCL.funcs.all (fun f => f.externs.all (·.2.name != f.name)) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := checks2; exact h

theorem inside_ld : CallsInside ldF := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := checks2; exact callsInside_of h

theorem inside_C : CallsInside callerF := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := checks2; exact callsInside_of h

theorem retsX0_C : retsX0B vcpC = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := checks2; exact h

theorem defsRet_L : CallDefsRet vcpL [.x 0] := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := checks2; exact (callDefsRetB_iff _ _).1 h

theorem fs_C : callerF.af.frameSize = 160 := spC.2.2.2.2.2.2.2.1

theorem fs_ld : ldF.af.frameSize = 160 := spC.2.2.2.2.2.2.2.2

theorem drop_C : frameDrop callerF.af = 176 := spC.2.1

theorem drop_ld : frameDrop ldF.af = 176 := spC.2.2.1

/-- `pCL` has no `return_call`. -/
theorem linkFree_CL : ∀ f : Clif.Function, f ∈ Clif.Program.funcs pCL → Clif.LinkFree f := by
  intro g hg b hb fn args he
  have h := List.all_eq_true.mp
    (by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := checks2; exact h) g hg
  have := List.all_eq_true.mp h b hb
  rw [he] at this
  cases this

theorem mem_link2 {n : String} {F : LFn} (h : (n, F) ∈ link2.fns) :
    (n = "ld" ∧ F = ldF) ∨ (n = "f" ∧ F = callerF) := by
  simpa [link2] using h

/-! ## The scopes and the static checks of the two functions -/

/-- Every activation of the caller is in the scope with calls (as `scopeRC`). -/
theorem scope_C {R : RL} (hR : R.vc = vcpC) : MemScopeLSC R := by
  intro b vb k i hb hi
  rw [hR] at hb
  obtain ⟨hb', rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨hk', rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  have h1 := (Array.all_eq_true.mp scopeCB_eq) b hb'
  have h2 : callerFormB vcpC.blocks[b].insts[k] = true := (Array.all_eq_true.mp h1) k hk'
  revert h2
  generalize vcpC.blocks[b].insts[k] = i
  intro h2
  cases i with
  | args ds => exact .inl (.inl (.inl (.inr (.inl ⟨ds, rfl⟩))))
  | rets us => exact .inl (.inl (.inl (.inr (.inr (.inl ⟨us, rfl⟩)))))
  | call info => exact .inr (.inr (.inr ⟨info, rfl⟩))
  | _ => simp [callerFormB] at h2

/-- Every activation of `atomic_load` in the link is in the scope with calls (as `scopeX`). -/
theorem scope_ld (s0 : ArmState) (K : Nat) (G : BitVec 64 → Prop) :
    MemScopeLSC (link2.act ldF s0 K G) := by
  refine memScopeLSC_of_ls (memScopeLS_of_memScopeB (memScopeB_of_memScopeL
    (memScopeL_of_memScope ?_)))
  have h := scopeLB
  intro b vb k i hb hi
  obtain ⟨hb', rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨hk', rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  have h1 := (Array.all_eq_true.mp h) b hb'
  have h2 : memFormLB (link2.act ldF s0 K G).ctx
      (link2.act ldF s0 K G).vc.blocks[b].insts[k] = true := (Array.all_eq_true.mp h1) k hk'
  revert h2
  generalize (link2.act ldF s0 K G).vc.blocks[b].insts[k] = i
  intro h2
  cases i with
  | fence => exact .inr (.inl rfl)
  | args ds => exact .inl (.inr (.inl ⟨ds, rfl⟩))
  | rets us => exact .inl (.inr (.inr (.inl ⟨us, rfl⟩)))
  | loadAcquire ty rt rn fl => exact .inr (.inr (.inl ⟨ty, rt, rn, fl, rfl, h2⟩))
  | _ => simp [memFormLB] at h2

/-- The compiled caller is statically checked. -/
theorem static_C : callerF.Static :=
  ⟨wf_C.check, wf_C.alloc, wf_C.emit, wf_C.layout, wf_C.lm, wf_C.fit, wf_C.psF, entryArgRC⟩

/-! ## The two functions compiled -/

/-- **The caller is compiled** (module doc). -/
theorem fnOk_C {env : Clif.Env} (henv : env.extern "ld" = none) :
    FnOk link2 env pCL (fun _ => none) "f" callerF fC := by
  obtain ⟨hlow, hthr, -, hnames, hind, hv, hnt, -, hout0, -, hexts⟩ := checksFC
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hbl, har, hcu⟩ :=
    obligations_of_checksA hlow hthr CallResumeAll.Witness.arity_fC.1
      CallArgsEntry.Witness.useRegs_fC
  obtain ⟨Lp, ss, ss', H3, hm3⟩ := CallLayers.prep_init (vc := vcC) (vcp := callerF.vc) prepC
  obtain ⟨cc, ins, a0, hat, hm4⟩ :=
    CallLayers.alloc_init (vc := callerF.vc) (rf := callerF.rf) allocC ckeep
  have hext : ∀ e ∈ fC.externs, env.extern e.2.name = none := by
    intro e he
    have : e.2.name ∈ fC.externs.map (·.2.name) := List.mem_map_of_mem he
    rw [hnames, List.mem_singleton] at this
    rw [this]; exact henv
  refine ⟨static_C, by rw [fs_C], fun q hq => (by rw [slots_fC] at hq; cases hq), vcC, ctx, st0, R,
    gn, bl, A, Lp, ss, ss', cc, ins, a0,
    fun s0 K G ra c slots ext caller opens N sps hwf habi hc => ?_⟩
  exact {
    mem := mem_caller
    wf := hwf
    scope := scope_C rfl
    abi := habi
    H := driverHypT_mk (Γ := ⟨(link2.act callerF s0 K G).F, fun _ => none,
        (link2.act callerF s0 K G).ctx.slotBase, 0⟩) (fctx := (link2.act callerF s0 K G).ctx)
      (X := callerF.X) hshape hcert hbr hlow (List.isEmpty_iff.mp hind) hv hnt cfgFC hout0 rfl
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
    ok := ok2
    slot := rfl
    sym := fun _ _ h => by cases h
    reg := IselCall.Witness.fC_reg
    pinit := hm3 _ _
    minit := hm4
    res := CallArgsL2.Witness.resLen_fC
    cu := hcu
    ar := har
    low := hlow
    ind := List.isEmpty_iff.mp hind
    ver := hv
    nt := hnt
    out0 := hout0
    uv := Concurrency.CallArgsAt.Witness.usesV_fC
    dv := CallResumeAll.Witness.defs_fC.1
    uniq := fun e he e' he' _ => by
      rw [hexts, List.mem_singleton] at he he'; rw [he, he']
    envx := hext
    sigs := fun e he callee hp => by
      rw [hexts, List.mem_singleton] at he
      subst he
      obtain ⟨-, hf, -⟩ := clifC
      rw [hf] at hp; cases hp
      exact LinkedMachine.Witness.sig_fL
    probe := ArmAllocThread.ProbeF.of_small
      (show callerF.af.frameSize + 16 < 4096 by rw [fs_C]; decide) }

/-- **`atomic_load` is compiled** (module doc; no extern, for every environment). -/
theorem fnOk_L {env : Clif.Env} : FnOk link2 env pCL (fun _ => none) "ld" ldF fL := by
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
  refine ⟨static_ld, by rw [fs_ld], fun q hq => (by rw [slots_fL] at hq; cases hq), vcL, ctx, st0,
    R, gn, bl, A, Lp, ss, ss', cc, ins, a0,
    fun s0 K G ra c slots ext caller opens N sps hwf habi hc => ?_⟩
  exact {
    mem := mem_ld
    wf := hwf
    scope := scope_ld s0 K G
    abi := habi
    H := driverHypT_mk (Γ := ⟨(link2.act ldF s0 K G).F, fun _ => none,
        (link2.act ldF s0 K G).ctx.slotBase, 0⟩) (fctx := (link2.act ldF s0 K G).ctx)
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
    ok := ok2
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
    sigs := fun e he => by rw [hnil] at he; cases he
    probe := ArmAllocThread.ProbeF.of_small (show ldF.af.frameSize + 16 < 4096 by rw [fs_ld]; decide) }

/-! ## The link -/

/-- **The oracle's frames** (module doc). -/
def fr2 (n : String) : Option (Nat × (Clif.SlotId → Nat)) :=
  if n = "f" then some (frameDrop callerF.af, slotOffs callerF.af fC)
  else if n = "ld" then some (frameDrop ldF.af, slotOffs ldF.af fL)
  else none

/-- **The frame bound**: both frames are 160 bytes, 176 with the frame record (bound 240). -/
def Mx2 : Nat := 240

theorem fr2_f : fr2 "f" = some (frameDrop callerF.af, slotOffs callerF.af fC) := by simp [fr2]

theorem fr2_ld : fr2 "ld" = some (frameDrop ldF.af, slotOffs ldF.af fL) := by simp [fr2]

/-- **The static premises of `link2` on `pCL`** (module doc). -/
theorem linkOk_2 {env : Clif.Env} (henv : env.extern "ld" = none) :
    LinkOk link2 env pCL (fun _ => none) fr2 Mx2 where
  fn := by
    intro n f hf
    obtain ⟨hm, rfl⟩ := Clif.Program.func?_some hf
    simp only [pCL, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · rw [name_fC]
      exact ⟨callerF, mem_caller, fnOk_C henv, fr2_f, by
        rw [ArmAllocThread.Witness.probeBelow_small (af := callerF.af) (by rw [fs_C]; decide), fs_C]
        decide⟩
    · rw [name_fL]
      exact ⟨ldF, mem_ld, fnOk_L, fr2_ld, by
        rw [ArmAllocThread.Witness.probeBelow_small (af := ldF.af) (by rw [fs_ld]; decide), fs_ld]
        decide⟩
  inside := by
    intro n F h
    rcases mem_link2 h with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact inside_ld
    · exact inside_C
  noSelf := by
    intro n f hf e he
    obtain ⟨hm, rfl⟩ := Clif.Program.func?_some hf
    have h := List.all_eq_true.mp noSelfB f hm
    simpa using List.all_eq_true.mp h e he
  defsRet := by
    intro nA FA nB FB hA hB b vb us hb hk
    have hus : us.map (·.2) = [.x 0] := by
      rcases mem_link2 hB with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact CallSegCall.Witness.rets_ld hb hk
      · exact rets_x0 retsX0_C hb hk
    rw [hus]
    rcases mem_link2 hA with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact defsRet_L
    · exact CallResumeAll.Witness.defs_fC.2

/-- **The oracle's frames of `pCL`** hold its slots within `Mx2` bytes. -/
theorem placeOk_2 : PlaceOk pCL fr2 Mx2 := by
  intro g hg
  simp only [pCL, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · refine ⟨_, _, by rw [name_fC]; exact fr2_f, by rw [drop_C]; decide, fun q hq => ?_⟩
    rw [slots_fC] at hq; cases hq
  · refine ⟨_, _, by rw [name_fL]; exact fr2_ld, by rw [drop_ld]; decide, fun q hq => ?_⟩
    rw [slots_fL] at hq; cases hq

/-- **Every activation of `link2` is realized** (`funRealT_link` on `link2`/`pCL`, its static
premises `LinkOk`, `PlaceOk`, `LinkFree` discharged; the partition, the environment's keeping of
allocations and of the oracle and the depth bound stay premises). -/
theorem funRealT_link_2 {env : Clif.Env} (henv : env.extern "ld" = none) {Bnd : Nat → Prop}
    {c0 : TState} {Loc : Nat → Nat → Prop} {Dcap : Nat}
    (hP : PartsOk env pCL c0 Loc) (hdisj : PartDisj Loc)
    (hk : Clif.EnvKeepsAllocs env) (hkp : Clif.EnvKeepsPlace env)
    (hdep : ∀ S, RReach env pCL c0 (.run S) → S.callers.length < Dcap) :
    ∀ g u c, Ent link2 env pCL Bnd c0 Loc fr2 Mx2 Dcap (fun _ => none) g u c →
      FunRealG (RealT env pCL Bnd) link2.M (OkB Bnd) (Ret link2 env pCL c0 Loc fr2 g)
        (EndT env pCL Dcap) u c :=
  funRealT_link hP hdisj linkFree_CL hk hkp placeOk_2 hdep (linkOk_2 henv)

/-- **Non-vacuity of `segOkG`**: every activation of the link of the caller and
`atomic_load`, `LinkOk`, `PlaceOk` and `LinkFree` discharged. -/
theorem segOkG_2 {env : Clif.Env} (henv : env.extern "ld" = none) {Bnd : Nat → Prop}
    {c0 : TState} {Loc : Nat → Nat → Prop} {Dcap : Nat}
    (hP : PartsOk env pCL c0 Loc) (hdisj : PartDisj Loc)
    (hk : Clif.EnvKeepsAllocs env) (hkp : Clif.EnvKeepsPlace env)
    (hdep : ∀ S, RReach env pCL c0 (.run S) → S.callers.length < Dcap) (g : Act) :
    SegOkG (RealT env pCL Bnd) link2.M (OkB Bnd)
      (Ent link2 env pCL Bnd c0 Loc fr2 Mx2 Dcap (fun _ => none)) (Ret link2 env pCL c0 Loc fr2)
      (EndT env pCL Dcap) (Inv link2 env pCL Bnd c0 Loc fr2 Mx2 Dcap (fun _ => none) g) g :=
  segOkG hP hdisj linkFree_CL hk hkp placeOk_2 hdep (linkOk_2 henv) g

open ProgE2E PrivCohT Rel in
/-- **Non-vacuity of `realizes_linked_calls`**: threads of the link of the caller and
`atomic_load`, `LinkOk`, `PlaceOk` and `LinkFree` discharged. -/
theorem realizes_linked_calls_2 {env : Clif.Env} (henv : env.extern "ld" = none) {n : Nat}
    {Bnd : Nat → Nat → Prop} {c0 : Nat → TState} {Loc : Nat → Nat → Nat → Prop} {Dcap : Nat → Nat}
    {g : Nat → Act} {sA : Nat → CallCompose.AT} {cs : Nat → TState} {D0 : Nat → Nat → Prop}
    (hP : ∀ i < n, PartsOk env pCL (c0 i) (Loc i)) (hdisj : ∀ i < n, PartDisj (Loc i))
    (hk : Clif.EnvKeepsAllocs env) (hkp : Clif.EnvKeepsPlace env)
    (hdep : ∀ i < n, ∀ S, RReach env pCL (c0 i) (.run S) → S.callers.length < Dcap i)
    (hent : ∀ i < n, Ent link2 env pCL (Bnd i) (c0 i) (Loc i) fr2 Mx2 (Dcap i) (fun _ => none)
      (g i) (sA i) (cs i, D0 i))
    {ls : Nat → List Lab} {t' : Nat → CallCompose.AT}
    (hr : ∀ i < n, PRun Policy.arm link2.M (OkB (Bnd i)) (sA i) (ls i) (t' i)) :
    ∃ k : Nat → Nat, (∀ i < n, k i ≤ (ls i).length) ∧
      ∀ (PA : Traces ProgE2E.AState AKind BVal) (locsA locsC : List (Nat × Nat)) (MA0 MC0 : Bytes)
        (rfA coA rmwA : Concurrency.Rel PEv), PA.n = n →
        (∀ i < n, PA.tr i = conv (evTr ((ls i).take (k i)))) →
        (PA.exec locsA rfA coA rmwA).Wf →
        Acyclic (union (PA.exec locsA rfA coA rmwA).poLoc (PA.exec locsA rfA coA rmwA).com) →
        InitFirst (PA.exec locsA rfA coA rmwA) →
        (∀ i < n, ∀ a b, rmwA (.thr i a.1 a.2) (.thr i b.1 b.2) ↔
          MonPair (evTr ((ls i).take (k i))) a b) →
        locsC <+: locsA →
        (∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j < n, D0 j (locsA[q]).1) →
        (∀ q (h : q < locsC.length),
          bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2) →
        StackDisjoint PA (fun j l => D0 j l ∨ Bnd j l) →
        ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = n ∧
          (∀ i < n, PC.st i 0 = cs i) ∧ PC.Runs (CStepS env pCL) ∧
          Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ (fun _ _ _ => True) :=
  realizes_linked_calls hP hdisj linkFree_CL hk hkp placeOk_2 hdep (linkOk_2 henv) hent hr

end Concurrency.CallSegOkGT.Witness
