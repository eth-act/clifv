import FV.E2E.SretReturnWorld
import FV.E2E.DeadCleanupExecGot
import FV.E2E.DeadCleanupExecGoodReads

/-!
# The `sret` return register through the linked program and executable theorems (S7)

`_abi` copies of the whole-program chain of `Link.DeadCleanup.compileExe_correct`: for an
outside call of a function `f` whose `sret` value is bound once (`sretStableB f`), a return of
the linked machine (and of the executable machine) also leaves the ABI return values
`sretArg f args` after the CLIF ones, in x8 (`ArmRefinesAbi`, `ExecRefinesAbi`; until #587: in
x0.. after the CLIF values).

Only the outside activation's return is strengthened: its returned branch applies the world
theorem with the ABI return values (`backend_correct_world_pipeline_abi`) to `f`, with the
callee contracts from the linked induction at depth `M - 1` (`LinkSys.thm`, unchanged; a
compiled callee's contract keeps claiming only its CLIF results, `PrefixHold`). The trap branch
is the existing theorem's.

* `backend_correct_program_core_abi`, `backend_correct_program_budget_abi`,
  `backend_correct_program_stack_abi`;
* `DeadCleanupBinary.binary_correct_abi`, `DeadCleanupBinary.binary_correct_of_checks_abi`;
* `DeadCleanupExecBytes.ExecRefinesAbi` (`.execRefines` gives back `ExecRefines`),
  `exec_of_modelN_abi`, `binary_correct_exec_staticN_abi`, `binary_correct_exec_of_reads_abi`,
  `binary_correct_exec_of_insn_abi`, `binary_correct_exec_proven_abi`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- `backend_correct_program_core` with the ABI return values (`sretStableB f`). -/
theorem backend_correct_program_core_abi (L : LinkSys) (hL : L.Ok) [L.CrunOk]
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (hS : sretStableB f = true) (M : Nat) {ra : BitVec 64}
    {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs) {o : Clif.Outcome}
    (hlink : ((∃ vals cm, o = .returned vals cm) ∨ ∃ c, o = .trapped c) →
      ∃ m, Clif.runLoop (L.envR M f) L.P.bare m cs = o) :
    ArmRefinesAbi (L.A f).fb (L.A f).base ra (L.mach M f) s (sretArg f args) o := by
  cases o with
  | stuck m => trivial
  | outOfFuel => trivial
  | trapped c =>
    exact backend_correct_program_core L hL hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav
      hrel hpl htr hlink
  | returned vals cm =>
    have hc := hL.compiled f hf
    have hfr := lowerRFunc_frame hc.alloc
    obtain ⟨hB, hK⟩ := spBody_toNat hres
    have hd : frameDrop (L.A f).af = (L.A f).af.frameSize + 16 := by simp [frameDrop, hfr]
    -- the world side
    have hWE : L.WorldEntry κ M f L.F args cs w₀ := by
      refine ⟨hcs, ⟨hrel, rfl, ?_⟩, ?_, ?_, ?_, ?_, hL.imgF, hpl⟩
      · rw [hbe.other .ERR (by simp [Masked]) (by simp) (by simp)]; exact hent.err
      · refine argsAtEntry_body hfr (entryRegs_of_check hc.lowerOk) hbe hargs fun off v hm k hk hk' => ?_
        rw [hF] at hk'
        rcases hk' with hw | hi
        · exact stackArgsAvoid_frameW_pipeline hc hres hent hargs off v hm k hk hw
        · exact hsav off v hm k hk hi
      · rw [hbe.sp, hB]; omega
      · intro a ha
        rw [hbe.sp] at ha
        refine ⟨by rw [hF]; exact .inl (.inr ha), fun hi => hgfree a hi ?_⟩
        obtain ⟨h1, h2⟩ := ha
        rw [hB] at h1 h2
        exact ⟨by omega, by omega⟩
      · rw [hbe.sp, hB, hd]
        have := hent.spAligned
        have := L.frameSize_mod hL hf
        omega
    -- the machine side
    have hME : L.MachEntry κ M f L.F L.Img ra s w₀ :=
      ⟨hent.toCall, hres, hgfree, hF.symm, fun _ h => h, himg,
        hbe.w L.F fun r ⟨_, _, hvb, hi, _, hv⟩ =>
          ((ctlCheck_args (lowerRFunc_ok hc.alloc).2.2 hvb hi).2.2 _ hv).2⟩
    have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
    obtain ⟨m, hm⟩ := hlink (.inl ⟨_, _, rfl⟩)
    have ih : 0 < M → L.Thm κ (M - 1) := fun _ => L.thm hL hκ (M - 1)
    have hJ : L.ActInv f (spv w₀) cs := ⟨hIf, hcs.callers, hpl⟩
    have hm' : Clif.runLoop (L.envOf M f (spv w₀)) L.P.bare m cs = .returned vals cm := by
      rw [L.runLoop_envOf hL hf m cs hJ]; exact hm
    have h := backend_correct_world_pipeline_abi (hL.subset f hf) hc hS
      (X := L.X κ M f L.F) (syms := L.syms)
      (env := L.envOf M f (spv w₀)) (K := κ M f) (F := L.F) (c := spv w₀) (hL.covered f hf)
      (L.xCallsOk hL hκ ih hf hL.imgF hWE.room hWE.dead hWE.align)
      (L.xCallsIndOk hL hκ ih hf hL.imgF hWE.room hWE.dead hWE.align)
      (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel hWE.args
      (L.trapsExplicit_envOf hL hf hJ htr) m
    obtain ⟨us, outs, wf, hus, hlen, hhold, hmemR, -, hall⟩ := h.1 vals cm hm'
    obtain ⟨n, hret, -⟩ := hall (L.hooks M) L.Img (L.A f).base ra s ⟨hME.abi, hME.stack, hME.gfree,
      hME.hF, L.calleeOk hL hκ ih hf hME,
      fun _ => L.calleeTryOk hL hκ ih hf hME,
      fun ht => L.tlsOk_hooks (hL.baseTls f hf (hasTls_of_vcode_pipeline hc ht) L.F (κ M f)),
      hME.body⟩
    exact armRefinesAbi_of_actRet hus hlen hhold hmemR hret

/-- `backend_correct_program_budget` with the ABI return values (`sretStableB f`). -/
theorem backend_correct_program_budget_abi (L : LinkSys) (hL : L.Ok)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (hS : sretStableB f = true) (M : Nat) {ra : BitVec 64}
    {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) :
    ArmRefinesAbi (L.A f).fb (L.A f).base ra (L.mach M f) s (sretArg f args)
      (Clif.runLoop L.base L.P (M + 1) cs) := by
  haveI := L.crunOk_std hL
  rw [← L.mach_std]
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  refine backend_correct_program_core_abi L.std (hL.withCrun _) hκ hf hS M hent hres hF hgfree
    himg hbe hargs hcs hsav hrel hpl htr fun ho => ?_
  exact Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf) (E := L.std.envR M f)
    rfl rfl (fun _ hn => L.std.envR_of (.inl hn))
    (L.std.envR_link hL.names) (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ <;> rw [ho] <;> exact fun _ h => nomatch h)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ <;> rw [ho] <;> exact fun h => nomatch h)

/-- `backend_correct_program_stack` with the ABI return values (`sretStableB f`). -/
theorem backend_correct_program_stack_abi (L : LinkSys) (hL : L.Ok)
    {κ : Nat → Clif.Function → Nat}
    (hκ : L.Budget κ) {f : Clif.Function} (b : Nat) (hb : ∀ M, κ M f = b)
    (hf : f ∈ L.P.funcs) (hS : sretStableB f = true) (M : Nat) {ra : BitVec 64}
    {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s)
    (hroom : frameDrop (L.A f).af + b ≤ (spv s).toNat)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + b) (spv s) a)
    (hF : L.F = frameWG b (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) :
    ArmRefinesAbi (L.A f).fb (L.A f).base ra (L.mach M f) s (sretArg f args)
      (Clif.runLoop L.base L.P (M + 1) cs) := by
  have hd := L.frameDrop_eq hL hf
  have hres : StackAvail b (L.A f).af s := by
    unfold StackAvail
    rw [show (L.A f).af.frameSize + 16 + b = frameDrop (L.A f).af + b by omega]
    refine stackRoom_of hroom fun a ha => hgfree a (hL.imgAddr f hf a ?_)
    simpa [CodeAddr, hent.program] using ha
  rw [← hb M] at hres hF hgfree
  exact backend_correct_program_budget_abi L hL hκ hf hS M hent hres hF hgfree himg hbe hargs hcs
    hsav hrel hpl htr

end E2E

namespace E2E.DeadCleanupBinary
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck
open Backend.Proof.Driver (sretStableB)

/-- `binary_correct` with the ABI return values (`sretStableB f`): the linked machine's return
also leaves `sretArg f args` after the CLIF results, in x8. -/
theorem binary_correct_abi {I : LinkInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} (hn : DeadCleanupStackBound.goodN I n = true)
    {f : Clif.Function} (hf : (prog I).func? n = some f) (hS : sretStableB f = true)
    (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefinesAbi (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (sretArg f args) (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    ∀ a, (modelOf I f r).mem a ≠ r.mem a → R a := by
  refine ⟨?_, (binary_correct hbin B hB hn hf M hX ho hr htr).2⟩
  have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) :=
    baseOk_F hB
  have himgF : ∀ a, (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)).Img a →
      worldF I f (DeadCleanupStackBound.bud I f) r a := fun _ h => .inr h
  have hL := okBCleanup_sound hbin.ok hB' himgF
  have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h =>
    hX a b (hbin.data a b h).1 (hbin.data a b h).2
  obtain ⟨hent, -, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
    premises hL (Clif.Program.func?_some hf).1 hro ho hr
  rw [mach_F I B (fun _ => False) (worldF I f (DeadCleanupStackBound.bud I f) r)]
  have hf' : (progOf I.resultsCleanup).func? n = some f := hf
  have hn' := hn
  unfold DeadCleanupStackBound.goodN at hn'
  rw [hf'] at hn'
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn'
  have hbud : DeadCleanupStackBound.bud I f = b := by simp [DeadCleanupStackBound.bud, hb]
  exact backend_correct_program_stack_abi _ hL (DeadCleanupStackBound.budget_of hbin.ok B _)
    (DeadCleanupStackBound.bud I f) (fun M => by simp [LinkSys.hybrid, hb, hbud])
    (Clif.Program.func?_some hf).1 hS M hent (by rw [spv_modelOf]; exact ho.stack) hgfree rfl himg
    hbe hargs hr.entry hsav hrel hpl htr

/-- `binary_correct_of_checks` with the ABI return values (`sretStableB f`). -/
theorem binary_correct_of_checks_abi {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okBCleanup I = true) (hbin : DeadCleanupBinCheck.BinOk I D file) (B : BaseEnv)
    (hB : BaseOk (sys I B))
    {n : String} (hn : DeadCleanupStackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (hS : sretStableB f = true) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefinesAbi (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (sretArg f args) (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    ∀ a, (modelOf I f r).mem a ≠ r.mem a → DeadCleanupBinCheck.RelocAt I a :=
  binary_correct_abi (binFacts_of_checks hI hbin) B hB hn hf hS M hX ho hr htr

end E2E.DeadCleanupBinary

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck Elf
open Backend.Proof.Driver (sretStableB)

/-- **`ExecRefines` with the ABI return values** `rets` after the CLIF ones (as `ArmRefinesAbi`
for `ArmRefines`): the CLIF values in x0.., the ABI return values in x8. Restated for #587 with
`ArmRefinesAbi`: it put them in x0.. after the CLIF values, true of the backend before #587
(`mov x0, x8` before `ret`); Cranelift returns the `sret` pointer in x8 on aarch64. -/
def ExecRefinesAbi (fb : FnBin) (base ra : BitVec 64) (astep : Arm.ArmState → Arm.ArmState)
    (s : Arm.ArmState) (R : BitVec 64 → Prop) (rets : List Clif.Val) : Clif.Outcome → Prop
  | .returned vals cm => ∃ n, ArmRet ra s (runX astep n s) ∧
      (∀ (j : Nat) v, (vals ++ rets)[j]? = some v →
        XHolds v (xreg (if j < vals.length then j else 8) (runX astep n s))) ∧
      ∀ a b, cm.valid a 1 = true → cm.bytes a = some b → ¬ R (BitVec.ofNat 64 a) →
        Arm.read_mem (BitVec.ofNat 64 a) (runX astep n s) = b
  | .trapped c => ∃ n, TrapAt fb base c (runX astep n s)
  | .stuck _ | .outOfFuel => True

theorem ExecRefinesAbi.execRefines {fb : FnBin} {base ra : BitVec 64}
    {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {R : BitVec 64 → Prop}
    {rets : List Clif.Val} {o : Clif.Outcome} (h : ExecRefinesAbi fb base ra astep s R rets o) :
    ExecRefines fb base ra astep s R o := by
  cases o with
  | returned vals cm =>
    obtain ⟨n, hret, hx, hm⟩ := h
    have hjv := fun j (v : Clif.Val) (hj : vals[j]? = some v) => (List.getElem?_eq_some_iff.mp hj).1
    refine ⟨n, hret, fun j v hj => ?_, hm⟩
    have := hx j v (by rw [List.getElem?_append_left (hjv j v hj)]; exact hj)
    rwa [if_pos (hjv j v hj)] at this
  | trapped c => exact h
  | _ => trivial

section Transfer

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- `exec_of_modelN` with the ABI return values. -/
theorem exec_of_modelN_abi (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat}
    {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) {r : Arm.ArmState} (hpc : Arm.r .PC r = (art I f).base)
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 r ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → E2E.DeadCleanupBinCheck.RelocAt I a)
    (hrun : RunOkSN I B file M f (modelOf I f r)) {rets : List Clif.Val} {o : Clif.Outcome}
    (h : ArmRefinesAbi (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f)
      (modelOf I f r) rets o) :
    ExecRefinesAbi (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (E2E.DeadCleanupBinCheck.RelocAt I) rets o := by
  cases o with
  | returned vals cm =>
    have hFf := hF f hf
    have hsim := sim_modelOf hd
    have hra' : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      simp only [xreg, r_modelOf]; exact hra
    have hpc' : Arm.r .PC (modelOf I f r) = (art I f).base := by rw [r_modelOf]; exact hpc
    have hsimN := act_simN (B := B) hF M f _ r hf hpc' hsim hrun
    obtain ⟨n, hret, hx, hmem⟩ := h
    obtain ⟨k', hk'⟩ := hsimN n (no_return hFf hra' hret.err) (fun hs => by
      obtain ⟨k, hk, he⟩ := second_code hFf hs
      exact hra k hk (by rw [← he, hret.pc])) hret.err
    refine ⟨k', ⟨?_, ?_, ?_, fun n hn => ?_, fun n h8 h16 => ?_⟩, fun j v hv => ?_,
      fun a b hv hb hR => ?_⟩
    · rw [hk'.1, hret.pc]
    · rw [hk'.1, hret.err]
    · simp only [spv]; rw [hk'.1]; exact (hret.sp.trans (spv_modelOf I f r))
    · simp only [xreg]; rw [hk'.1]; exact (hret.savedX n hn).trans (r_modelOf I f r _)
    · rw [hk'.1, hret.savedV n h8 h16, r_modelOf]
    · simp only [xreg]; rw [hk'.1]; exact hx j v hv
    · show Arm.read_store _ _ = b
      rw [show Arm.read_store (BitVec.ofNat 64 a) (runX (step I B file) k' r).mem =
        (runX (step I B file) k' r).mem (BitVec.ofNat 64 a) from rfl, hk'.2 _ hR]
      exact hmem a b hv hb
  | trapped c0 => exact exec_of_modelN hF hf hpc hra hd hrun h.armRefines
  | stuck _ => trivial
  | outOfFuel => trivial

end Transfer

/-- `binary_correct_exec_staticN` with the ABI return values (`sretStableB f`). -/
theorem binary_correct_exec_staticN_abi {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray}
    (hI : okBCleanup I = true) (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B)
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f) (hS : sretStableB f = true)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f)
    (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hrun : RunOkN I B file M f (modelOf I f r)) :
    ExecRefinesAbi (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (E2E.DeadCleanupBinCheck.RelocAt I) (sretArg f args)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (DeadCleanupStackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  obtain ⟨h1, h2⟩ := binary_correct_of_checks_abi hI hbin B hB hn hf hS M hX ho hr htr
  have hfm := (Clif.Program.func?_some hf).1
  have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) :=
    baseOk_F hB
  have hL := okBCleanup_sound hI hB' fun _ h => .inr h
  have hfacts := binFacts_of_checks hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premises hL hfm hro ho hr
  have hL' := okBCleanup_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
  have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
  exact exec_of_modelN_abi hF hfm (by rw [← r_modelOf I f r]; exact hent.pc) hent.raOutside h2
    (runOkSN_of_n hI hcm hF hH hfm hrun) h1

/-- `binary_correct_exec_of_reads` with the ABI return values (`sretStableB f`). -/
theorem binary_correct_exec_of_reads_abi {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B)
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f) (hS : sretStableB f = true)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f)
    (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hreads : RunReadsN I B file M f (modelOf I f r)) :
    ExecRefinesAbi (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (E2E.DeadCleanupBinCheck.RelocAt I) (sretArg f args)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (DeadCleanupStackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  obtain ⟨-, -, hG⟩ := binary_correct_of_checksX hI hbin B hB hn hf M hX ho hr htr
  by_cases hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)
  · have hfm := (Clif.Program.func?_some hf).1
    have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) :=
      baseOk_F hB
    have hL := okBCleanup_sound hI hB' fun _ h => .inr h
    have hfacts := binFacts_of_checks hI hbin
    have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
      hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
    obtain ⟨hent, -⟩ := premises hL hfm hro ho hr
    have hL' := okBCleanup_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
    have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
    have hra : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      simp only [xreg, r_modelOf]; exact hent.raOutside
    exact binary_correct_exec_staticN_abi hI hcm hbin B hB hH hf hS hc M hX ho hr htr
      (runOkN_of_good hI hcm hF (fun g hg => destsInt_of_ok hL' hg) hfm hra (hG hout) hreads)
  · cases h : Clif.runLoop B.env (prog I) (M + 1) cs with
    | returned vals cm => exact absurd (.inl ⟨vals, cm, h⟩) hout
    | trapped c => exact absurd (.inr ⟨c, h⟩) hout
    | stuck _ => trivial
    | outOfFuel => trivial

/-- `binary_correct_exec_of_insn` with the ABI return values (`sretStableB f`). -/
theorem binary_correct_exec_of_insn_abi {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hS : sretStableB f = true)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f)
    (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hins : RunInsnN I B file M f (modelOf I f r)) :
    ExecRefinesAbi (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (E2E.DeadCleanupBinCheck.RelocAt I) (sretArg f args)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (DeadCleanupStackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  by_cases hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)
  · obtain ⟨-, -, hG⟩ := binary_correct_of_checksX hI hbin B hB hn hf M hX ho hr htr
    have hgS := runGood_sysS hI hbin hB hn hf M hX ho hav hr htr hout
    have hfm := (Clif.Program.func?_some hf).1
    have hL' := okBCleanup_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
    have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
    have hent : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      have hB'' : BaseOk (LinkSys.ofInputCleanup I B
          (worldF I f (DeadCleanupStackBound.bud I f) r)) := baseOk_F hB
      have hL0 := okBCleanup_sound hI hB'' fun _ h => .inr h
      have hfacts := binFacts_of_checks hI hbin
      have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
        hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
      obtain ⟨he, -⟩ := premises hL0 hfm hro ho hr
      simp only [xreg, r_modelOf]; exact he.raOutside
    refine binary_correct_exec_of_reads_abi hI hcm hbin B hB hH hf hS hc M hX ho hr htr
      fun M' g t hR he => ⟨hins M' g t hR he, ?_⟩
    obtain ⟨c', hRL, -⟩ := reachL_of_reachN hI hcm hF hR hfm (hG hout)
      (raNotSecond_top (hF f hfm) hent)
    have hRL' : (sysS I B f r (GotSlot I file)).ReachL M f (modelOf I f r) M' g c' t := by
      exact LinkSys.reachL_extImg
        (F := worldFS I f (DeadCleanupStackBound.bud I f) r (GotSlot I file))
        (S := GotSlot I file) (m := (modelOf I f r).mem)
        (E2E.DeadCleanupBinary.reachL_F (F := worldF I f (DeadCleanupStackBound.bud I f) r)
          (F' := fun _ => False) hRL)
    have hg := reachN_mem hR hfm
    exact got_of_good hI hbin hgot hX hg (hF g hg)
      (hgS _ _ _ _ hRL' (by rw [mach_sysS]; exact he))
  · cases h : Clif.runLoop B.env (prog I) (M + 1) cs with
    | returned vals cm => exact absurd (.inl ⟨vals, cm, h⟩) hout
    | trapped c => exact absurd (.inr ⟨c, h⟩) hout
    | stuck _ => trivial
    | outOfFuel => trivial

/-- `binary_correct_exec_proven` with the ABI return values (`sretStableB f`): the executable
machine's return also leaves `sretArg f args` after the CLIF results, in x8. -/
theorem binary_correct_exec_proven_abi {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hS : sretStableB f = true)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f)
    (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ExecRefinesAbi (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (E2E.DeadCleanupBinCheck.RelocAt I) (sretArg f args)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (DeadCleanupStackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  obtain ⟨-, -, hG⟩ := binary_correct_of_checksX hI hbin B hB hn hf M hX ho hr htr
  by_cases hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)
  · have hfm := (Clif.Program.func?_some hf).1
    have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) :=
      baseOk_F hB
    have hL := okBCleanup_sound hI hB' fun _ h => .inr h
    have hfacts := binFacts_of_checks hI hbin
    have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
      hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
    obtain ⟨hent, -⟩ := premises hL hfm hro ho hr
    have hL' := okBCleanup_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
    have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
    have hra : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      simp only [xreg, r_modelOf]; exact hent.raOutside
    refine binary_correct_exec_of_insn_abi hI hcm hbin hgot B hB hH hf hS hc M hX ho hav hr htr
      fun M' g t hR he => ?_
    obtain ⟨c', hRL, -⟩ := reachL_of_reachN hI hcm hF hR hfm (hG hout)
      (raNotSecond_top (hF f hfm) hra)
    exact insn_of_good hI hcm hF (reachN_mem hR hfm) (hG hout _ _ _ _ hRL he)
  · cases h : Clif.runLoop B.env (prog I) (M + 1) cs with
    | returned vals cm => exact absurd (.inl ⟨vals, cm, h⟩) hout
    | trapped c => exact absurd (.inr ⟨c, h⟩) hout
    | stuck _ => trivial
    | outOfFuel => trivial

end E2E.DeadCleanupExecBytes
