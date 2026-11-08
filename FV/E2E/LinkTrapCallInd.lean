import FV.E2E.LinkTrapCall
import FV.E2E.WorldTrapStop
import FV.E2E.RegLevelTrapCallTry

/-! # Callee traps in the linked program: the induction and the program theorem (S9c, #376)

The trap counterpart of the linking induction of `FV/E2E/LinkArm.lean`: an activation of a
function of the linked program whose run traps under the run premise `LinkSys.TrapsD` has the
trap observable `LinkSys.TrapIn` (`FV/E2E/LinkTrapCall.lean`) on the linked machine.

* `LinkSys.TrapsOk`: the per-function facts the trap theorem needs beyond `LinkSys.Ok`: every
  function compiled by the shipped dead-cleanup pipeline (`CompiledCleanup`), passing the
  lowering's unwinding validator (`lowerCheckU`, decided by `lean-link`), without `try_call`
  terminators (their callee traps are S9b, #375).
* `LinkSys.thmT_of`, `LinkSys.thmT`: the induction (`ThmT κ M` from `ThmT κ (M - 1)`): the
  per-function theorem `backend_correct_world_cleanup_trapstop` for the activation's environment
  with the uncovered program callee traps made stuck (`cutEnv`), whose trapping callees' contract
  is `LinkSys.xTrapsOk` (from `ThmT κ (M - 1)`); at a callee-trap state the call goes outside `P`
  (`BaseTrapCall`, the base hook errs, `BaseTrapsOk.stop`) or to a function of `P` whose
  activation from that state has the observable one level down (`progCallT`), so its linked call
  is `junkAt`.
* **`E2E.backend_correct_program_trap_budget`**, `backend_correct_program_trap`,
  `backend_correct_program_trap_peak`: the whole-program run of `f` that traps with `c` under
  the run premise is matched by the linked machine's `TrapIn` (instead of `ArmRefines`' trap
  clause, a trap site of `f` only, under `TrapsExplicit`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

theorem destOf_eq_callDest (info : CallInfo) : destOf info = callDest info := by
  unfold destOf callDest; rfl

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The program's functions as the trap theorem needs them** (beyond `LinkSys.Ok`, all decided
by the compiler): compiled by the shipped dead-cleanup pipeline, passing the lowering's
unwinding validator, without `try_call` terminators. -/
structure TrapsOk : Prop where
  cleanup : ∀ g ∈ L.P.funcs, CompiledCleanup g (L.A g).k (L.A g).vc (L.A g).vcp (L.A g).rf
    (L.A g).af (L.A g).fa (L.A g).fb
  lowerU : ∀ g ∈ L.P.funcs, lowerCheckU g (L.A g).vc = true
  noTry : ∀ g ∈ L.P.funcs, ∀ B ∈ g.blocks, B.term.isTry = false

/-! ## The call at a callee-trap state -/

/-- At a call line of `g`'s code the linked machine's step is the hooked call. -/
theorem mach_callAt (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {u : Arm.ArmState} {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) {regs : Array Reg}
    {i' : MInst} (hprog : u.program = (L.A g).fb.program (L.A g).base)
    (hasg : (MInst.call info).assign regs = .ok i')
    (hca : CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) i') :
    L.mach M g u = (L.hooks M).call (destOf info) u := by
  have hc := hL.compiled g hg
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨j, x, t, hj, hx, hpc⟩ := hca
  obtain ⟨_, w, -, hk⟩ := FnAsm.layout_word hc.layout hlm hj rfl
  have hne : (L.A g).fb.words.toList ≠ [] := by
    intro h
    have : (L.A g).fb.words.size = 0 := by simpa using congrArg List.length h
    simp [this] at hk
  have hb : progBase u = (L.A g).base := progBase_eq (by rw [hprog]; rfl) hne
  have hsum := layout_sum hc.layout
  have hfit := hL.fits g hg
  have hins : insnAt (L.A g).fa (progBase u) (Arm.r .PC u) = some x := by
    rw [hb, hpc]; exact insnAt_line (by omega) hj
  cases hd : info.dest with
  | sym n =>
    obtain ⟨d, us, ds⟩ := info
    simp only at hd
    subst hd
    obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    simp only [mach, ArmStepX, hins, destOf]
  | reg r =>
    obtain ⟨tv, Lu, Ld, rfl, -⟩ := hL.blrRegs g hg info hsite (fun n => by rw [hd]; simp)
    obtain ⟨r0, us', ds', -, rfl⟩ := assign_call_reg hasg
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    simp only [mach, ArmStepX, hins, destOf]

/-- At a call line of `g`'s code: the instruction there is the allocated call's. -/
theorem insnAt_callAt (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs) {u : Arm.ArmState}
    {i' : MInst} (hca : CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) i') :
    ∃ x, insnAt (L.A g).fa (L.A g).base (Arm.r .PC u) = some x ∧ i'.callInsn? = some x := by
  have hc := hL.compiled g hg
  obtain ⟨j, x, t, hj, hx, hpc⟩ := hca
  have hsum := layout_sum hc.layout
  have hfit := hL.fits g hg
  exact ⟨x, by rw [hpc]; exact insnAt_line (by omega) hj, hx⟩

/-- **`ProgCallOk` at a `bl h`.** -/
theorem progCallOk_bl (hL : L.Ok) {g h : Clif.Function} (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    {u : Arm.ArmState} {info : CallInfo} {regs : Array Reg} {i' : MInst} {n : String}
    (hd : info.dest = .sym n) (hasg : (MInst.call info).assign regs = .ok i')
    (hP : CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) i')
    (hcode : ∀ a, L.Img a → u.mem a = L.imgMem a) : L.ProgCallOk g h u := by
  obtain ⟨x, hins, hx⟩ := L.insnAt_callAt hL hg hP
  obtain ⟨d, us, ds⟩ := info
  simp only at hd
  subst hd
  obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
  simp only [MInst.callInsn?, Option.some.injEq] at hx
  subst hx
  refine ⟨hh, hcode, fun x' h' => ?_, fun x' h' h1 _ => ?_⟩
  · rw [hins] at h'; cases h'
  · rw [hins] at h1; cases h1

/-- **`ProgCallOk` at a `blr` of `h`** (through the vreg `tv` by which `g` may enter `h`). -/
theorem progCallOk_blr (hL : L.Ok) {g h : Clif.Function} (hg : g ∈ L.P.funcs)
    (hh : h ∈ L.P.funcs) {u : Arm.ArmState} {info : CallInfo} {regs : Array Reg} {i' : MInst}
    {tv : Nat} (hsite : (L.A g).vcp.CallSite info) (hd : info.dest = .reg (.vreg tv .int))
    {c : CheckCtx} {wh : String} {ops : Array Operand}
    (hst : c.checkStatic wh ops (regs.map .reg) (MInst.call info).clobbers = .ok ())
    (hasg : (MInst.call info).assign regs = .ok i')
    (hP : CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) i')
    (hcode : ∀ a, L.Img a → u.mem a = L.imgMem a)
    (hb : (blrTarget u).bind (symCallee L.Xb L.P) = some h) (hBlr : L.BlrTo g tv h) :
    L.ProgCallOk g h u := by
  obtain ⟨x, hins, hx⟩ := L.insnAt_callAt hL hg hP
  obtain ⟨d, us, ds⟩ := info
  simp only at hd
  subst hd
  obtain ⟨r0, us', ds', -, rfl⟩ := assign_call_reg hasg
  simp only [MInst.callInsn?, Option.some.injEq] at hx
  subst hx
  refine ⟨hh, hcode, fun x' h' => ?_, fun x' h' h1 h2 => ?_⟩
  · rw [hins] at h'
    cases h'
    exact callDest_ne_xzr (fun r e => by cases e; exact ⟨tv, rfl⟩) hst hasg rfl
  · rw [hb] at h2
    cases h2
    exact ⟨_, tv, hsite, rfl, hBlr⟩

/-- **A `bl` call site of a function `h` of `P`**: its operand values are `h`'s parameter
registers' values. -/
theorem blSite (hL : L.Ok) {g h : Clif.Function} (hg : g ∈ L.P.funcs) {info : CallInfo}
    (hsite : L.ProgSite g info h) {u : Arm.ArmState} {c : CheckCtx} {wh : String}
    {ops : Array Operand} {regs : Array Reg}
    (hops : (MInst.call info).operands = .ok ops)
    (hst : c.checkStatic wh ops (regs.map .reg) (MInst.call info).clobbers = .ok ()) :
    ∃ Lu : List (Nat × Reg), Lu.map (·.2) = regLocs h.sig ∧
      useVals ops regs u = Lu.map (fun q => regVal u q.2) := by
  have ⟨_, n, hdest, hpf⟩ := hsite
  obtain ⟨n', Lu, Ld, hinfo, hLu, -⟩ := hL.callRegs g hg info h hsite
  subst hinfo
  cases hdest
  rw [operands_call_sym] at hops
  cases hops
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
  have hregs := callRegs_eq (regs := regs) (by simpa using hsz')
    (fun p hp r hr => (hloc p hp).2 r hr)
  exact ⟨Lu, hLu, call_useVals hregs u⟩

/-- **A `blr` call site**: the target register, the parameter registers of the functions of `P`
it may enter, the operand values, and the target the machine reads. -/
theorem blrSite (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs) {info : CallInfo}
    (hsite : (L.A g).vcp.CallSite info) (hreg : ∀ n, info.dest ≠ .sym n) {u : Arm.ArmState}
    {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg} {i' : MInst}
    (hops : (MInst.call info).operands = .ok ops)
    (hst : c.checkStatic wh ops (regs.map .reg) (MInst.call info).clobbers = .ok ())
    (hasg : (MInst.call info).assign regs = .ok i')
    (hP : CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) i')
    (hcode : ∀ a, L.Img a → u.mem a = L.imgMem a) :
    ∃ (tv : Nat) (Lu : List (Nat × Reg)) (Ld : List (Reg × Nat)) (n0 : Nat),
      info = ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩ ∧
      (∀ h ∈ L.P.funcs, L.BlrTo g tv h → (regLocs h.sig).length = Lu.length →
        Lu.map (·.2) = regLocs h.sig) ∧
      useVals ops regs u = regVal u (.x n0) :: Lu.map (fun q => regVal u q.2) ∧
      blrTarget u = some (lo64 (regVal u (.x n0))) ∧
      ops = (tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray := by
  obtain ⟨tv, Lu, Ld, rfl, hregs⟩ := hL.blrRegs g hg info hsite hreg
  rw [operands_call_reg] at hops
  cases hops
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
  obtain ⟨r0, hregs0⟩ := callRegs_eq_reg (regs := regs) (by simpa using hsz')
    (fun p hp r hr => (hloc p hp).2 r hr)
  obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
    have hmem : (tgtOp tv, Loc.reg r0) ∈
        (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
      simp [Array.toList_zip, Array.toList_map, hregs0]
    obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
    exact ⟨n, hn, h29, h16⟩
  obtain ⟨r1, us', ds', hr1, rfl⟩ := assign_call_reg hasg
  have h0 : regs[0]? = some (.x n0) := by
    rw [← Array.getElem?_toList, hregs0]; rfl
  rw [h0] at hr1
  cases hr1
  have hc := hL.compiled g hg
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have htgt : blrTarget u = some (lo64 (regVal u (.x n0))) := by
    obtain ⟨j, x, tt, hj, hx, hpc⟩ := hP
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    rw [lo64_regVal_x]
    exact blrTarget_of hc.layout hlm hj hn0 hpc
      (fun k wd hk => hL.imgCode g hg u hcode k wd hk)
  exact ⟨tv, Lu, Ld, n0, rfl, fun h hh hb hl => (hregs h hh hb hl).1, call_useVals_reg hregs0 u,
    htgt, rfl⟩

/-- A caller state whose parameter registers of `h` hold the call's arguments is compatible with
the canonical call state (`CallerOk`). -/
theorem callerOk_of_regs (hL : L.Ok) {h : Clif.Function} (hh : h ∈ L.P.funcs)
    {F : BitVec 64 → Prop} {u w : Arm.ArmState} {Lu : List (Nat × Reg)}
    (hLu : Lu.map (·.2) = regLocs h.sig) (hsw : SameWorld F u w)
    (himg : ∀ a, L.Img a → u.mem a = L.imgMem a) (hra : RaOk (L.A h) (Arm.r .PC u)) :
    L.CallerOk F h (Lu.map (fun q => regVal u q.2)) w u := by
  obtain ⟨hnd, harg, -⟩ := hL.argRegs h hh
  refine ⟨hsw, himg, fun r hr => ?_, hra⟩
  rw [← hLu] at hr
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
  have hrA : r.isArgReg = true := harg r (by rw [← hLu]; exact List.mem_of_getElem? hj)
  have hu : (Lu.map (fun q => regVal u q.2))[j]? = some (regVal u r) := by
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hj
    obtain ⟨q, hq, rfl⟩ := hj
    simp [hq]
  rw [L.regVal_canon _ _ _ hrA, placeArgs_regVal _ _ _ hnd harg (by rw [← hLu]; exact hj) hu,
    setVal_regVal]

/-! ## The induction step -/

/-- **A callee-trap state of an activation at depth `M`** (the per-function theorem's
`CallTrapAtT`, at a call site of either kind, under the activation's environment with the callee
traps outside `covQ Dn` stuck, `Dn` the run premise `D` one level down): the call goes outside
`P` and its callee traps there (the base hook errs, `BaseTrapsOk.stop`), or it goes to a function
`h` of `P` whose activation from the call state has the trap observable one level down
(`progCallTG`; its linked call is `junkAt`). Either way the run stops (`hstop`). -/
theorem trapIn_callTrapG (hL : L.Ok) [hR : L.CrunOk] (hB : L.BaseTrapsOk) (hκ : L.Budget κ)
    {D : Nat → Clif.Function → Clif.State → Prop} {Dn : Clif.Function → Clif.State → Prop}
    {M : Nat} (hDnM : ∀ {h : Clif.Function} {cs : Clif.State}, Dn h cs → ∃ M', M = M' + 1 ∧ D M' h cs)
    (ih : 0 < M → L.ThmTG D κ (M - 1)) {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {F G : BitVec 64 → Prop} {vals : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState}
    {ra : BitVec 64} {s : Arm.ArmState} (hWE : L.WorldEntry κ M g F vals cs w₀)
    (hME : L.MachEntry κ M g F G ra s w₀) {n : Nat} {tc : Clif.TrapCode}
    (hstop : Arm.r .ERR (L.mach M g (runX (L.mach M g) n s)) ≠ .None → L.Stop M g s n)
    (hprog : (runX (L.mach M g) n s).program = (L.A g).fb.program (L.A g).base)
    (hct : CallTrapAtT (L.A g).vcp F (κ M g) G s (L.A g).fa (L.A g).base (L.X κ M g F)
      (GotV (L.A g).vcp)
      (TrapCallSem (cutEnv (L.envOf M g (spv w₀)) (L.covQ Dn)) (g.externs.map (·.2))
        (indSigs g)
        (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
          g (spv w₀)) (L.X κ M g F) tc)
      (runX (L.mach M g) n s)) :
    L.TrapIn M g s tc := by
  obtain ⟨info, hsite, -, -, hGk, cc, wh, ops, regs, i', w, hops, hst, hasg, hP, hsw,
    -, herr, hgg, hX0, hdisj⟩ := hct
  generalize hu : runX (L.mach M g) n s = u at hstop hprog hGk hP hsw herr hgg hX0 hdisj
  have hcode : ∀ a, L.Img a → u.mem a = L.imgMem a := fun a ha =>
    (hGk a (hME.imgG a ha)).trans (hME.imgS a ha)
  have hstep := L.mach_callAt (M := M) hL hg hsite hprog hasg hP
  rcases hdisj with ⟨ext, hin, G', sl, cm, args, vals', hG', hd, hargs, hmr, htr'⟩ |
    ⟨sig, hsig, nm, G', sl, cm, u0, args, vals', hG', hsg, hu0, hl8, hall, hmr, htr', hty, hdn, hus⟩
  · -- an extern of `g` (`bl`, or `blr` of its GOT address)
    obtain ⟨Gb, hGb, rfl⟩ := cutEnv_extern hG'
    obtain ⟨htrG, hQ⟩ := cutO_trapped htr'
    cases hpf : L.P.func? ext.name with
    | none =>
      have hbase : L.base.extern ext.name = some Gb := by
        simpa [envOf, hpf, Clif.linkEnvR_none hpf] using hGb
      have hsn : symCallee L.Xb L.P (lo64 (ofX ((L.X κ M g F).sym ext.name 0))) = none := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = none
        rw [lo64_ofX]; exact (L.find_sym hL ext.name).2 hpf
      have hX0' : L.Xb.call (callDest info) (useVals ops regs u) w = none := by
        rcases hd with ⟨hd1, hd2⟩ | ⟨hd1, -, hd2⟩
        · rw [hd1] at hX0 ⊢; rwa [L.X_base hpf] at hX0
        · rw [hd1, hd2] at hX0 ⊢; rwa [L.X_none hsn] at hX0
      have hgb : L.GoesBase info u := by
        refine ⟨?_, fun hdn => ?_⟩
        · rcases hd with ⟨hd1, -⟩ | ⟨hd1, -, -⟩
          · exact .inr ⟨ext.name, by rw [destOf_eq_callDest, hd1], hpf⟩
          · exact .inl (by rw [destOf_eq_callDest, hd1])
        · have hreg : ∀ nm, info.dest ≠ .sym nm := fun nm e => by
            simp [destOf, e] at hdn
          obtain ⟨tv, Lu, Ld, n0, -, -, huv, htgt, -⟩ :=
            L.blrSite hL hg hsite hreg hops hst hasg hP hcode
          rcases hd with ⟨hd1, -⟩ | ⟨-, -, hd2⟩
          · rw [← destOf_eq_callDest, hdn] at hd1; cases hd1
          · rw [huv] at hd2
            obtain ⟨h1, -⟩ := List.cons.inj hd2
            rw [htgt, h1]
            exact hsn
      have hBT : L.BaseTrapCallI g tc info u := ⟨hsite, hgb, herr, ops, regs, i', w, F, _, _,
        spv w₀, hops, hasg, hP, hsw, hX0', .inl ⟨ext, List.mem_filter.mpr ⟨hin, by simp [hpf]⟩, Gb,
        sl, cm, args, vals', hbase, hd, hargs, hmr, htrG⟩⟩
      refine .base (hstop ?_) (by rw [hu]; exact ⟨info, hBT⟩)
      rw [hstep, L.hooks_base hgb.1 u hgb.2]; exact hB.stop g hg tc info u hBT
    | some h =>
      obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
      obtain ⟨hdecl, G0, hG0, hGt⟩ := L.envOf_prog hGb hpf
      obtain ⟨hpl, ht0⟩ := hGt _ _ _ htrG
      obtain ⟨cs', hinit, hret⟩ := L.linkEnvR_trap hpf hG0 ht0
      obtain ⟨M', rfl, hDn⟩ := hDnM (hQ h cs' hpf hinit)
      have hsav := L.stackArgsAvoid_decl hL hg hin hpf hinit hmr
      rw [hL.declSig g hg ext hin h hpf] at hargs
      rw [← hname] at hinit
      have hcallee : L.Callee g h := .inr (.inl ⟨ext, hin, hpf⟩)
      obtain ⟨⟨hmemR0, -, -⟩, hspw, herrw⟩ := hmr
      have hbs : frameDrop (L.A h).af + κ M' h ≤ κ (M' + 1) g := hκ.1 M' g hg h hcallee
      have hroom' : frameDrop (L.A h).af + κ M' h ≤ (spv w).toNat := by
        rw [hspw]; have := hWE.room; omega
      have hdead' : ∀ a, StackBelow (frameDrop (L.A h).af + κ M' h) (spv w) a →
          F a ∧ ¬ L.Img a := fun a ha =>
        hWE.dead a (by rw [← hspw]; exact stackBelow_mono ha hbs)
      have hal' : (spv w).toNat % 16 = 0 := by rw [hspw]; exact hWE.align
      have hpl' : L.NeedSlots → L.PlaceAt cm (spv w) := fun hN => by rw [hspw]; exact hpl hN
      have hpfh := func?_of_mem hL.names hh
      rcases hd with ⟨hd1, hd2⟩ | ⟨hd1, hcol, hd2⟩
      · -- `bl h`
        have hdest : info.dest = .sym ext.name := by
          cases hi : info.dest with
          | sym nm => simp [callDest, hi] at hd1; rw [hd1]
          | reg r => simp [callDest, hi] at hd1
        have hps : L.ProgSite g info h := ⟨hsite, ext.name, hdest, hpf⟩
        obtain ⟨Lu, hLu, huv⟩ := L.blSite hL hg hps hops hst (u := u)
        have hra := hL.raCall g hg info h hps _ hP.callPc
        have hcOk := L.callerOk_of_regs hL hh hLu hsw hcode hra
        rw [← huv, hd2] at hcOk
        have hTI : L.TrapIn M' h (enterAt (L.A h) u) tc := L.progCallTG hL (Nat.succ_pos M')
          (ih (Nat.succ_pos M')) hpfh ⟨g, hg, hcallee⟩
          hWE.img herrw hal' hroom' hdead' (hκ.2 _ h hh) hmemR0 hargs hsav hpl' hinit hret hDn u hcOk
        have hjunk := L.pcall_junk hL hh hTI hra
        have hhook : (L.hooks (M' + 1)).call (destOf info) u = L.pcall (M' + 1) h u := by
          rw [destOf_eq_callDest, hd1]; exact L.hooks_some hpf u
        refine .prog (hstop ?_) (by rw [hu]; exact ⟨info, regs, i', hsite, hasg, hP, herr,
          .inl (by rw [destOf_eq_callDest, hd1, hname])⟩)
          (by rw [hu]; exact L.progCallOk_bl hL hg hh hdest hasg hP hcode)
          (by rw [hu]; exact hra) (by rw [hu]; exact hTI)
        rw [hstep, hhook, hjunk]; exact junkAt_err u
      · -- `blr` of `h`'s GOT entry
        have hreg : ∀ nm, info.dest ≠ .sym nm := fun nm e => by simp [callDest, e] at hd1
        obtain ⟨tv, Lu, Ld, n0, hinfo, hLuB, huv, htgt, hops'⟩ :=
          L.blrSite hL hg hsite hreg hops hst hasg hP hcode
        rw [huv] at hd2
        obtain ⟨h1, h2⟩ := List.cons.inj hd2
        have hs : symCallee L.Xb L.P (lo64 (regVal u (.x n0))) = some h := by
          rw [h1]
          show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = some h
          rw [lo64_ofX]; exact (L.find_sym hL ext.name).1 h hpf
        have hgot : ∀ nm, GotV (L.A g).vcp tv nm → nm = h.name := by
          intro nm hn
          have e := hgg tv nm ops (by rw [hinfo]) hn hops (by rw [hops']; simp [tgtOp, Operand.isUse])
          rw [huv] at e
          simp only [List.head?_cons, Option.map_some, Option.some.injEq] at e
          exact L.got_target hL hs e
        have hmay : L.MayCall g h.name := by rw [hname]; exact hdecl
        have hBlr : L.BlrTo g tv h :=
          ⟨⟨hmay, .inl ⟨by
            obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hin
            exact List.mem_map.mpr ⟨p, hp, by rw [hpe]; exact hname.symm⟩,
            ext, hin, hname.symm, hcol⟩⟩, hgot⟩
        have hlen : (regLocs h.sig).length = Lu.length := by
          have := argsAt_regLocs hargs
          rw [← h2] at this
          simpa using this.symm
        have hLu := hLuB h hh hBlr hlen
        have hra := hL.raBlr g hg info hsite hreg h hh hmay _ hP.callPc
        have hcOk := L.callerOk_of_regs hL hh hLu hsw hcode hra
        rw [h2] at hcOk
        have hTI : L.TrapIn M' h (enterAt (L.A h) u) tc := L.progCallTG hL (Nat.succ_pos M')
          (ih (Nat.succ_pos M')) hpfh ⟨g, hg, hcallee⟩
          hWE.img herrw hal' hroom' hdead' (hκ.2 _ h hh) hmemR0 hargs hsav hpl' hinit hret hDn u hcOk
        have hjunk := L.pcall_junk hL hh hTI hra
        have hb : (blrTarget u).bind (symCallee L.Xb L.P) = some h := by rw [htgt]; exact hs
        have hhook : (L.hooks (M' + 1)).call (destOf info) u = L.pcall (M' + 1) h u := by
          rw [destOf_eq_callDest, hd1]; exact L.hooks_none hb
        refine .prog (hstop ?_) (by rw [hu]; exact ⟨info, regs, i', hsite, hasg, hP, herr,
          .inr ⟨by rw [destOf_eq_callDest, hd1], hb⟩⟩)
          (by rw [hu]; exact L.progCallOk_blr hL hg hh hsite (by rw [hinfo]) hst hasg hP hcode hb hBlr)
          (by rw [hu]; exact hra) (by rw [hu]; exact hTI)
        rw [hstep, hhook, hjunk]; exact junkAt_err u
  · -- an indirect call
    obtain ⟨Gb, hGb, rfl⟩ := cutEnv_extern hG'
    obtain ⟨htrG, hQ⟩ := cutO_trapped htr'
    have hreg : ∀ nm', info.dest ≠ .sym nm' := fun nm' e => by simp [callDest, e] at hdn
    obtain ⟨tv, Lu, Ld, n0, hinfo, hLuB, huv, htgt, hops'⟩ :=
      L.blrSite hL hg hsite hreg hops hst hasg hP hcode
    have hus' := hus
    rw [huv] at hus'
    obtain ⟨h1, h2⟩ := List.cons.inj hus'
    cases hpf : L.P.func? nm with
    | none =>
      have hs : symCallee L.Xb L.P (lo64 u0) = none := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u0) = none
        rw [hu0]; exact (L.find_sym hL nm).2 hpf
      have hbase : L.base.extern nm = some Gb := by
        simpa [envOf, hpf, Clif.linkEnvR_none hpf] using hGb
      have hgb : L.GoesBase info u :=
        ⟨.inl (by rw [destOf_eq_callDest, hdn]), fun _ => by rw [htgt, h1]; exact hs⟩
      have hX0' : L.Xb.call (callDest info) (useVals ops regs u) w = none := by
        rw [hdn, hus] at hX0 ⊢; rwa [L.X_none hs] at hX0
      have hBT : L.BaseTrapCallI g tc info u := ⟨hsite, hgb, herr, ops, regs, i', w, F, _, _,
        spv w₀, hops, hasg, hP, hsw, hX0', .inr ⟨sig, hsig, nm, Gb, sl, cm, u0, args, vals', hbase,
        (fun _ h => nomatch h), hu0, hl8, hall, hmr, htrG, hty, hdn, hus⟩⟩
      refine .base (hstop ?_) (by rw [hu]; exact ⟨info, hBT⟩)
      rw [hstep, L.hooks_base hgb.1 u hgb.2]; exact hB.stop g hg tc info u hBT
    | some h =>
      obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
      subst hname
      obtain ⟨hdecl, G0, hG0, hGt⟩ := L.envOf_prog hGb hpf
      obtain ⟨hpl, ht0⟩ := hGt _ _ _ htrG
      obtain ⟨cs', hinit, hret⟩ := L.linkEnvR_trap hpf hG0 ht0
      obtain ⟨M', rfl, hDn⟩ := hDnM (hQ h cs' hpf hinit)
      have hnf : ¬ Clif.IndFree g := fun hif => by
        rw [indSigs_nil_of_indFree hif] at hsig; cases hsig
      have hce := clifEntry_initState (f := h) hpf hinit
      have hvl : vals'.length = h.sig.params.length := by
        have := congrArg List.length hce.sig
        simpa using this
      have hm : IndSigMatch sig h :=
        hsg h.sig (by simp only [cutEnv, envOf, Clif.linkEnvR_sigOf, hpf, Option.map_some])
      obtain ⟨⟨bytes, hbb, hb8⟩, -⟩ := hL.indSig g hg hnf h hh hdecl (.inl ⟨sig, hsig, hm⟩)
      have hargs : ArgsAt h.sig vals' args w := (argsAt_iff_of_regs hbb hb8 hvl).mpr hall
      have hsav : StackArgsAvoid F h.sig vals' w := by
        intro off v hm'
        obtain ⟨r, hr⟩ := (locsOf_small hbb hb8).2 _ (List.of_mem_zip hm').1
        cases hr
      have hcallee : L.Callee g h := .inr (.inr ⟨hh, hdecl⟩)
      obtain ⟨⟨hmemR0, -, -⟩, hspw, herrw⟩ := hmr
      have hbs : frameDrop (L.A h).af + κ M' h ≤ κ (M' + 1) g := hκ.1 M' g hg h hcallee
      have hroom' : frameDrop (L.A h).af + κ M' h ≤ (spv w).toNat := by
        rw [hspw]; have := hWE.room; omega
      have hdead' : ∀ a, StackBelow (frameDrop (L.A h).af + κ M' h) (spv w) a →
          F a ∧ ¬ L.Img a := fun a ha =>
        hWE.dead a (by rw [← hspw]; exact stackBelow_mono ha hbs)
      have hal' : (spv w).toNat % 16 = 0 := by rw [hspw]; exact hWE.align
      have hpl' : L.NeedSlots → L.PlaceAt cm (spv w) := fun hN => by rw [hspw]; exact hpl hN
      have hs : symCallee L.Xb L.P (lo64 (regVal u (.x n0))) = some h := by
        rw [h1]
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u0) = some h
        rw [hu0]; exact (L.find_sym hL h.name).1 h hpf
      have hgot : ∀ nm, GotV (L.A g).vcp tv nm → nm = h.name := by
        intro nm hn
        have e := hgg tv nm ops (by rw [hinfo]) hn hops (by rw [hops']; simp [tgtOp, Operand.isUse])
        rw [huv] at e
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at e
        exact L.got_target hL hs e
      have hBlr : L.BlrTo g tv h := ⟨⟨hdecl, .inr ⟨sig, hsig, hm, hm.returns_length⟩⟩, hgot⟩
      have hlen : (regLocs h.sig).length = Lu.length := by
        have := argsAt_regLocs hargs
        rw [← h2] at this
        simpa using this.symm
      have hLu := hLuB h hh hBlr hlen
      have hra := hL.raBlr g hg info hsite hreg h hh hdecl _ hP.callPc
      have hcOk := L.callerOk_of_regs hL hh hLu hsw hcode hra
      rw [h2] at hcOk
      have hTI : L.TrapIn M' h (enterAt (L.A h) u) tc := L.progCallTG hL (Nat.succ_pos M')
        (ih (Nat.succ_pos M')) hpf ⟨g, hg, hcallee⟩
        hWE.img herrw hal' hroom' hdead' (hκ.2 _ h hh) hmemR0 hargs hsav hpl' hinit hret hDn u hcOk
      have hjunk := L.pcall_junk hL hh hTI hra
      have hb : (blrTarget u).bind (symCallee L.Xb L.P) = some h := by rw [htgt]; exact hs
      have hhook : (L.hooks (M' + 1)).call (destOf info) u = L.pcall (M' + 1) h u := by
        rw [destOf_eq_callDest, hdn]; exact L.hooks_none hb
      refine .prog (hstop ?_) (by rw [hu]; exact ⟨info, regs, i', hsite, hasg, hP, herr,
        .inr ⟨by rw [destOf_eq_callDest, hdn], hb⟩⟩)
        (by rw [hu]; exact L.progCallOk_blr hL hg hh hsite (by rw [hinfo]) hst hasg hP hcode hb hBlr)
        (by rw [hu]; exact hra) (by rw [hu]; exact hTI)
      rw [hstep, hhook, hjunk]; exact junkAt_err u

/-- `trapIn_callTrapG` for the run premise `TrapsD` and a `call` site (`CallTrapAt`). -/
theorem trapIn_callTrap (hL : L.Ok) [hR : L.CrunOk] (hB : L.BaseTrapsOk) (hκ : L.Budget κ)
    {M : Nat} (ih : 0 < M → L.ThmT κ (M - 1)) {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {F G : BitVec 64 → Prop} {vals : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState}
    {ra : BitVec 64} {s : Arm.ArmState} (hWE : L.WorldEntry κ M g F vals cs w₀)
    (hME : L.MachEntry κ M g F G ra s w₀) {n : Nat} {tc : Clif.TrapCode}
    (hstop : Arm.r .ERR (L.mach M g (runX (L.mach M g) n s)) ≠ .None → L.Stop M g s n)
    (hprog : (runX (L.mach M g) n s).program = (L.A g).fb.program (L.A g).base)
    (hct : CallTrapAt (L.A g).vcp F (κ M g) G s (L.A g).fa (L.A g).base (L.X κ M g F)
      (GotV (L.A g).vcp)
      (TrapCallSem (cutEnv (L.envOf M g (spv w₀)) (L.covQ (L.TrapsDn M))) (g.externs.map (·.2))
        (indSigs g)
        (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
          g (spv w₀)) (L.X κ M g F) tc)
      (runX (L.mach M g) n s)) :
    L.TrapIn M g s tc :=
  L.trapIn_callTrapG (D := L.TrapsD) hL hB hκ (fun {h cs} hD => by
    cases M with
    | zero => exact hD.elim
    | succ M' => exact ⟨M', rfl, hD⟩) ih hg hWE hME hstop hprog hct.toT

/-- **The induction step**: the trap statement at depth `M` from the one at depth `M - 1` (and
the linking statement `LinkSys.thm` for the returning callees). -/
theorem thmT_of (hL : L.Ok) [hR : L.CrunOk] (hT : L.TrapsOk) (hB : L.BaseTrapsOk)
    (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmT κ (M - 1)) : L.ThmT κ M := by
  intro g hg F vals cs w₀ fuel tc hWE hTD hrun G ra s hME
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInv g (spv w₀) cs := ⟨hI, hWE.clif.callers, hWE.place⟩
  rw [L.trapsD_eq] at hTD
  obtain ⟨htrC, hcut⟩ := hTD
  have hrunE : Clif.runLoop (cutEnv (L.envOf M g (spv w₀)) (L.covQ (L.TrapsDn M))) L.P.bare fuel cs =
      .trapped tc := by
    rw [L.runLoop_cut hL hg fuel cs hJ]; exact hcut fuel tc hrun
  have htrE := L.trapsExplicitC_cut hL hg (Q := L.covQ (L.TrapsDn M)) hJ htrC
  have ihR : 0 < M → L.Thm κ (M - 1) := fun _ => L.thm hL hκ (M - 1)
  have hAE : ActEntry (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G
      (L.X κ M g F) (L.hooks M) (L.A g).base ra s w₀ :=
    ⟨hME.abi, hME.stack, hME.gfree, hME.hF, L.calleeOk hL hκ ihR hg hME,
      fun _ => L.calleeTryOk hL hκ ihR hg hME,
      fun ht => L.tlsOk_hooks (hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)), hME.body⟩
  obtain ⟨n, htrace, hsp, hprog, hcase⟩ := backend_correct_world_cleanup_trapstop
    (hL.subset g hg) (hT.cleanup g hg) (hT.lowerU g hg) rfl (hT.noTry g hg)
    (X := L.X κ M g F) (syms := L.syms) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
    (xCallsOk_cut (L.xCallsOk hL hκ ihR hg hWE.img hWE.room hWE.dead hWE.align))
    (xCallsIndOk_cut (L.xCallsIndOk hL hκ ihR hg hWE.img hWE.room hWE.dead hWE.align))
    (L.xTrapsOk hL hB hκ ih hg hWE.img)
    (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel hWE.args htrE hrunE
    (L.hooks M) G (L.A g).base ra s hAE
  have hroom : frameDrop (L.A g).af ≤ (spv s).toNat := by
    rw [L.frameDrop_eq hL hg]; have := hME.stack.1.1; omega
  have htr : PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n :=
    by have := postTrace_of_actGoodX htrace; exact this
  have hgoodOf : (∀ m, Arm.r .ERR (runX (L.mach M g) (n + m + 1) s) ≠ .None) →
      L.RunGoodL M g s := fun hh =>
    L.runGood_of_trace hL hκ (fun _ => L.thmG hL hκ (M - 1)) hg hME (by exact htrace)
      fun k _ he => Nat.lt_of_not_le fun hle => hh (k - n) (by
        rw [show n + (k - n) + 1 = k + 1 by omega]; exact he)
  rcases hcase with ⟨hat, hhalt⟩ | hct
  · exact .site ⟨hroom, htr, hat.err, hprog, hsp, hhalt, hgoodOf hhalt⟩ hat
  · have herr : Arm.r .ERR (runX (L.mach M g) n s) = .None := by
      obtain ⟨_, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, he, -⟩ := hct
      exact he
    have hhalt : Arm.r .ERR (L.mach M g (runX (L.mach M g) n s)) ≠ .None →
        ∀ m, Arm.r .ERR (runX (L.mach M g) (n + m + 1) s) ≠ .None := fun he m => by
      rw [show n + m + 1 = n + (m + 1) by omega, runX_add]
      exact L.runX_mach_err hB M g m _ he
    exact L.trapIn_callTrap hL hB hκ ih hg hWE hME
      (fun he => ⟨hroom, htr, herr, hprog, hsp, hhalt he, hgoodOf (hhalt he)⟩) hprog hct

/-- **The trap statement at every depth.** -/
theorem thmT (hL : L.Ok) [L.CrunOk] (hT : L.TrapsOk) (hB : L.BaseTrapsOk) (hκ : L.Budget κ) :
    ∀ M, L.ThmT κ M
  | 0 => L.thmT_of hL hT hB hκ fun h => absurd h (Nat.lt_irrefl 0)
  | M + 1 => L.thmT_of hL hT hB hκ fun _ => thmT hL hT hB hκ M

end LinkSys

namespace LinkSys

variable (L : LinkSys)

/-! ## The observable does not read the callee runs -/

theorem stop_withCrun (c : Nat → Clif.State → Clif.Outcome) {M : Nat} {g : Clif.Function}
    {s : Arm.ArmState} {n : Nat} (h : (L.withCrun c).Stop M g s n) : L.Stop M g s n := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [L.mach_withCrun] at h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6, runGoodL_withCrun h7⟩

/-- The trap observable of `L` with other callee runs is `L`'s (the machine is `L`'s,
`mach_withCrun`). -/
theorem trapIn_withCrun (c : Nat → Clif.State → Clif.Outcome) {M : Nat} {g : Clif.Function}
    {s : Arm.ArmState} {tc : Clif.TrapCode} (h : (L.withCrun c).TrapIn M g s tc) :
    L.TrapIn M g s tc := by
  induction h with
  | site hs ht =>
    rw [L.mach_withCrun] at ht
    exact .site (L.stop_withCrun c hs) ht
  | base hs hb =>
    rw [L.mach_withCrun] at hb
    exact .base (L.stop_withCrun c hs) hb
  | prog hs hp hok hra _ ih =>
    rw [L.mach_withCrun] at hp hok hra ih
    exact .prog (L.stop_withCrun c hs) hp ⟨hok.mem, hok.code, hok.xzr, hok.blrAt⟩ hra ih

/-- The premises of the trap theorem do not read the callee runs. -/
theorem TrapsOk.withCrun {L : LinkSys} (h : L.TrapsOk) (c : Nat → Clif.State → Clif.Outcome) :
    (L.withCrun c).TrapsOk :=
  ⟨h.cleanup, h.lowerU, h.noTry⟩

theorem BaseTrapsOk.withCrun {L : LinkSys} (h : L.BaseTrapsOk)
    (c : Nat → Clif.State → Clif.Outcome) : (L.withCrun c).BaseTrapsOk :=
  ⟨h.xt, h.stop, h.err, h.tlsErr⟩

end LinkSys

/-! ## The whole-program theorem with callee traps -/

/-- **The whole-program trap theorem for any callee runs** (`LinkSys.CrunOk`): for a trap of
`f`'s activation that is a run of the program without functions under `envR M f`, under the run
premise `TrapsD`, the linked machine of depth `M` has the trap observable (the trap counterpart of
`backend_correct_program_core`). -/
theorem backend_correct_program_trap_core (L : LinkSys) (hL : L.Ok) [L.CrunOk]
    (hT : L.TrapsOk) (hB : L.BaseTrapsOk)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
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
    (htr : L.TrapsD M f cs) {tc : Clif.TrapCode} {m : Nat}
    (hrun : Clif.runLoop (L.envR M f) L.P.bare m cs = .trapped tc) :
    L.TrapIn M f s tc := by
  have hc := hL.compiled f hf
  have hfr := lowerRFunc_frame hc.alloc
  obtain ⟨hB', hK⟩ := spBody_toNat hres
  have hd : frameDrop (L.A f).af = (L.A f).af.frameSize + 16 := by simp [frameDrop, hfr]
  have hWE : L.WorldEntry κ M f L.F args cs w₀ := by
    refine ⟨hcs, ⟨hrel, rfl, ?_⟩, ?_, ?_, ?_, ?_, hL.imgF, hpl⟩
    · rw [hbe.other .ERR (by simp [Masked]) (by simp) (by simp)]; exact hent.err
    · refine argsAtEntry_body hfr (entryRegs_of_check hc.lowerOk) hbe hargs (fun off v hm k hk hk' => ?_) hres
      rw [hF] at hk'
      rcases hk' with hw | hi
      · exact stackArgsAvoid_frameW_pipeline hc hres hent hargs off v hm k hk hw
      · exact hsav off v hm k hk hi
    · rw [hbe.sp, hB']; omega
    · intro a ha
      rw [hbe.sp] at ha
      refine ⟨by rw [hF]; exact .inl (.inr ha), fun hi => hgfree a hi ?_⟩
      obtain ⟨h1, h2⟩ := ha
      rw [hB'] at h1 h2
      exact ⟨by omega, by omega⟩
    · rw [hbe.sp, hB', hd]
      have := hent.spAligned
      have := L.frameSize_mod hL hf
      omega
  have hME : L.MachEntry κ M f L.F L.Img ra s w₀ :=
    ⟨hent.toCall, hres, hgfree, hF.symm, fun _ h => h, himg,
      hbe.w L.F fun r ⟨_, _, hvb, hi, _, hv⟩ =>
        ((ctlCheck_args (lowerRFunc_ok hc.alloc).2.2 hvb hi).2.2 _ hv).2⟩
  exact L.thmT hL hT hB hκ M f hf L.F args cs w₀ m tc hWE htr hrun L.Img ra s hME

/-- **The whole-program theorem with callee traps, per-function stack budget `κ`**
(`backend_correct_program_budget`'s trap case widened): for a function `f` of the linked program
whose whole-program CLIF run of at most `M + 1` steps traps with `c`, under the run premise
`TrapsD` of the program callees running at most `M` steps (`LinkSys.std`: no memory-access trap,
and every callee trap the run hits is one of an activation that satisfies the premise one level
down), the shipped pipeline's per-function facts (`TrapsOk`) and the outside code's trap contract
(`BaseTrapsOk`), the linked machine of depth `M` has the trap observable `TrapIn`: it stops at a
trap site of `f` with `c`, at a call of `f` whose callee outside `P` traps with `c`, or at a call
of a function of `P` whose own activation has the observable one level down. -/
theorem backend_correct_program_trap_budget (L : LinkSys) (hL : L.Ok) (hT : L.TrapsOk)
    (hB : L.BaseTrapsOk) {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
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
    (htr : L.std.TrapsD M f cs) {tc : Clif.TrapCode}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .trapped tc) :
    L.TrapIn M f s tc := by
  haveI := L.crunOk_std hL
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf) (E := L.std.envR M f)
    rfl rfl (fun _ hn => L.std.envR_of (.inl hn))
    (L.std.envR_link hL.names) (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  exact L.trapIn_withCrun _ (backend_correct_program_trap_core L.std (hL.withCrun _) (hT.withCrun _) (hB.withCrun _) hκ hf M
    hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr hm)

/-- **The whole-program theorem with callee traps** (`backend_correct_program`'s trap case
widened; the stack budget `L.K M`). -/
theorem backend_correct_program_trap (L : LinkSys) (hL : L.Ok) (hT : L.TrapsOk)
    (hB : L.BaseTrapsOk) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (L.K M) (L.A f).af s)
    (hF : L.F = frameWG (L.K M) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + L.K M) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : L.std.TrapsD M f cs) {tc : Clif.TrapCode}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .trapped tc) :
    L.TrapIn M f s tc :=
  backend_correct_program_trap_budget L hL hT hB (κ := fun M _ => L.K M) (L.budget_K hL) hf M
    hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr hrun

/-- **The whole-program theorem with callee traps for the run's peak call depth**
(`backend_correct_program_peak`'s trap case widened): the linked machine of depth `d`, the peak
call depth of the whole-program run of at most `F + 1` steps, the program callees running with
fuel `F` and at most `d - 1` callers of their own (`LinkSys.peak`). -/
theorem backend_correct_program_trap_peak (L : LinkSys) (hL : L.Ok) (hT : L.TrapsOk)
    (hB : L.BaseTrapsOk) {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (F d : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ d f) (L.A f).af s)
    (hF : L.F = frameWG (κ d f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ d f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (hd : Clif.DepthLe L.base L.P d cs)
    (htr : (L.peak F).TrapsD d f cs) {tc : Clif.TrapCode}
    (hrun : Clif.runLoop L.base L.P (F + 1) cs = .trapped tc) :
    L.TrapIn d f s tc := by
  haveI := L.crunOk_peak hL F
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkD (base := L.base) (syms := L.syms) F d hL.names hf hL.free
    (hL.indScope f hf) (E := (L.peak F).envR d f)
    rfl rfl (fun _ hn => (L.peak F).envR_of (.inl hn))
    ((L.peak F).envR_link hL.names) (F + 1) cs (Nat.le_refl _) hd (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  exact L.trapIn_withCrun _ (backend_correct_program_trap_core (L.peak F) (hL.withCrun _) (hT.withCrun _) (hB.withCrun _) hκ
    hf d hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr hm)

end E2E
