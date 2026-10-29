import FV.Concurrency.CallSegOkGTFull

/-!
# Witness: a compiled caller calling an external under its event contract (#649)

The compiled caller `fC` of `CallLoadData` (`v1 = call fn0(v0)`, `fn0 = %ld(i64) -> i64`) linked
with an **external** `ld` instead of the compiled `atomic_load`:

* `idF`: the external's Arm code, one `ret` (the word at the end of the compiled `atomic_load`'s
  code, so the caller's memory holds it), at `retBase`; `linkX`: the link of `ld` and `f`;
* `fX`: the external's CLIF specification `v1 = bor v0, v0; return v1` (it returns its
  argument), `pX = [fC, fX]`;
* **`ext_ret`**: the event contract `CallSegExt.ExtEvContractT` of an external whose code is one
  `ret` and whose specification returns its argument (`RetSpec`), in any well-formed link where
  it is the only function of its name (proven, not assumed): from every call, the `ret` is one
  event-free label realized by the specification's statement, and the return keeps `sp`, the
  callee-saved registers and the memory, back on the caller's program with the argument in `x0`;
  **`extX`** its instance on `linkX`;
* `fnOk_CX`, **`linkOkX`** (`LinkOkX`: the caller compiled, the external's code and slot-free
  specification, `x0` the return register), `placeOkX`, `linkFreeX`;
* **`funRealT_link_X`**: `funRealT_link_ext` on `linkX`/`pX` with the static premises and the
  contract discharged.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallSegOkGT.WitnessExt

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck ThreadRefine IselCall IselCallRet ArmAllocThread E2E
  LinkedMachine LinkedMachine.Link LinkedMachine.Witness CallComposeT CallSegOkG CallSegPc
  CallSegRun CallResumeChecks CallEntryRel CallSeg.WitnessC CallEntry.Witness CallResumeL.Witness
  RealizeCompiled.WitnessL IselResume CallArity CallArgsEntry CallArgsL2 CallArgsAt
  IselCall.Witness CallEntryRel.Witness CallSegExt CallSegOkGT.Witness ArmInstFoot ClifLift ArmFoot
open ArmAllocThread.Witness (ok_getD)

/-! ## The external and its specification -/

/-- The external's CLIF specification: it returns its argument. -/
def srcX : String := "function %ld(i64) -> i64 {
block0(v0: i64):
    v1 = bor v0, v0
    return v1
}
"

def fX : Clif.Function :=
  match Clif.parse srcX with
  | .ok p => p.funcs.headD default
  | .error _ => default

/-- The specification's entry block. -/
def B0X : Clif.Block := fX.blocks.headD default

/-- The program: the caller and the external's specification. -/
def pX : Clif.Program := { funcs := [fC, fX] }

/-- The external's code: one `ret`. -/
def retFa : FnAsm := { name := "ld", k := 0, lines := #[.ins .ret none], size := 4, traps := [] }

def retFb : FnBin := retFa.layout.toOption.getD default

/-- The address of the compiled `atomic_load`'s last word (a `ret`). -/
def retBase : BitVec 64 := 0x20000#64 + BitVec.ofNat 64 (4 * 28)

/-- **The external's code in the link.** -/
def idF : LFn :=
  { ldF with
    fa := retFa
    fb := retFb
    lm := (labelOffsets retFa.lines).toOption.getD default
    base := retBase }

/-- **The link of the external and the compiled caller.** -/
def linkX : Link := ⟨[("ld", idF), ("f", callerF)]⟩

theorem checksX : retFa.layout.toBool = true ∧ (labelOffsets retFa.lines).toBool = true ∧
    retFb.words = #[0xd65f03c0#32] ∧ ldF.fb.words[28]? = some 0xd65f03c0#32 ∧
    retBase.toNat + 4 * retFb.words.size ≤ 0x30000 ∧ callsInsideB idF = true := by
  native_decide -- witness: native_decide

theorem name_fX : fX.name = "ld" := by native_decide -- witness: native_decide

theorem slots_fX : fX.slots = [] := by native_decide -- witness: native_decide

theorem b0X : fX.blocks[0]? = some B0X := by native_decide -- witness: native_decide

theorem params_B0X : B0X.params = [(0, .i64)] := by native_decide -- witness: native_decide

theorem body_B0X : B0X.body = [{ results := [1], inst := .binary .bor .i64 0 0 }] := by
  native_decide -- witness: native_decide

theorem term_B0X : B0X.term = .ret [1] := by native_decide -- witness: native_decide

theorem sig_fX : fX.sig = extF.sig := by native_decide -- witness: native_decide

theorem externs_fX : fX.externs = [] := by native_decide -- witness: native_decide

theorem sig_fX_fC : fX.sig = fC.sig := by native_decide -- witness: native_decide

theorem locs_fX : locsOf fX.sig = [.reg (.x 0)] := by rw [sig_fX_fC]; exact WitnessFull.locsC

theorem func_fX : pX.func? extF.name = some fX := by native_decide -- witness: native_decide

theorem func_ldX : pX.func? "ld" = some fX := by native_decide -- witness: native_decide

theorem boolsX : pX.funcs.all (fun f => f.externs.all (·.2.name != f.name)) = true ∧
    pX.funcs.all (fun g => g.blocks.all fun b => match b.term with
      | .returnCall .. => false
      | _ => true) = true := by
  native_decide -- witness: native_decide

theorem laidX : idF.LaidOut where
  layout := ok_getD checksX.1
  lm := ok_getD checksX.2.1
  pos := by show 0 < retFb.words.size; rw [checksX.2.2.1]; decide
  fit := by
    have := checksX.2.2.2.2.1
    show retBase.toNat + 4 * retFb.words.size ≤ 2 ^ 64
    omega

theorem mem_idX : ("ld", idF) ∈ linkX.fns := .head _

theorem mem_callerX : ("f", callerF) ∈ linkX.fns := .tail _ (.head _)

theorem mem_linkX {n : String} {F : LFn} (h : (n, F) ∈ linkX.fns) :
    (n = "ld" ∧ F = idF) ∨ (n = "f" ∧ F = callerF) := by
  simpa [linkX] using h

/-- **The link is well formed.** -/
theorem okX : linkX.Ok where
  sep := by
    refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    refine ⟨by decide, .inl ?_⟩
    show retBase.toNat + 4 * retFb.words.size ≤ (0x30000#64 : BitVec 64).toNat
    have := checksX.2.2.2.2.1
    simpa using this
  laid := by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact laidX
    · rw [List.mem_singleton] at hp
      subst hp
      exact laidC

/-! ## The external's step -/

theorem enter_ofNat_zero (F : LFn) (x : ArmState) :
    Arm.r .PC (enter F x) = F.base + BitVec.ofNat 64 (lineOffset F.fa.lines.toList 0) := by
  rw [enter_pc]; simp [lineOffset]

/-- **A `ret` line of linked code has no event and is plain.** -/
theorem ret_evs {F : LFn} (hl : F.LaidOut) {j : Nat} {t : Option Clif.TrapCode}
    (hj : F.fa.lines.toList[j]? = some (.ins .ret t)) {s : ArmState}
    (hprog : s.program = F.fb.program F.base)
    (hpc : Arm.r .PC s = F.base + BitVec.ofNat 64 (lineOffset F.fa.lines.toList j)) :
    stepEvs s = [] ∧ cls s = .plain := by
  obtain ⟨h4, w, hw, hk⟩ := FnAsm.layout_word hl.layout hl.lm hj rfl
  have ha : (Insn.ret).toArmInst ⟨lineOffset F.fa.lines.toList j, (F.lm[·]?)⟩ =
      .ok (.BR (.Uncond_branch_reg
        { _fixed := 0x6b#7, opc := 0x2#4, op2 := 0x1f#5, op3 := 0x00#6, Rn := 0x1e#5,
          op4 := 0x00#5 })) := rfl
  have hfetch : fetch_inst (Arm.r .PC s) s = some w := by
    rw [fetch_inst_from_program, hprog, hpc]
    have := FnBin.program_find (base := F.base)
      (by have := (FnAsm.layout_size hl.layout).1; have := hl.fit; omega) hk
    rwa [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4)] at this
  have hd := Insn.decode_encode_of ha hw
  have hdec : decodeAt s = some (.BR (.Uncond_branch_reg
      { _fixed := 0x6b#7, opc := 0x2#4, op2 := 0x1f#5, op3 := 0x00#6, Rn := 0x1e#5,
        op4 := 0x00#5 })) := by
    simp only [decodeAt, hfetch, hd]
  refine ⟨?_, ?_⟩
  · simp only [stepEvs, hdec]
    split <;> rfl
  · unfold cls
    rw [hdec]

/-- The external's entry is at its `ret` line. -/
theorem isRet_idF (x : ArmState) : idF.IsRet (enter idF x) :=
  ⟨0, none, rfl, enter_ofNat_zero idF x⟩

/-- The registers of the entry and the call-site state agree except in the pc and `x30`. -/
theorem regVal_enter_saved (F : LFn) (x : ArmState) {r : Reg} (hr : r ∈ calleeSaved) :
    regVal (enter F x) r = regVal x r := by
  simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range] at hr
  rcases hr with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · have hne : StateField.GPR (rnum (19 + i)) ≠ .GPR 30#5 := by
      intro e
      have := congrArg (fun f => match f with | StateField.GPR j => j.toNat | _ => 0) e
      simp [rnum] at this; omega
    simp only [regVal]
    rw [Link.r_enter (by simp) hne]
  · simp only [regVal]
    rw [Link.r_enter (by simp) (by simp)]

theorem regVal_enter_x0 (F : LFn) (x : ArmState) : regVal (enter F x) (.x 0) = regVal x (.x 0) := by
  simp only [regVal]
  rw [Link.r_enter (by simp) (by simp [rnum])]

/-- An entry without stack slots keeps the allocations, the bytes and the symbols. -/
theorem enterSlots_nil' {f : Clif.Function} (hf : f.slots = []) (m : Clif.Mem) :
    (Clif.enterSlots f m).2.allocs = m.allocs ∧ (Clif.enterSlots f m).2.bytes = m.bytes ∧
      (Clif.enterSlots f m).2.symbols = m.symbols := by
  unfold Clif.enterSlots
  split
  · simp [hf, Clif.bumpSlots]
  · split
    · simp only [hf, Clif.placeSlots]; unfold Clif.initSlots; split <;> simp
    · simp [hf, Clif.bumpSlots]

/-- **A specification returning its argument**: entry block `B` on one `i64` argument `v0`, the
statement `v1 = bor v0, v0`, `return v1`, no stack slot, the argument and the result in `x0`. -/
structure RetSpec (fS : Clif.Function) (B : Clif.Block) : Prop where
  b0 : fS.blocks[0]? = some B
  params : B.params = [(0, .i64)]
  body : B.body = [{ results := [1], inst := .binary .bor .i64 0 0 }]
  term : B.term = .ret [1]
  slots : fS.slots = []
  locs : locsOf fS.sig = [.reg (.x 0)]

/-- A `RetSpec` specification entered on one `i64` argument. -/
theorem regs_enteredG {fS : Clif.Function} {B : Clif.Block} (hS : RetSpec fS B)
    {vals : List Clif.Val} {m : Clif.Mem} {s : Clif.State} (hEn : Entered fS vals m s) :
    ∃ b : BitVec 64, vals = [⟨.i64, b⟩] ∧ s.frame.regs 0 = some ⟨.i64, b⟩ := by
  obtain ⟨-, -, -, -, B0, hB0, -, -, hregs, htys⟩ := hEn
  rw [hS.b0] at hB0
  cases hB0
  rw [hS.params] at hregs htys
  cases vals with
  | nil => simp [Clif.Regs.setMany] at hregs
  | cons v vs =>
    cases vs with
    | cons _ _ => simp [Clif.Regs.setMany] at hregs
    | nil =>
      obtain ⟨ty, b⟩ := v
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at htys
      subst htys
      refine ⟨b, rfl, ?_⟩
      simp only [List.map_cons, List.map_nil, Clif.Regs.setMany, Option.some.injEq] at hregs
      rw [← hregs]
      simp

/-- **A `RetSpec` specification's statement**: `v1 = v0`, no event. -/
theorem cstepG (env : Clif.Env) (p : Clif.Program) {fS : Clif.Function} {B : Clif.Block}
    (hS : RetSpec fS B) {vals : List Clif.Val} {m : Clif.Mem} {s : Clif.State}
    (hEn : Entered fS vals m s) {b : BitVec 64} (hr0 : s.frame.regs 0 = some ⟨.i64, b⟩) :
    CStep env p (.run s) [] (.run { s with frame := { s.frame with
      regs := s.frame.regs.set 1 ⟨.i64, b⟩, body := [] } }) := by
  obtain ⟨-, -, -, -, B0, hB0, hbody, -, -, -⟩ := hEn
  rw [hS.b0] at hB0
  cases hB0
  rw [hS.body] at hbody
  have hga : s.frame.getAs 0 .i64 = .ok b := by
    simp [Clif.Frame.getAs, Clif.Frame.get, hr0, Clif.Val.as?, Clif.Res.ofOption]
  have hev : ∀ mem : Clif.Mem, Clif.evalInst s.frame mem (.binary .bor .i64 0 0) =
      .ok ([⟨.i64, b⟩], mem) := by
    intro mem
    simp [Clif.evalInst, hga, Clif.BinaryOp.isShift, Clif.Sem.binary]
    exact ⟨b, rfl, b, rfl, by simp only [Clif.Sem.bor]; congr 1; exact BitVec.or_self⟩
  have hs : Clif.step env p s = .next { s with frame := { s.frame with
      regs := s.frame.regs.set 1 ⟨.i64, b⟩, body := [] } } := by
    rw [Clif.step_inst env p s _ [] hbody (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)]
    rw [hev]
    simp [Clif.StepResult.ofRes, Clif.continueWith, Clif.Regs.setMany]
  exact ClifCStep.cstep_of_eval (evs := []) (m0 := s.mem) hbody (fun _ _ h => by cases h)
    (fun _ _ _ h => by cases h) ⟨by simp [evShape, hbody], by simp⟩ trivial
    (fun B _ => by rw [hev]; rfl) hs

/-- **The event contract of an external whose code is one `ret`** and whose specification
returns its argument (`RetSpec`), in any well-formed link where it is the only function named
`nm`: from every call, the `ret` is one event-free label realized by the specification's
statement, and the return keeps `sp`, the callee-saved registers and the memory, back on the
caller's program with the argument in `x0`. -/
theorem ext_ret {L : Link} {env : Clif.Env} {p : Clif.Program} {syms : String → Option Nat}
    {nm : String} {FX : LFn} {fS : Clif.Function} {BS : Clif.Block} (hok : L.Ok)
    (hmem : (nm, FX) ∈ L.fns) (huniq : ∀ F, (nm, F) ∈ L.fns → F = FX) (hl : FX.LaidOut)
    (hline : FX.fa.lines.toList[0]? = some (.ins .ret none)) (hfS : p.func? nm = some fS)
    (hS : RetSpec fS BS) :
    ExtEvContractT L env p syms (· = nm) (fun _ => [.x 0]) := by
  refine ⟨fun n F fs hn hF hfs x mon K Fr m vals s hEn hAr hMR hFr hK hal herr hcl => ?_⟩
  subst hn
  have hFX : FX = F := (huniq F hF).symm
  subst hFX
  rw [hfS] at hfs
  cases hfs
  obtain ⟨b, rfl, hr0⟩ := regs_enteredG hS hEn
  have hcs := cstepG env p hS hEn hr0
  obtain ⟨hcall, -, -, hmem', B0, hB0, -, hterm, -, -⟩ := hEn
  rw [hS.b0] at hB0
  cases hB0
  rw [hS.term] at hterm
  obtain ⟨nc, Fc, hFc, hprog, hIn⟩ := hcl
  obtain ⟨hal0, hby0, hsy0⟩ := enterSlots_nil' hS.slots m
  intro ls t' hr
  cases hr with
  | nil =>
    exact ⟨0, [], .run s, id, Nat.le_refl _, by simpa [evTr] using CallCompose.xClosed_nil, .nil,
      by simpa [evTr] using CallCompose.refines_nil, .inl rfl⟩
  | cons hs hp ho hrest =>
    obtain ⟨hev, hcls⟩ := ret_evs hl (j := 0) (t := none) hline (enter_program FX x)
      (enter_ofNat_zero FX x)
    obtain ⟨rfl, rfl⟩ := CallSeg.tstep_plain_nil hs hp hev hcls
    have herr' : Arm.r .ERR (enter FX x) = .None := by
      rw [Link.r_enter (by simp) (by simp)]; exact herr
    have hM : L.M (enter FX x) = set_program (w .PC (xreg 30 (enter FX x)) (enter FX x))
        (Fc.fb.program Fc.base) :=
      M_ret_x30 hok hF hFc (enter_program FX x) ⟨0, none, hline, enter_ofNat_zero FX x⟩ herr'
        (by have hx30 : xreg 30 (enter FX x) = Arm.r .PC x + 4#64 := enter_x30 FX x
            rw [hx30]; exact hIn)
    have hmemv : (L.M (enter FX x)).mem = x.mem := by
      rw [hM, mem_set_program, ArmFoot.w_mem, enter_mem]
    have hregv : ∀ r : Reg, (r ∈ calleeSaved ∨ r = .x 0) →
        regVal (L.M (enter FX x)) r = regVal x r := by
      intro r hr
      rw [hM, regVal_set_program, CallResumeL.Witness.regVal_w_pc]
      rcases hr with hr | rfl
      · exact regVal_enter_saved FX x hr
      · exact regVal_enter_x0 FX x
    have htr : ∀ rest : List Lab, evTr ((⟨[], false⟩ :: rest : List Lab).take 1) = [[]] :=
      fun _ => by simp [evTr]
    refine ⟨1, [[]], _, id, by simp, ?_, .cons hcs .nil, ?_, .inr (.inr ⟨_, rfl, hcall,
      ⟨rfl, [1], hterm⟩, _, .cons hs hp ho .nil, ?_⟩)⟩
    · rw [htr]
      exact CallCompose.xClosed_of fun b y hy => by rw [CallStepT.evAt_nil1] at hy; cases hy
    · rw [htr]
      exact CallSeg.refines_nilS (by simp) fun q y hy => by
        rw [CallStepT.evAt_nil1] at hy; cases hy
    · exact {
        pc := by
          have hx30 : xreg 30 (enter FX x) = Arm.r .PC x + 4#64 := enter_x30 FX x
          rw [hM, r_set_program, r_of_w_same, hx30]
        err := by rw [hM, r_set_program, r_of_w_different (by simp)]; exact herr'
        sp := by
          show Arm.r (.GPR 31#5) _ = Arm.r (.GPR 31#5) x
          rw [hM, r_set_program, r_of_w_different (by simp),
            Link.r_enter (by simp) (by simp)]
        saved := fun r hr => by rw [hregv r (.inl hr)]
        keep := fun a _ => by rw [hmemv]
        prog := by rw [hM, program_set_program, hprog]
        fp := by
          show Arm.r (.GPR 29#5) _ = Arm.r (.GPR 29#5) x
          rw [hM, r_set_program, r_of_w_different (by simp),
            Link.r_enter (by simp) (by simp)]
        mem := {
          bytes := fun a b' hv hb => by
            have hv' : m.valid a 1 = true := by
              simpa [Clif.Mem.valid, hmem', hal0] using hv
            have hb' : m.bytes a = some b' := by simpa [hmem', hby0] using hb
            have := hMR.bytes a b' hv' hb'
            unfold Arm.read_mem at this ⊢
            rw [hmemv]; exact this
          valid := fun a n hv =>
            ⟨(hMR.valid a n (by simpa [Clif.Mem.valid, hmem', hal0] using hv)).1, fun _ _ h => h⟩
          symbols := by simp [hmem', hsy0, hMR.symbols] }
        rets := fun vals' cm hdone => by
          have hst : Clif.step env p { s with frame := { s.frame with
                regs := s.frame.regs.set 1 ⟨.i64, b⟩, body := [] } } =
              Clif.stepTerm env p { s with frame := { s.frame with
                regs := s.frame.regs.set 1 ⟨.i64, b⟩, body := [] } } (.ret [1]) := by
            rw [Clif.step_term env p _ rfl]
            exact congrArg _ hterm
          obtain ⟨hgm, -⟩ := (stepTerm_ret (env := env) (p := p) (xs := [1])
            (s := { s with frame := { s.frame with
              regs := s.frame.regs.set 1 ⟨.i64, b⟩, body := [] } }) hcall).2.2 vals' cm
            (by rw [← hst]; exact hdone)
          have hv' : vals' = [⟨.i64, b⟩] := by
            simp [Clif.Frame.getMany, Clif.Frame.get] at hgm
            exact hgm.symm
          subst hv'
          refine ⟨[regVal (L.M (enter FX x)) (.x 0)], ⟨by simp, fun j v y hj hy => ?_⟩,
            fun j r y hj hy => ?_⟩
          · cases j with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hy
              subst hj hy
              rw [hregv _ (.inr rfl)]
              exact hAr (.x 0) _ (by rw [hS.locs]; simp)
            | succ j => simp at hj
          · cases j with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hy
              subst hj hy
              rfl
            | succ j => simp at hj }

/-- `fX` returns its argument. -/
theorem specX : RetSpec fX B0X := ⟨b0X, params_B0X, body_B0X, term_B0X, slots_fX, locs_fX⟩

/-- The specification entered on one `i64` argument. -/
theorem regs_entered {vals : List Clif.Val} {m : Clif.Mem} {s : Clif.State}
    (hEn : Entered fX vals m s) :
    ∃ b : BitVec 64, vals = [⟨.i64, b⟩] ∧ s.frame.regs 0 = some ⟨.i64, b⟩ :=
  regs_enteredG specX hEn

/-- **The specification's statement**: `v1 = v0`, no event. -/
theorem cstepX (env : Clif.Env) {vals : List Clif.Val} {m : Clif.Mem} {s : Clif.State}
    (hEn : Entered fX vals m s) {b : BitVec 64} (hr0 : s.frame.regs 0 = some ⟨.i64, b⟩) :
    CStep env pX (.run s) [] (.run { s with frame := { s.frame with
      regs := s.frame.regs.set 1 ⟨.i64, b⟩, body := [] } }) :=
  cstepG env pX specX hEn hr0

/-- **The external's event contract holds** (module doc): its code is one `ret`. -/
theorem extX {env : Clif.Env} :
    ExtEvContractT linkX env pX (fun _ => none) (· = "ld") (fun _ => [.x 0]) :=
  ext_ret okX mem_idX (fun F hF => by
    rcases mem_linkX hF with ⟨-, rfl⟩ | ⟨h, -⟩
    · rfl
    · exact absurd h (by decide)) laidX rfl func_ldX specX

/-! ## The link's static premises -/

/-- **The caller is compiled in `linkX`** (as `fnOk_C`). -/
theorem fnOk_CX {env : Clif.Env} (henv : env.extern "ld" = none) :
    FnOk linkX env pX (fun _ => none) "f" callerF fC := by
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
    mem := mem_callerX
    wf := hwf
    scope := scope_C rfl
    abi := habi
    H := driverHypT_mk (Γ := ⟨(linkX.act callerF s0 K G).F, fun _ => none,
        (linkX.act callerF s0 K G).ctx.slotBase, 0⟩) (fctx := (linkX.act callerF s0 K G).ctx)
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
    ok := okX
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
      rw [func_fX] at hp; cases hp
      exact sig_fX
    probe := ArmAllocThread.ProbeF.of_small
      (show callerF.af.frameSize + 16 < 4096 by rw [fs_C]; decide) }

/-- `pX` has no `return_call`. -/
theorem linkFreeX : ∀ f : Clif.Function, f ∈ Clif.Program.funcs pX → Clif.LinkFree f := by
  intro g hg b hb fn args he
  have h := List.all_eq_true.mp boolsX.2 g hg
  have := List.all_eq_true.mp h b hb
  rw [he] at this
  cases this

/-- **The static premises of `linkX` on `pX`**: `f` compiled, `ld` the external with its
specification, `x0` the return register. -/
theorem linkOkX {env : Clif.Env} (henv : env.extern "ld" = none) :
    LinkOkX linkX env pX (fun _ => none) fr2 Mx2 (· = "ld") (fun _ => [.x 0]) where
  fn := by
    intro n f hf hn
    obtain ⟨hm, rfl⟩ := Clif.Program.func?_some hf
    simp only [pX, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · rw [name_fC]
      exact ⟨callerF, mem_callerX, fnOk_CX henv, fr2_f, by
        rw [ArmAllocThread.Witness.probeBelow_small (af := callerF.af) (by rw [fs_C]; decide), fs_C]
        decide⟩
    · exact absurd name_fX hn
  xfn := by
    intro n f hf hn
    obtain ⟨hm, rfl⟩ := Clif.Program.func?_some hf
    simp only [pX, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact absurd (name_fC.symm.trans hn) (by decide)
    · exact ⟨⟨idF, by rw [hn]; exact mem_idX⟩, slots_fX⟩
  inside := by
    intro n F h
    rcases mem_linkX h with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact callsInside_of checksX.2.2.2.2.2
    · exact inside_C
  noSelf := by
    intro n f hf e he
    obtain ⟨hm, rfl⟩ := Clif.Program.func?_some hf
    have h := List.all_eq_true.mp boolsX.1 f hm
    simpa using List.all_eq_true.mp h e he
  defsRet := by
    intro nA FA nB FB hA hB b vb us hb hk
    have hus : us.map (·.2) = [.x 0] := by
      rcases mem_linkX hB with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact CallSegCall.Witness.rets_ld hb hk
      · exact rets_x0 retsX0_C hb hk
    rw [hus]
    rcases mem_linkX hA with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact defsRet_L
    · exact CallResumeAll.Witness.defs_fC.2
  defsRetX := by
    intro nA FA n hA _
    rcases mem_linkX hA with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact defsRet_L
    · exact CallResumeAll.Witness.defs_fC.2

/-- **The oracle's frames of `pX`** hold its slots within `Mx2` bytes. -/
theorem placeOkX : PlaceOk pX fr2 Mx2 := by
  intro g hg
  simp only [pX, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · refine ⟨_, _, by rw [name_fC]; exact fr2_f, by rw [drop_C]; decide, fun q hq => ?_⟩
    rw [slots_fC] at hq; cases hq
  · refine ⟨_, _, by rw [name_fX]; exact fr2_ld, by rw [drop_ld]; decide, fun q hq => ?_⟩
    rw [slots_fX] at hq; cases hq

/-- **Every compiled activation of `linkX` is realized, the external under its (proven)
contract** (`funRealT_link_ext` on `linkX`/`pX`, its static premises `LinkOkX`, `PlaceOk`,
`LinkFree` and the contract `ExtEvContractT` discharged; the partition, the environment's keeping
of allocations and of the oracle and the depth bound stay premises). -/
theorem funRealT_link_X {env : Clif.Env} (henv : env.extern "ld" = none) {Bnd : Nat → Prop}
    {c0 : TState} {Loc : Nat → Nat → Prop} {Dcap : Nat}
    (hP : PartsOk env pX c0 Loc) (hdisj : PartDisj Loc)
    (hk : Clif.EnvKeepsAllocs env) (hkp : Clif.EnvKeepsPlace env)
    (hdep : ∀ S, RReach env pX c0 (.run S) → S.callers.length < Dcap) :
    ∀ g u c, EntX linkX env pX Bnd c0 Loc fr2 Mx2 Dcap (fun _ => none) (· = "ld") g u c →
      FunRealG (RealT env pX Bnd) linkX.M (OkB Bnd)
        (RetX linkX env pX c0 Loc fr2 (fun _ => none) (fun _ => [.x 0]) g) (EndT env pX Dcap) u c :=
  funRealT_link_ext hP hdisj linkFreeX hk hkp placeOkX hdep (linkOkX henv) extX

end Concurrency.CallSegOkGT.WitnessExt
