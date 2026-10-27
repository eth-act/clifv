import FV.Concurrency.RealizeWitnessRmw

/-!
# `Realizes` on a run of compiled code through an `atomic_cas` loop (T2m, #311)

The CLIF function `%cas(i64, i64, i64) -> i64 { v3 = atomic_cas.i64 v0, v1, v2; return v3 }`
(`fC`) as the pipeline compiles it (`lowerFunction`, `prepare`, `spillAlloc`): after the 18
saves, the entry `args`, the spills of `x0`–`x2` and their reloads into x25, x26, x28, the LL/SC
loop `ldaxr x27, [x25]; cmp x27, x26; b.ne out; stlxr w24, x28, [x25]; cbnz w24`.

* `compiled_ofC`: every premise of `RealizeCompiled.CompiledLS`;
* `run_cas`: the precise run (reading the thread's own bytes) through the saves, the `args`, the
  moves and one successful iteration of the loop (`ArmAllocThread.cas_fwd`: the bytes at the
  address equal the expected value, 0): an `acqXR` read and a `relXW` write, 8 bytes at address
  0, two steps without events between them; every earlier event private and plain;
* **`realizes_cas`**: `WitnessR.realizes_pair` on `run_cas`: every execution of the realized
  prefix (reads from the latest earlier write, `rmw` the prefix's monitor pairs) is `Realizes`d by
  a CLIF thread from `csC`; on the whole run that `rmw` relates the read to the write.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.RealizeCompiled.WitnessC

open Arm ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine
  ArmAllocThread ThreadCompose E2E ArmInstFoot Code RealizeCompiled.Witness RealizeCompiled.WitnessL
  RealizeCompiled.WitnessR

/-! ## `atomic_cas`, compiled -/

/-- `atomic_cas.i64` at the first argument, expected the second, new value the third. -/
def srcC : String := "function %cas(i64, i64, i64) -> i64 {
block0(v0: i64, v1: i64, v2: i64):
    v3 = atomic_cas.i64 v0, v1, v2
    return v3
}
"

/-- The parsed function. -/
def fC : Clif.Function :=
  match Clif.parse srcC with
  | .ok p => p.funcs.headD default
  | .error _ => default

/-- Its lowering. -/
def vcC : VCode := match lowerFunction fC with
  | .ok vc => vc
  | .error _ => default

/-- `prepare`'s output. -/
def vcpC : VCode := match Backend.prepare vcC with
  | .ok vcp => vcp
  | .error _ => default

/-- The spill allocation. -/
def rfC : RFunc := spillAlloc vcpC

/-- The activation, entered with `sp = 0x6000`, its code at `0x20000`. -/
abbrev RAC : RL := ArmAllocThread.Witness.actAt 0x6000#64 0x20000#64 vcpC rfC

theorem checksC : lowerCheck fC vcC = true ∧ IselCheck.threadCheck fC = true ∧
    fC.externs.isEmpty = true ∧ (indSigs fC).isEmpty = true ∧ verifiable fC = true ∧
    IselThread.Witness.isOkB vcC.cfg = true ∧ vcC.outgoing = 0 ∧ prepCheck vcC vcpC = true ∧
    (checkAlloc vcpC rfC).isOk = true ∧ rfC.blocks.size = 1 ∧ (rfC.blocks[0]!).size = 47 := by
  native_decide

theorem allocC : checkAlloc vcpC rfC = .ok () := by
  have h := checksC.2.2.2.2.2.2.2.2.1
  revert h
  cases checkAlloc vcpC rfC with
  | ok u => intro _; rfl
  | error e => intro h; cases h

theorem cfgC : ∃ ss ps, vcC.cfg = .ok (ss, ps) := by
  have hb := checksC.2.2.2.2.2.1
  revert hb
  cases vcC.cfg with
  | ok r => intro _; exact ⟨r.1, r.2, rfl⟩
  | error e => intro h; cases h

theorem factsC : (lowerRFunc vcpC rfC).toBool = true ∧ (emitFunc 0 RAC.af).toBool = true ∧
    RAC.fa.k = 0 ∧ RAC.fa.layout.toBool = true ∧ (labelOffsets RAC.fa.lines).toBool = true ∧
    4 * RAC.fb.words.size ≤ 2 ^ 64 ∧ RAC.af.frameSize ≤ 0x100 ∧ 4 * RAC.fb.words.size ≤ 0x10000 ∧
    (blocksLinesE RAC.ctx RAC.af RAC.af.blocks.toList {}).toBool = true := by
  native_decide

theorem wfRC : RAC.Wf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := factsC
  exact ArmAllocThread.Witness.wf_ofAt (by decide) (by decide) (by decide) (by decide) allocC h1 h2
    h3 h4 h5 h6 h7 h8 h9

theorem codeRC : ∀ k < RAC.fb.words.size,
    Arm.read_mem_bytes 4 (0x20000#64 + BitVec.ofNat 64 (4 * k)) RAC.s0 = RAC.fb.words[k]! := by
  native_decide

theorem entryArgRC : ∀ r, RAC.vc.EntryArg r → r.isArgReg = true := by
  rintro r ⟨vb, ds, h1, h2, v, hv⟩
  have h : entryArgsB vcpC = true := by native_decide
  simp only [entryArgsB, show vcpC = RAC.vc from rfl, h1, h2, List.all_eq_true] at h
  exact h _ hv

/-- The entry world of the body. -/
abbrev w₀C : ArmState := E2E.bodyOf RAC.af RAC.s0

theorem qRC : ∃ n, Q RAC (iterN RAC.step n RAC.s0)
      (MConf.init RAC.rf (locVal RAC.fr (iterN RAC.step n RAC.s0)) w₀C) ∧
    AInv RAC (MConf.init RAC.rf (locVal RAC.fr (iterN RAC.step n RAC.s0)) w₀C) := by
  obtain ⟨n, -, hq, hA, -⟩ := q_init wfRC
    (ArmAllocThread.Witness.abi_ofAt (by decide) (by decide) factsC.2.2.2.2.2.2.2.1 codeRC)
    ((E2E.Binary.bodyEntry_bodyOf RAC.af RAC.s0).w RAC.F entryArgRC)
  exact ⟨n, hq, hA⟩

/-- The instructions the scope with LL/SC loops admits here, as a check. -/
def formCB (ctx : FnCtx) : MInst → Bool
  | .fence | .args _ | .rets _ | .atomicCasLoop .. => true
  | i@(.loadAcquire ..) => FormOk ctx i
  | _ => false

theorem scopeRC : MemScopeL RAC := by
  have h : RAC.vc.blocks.all (·.insts.all (formCB RAC.ctx)) = true := by native_decide
  intro b vb k i hb hi
  obtain ⟨hb', rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨hk', rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  have h1 := (Array.all_eq_true.mp h) b hb'
  have h2 := (Array.all_eq_true.mp h1) k hk'
  revert h2
  generalize RAC.vc.blocks[b].insts[k] = i
  intro h2
  cases i with
  | fence => exact .inl (.inr (.inl rfl))
  | args ds => exact .inl (.inl (.inr (.inl ⟨ds, rfl⟩)))
  | rets us => exact .inl (.inl (.inr (.inr (.inl ⟨us, rfl⟩))))
  | loadAcquire ty rt rn fl => exact .inl (.inr (.inr (.inl ⟨ty, rt, rn, fl, rfl, h2⟩)))
  | atomicCasLoop => exact .inr (.inr ⟨_, _, _, _, _, _, _, rfl⟩)
  | _ => simp [formCB] at h2

theorem scopeLSC : MemScopeLS RAC := memScopeLS_of_memScopeB (memScopeB_of_memScopeL scopeRC)

/-! ## The CLIF entry -/

/-- The function's entry block. -/
def B0C : Clif.Block := fC.blocks.headD default

/-- The arguments: `0 : i64` (the address), `0 : i64` (the expected value), `0 : i64` (the new
value). -/
def argsC : List Clif.Val := [⟨.i64, 0⟩, ⟨.i64, 0⟩, ⟨.i64, 0⟩]

/-- The entry registers. -/
def regsC : Clif.Regs := (Clif.Regs.empty.setMany (B0C.params.map (·.1)) argsC).getD Clif.Regs.empty

/-- **The CLIF entry state**: block 0, `v0 = v1 = v2 = 0`, no slots, one 8-byte allocation at 0. -/
def csC : Clif.State :=
  { frame := { func := fC, regs := regsC, slots := [], body := B0C.body, term := B0C.term }
    callers := []
    mem := memL }

/-- The memory relation's parameters. -/
def ΓC : E2E.Rel := ⟨RAC.F, fun _ => none, RAC.ctx.slotBase, 0⟩

theorem shapeC : fC.blocks.isEmpty = false ∧
    (Clif.Regs.empty.setMany (B0C.params.map (·.1)) argsC).isSome = true ∧
    argsC.map (·.ty) = B0C.params.map (·.2) ∧ argsC.map (·.ty) = fC.sig.params.map (·.ty) ∧
    (locsOf fC.sig).all (fun l => match l with | .stack _ => false | _ => true) = true ∧
    (match locsOf fC.sig with | [.reg (.x 0), .reg (.x 1), .reg (.x 2)] => true | _ => false) = true ∧
    (E2E.spv w₀C).toNat % 16 = 0 ∧ regVal RAC.s0 (.x 0) = 0 ∧ regVal RAC.s0 (.x 1) = 0 ∧
    regVal RAC.s0 (.x 2) = 0 ∧ Arm.read_mem_bytes 8 0 w₀C = 0 := by
  native_decide

theorem b0C : fC.blocks[0]? = some B0C := by
  have h := shapeC.1
  unfold B0C
  revert h
  cases fC.blocks with
  | nil => intro h; cases h
  | cons b bs => intro _; rfl

theorem regsC_eq : Clif.Regs.empty.setMany (B0C.params.map (·.1)) argsC = some regsC := by
  have h := shapeC.2.1
  unfold regsC
  revert h
  cases Clif.Regs.empty.setMany (B0C.params.map (·.1)) argsC with
  | none => intro h; cases h
  | some r => intro _; rfl

theorem errW₀C : Arm.r .ERR w₀C = .None := by
  rw [E2E.r_bodyOf _ _ (by simp) (by simp)]
  exact (ArmAllocThread.Witness.abi_ofAt (by decide) (by decide) factsC.2.2.2.2.2.2.2.1 codeRC).err

/-- **The first 8 bytes are no frame address.** -/
theorem notF_lowC : ∀ x < 8, ¬ RAC.F (BitVec.ofNat 64 x) := by
  have h : ∀ x < 8, fB RAC (BitVec.ofNat 64 x) = false := by native_decide
  intro x hx hF
  have := h x hx
  rw [fB_of rfl (fun _ h => h) hF] at this
  cases this

theorem relC : E2E.RelW ΓC fC (E2E.spv w₀C) [] memL w₀C := by
  refine ⟨⟨⟨fun a b _ hb => by simp [memL] at hb, fun a n hv => ?_, rfl⟩,
      fun id b h => by simp at h, E2E.outRel_zero _ _ _⟩, rfl, errW₀C⟩
  simp only [Clif.Mem.valid, memL, List.any_cons, List.any_nil, Bool.or_false,
    Clif.Alloc.contains] at hv
  have hv' : a + n ≤ 8 := by
    revert hv; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  exact ⟨by omega, fun k hk => notF_lowC _ (by omega)⟩

theorem locsC : locsOf fC.sig = [.reg (.x 0), .reg (.x 1), .reg (.x 2)] := by
  have h := shapeC.2.2.2.2.2.1
  revert h
  generalize locsOf fC.sig = l
  intro h
  match l, h with
  | [.reg (.x 0), .reg (.x 1), .reg (.x 2)], _ => rfl

theorem argsAtC : ArgsAtEntry RAC.F fC.sig argsC w₀C := by
  intro loc v h
  rw [locsC] at h
  simp only [argsC, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.mem_singleton,
    Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show VHolds _ _
    rw [VHolds, E2E.regVal_bodyOf _ _ (by decide), shapeC.2.2.2.2.2.2.2.1]
    rfl
  · show VHolds _ _
    rw [VHolds, E2E.regVal_bodyOf _ _ (by decide), shapeC.2.2.2.2.2.2.2.2.1]
    rfl
  · show VHolds _ _
    rw [VHolds, E2E.regVal_bodyOf _ _ (by decide), shapeC.2.2.2.2.2.2.2.2.2.1]
    rfl

/-- `CompiledLS` for the compiled `atomic_cas` at every Arm state `Q`-related to its entry
configuration. -/
theorem compiled_ofC {s : ArmState} (hq : Q RAC s (MConf.init RAC.rf (locVal RAC.fr s) w₀C))
    (hA : AInv RAC (MConf.init RAC.rf (locVal RAC.fr s) w₀C)) (env : Clif.Env) (p : Clif.Program) :
    CompiledLS env p RAC csC s := by
  obtain ⟨hlow, hthr, hext, hind, hv, -, hout, hprep, -⟩ := checksC
  obtain ⟨ctx, st0, R, gn, bl, A, H, hbl⟩ := driverHyp_of (Γ := ΓC) (fctx := RAC.ctx) (X := RAC.X)
    (c := E2E.spv w₀C) (env := env) (p := p) hlow hthr (List.isEmpty_iff.mp hext)
    (List.isEmpty_iff.mp hind) hv cfgC hout rfl (fun _ _ h => by cases h)
  obtain ⟨-, -, hpar, hsig, hlocs, -, hc, -⟩ := shapeC
  exact {
    wf := wfRC
    scope := scopeLSC
    gv := rfl
    front := ⟨fC, vcC, ctx, st0, R, gn, bl, A, _, [], ΓC.slotOff, ΓC.syms, B0C, argsC, _, w₀C, H,
      hbl, E2E.memRelOk_relW ΓC fC _, IselRefines.Witness.relW_wf hc,
      VCodeThread.Witness.X0_tls, memRefines_csem RAC.F RAC.ctx _ rfl (fun _ _ h => by cases h),
      E2E.mrStable_relW ΓC fC _,
      (fun off h => by
        have := List.all_eq_true.mp hlocs _ h
        simp at this),
      hprep, allocC, b0C, rfl, rfl, rfl, rfl, rfl, regsC_eq, hpar, hsig, relC, argsAtC, hq, hA⟩ }

/-! ## The run through the loop -/

/-- The spills of `x0`–`x2` and their reloads into x25, x26, x28. -/
def spillC : List (Loc × Loc) :=
  [(.reg (.x 0), .stack 0 .int), (.reg (.x 1), .stack 1 .int), (.reg (.x 2), .stack 2 .int),
    (.stack 0 .int, .reg (.x 25)), (.stack 1 .int, .reg (.x 26)), (.stack 2 .int, .reg (.x 28))]

/-- The loop item's allocation. -/
def allocsC : Array Loc := #[.reg (.x 25), .reg (.x 26), .reg (.x 28), .reg (.x 27), .reg (.x 24)]

/-- The items after the loop item. -/
def itsC : List RItem := (rfC.blocks[0]!).toList.drop 26

/-- The entry `args` and the loop instruction (as a check). -/
def instsB : Bool :=
  match vcpC.blocks[0]? with
  | some vb => (match vb.insts[0]? with
      | some (MInst.args [(Reg.vreg 0 RegClass.int, Reg.x 0), (Reg.vreg 1 RegClass.int, Reg.x 1),
          (Reg.vreg 2 RegClass.int, Reg.x 2)]) =>
        true
      | _ => false) &&
    (match vb.insts[1]? with
      | some (MInst.atomicCasLoop (.int 64) _ _ _ _ _ _) => true
      | _ => false) && vb.insts.size == 3
  | none => false

theorem checksRunC : (rfC.blocks[0]!).toList = savesL.map (fun p => RItem.move p.1 p.2) ++
      (.op 0 #[.reg (.x 0), .reg (.x 1), .reg (.x 2)] :: (spillC.map (fun p => RItem.move p.1 p.2) ++
        (.op 1 allocsC :: itsC))) ∧
    savesL.all (moveOkB RAC (· == .plainW)) = true ∧
    spillC.all (moveOkB RAC fun K => K == .plainW || K == .plainR) = true ∧
    instsB = true ∧ 0 < vcpC.blocks.size := by
  native_decide

theorem vb0C : RAC.vc.blocks[0]? = some vcpC.blocks[0]! := by
  show vcpC.blocks[0]? = _
  rw [Array.getElem?_eq_getElem checksRunC.2.2.2.2]
  simp [getElem!_def, Array.getElem?_eq_getElem checksRunC.2.2.2.2]

theorem instsC : (vcpC.blocks[0]!).insts[0]? =
      some (.args [(.vreg 0 .int, .x 0), (.vreg 1 .int, .x 1), (.vreg 2 .int, .x 2)]) ∧
    (∃ fl ra re rx rd r1, (vcpC.blocks[0]!).insts[1]? =
      some (.atomicCasLoop (.int 64) fl ra re rx rd r1)) ∧
    (vcpC.blocks[0]!).insts.size = 3 := by
  have h := checksRunC.2.2.2.1
  unfold instsB at h
  rw [show vcpC.blocks[0]? = some vcpC.blocks[0]! from vb0C] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, h3⟩
  · revert h1
    generalize (vcpC.blocks[0]!).insts[0]? = oi
    intro h1
    split at h1
    · rfl
    · cases h1
  · revert h2
    generalize (vcpC.blocks[0]!).insts[1]? = oi
    intro h2
    split at h2
    · exact ⟨_, _, _, _, _, _, rfl⟩
    · cases h2

/-- The entry `args` as a step of the allocated code. -/
theorem args_stepC (its : List RItem) (m : Loc → CV) (w : ArmState) :
    ∃ m', MStep RAC.vc RAC.sem ckeep RAC.rf
      (.run ⟨0, .op 0 #[.reg (.x 0), .reg (.x 1), .reg (.x 2)] :: its, m, w⟩) (.run ⟨0, its, m', w⟩) ∧
      m' (.reg (.x 0)) = regVal w (.x 0) ∧ m' (.reg (.x 1)) = regVal w (.x 1) := by
  obtain ⟨hi, -, hsz⟩ := instsC
  refine ⟨_, MStep.op vb0C hi (operands_args [(0, .x 0), (1, .x 1), (2, .x 2)]) rfl rfl
    (by simp [argOps, Operand.isDef]) (HavocOuts.refl _ _ _)
    ⟨fun _ _ => rfl, fun c hc => by cases hc⟩ (MNext.next (by rw [hsz]; decide)), ?_, ?_⟩
  all_goals simp [writeM, argOps, Operand.isDef, Operand.isLate, Operand.isEarly, Backend.Proof.upd]

/-- **The run of the compiled `atomic_cas` through one successful iteration of its loop**: after
the prologue, a precise run reading the thread's own bytes ending in the `ldaxr`'s `acqXR` read,
the `cmp` and the `b.ne` (no events; the bytes at address 0 are the expected 0) and the `stlxr`'s
`relXW` write, both 8 bytes at address 0 (the argument); every earlier event private and plain;
`CompiledLS` at its start. -/
theorem run_cas : ∃ (n : Nat) (lsP : List Lab) (eR eW : Ev) (t' : ArmState × Mon),
    (∀ env p, CompiledLS env p RAC csC (iterN RAC.step n RAC.s0)) ∧
    PRun Policy.arm RAC.step (OkPriv RAC) (iterN RAC.step n RAC.s0, none) (pairLs lsP eR eW 2) t' ∧
    eR.k = .acqXR ∧ eW.k = .relXW ∧ eR.addr = 0 ∧ eW.addr = 0 ∧ eR.n = 8 ∧ eW.n = 8 ∧
    (∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RAC e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR)) := by
  obtain ⟨n', hq, hA⟩ := qRC
  have e0 := checksRunC.1
  have hq0 := hq
  have hA0 := hA
  simp only [MConf.init] at hq0 hA0
  rw [show RAC.rf = rfC from rfl, e0] at hq0 hA0
  -- the saves
  obtain ⟨ls1, t1, r1, hq1, hA1, hev1⟩ := moves_fwdA wfRC (fun K => (K == .plainW) = true)
    savesL _ _ _ none hq0 hA0 (moves_kinds checksRunC.2.1) (by simp [savesL, Loc.isSave])
  -- the entry `args`
  obtain ⟨m', hst, hm0, hm1⟩ := args_stepC (spillC.map (fun p => RItem.move p.1 p.2) ++
    (.op 1 allocsC :: itsC)) _ w₀C
  have hq2 := realizes_args wfRC hq1 hA1 vb0C instsC.1 hst
  have hA2 := Backend.Proof.aInv_step wfRC hq1 hA1 hst
  -- the spills and reloads
  obtain ⟨ls2, t2, r2, hq3, -, hev2⟩ := moves_fwdA wfRC
    (fun K => (K == .plainW || K == .plainR) = true) spillC (.op 1 allocsC :: itsC) t1.1 m' t1.2
    hq2 hA2 (moves_kinds checksRunC.2.2.1) (by simp [spillC, Loc.isSave])
  -- the loop
  obtain ⟨fl, ra, re, rx, rd, q1, hi1⟩ := instsC.2.1
  obtain ⟨j0, nl, X, hdrop, hprog, hpc, herr, hstr⟩ :=
    cas_lines wfRC hq3 LoopWitness.hty64 vb0C hi1
  -- the address and the expected value: the arguments, `0`
  have hreg : ∀ (q : Nat), movesM spillC m' (.reg (.x q)) = 0 → (q = 25 ∨ q = 26) →
      Arm.r (.GPR (rnum q)) t2.1 = 0 := by
    intro q hv hq
    have hs := hstr.store (.reg (.x q)) (fun r h => by cases h; rcases hq with rfl | rfl <;> rfl)
      trivial
    rw [hv] at hs
    have := congrArg lo64 hs
    simp only [locVal, lo64_regVal_x] at this
    exact this.symm.trans (by simp [lo64])
  have hx25 : movesM spillC m' (.reg (.x 25)) = regVal w₀C (.x 0) := by
    simp [movesM, spillC, Backend.Proof.upd, hm0]
  have hx26 : movesM spillC m' (.reg (.x 26)) = regVal w₀C (.x 1) := by
    simp [movesM, spillC, Backend.Proof.upd, hm1]
  have hz0 : regVal w₀C (.x 0) = 0 := by
    rw [E2E.regVal_bodyOf _ _ (by decide), shapeC.2.2.2.2.2.2.2.1]
  have hz1 : regVal w₀C (.x 1) = 0 := by
    rw [E2E.regVal_bodyOf _ _ (by decide), shapeC.2.2.2.2.2.2.2.2.1]
  have h25 : Arm.r (.GPR 25#5) t2.1 = 0 := hreg 25 (hx25.trans hz0) (.inl rfl)
  have h26 : Arm.r (.GPR 26#5) t2.1 = 0 := hreg 26 (hx26.trans hz1) (.inr rfl)
  have hmem : Arm.read_mem_bytes (CTy.int 64).bytes (Arm.r (.GPR 25#5) t2.1) t2.1 =
      (Arm.r (.GPR 26#5) t2.1).setWidth ((CTy.int 64).bytes * 8) := by
    rw [h25, h26]
    show Arm.read_mem_bytes 8 0 t2.1 = (0 : BitVec 64).setWidth 64
    rw [read_mem_bytes_sameWorld hstr.world (fun k hk => by
      have := notF_lowC k hk; simpa using this), shapeC.2.2.2.2.2.2.2.2.2.2]
    rfl
  obtain ⟨v, t3, r3⟩ := cas_fwd wfRC LoopWitness.hty64 hdrop hprog hpc herr hmem t2.2
  have hr := PRun.append (PRun.append r1 r2) r3
  have hevP : ∀ l ∈ ls1 ++ ls2, ∀ e' ∈ l.evs,
      PrivA RAC e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR) := by
    intro l hl e' he'
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨hF, hK⟩ := hev1 l hl e' he'
      exact ⟨privA_addr.2 hF, .inl (by simpa using hK)⟩
    · obtain ⟨hF, hK⟩ := hev2 l hl e' he'
      exact ⟨privA_addr.2 hF, by simpa using hK⟩
  exact ⟨n', ls1 ++ ls2, _, _, _, fun env p => compiled_ofC hq hA env p, hr, rfl, rfl, h25, h25,
    rfl, rfl, hevP⟩

/-- **`Realizes` on the compiled `atomic_cas` through one successful iteration of its loop**
(module doc): the run of `run_cas`; every execution of its realized prefix (initial locations
`locs1`, the pair's first; `rmw` the prefix's monitor pairs) is `Realizes`d by a CLIF thread from
`csC`; on the whole run, that `rmw` relates the read to the write. -/
theorem realizes_cas : ∃ (n : Nat) (lsP : List Lab) (eR eW : Ev) (t' : ArmState × Mon),
    PRun Policy.arm RAC.step (OkPriv RAC) (iterN RAC.step n RAC.s0, none) (pairLs lsP eR eW 2) t' ∧
    eR.k = .acqXR ∧ eW.k = .relXW ∧ eR.addr = 0 ∧ eW.addr = 0 ∧ eR.n = 8 ∧ eW.n = 8 ∧
    (∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RAC e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR)) ∧
    rmwP (pairLs lsP eR eW 2) (pairLs lsP eR eW 2).length (.thr 0 lsP.length 0)
      (.thr 0 (lsP.length + 2 + 1) 0) ∧
    ∀ (env : Clif.Env) (p : Clif.Program) (M0 : Bytes), ∃ k ≤ (pairLs lsP eR eW 2).length,
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧ PC.st 0 0 = .run csC ∧
        PC.Runs (CStep env p) ∧
        Realizes (PA1 RAC (iterN RAC.step n RAC.s0) (pairLs lsP eR eW 2) k) (locs1 lsP eR) M0
          (latestW (PA1 RAC (iterN RAC.step n RAC.s0) (pairLs lsP eR eW 2) k) (locs1 lsP eR))
          (coL (PA1 RAC (iterN RAC.step n RAC.s0) (pairLs lsP eR eW 2) k) (locs1 lsP eR))
          (rmwP (pairLs lsP eR eW 2) k) PC [(eR.addr.toNat, eR.n)] M0 φ (fun _ _ _ => True) := by
  obtain ⟨n, lsP, eR, eW, t', hc, hr, hkR, hkW, haR, haW, hnR, hnW, hevP⟩ := run_cas
  exact ⟨n, lsP, eR, eW, t', hr, hkR, hkW, haR, haW, hnR, hnW, hevP,
    rmw_full hkR hkW fun l hl e he => (hevP l hl e he).2, fun env p M0 =>
    realizes_pair hc hr hevP hkR hkW (haW.trans haR.symm) (hnW.trans hnR.symm) env p M0⟩

/-- **`Realizes` on the compiled `atomic_cas`, the realized prefix covering the run** (T2j,
`realizes_pair_cov`): the run of `run_cas`; its realized prefix is the whole run, or a CLIF thread
run from `csC` realizes it and then stops (`Covers`). The whole run does not follow here (unlike
`WitnessR.realizes_rmw_full`): this `atomic_cas` stores the value it finds (`0` over `0`), and a
CLIF `atomic_cas` whose store leaves the bytes unchanged is a step with the read alone
(`ClifThread.evShape`), which realizes the run up to the `ldaxr` and then returns. -/
theorem realizes_cas_cov : ∃ (n : Nat) (lsP : List Lab) (eR eW : Ev) (t' : ArmState × Mon),
    PRun Policy.arm RAC.step (OkPriv RAC) (iterN RAC.step n RAC.s0, none) (pairLs lsP eR eW 2) t' ∧
    eR.k = .acqXR ∧ eW.k = .relXW ∧ eR.addr = 0 ∧ eW.addr = 0 ∧ eR.n = 8 ∧ eW.n = 8 ∧
    (∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RAC e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR)) ∧
    ∀ (env : Clif.Env) (p : Clif.Program) (M0 : Bytes), ∃ k ≤ (pairLs lsP eR eW 2).length,
      Covers env p RAC csC (pairLs lsP eR eW 2) k ∧
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧ PC.st 0 0 = .run csC ∧
        PC.Runs (CStep env p) ∧
        Realizes (PA1 RAC (iterN RAC.step n RAC.s0) (pairLs lsP eR eW 2) k) (locs1 lsP eR) M0
          (latestW (PA1 RAC (iterN RAC.step n RAC.s0) (pairLs lsP eR eW 2) k) (locs1 lsP eR))
          (coL (PA1 RAC (iterN RAC.step n RAC.s0) (pairLs lsP eR eW 2) k) (locs1 lsP eR))
          (rmwP (pairLs lsP eR eW 2) k) PC [(eR.addr.toNat, eR.n)] M0 φ (fun _ _ _ => True) := by
  obtain ⟨n, lsP, eR, eW, t', hc, hr, hkR, hkW, haR, haW, hnR, hnW, hevP⟩ := run_cas
  exact ⟨n, lsP, eR, eW, t', hr, hkR, hkW, haR, haW, hnR, hnW, hevP, fun env p M0 =>
    realizes_pair_cov hc hr hevP hkR hkW (haW.trans haR.symm) (hnW.trans hnR.symm) env p M0⟩

end Concurrency.RealizeCompiled.WitnessC
