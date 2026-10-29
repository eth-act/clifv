module

public import FV.Concurrency.RealizeWitnessLoad
public import FV.Concurrency.ArmAllocLoopFwd
public import FV.Concurrency.ArmAllocLoopWitness

@[expose] public section

/-!
# `Realizes` on a run of compiled code through an `atomic_rmw` loop (T2m, #311)

The CLIF function `%rmw(i64, i64) -> i64 { v2 = atomic_rmw.i64 add v0, v1; return v2 }` (`fR`)
as the pipeline compiles it (`lowerFunction`, `prepare`, `spillAlloc`; the activation loaded as
`ArmAllocThread.Witness.actAt` loads it): after the 18 saves, the entry `args`, the spills of `x0`,
`x1` and their reloads into x25, x26, the LL/SC loop `ldaxr x27, [x25]; add; stlxr w24, x28,
[x25]; cbnz w24`.

* `compiled_ofR`: every premise of `RealizeCompiled.CompiledLS` (the scope with LL/SC loops);
* `run_rmw`: the precise run (reading the thread's own bytes) through the saves, the `args`, the
  moves and one successful iteration of the loop (`ArmAllocThread.rmw_fwd`): an `acqXR` read and
  a `relXW` write, 8 bytes at address 0 (the argument), with no event between them; every
  earlier event private and plain;
* `realizes_pair`: one compiled thread whose run is private plain accesses then such an exclusive
  pair: every execution of the realized prefix with reads from the latest earlier write and the
  prefix's monitor pairs as `rmw` is well formed (`wf_rmw`, `Exec.Wf.rmw_imm` over events) and
  `Realizes`d by a CLIF thread (`realizes_compiledLS`);
* **`realizes_rmw`**: `realizes_pair` on `run_rmw`; when the realized prefix is the whole run, the
  `rmw` relates the `ldaxr` read to the `stlxr` write (`rmw_full`).

Checks by `native_decide` (witness only).
-/

namespace Concurrency.RealizeCompiled.WitnessR

open Arm ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine
  ArmAllocThread ThreadCompose E2E ArmInstFoot Code RealizeCompiled.Witness RealizeCompiled.WitnessL

/-! ## `atomic_rmw`, compiled -/

/-- `atomic_rmw.i64 add` of the arguments. -/
def srcR : String := "function %rmw(i64, i64) -> i64 {
block0(v0: i64, v1: i64):
    v2 = atomic_rmw.i64 add v0, v1
    return v2
}
"

/-- The parsed function. -/
def fR : Clif.Function :=
  match Clif.parse srcR with
  | .ok p => p.funcs.headD default
  | .error _ => default

/-- Its lowering. -/
def vcR : VCode := match lowerFunction fR with
  | .ok vc => vc
  | .error _ => default

/-- `prepare`'s output. -/
def vcpR : VCode := match Backend.prepare vcR with
  | .ok vcp => vcp
  | .error _ => default

/-- The spill allocation. -/
def rfR : RFunc := spillAlloc vcpR

/-- The activation, entered with `sp = 0x6000`, its code at `0x20000`. -/
abbrev RAR : RL := ArmAllocThread.Witness.actAt 0x6000#64 0x20000#64 vcpR rfR

theorem checksR : lowerCheck fR vcR = true ∧ IselCheck.threadCheck fR = true ∧
    fR.externs.isEmpty = true ∧ (indSigs fR).isEmpty = true ∧ verifiable fR = true ∧
    IselThread.Witness.isOkB vcR.cfg = true ∧ vcR.outgoing = 0 ∧ prepCheck vcR vcpR = true ∧
    (checkAlloc vcpR rfR).isOk = true ∧ rfR.blocks.size = 1 ∧ (rfR.blocks[0]!).size = 45 := by
  native_decide

theorem allocR : checkAlloc vcpR rfR = .ok () := by
  have h := checksR.2.2.2.2.2.2.2.2.1
  revert h
  cases checkAlloc vcpR rfR with
  | ok u => intro _; rfl
  | error e => intro h; cases h

theorem cfgR : ∃ ss ps, vcR.cfg = .ok (ss, ps) := by
  have hb := checksR.2.2.2.2.2.1
  revert hb
  cases vcR.cfg with
  | ok r => intro _; exact ⟨r.1, r.2, rfl⟩
  | error e => intro h; cases h

theorem factsR : (lowerRFunc vcpR rfR).toBool = true ∧ (emitFunc 0 RAR.af).toBool = true ∧
    RAR.fa.k = 0 ∧ RAR.fa.layout.toBool = true ∧ (labelOffsets RAR.fa.lines).toBool = true ∧
    4 * RAR.fb.words.size ≤ 2 ^ 64 ∧ RAR.af.frameSize ≤ 0x100 ∧ 4 * RAR.fb.words.size ≤ 0x10000 ∧
    (blocksLinesE RAR.ctx RAR.af RAR.af.blocks.toList {}).toBool = true := by
  native_decide

theorem wfRR : RAR.Wf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := factsR
  exact ArmAllocThread.Witness.wf_ofAt (by decide) (by decide) (by decide) (by decide) allocR h1 h2
    h3 h4 h5 h6 h7 h8 h9

theorem codeRR : ∀ k < RAR.fb.words.size,
    Arm.read_mem_bytes 4 (0x20000#64 + BitVec.ofNat 64 (4 * k)) RAR.s0 = RAR.fb.words[k]! := by
  native_decide

theorem entryArgRR : ∀ r, RAR.vc.EntryArg r → r.isArgReg = true := by
  rintro r ⟨vb, ds, h1, h2, v, hv⟩
  have h : entryArgsB vcpR = true := by native_decide
  simp only [entryArgsB, show vcpR = RAR.vc from rfl, h1, h2, List.all_eq_true] at h
  exact h _ hv

/-- The entry world of the body. -/
abbrev w₀R : ArmState := E2E.bodyOf RAR.af RAR.s0

theorem qRR : ∃ n, Q RAR (iterN RAR.step n RAR.s0)
      (MConf.init RAR.rf (locVal RAR.fr (iterN RAR.step n RAR.s0)) w₀R) ∧
    AInv RAR (MConf.init RAR.rf (locVal RAR.fr (iterN RAR.step n RAR.s0)) w₀R) := by
  obtain ⟨n, -, hq, hA, -⟩ := q_init wfRR
    (ArmAllocThread.Witness.abi_ofAt (by decide) (by decide) factsR.2.2.2.2.2.2.2.1 codeRR)
    ((E2E.Binary.bodyEntry_bodyOf RAR.af RAR.s0).w RAR.F entryArgRR)
  exact ⟨n, hq, hA⟩

/-- The instructions the scope with LL/SC loops admits here, as a check. -/
def formRB (ctx : FnCtx) : MInst → Bool
  | .fence | .args _ | .rets _ | .atomicRmwLoop .. => true
  | i@(.loadAcquire ..) => FormOk ctx i
  | _ => false

theorem scopeRR : MemScopeL RAR := by
  have h : RAR.vc.blocks.all (·.insts.all (formRB RAR.ctx)) = true := by native_decide
  intro b vb k i hb hi
  obtain ⟨hb', rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨hk', rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  have h1 := (Array.all_eq_true.mp h) b hb'
  have h2 := (Array.all_eq_true.mp h1) k hk'
  revert h2
  generalize RAR.vc.blocks[b].insts[k] = i
  intro h2
  cases i with
  | fence => exact .inl (.inr (.inl rfl))
  | args ds => exact .inl (.inl (.inr (.inl ⟨ds, rfl⟩)))
  | rets us => exact .inl (.inl (.inr (.inr (.inl ⟨us, rfl⟩))))
  | loadAcquire ty rt rn fl => exact .inl (.inr (.inr (.inl ⟨ty, rt, rn, fl, rfl, h2⟩)))
  | atomicRmwLoop => exact .inr (.inl ⟨_, _, _, _, _, _, _, _, rfl⟩)
  | _ => simp [formRB] at h2

theorem scopeLSR : MemScopeLS RAR := memScopeLS_of_memScopeB (memScopeB_of_memScopeL scopeRR)

/-! ## The CLIF entry -/

/-- The function's entry block. -/
def B0R : Clif.Block := fR.blocks.headD default

/-- The arguments: `0 : i64` (the address) and `0 : i64` (the addend). -/
def argsR : List Clif.Val := [⟨.i64, 0⟩, ⟨.i64, 0⟩]

/-- The entry registers. -/
def regsR : Clif.Regs := (Clif.Regs.empty.setMany (B0R.params.map (·.1)) argsR).getD Clif.Regs.empty

/-- **The CLIF entry state**: block 0, `v0 = v1 = 0`, no slots, one 8-byte allocation at 0. -/
def csR : Clif.State :=
  { frame := { func := fR, regs := regsR, slots := [], body := B0R.body, term := B0R.term }
    callers := []
    mem := memL }

/-- The memory relation's parameters. -/
def ΓR : E2E.Rel := ⟨RAR.F, fun _ => none, RAR.ctx.slotBase, 0⟩

theorem shapeR : fR.blocks.isEmpty = false ∧
    (Clif.Regs.empty.setMany (B0R.params.map (·.1)) argsR).isSome = true ∧
    argsR.map (·.ty) = B0R.params.map (·.2) ∧ argsR.map (·.ty) = fR.sig.params.map (·.ty) ∧
    (locsOf fR.sig).all (fun l => match l with | .stack _ => false | _ => true) = true ∧
    (match locsOf fR.sig with | [.reg (.x 0), .reg (.x 1)] => true | _ => false) = true ∧
    (E2E.spv w₀R).toNat % 16 = 0 ∧ regVal RAR.s0 (.x 0) = 0 ∧ regVal RAR.s0 (.x 1) = 0 := by
  native_decide

theorem b0R : fR.blocks[0]? = some B0R := by
  have h := shapeR.1
  unfold B0R
  revert h
  cases fR.blocks with
  | nil => intro h; cases h
  | cons b bs => intro _; rfl

theorem regsR_eq : Clif.Regs.empty.setMany (B0R.params.map (·.1)) argsR = some regsR := by
  have h := shapeR.2.1
  unfold regsR
  revert h
  cases Clif.Regs.empty.setMany (B0R.params.map (·.1)) argsR with
  | none => intro h; cases h
  | some r => intro _; rfl

theorem errW₀R : Arm.r .ERR w₀R = .None := by
  rw [E2E.r_bodyOf _ _ (by simp) (by simp)]
  exact (ArmAllocThread.Witness.abi_ofAt (by decide) (by decide) factsR.2.2.2.2.2.2.2.1 codeRR).err

/-- **The first 8 bytes are no frame address.** -/
theorem notF_lowR : ∀ x < 8, ¬ RAR.F (BitVec.ofNat 64 x) := by
  have h : ∀ x < 8, fB RAR (BitVec.ofNat 64 x) = false := by native_decide
  intro x hx hF
  have := h x hx
  rw [fB_of rfl (fun _ h => h) hF] at this
  cases this

theorem relR : E2E.RelW ΓR fR (E2E.spv w₀R) [] memL w₀R := by
  refine ⟨⟨⟨fun a b _ hb => by simp [memL] at hb, fun a n hv => ?_, rfl⟩,
      fun id b h => by simp at h, E2E.outRel_zero _ _ _⟩, rfl, errW₀R⟩
  simp only [Clif.Mem.valid, memL, List.any_cons, List.any_nil, Bool.or_false,
    Clif.Alloc.contains] at hv
  have hv' : a + n ≤ 8 := by
    revert hv; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  exact ⟨by omega, fun k hk => notF_lowR _ (by omega)⟩

theorem locsR : locsOf fR.sig = [.reg (.x 0), .reg (.x 1)] := by
  have h := shapeR.2.2.2.2.2.1
  revert h
  generalize locsOf fR.sig = l
  intro h
  match l, h with
  | [.reg (.x 0), .reg (.x 1)], _ => rfl

theorem argsAtR : ArgsAtEntry RAR.F fR.sig argsR w₀R := by
  intro loc v h
  rw [locsR] at h
  simp only [argsR, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.mem_singleton,
    Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show VHolds _ _
    rw [VHolds, E2E.regVal_bodyOf _ _ (by decide), shapeR.2.2.2.2.2.2.2.1]
    rfl
  · show VHolds _ _
    rw [VHolds, E2E.regVal_bodyOf _ _ (by decide), shapeR.2.2.2.2.2.2.2.2]
    rfl

/-- `CompiledLS` for the compiled `atomic_rmw` at every Arm state `Q`-related to its entry
configuration. -/
theorem compiled_ofR {s : ArmState} (hq : Q RAR s (MConf.init RAR.rf (locVal RAR.fr s) w₀R))
    (hA : AInv RAR (MConf.init RAR.rf (locVal RAR.fr s) w₀R)) (env : Clif.Env) (p : Clif.Program) :
    CompiledLS env p RAR csR s := by
  obtain ⟨hlow, hthr, hext, hind, hv, -, hout, hprep, -⟩ := checksR
  obtain ⟨ctx, st0, R, gn, bl, A, H, hbl⟩ := driverHyp_of (Γ := ΓR) (fctx := RAR.ctx) (X := RAR.X)
    (c := E2E.spv w₀R) (env := env) (p := p) hlow hthr (List.isEmpty_iff.mp hext)
    (List.isEmpty_iff.mp hind) hv cfgR hout rfl (fun _ _ h => by cases h)
  obtain ⟨-, -, hpar, hsig, hlocs, -, hc, -⟩ := shapeR
  exact {
    wf := wfRR
    scope := scopeLSR
    gv := rfl
    front := ⟨fR, vcR, ctx, st0, R, gn, bl, A, _, [], ΓR.slotOff, ΓR.syms, B0R, argsR, _, w₀R, H,
      hbl, E2E.memRelOk_relW ΓR fR _, IselRefines.Witness.relW_wf hc,
      VCodeThread.Witness.X0_tls, memRefines_csem RAR.F RAR.ctx _ rfl (fun _ _ h => by cases h),
      E2E.mrStable_relW ΓR fR _,
      (fun off h => by
        have := List.all_eq_true.mp hlocs _ h
        simp at this),
      hprep, allocR, b0R, rfl, rfl, rfl, rfl, rfl, regsR_eq, hpar, hsig, relR, argsAtR, hq, hA⟩ }

/-! ## The run through the loop -/

/-- The spills of `x0`, `x1` and their reloads into x25, x26. -/
def spillR : List (Loc × Loc) :=
  [(.reg (.x 0), .stack 0 .int), (.reg (.x 1), .stack 1 .int), (.stack 0 .int, .reg (.x 25)),
    (.stack 1 .int, .reg (.x 26))]

/-- The loop item's allocation. -/
def allocsR : Array Loc := #[.reg (.x 25), .reg (.x 26), .reg (.x 27), .reg (.x 24), .reg (.x 28)]

/-- The items after the loop item. -/
def itsR : List RItem := (rfR.blocks[0]!).toList.drop 24

/-- The entry `args` and the loop instruction (as a check). -/
def instsB : Bool :=
  match vcpR.blocks[0]? with
  | some vb => (match vb.insts[0]? with
      | some (MInst.args [(Reg.vreg 0 RegClass.int, Reg.x 0), (Reg.vreg 1 RegClass.int, Reg.x 1)]) =>
        true
      | _ => false) &&
    (match vb.insts[1]? with
      | some (MInst.atomicRmwLoop (.int 64) .add _ _ _ _ _ _) => true
      | _ => false) && vb.insts.size == 3
  | none => false

theorem checksRunR : (rfR.blocks[0]!).toList = savesL.map (fun p => RItem.move p.1 p.2) ++
      (.op 0 #[.reg (.x 0), .reg (.x 1)] :: (spillR.map (fun p => RItem.move p.1 p.2) ++
        (.op 1 allocsR :: itsR))) ∧
    savesL.all (moveOkB RAR (· == .plainW)) = true ∧
    spillR.all (moveOkB RAR fun K => K == .plainW || K == .plainR) = true ∧
    instsB = true ∧ 0 < vcpR.blocks.size := by
  native_decide

theorem vb0R : RAR.vc.blocks[0]? = some vcpR.blocks[0]! := by
  show vcpR.blocks[0]? = _
  rw [Array.getElem?_eq_getElem checksRunR.2.2.2.2]
  simp [getElem!_def, Array.getElem?_eq_getElem checksRunR.2.2.2.2]

theorem instsR : (vcpR.blocks[0]!).insts[0]? =
      some (.args [(.vreg 0 .int, .x 0), (.vreg 1 .int, .x 1)]) ∧
    (∃ fl ra ro rd r1 r2, (vcpR.blocks[0]!).insts[1]? =
      some (.atomicRmwLoop (.int 64) .add fl ra ro rd r1 r2)) ∧
    (vcpR.blocks[0]!).insts.size = 3 := by
  have h := checksRunR.2.2.2.1
  unfold instsB at h
  rw [show vcpR.blocks[0]? = some vcpR.blocks[0]! from vb0R] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, h3⟩
  · revert h1
    generalize (vcpR.blocks[0]!).insts[0]? = oi
    intro h1
    split at h1
    · rfl
    · cases h1
  · revert h2
    generalize (vcpR.blocks[0]!).insts[1]? = oi
    intro h2
    split at h2
    · exact ⟨_, _, _, _, _, _, rfl⟩
    · cases h2

/-- The entry `args` as a step of the allocated code. -/
theorem args_stepR (its : List RItem) (m : Loc → CV) (w : ArmState) :
    ∃ m', MStep RAR.vc RAR.sem ckeep RAR.rf
      (.run ⟨0, .op 0 #[.reg (.x 0), .reg (.x 1)] :: its, m, w⟩) (.run ⟨0, its, m', w⟩) ∧
      m' (.reg (.x 0)) = regVal w (.x 0) ∧ m' (.reg (.x 1)) = regVal w (.x 1) := by
  obtain ⟨hi, -, hsz⟩ := instsR
  refine ⟨_, MStep.op vb0R hi (operands_args [(0, .x 0), (1, .x 1)]) rfl rfl
    (by simp [argOps, Operand.isDef]) (HavocOuts.refl _ _ _)
    ⟨fun _ _ => rfl, fun c hc => by cases hc⟩ (MNext.next (by rw [hsz]; decide)), ?_, ?_⟩
  all_goals simp [writeM, argOps, Operand.isDef, Operand.isLate, Operand.isEarly, Backend.Proof.upd]

/-- The number of middle lines of the loop. -/
abbrev MR : Nat := (rmwLoopMid .add (CTy.int 64).bits).length

/-- **The run of the compiled `atomic_rmw` through one successful iteration of its loop**: after
the prologue, a precise run reading the thread's own bytes ending in the `ldaxr`'s `acqXR` read,
`MR` steps without events and the `stlxr`'s `relXW` write, both 8 bytes at address 0 (the
argument); every earlier event private and plain; `CompiledLS` at its start. -/
theorem run_rmw : ∃ (n : Nat) (lsP : List Lab) (eR eW : Ev) (t' : ArmState × Mon),
    (∀ env p, CompiledLS env p RAR csR (iterN RAR.step n RAR.s0)) ∧
    PRun Policy.arm RAR.step (OkPriv RAR) (iterN RAR.step n RAR.s0, none)
      (lsP ++ (⟨[eR], false⟩ :: (List.replicate MR ⟨[], false⟩ ++ [⟨[eW], false⟩]))) t' ∧
    eR.k = .acqXR ∧ eW.k = .relXW ∧ eR.addr = 0 ∧ eW.addr = 0 ∧ eR.n = 8 ∧ eW.n = 8 ∧
    (∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RAR e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR)) := by
  obtain ⟨n', hq, hA⟩ := qRR
  have e0 := checksRunR.1
  have hq0 := hq
  have hA0 := hA
  simp only [MConf.init] at hq0 hA0
  rw [show RAR.rf = rfR from rfl, e0] at hq0 hA0
  -- the saves
  obtain ⟨ls1, t1, r1, hq1, hA1, hev1⟩ := moves_fwdA wfRR (fun K => (K == .plainW) = true)
    savesL _ _ _ none hq0 hA0 (moves_kinds checksRunR.2.1)
  -- the entry `args`
  obtain ⟨m', hst, hm0, -⟩ := args_stepR (spillR.map (fun p => RItem.move p.1 p.2) ++
    (.op 1 allocsR :: itsR)) _ w₀R
  have hq2 := realizes_args wfRR hq1 hA1 vb0R instsR.1 hst
  have hA2 := Backend.Proof.aInv_step wfRR hq1 hA1 hst
  -- the spills and reloads
  obtain ⟨ls2, t2, r2, hq3, -, hev2⟩ := moves_fwdA wfRR
    (fun K => (K == .plainW || K == .plainR) = true) spillR (.op 1 allocsR :: itsR) t1.1 m' t1.2
    hq2 hA2 (moves_kinds checksRunR.2.2.1)
  -- the loop
  obtain ⟨fl, ra, ro, rd, q1, q2, hi1⟩ := instsR.2.1
  obtain ⟨j0, nl, T, hd1, hL0, hprog, hpc, herr, hstr⟩ :=
    rmw_lines wfRR hq3 LoopWitness.hty64 vb0R hi1
  have r3 := rmw_fwd wfRR LoopWitness.hty64 hd1 hL0 hprog hpc herr t2.2
  -- the address: the argument, `x0 = 0`
  have hx25 : movesM spillR m' (.reg (.x 25)) = regVal w₀R (.x 0) := by
    simp [movesM, spillR, Backend.Proof.upd, hm0]
  have hs3 := hstr.store (.reg (.x 25)) (fun r h => by cases h; rfl) trivial
  rw [hx25] at hs3
  have hz : regVal w₀R (.x 0) = 0 := by
    rw [E2E.regVal_bodyOf _ _ (by decide), shapeR.2.2.2.2.2.2.2.1]
  have ha : Arm.r (.GPR 25#5) t2.1 = 0 := by
    rw [hz] at hs3
    have := congrArg lo64 hs3
    simp only [locVal, lo64_regVal_x] at this
    exact this.symm.trans (by simp [lo64])
  have hr : PRun Policy.arm RAR.step (OkPriv RAR) (iterN RAR.step n' RAR.s0, none)
      ((ls1 ++ ls2) ++ (⟨[loopRd (.int 64) t2.1 t2.1], false⟩ :: (List.replicate MR ⟨[], false⟩ ++
        [⟨[⟨.relXW, Arm.r (.GPR 25#5) t2.1, (CTy.int 64).bytes, rmwNew (.int 64) .add t2.1⟩],
          false⟩]))) _ :=
    PRun.append (PRun.append r1 r2) r3
  have hevP : ∀ l ∈ ls1 ++ ls2, ∀ e' ∈ l.evs,
      PrivA RAR e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR) := by
    intro l hl e' he'
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨hF, hK⟩ := hev1 l hl e' he'
      exact ⟨privA_addr.2 hF, .inl (by simpa using hK)⟩
    · obtain ⟨hF, hK⟩ := hev2 l hl e' he'
      exact ⟨privA_addr.2 hF, by simpa using hK⟩
  exact ⟨n', ls1 ++ ls2, _, _, _, fun env p => compiled_ofR hq hA env p, hr, rfl, rfl, ha, ha,
    rfl, rfl, hevP⟩

/-! ## One compiled thread, a private prefix and an exclusive pair -/

/-- The Arm trace shape: a prefix, the `ldaxr`'s read, `M` steps without events, the `stlxr`'s
write. -/
abbrev pairLs (lsP : List Lab) (eR eW : Ev) (M : Nat) : List Lab :=
  lsP ++ (⟨[eR], false⟩ :: (List.replicate M ⟨[], false⟩ ++ [⟨[eW], false⟩]))

/-- The `rmw` of the realized prefix: its monitor pairs. -/
def rmwP (ls : List Lab) (k : Nat) (a b : PEv) : Prop :=
  ∃ j kk j' kk', a = .thr 0 j kk ∧ b = .thr 0 j' kk' ∧ MonPair (evTr (ls.take k)) (j, kk) (j', kk')

theorem evAt_take_some {ls : List Lab} {k : Nat} {p : Nat × Nat} {x : Ev}
    (h : evAt (evTr (ls.take k)) p = some x) : evAt (evTr ls) p = some x := by
  rw [evTr_take] at h
  simp only [evAt, List.getElem?_take] at h ⊢
  split at h
  · exact h
  · simp at h

theorem evAt_single_some {e x : Ev} {kk : Nat} (h : ([e] : List Ev)[kk]? = some x) :
    kk = 0 ∧ x = e := by
  cases kk with
  | zero => simp at h; exact ⟨rfl, h.symm⟩
  | succ kk => simp at h

/-- The events of the pair's part of the trace: the read at its first step, the write at its
last. -/
theorem posE {lsP : List Lab} {eR eW : Ev} {M j kk : Nat} {x : Ev}
    (h : evAt (evTr (pairLs lsP eR eW M)) (j, kk) = some x) (hj : lsP.length ≤ j) :
    (j = lsP.length ∧ kk = 0 ∧ x = eR) ∨ (j = lsP.length + M + 1 ∧ kk = 0 ∧ x = eW) := by
  rw [evTr_append, evAt_append_ge _ _ (by simpa [evTr_length] using hj)] at h
  simp only [evTr_length] at h
  obtain ⟨d, rfl⟩ : ∃ d, j = lsP.length + d := ⟨j - lsP.length, by omega⟩
  simp only [Nat.add_sub_cancel_left] at h
  rcases d with _ | d
  · simp only [evAt, evTr, List.map_cons, List.getElem?_cons_zero, Option.bind_some] at h
    obtain ⟨rfl, rfl⟩ := evAt_single_some h
    exact .inl ⟨rfl, rfl, rfl⟩
  · simp only [evAt, evTr, List.map_cons, List.getElem?_cons_succ, List.map_append,
      List.map_replicate, List.map_cons, List.map_nil] at h
    rcases Nat.lt_trichotomy d M with hd | rfl | hd
    · rw [List.getElem?_append_left (by simpa using hd), List.getElem?_replicate] at h
      simp [hd] at h
    · rw [List.getElem?_append_right (by simp)] at h
      simp only [List.length_replicate, Nat.sub_self, List.getElem?_cons_zero, Option.bind_some] at h
      obtain ⟨rfl, rfl⟩ := evAt_single_some h
      exact .inr ⟨by omega, rfl, rfl⟩
    · rw [List.getElem?_append_right (by simp; omega)] at h
      simp only [List.length_replicate] at h
      rw [List.getElem?_eq_none (by simp; omega)] at h
      cases h

theorem posP {lsP : List Lab} {eR eW : Ev} {M j kk : Nat} {x : Ev}
    (h : evAt (evTr (pairLs lsP eR eW M)) (j, kk) = some x) (hj : j < lsP.length) :
    ∃ l ∈ lsP, x ∈ l.evs := by
  rw [evTr_append, evAt_append_lt _ _ (by simpa [evTr_length] using hj)] at h
  exact evAt_evTr_mem h

theorem evAt_PA1 (RA : Backend.Proof.RL) (sA : ArmState) (ls : List Lab) (k j kk : Nat) :
    (PA1 RA sA ls k).evAt (.thr 0 j kk) = (evAt (evTr (ls.take k)) (j, kk)).map convEv := by
  simp only [Traces.evAt, PA1, show (0 : Nat) < 1 from by decide, ite_true]
  exact evAt_conv (evTr (ls.take k)) (j, kk)

/-- **`Realizes` for one compiled thread whose run is private plain accesses, then an exclusive
pair**: an `acqXR` read, steps without events, and an `relXW` write of the same bytes. Every
execution of the realized prefix with the initial locations `locs1` (the pair's first), reads from
the latest earlier write and the prefix's monitor pairs as `rmw` (`rmwP`) is `Realizes`d by a
CLIF thread from `cs`, for every initial memory; the realized prefix covers the run (`Covers`). -/
theorem realizes_pair_cov {RA : Backend.Proof.RL} {cs : Clif.State} {sA : ArmState}
    (hc : ∀ env p, CompiledLS env p RA cs sA) {lsP : List Lab} {eR eW : Ev} {M : Nat}
    {t' : ArmState × Mon}
    (hr : PRun Policy.arm RA.step (OkPriv RA) (sA, none) (pairLs lsP eR eW M) t')
    (hevP : ∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RA e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR))
    (hkR : eR.k = .acqXR) (hkW : eW.k = .relXW) (ha : eW.addr = eR.addr) (hn : eW.n = eR.n)
    (env : Clif.Env) (p : Clif.Program) (M0 : Bytes) :
    ∃ k ≤ (pairLs lsP eR eW M).length, Covers env p RA cs (pairLs lsP eR eW M) k ∧
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv),
      PC.n = 1 ∧ PC.st 0 0 = .run cs ∧ PC.Runs (CStep env p) ∧
      Realizes (PA1 RA sA (pairLs lsP eR eW M) k) (locs1 lsP eR) M0
        (latestW (PA1 RA sA (pairLs lsP eR eW M) k) (locs1 lsP eR))
        (coL (PA1 RA sA (pairLs lsP eR eW M) k) (locs1 lsP eR)) (rmwP (pairLs lsP eR eW M) k)
        PC [(eR.addr.toNat, eR.n)] M0 φ (fun _ _ _ => True) := by
  obtain ⟨k, hk, hcv, hR⟩ := realizes_compiledLS_full (n := 1) (env := env) (p := p)
    (RA := fun _ => RA) (cs := fun _ => cs) (sA := fun _ => sA) (fun _ _ => hc env p)
    (mon := fun _ => none) (ls := fun _ => pairLs lsP eR eW M) (t' := fun _ => t')
    (fun _ _ => hr)
  let ls := pairLs lsP eR eW M
  -- the events of the run
  have hevs : ∀ l ∈ ls, ∀ e' ∈ l.evs, e' = eR ∨ e' = eW ∨
      (∃ q : Nat, ((lsP.flatMap (·.evs)).map fun e : Ev => (e.addr.toNat, e.n))[q]? =
        some (e'.addr.toNat, e'.n)) ∧ PrivA RA e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR) := by
    intro l hl e' he'
    rcases List.mem_append.mp hl with hl | hl
    · refine .inr (.inr ⟨?_, hevP l hl e' he'⟩)
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp
        (List.mem_map_of_mem (f := fun e : Ev => (e.addr.toNat, e.n))
          (List.mem_flatMap.mpr ⟨l, hl, he'⟩))
      exact ⟨q, hq⟩
    · simp only [List.mem_cons, List.mem_append, List.mem_replicate, List.mem_singleton,
        List.not_mem_nil, or_false] at hl
      rcases hl with rfl | ⟨-, rfl⟩ | rfl
      · exact .inl (List.mem_singleton.mp he')
      · cases he'
      · exact .inr (.inl (List.mem_singleton.mp he'))
  let P := PA1 RA sA ls (k 0)
  have hev : ∀ j kk x, P.evAt (.thr 0 j kk) = some x →
      ∃ l ∈ ls, ∃ e' ∈ l.evs, x = ProgE2E.convEv e' := by
    intro j kk x hx
    simp only [Traces.evAt, P, PA1, show (0 : Nat) < 1 from by decide, ite_true] at hx
    obtain ⟨l, hl, e', he', rfl⟩ := evAt_conv_mem (p := (j, kk)) hx
    exact ⟨l, List.mem_of_mem_take hl, e', he', rfl⟩
  have hwf0 := wf_single (P := P) (locs := locs1 lsP eR) rfl
    (take_len_le hr (k 0)) (fun r hr' => by
      cases r with
      | init q =>
        simp only [X0, Traces.exec] at hr'
        split at hr' <;> cases hr'
      | thr i j kk =>
        simp only [X0, Traces.exec] at hr' ⊢
        split at hr'
        · rename_i x hx
          have hi : i = 0 := by
            simp only [Traces.evAt, P, PA1] at hx
            split at hx
            · omega
            · cases hx
          subst hi
          obtain ⟨l, hl, e', he', rfl⟩ := hev j kk x hx
          rcases hevs l hl e' he' with rfl | rfl | ⟨⟨q, hq⟩, -⟩
          · refine ⟨.init 0, by simp [locs1], ?_, trivial⟩
            simp [hx, locs1, ProgE2E.convEv]
          · simp [ProgE2E.convEv, hkW] at hr'
            exact absurd hr' (by decide)
          · have hq' : q + 1 < (locs1 lsP eR).length := by
              have := (List.getElem?_eq_some_iff.mp hq).1
              simp only [locs1, List.length_cons]; omega
            refine ⟨.init (q + 1), by simp only [hq', ite_true], ?_, trivial⟩
            simp only [hx, locs1, List.getElem?_cons_succ, hq, Option.getD_some, ProgE2E.convEv]
        · cases hr')
  -- the monitor pairs of the prefix: the `ldaxr`'s read and the `stlxr`'s write
  have hexR : ∀ j kk x, evAt (evTr (ls.take (k 0))) (j, kk) = some x → x.k = .acqXR →
      j = lsP.length ∧ kk = 0 ∧ x = eR := by
    intro j kk x hx hk'
    have hx' := evAt_take_some hx
    by_cases hj : j < lsP.length
    · obtain ⟨l, hl, hxl⟩ := posP hx' hj
      rcases (hevP l hl x hxl).2 with h | h <;> rw [h] at hk' <;> cases hk'
    · rcases posE hx' (by omega) with h | ⟨-, -, rfl⟩
      · exact h
      · rw [hkW] at hk'; cases hk'
  have hexW : ∀ j kk x, evAt (evTr (ls.take (k 0))) (j, kk) = some x → x.k = .relXW →
      j = lsP.length + M + 1 ∧ kk = 0 ∧ x = eW := by
    intro j kk x hx hk'
    have hx' := evAt_take_some hx
    by_cases hj : j < lsP.length
    · obtain ⟨l, hl, hxl⟩ := posP hx' hj
      rcases (hevP l hl x hxl).2 with h | h <;> rw [h] at hk' <;> cases hk'
    · rcases posE hx' (by omega) with ⟨-, -, rfl⟩ | h
      · rw [hkR] at hk'; cases hk'
      · exact h
  have hdirS : ∀ j kk x, evAt (evTr (ls.take (k 0))) (j, kk) = some x →
      (X0 P (locs1 lsP eR)).dir (.thr 0 j kk) = x.k.dir ∧
      (X0 P (locs1 lsP eR)).loc (.thr 0 j kk) = x.addr.toNat := by
    intro j kk x hx
    have e := evAt_PA1 RA sA ls (k 0) j kk
    rw [hx] at e
    simp only [X0, Traces.exec]
    rw [show P.evAt (.thr 0 j kk) = some (convEv x) from e]
    exact ⟨rfl, rfl⟩
  have hnone : ∀ j kk, evAt (evTr (ls.take (k 0))) (j, kk) = none →
      (X0 P (locs1 lsP eR)).dir (.thr 0 j kk) = .F ∧ ¬ (X0 P (locs1 lsP eR)).ev (.thr 0 j kk) := by
    intro j kk hx
    have e := evAt_PA1 RA sA ls (k 0) j kk
    rw [hx] at e
    simp only [X0, Traces.exec]
    rw [show P.evAt (.thr 0 j kk) = none from e]
    exact ⟨rfl, by simp⟩
  have hwf := wf_rmw (rmw := rmwP ls (k 0)) hwf0
    (fun a b ⟨j, kk, j', kk', ea, eb, ⟨x, hx, hxk⟩, ⟨y, hy, hyk⟩, _⟩ => by
      subst ea eb
      rw [(hdirS _ _ _ hx).1, (hdirS _ _ _ hy).1, hxk, hyk]
      exact ⟨rfl, rfl⟩)
    (fun a b ⟨j, kk, j', kk', ea, eb, ⟨x, hx, hxk⟩, ⟨y, hy, hyk⟩, _⟩ => by
      subst ea eb
      rw [(hdirS _ _ _ hx).2, (hdirS _ _ _ hy).2]
      obtain ⟨-, -, rfl⟩ := hexR _ _ _ hx hxk
      obtain ⟨-, -, rfl⟩ := hexW _ _ _ hy hyk
      rw [ha])
    (fun a b ⟨j, kk, j', kk', ea, eb, _, _, hlt, _⟩ => by
      subst ea eb
      exact ⟨rfl, hlt⟩)
    (fun a b c ⟨j, kk, j', kk', ea, eb, ⟨x, hx, hxk⟩, ⟨y, hy, hyk⟩, _⟩ h1 h2 h3 => by
      subst ea eb
      obtain ⟨rfl, rfl, -⟩ := hexR _ _ _ hx hxk
      obtain ⟨rfl, rfl, -⟩ := hexW _ _ _ hy hyk
      cases c with
      | init q => exact h1
      | thr i j kk =>
        obtain ⟨rfl, h1⟩ := h1
        obtain ⟨-, h2⟩ := h2
        cases hz : evAt (evTr (ls.take (k 0))) (j, kk) with
        | none =>
          obtain ⟨hd, he⟩ := hnone j kk hz
          rcases h3 with h3 | h3
          · exact h3 hd
          · exact he h3
        | some z =>
          rcases posE (evAt_take_some hz) (by omega) with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> omega)
  obtain ⟨PC, φ, h1, h2, h3, h4⟩ := hR P (locs1 lsP eR) [(eR.addr.toNat, eR.n)] M0 M0
    (latestW P (locs1 lsP eR)) (coL P (locs1 lsP eR)) (rmwP ls (k 0)) rfl
    (fun i hi => by obtain rfl : i = 0 := by omega
                    rfl) hwf
    (fun i hi a b => by
      obtain rfl : i = 0 := by omega
      exact ⟨fun ⟨_, _, _, _, e1, e2, h⟩ => by cases e1; cases e2; exact h,
        fun h => ⟨_, _, _, _, rfl, rfl, h⟩⟩)
    ⟨_, rfl⟩
    (fun q hq hq1 => by
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by simp at hq1; omega⟩
      have hq2 : q' < ((lsP.flatMap (·.evs)).map fun e => (e.addr.toNat, e.n)).length := by
        simp only [locs1, List.length_cons] at hq; omega
      have hm := List.getElem_mem hq2
      obtain ⟨e', he', he'q⟩ := List.mem_map.mp hm
      obtain ⟨l, hl, he'l⟩ := List.mem_flatMap.mp he'
      refine ⟨0, by omega, ?_⟩
      simp only [locs1, List.getElem_cons_succ, ← he'q]
      exact (hevP l hl e' he'l).1)
    (fun q h => rfl) (fun i hi j hj hne => by omega)
  exact ⟨k 0, by have := hk 0 (by omega); simpa using this, hcv 0 (by omega), PC, φ, h1,
    h2 0 (by omega), h3, h4⟩

/-- **`Realizes` for one compiled thread whose run is private plain accesses, then an exclusive
pair** (`realizes_pair_cov` without the coverage). -/
theorem realizes_pair {RA : Backend.Proof.RL} {cs : Clif.State} {sA : ArmState}
    (hc : ∀ env p, CompiledLS env p RA cs sA) {lsP : List Lab} {eR eW : Ev} {M : Nat}
    {t' : ArmState × Mon}
    (hr : PRun Policy.arm RA.step (OkPriv RA) (sA, none) (pairLs lsP eR eW M) t')
    (hevP : ∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RA e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR))
    (hkR : eR.k = .acqXR) (hkW : eW.k = .relXW) (ha : eW.addr = eR.addr) (hn : eW.n = eR.n)
    (env : Clif.Env) (p : Clif.Program) (M0 : Bytes) :
    ∃ k ≤ (pairLs lsP eR eW M).length, ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv),
      PC.n = 1 ∧ PC.st 0 0 = .run cs ∧ PC.Runs (CStep env p) ∧
      Realizes (PA1 RA sA (pairLs lsP eR eW M) k) (locs1 lsP eR) M0
        (latestW (PA1 RA sA (pairLs lsP eR eW M) k) (locs1 lsP eR))
        (coL (PA1 RA sA (pairLs lsP eR eW M) k) (locs1 lsP eR)) (rmwP (pairLs lsP eR eW M) k)
        PC [(eR.addr.toNat, eR.n)] M0 φ (fun _ _ _ => True) := by
  obtain ⟨k, hk, -, h⟩ := realizes_pair_cov hc hr hevP hkR hkW ha hn env p M0
  exact ⟨k, hk, h⟩

/-- **A covering prefix of a private run ending in an exclusive pair is the whole run** when the
CLIF thread cannot stop at its start and steps with two non-fence events: a strict prefix has one
shared event (the read), at one position. -/
theorem pair_full {env : Clif.Env} {p : Clif.Program} {RA : Backend.Proof.RL} {cs : Clif.State}
    {lsP : List Lab} {eR eW : Ev} {M k : Nat} (hcov : Covers env p RA cs (pairLs lsP eR eW M) k)
    (hk : k ≤ (pairLs lsP eR eW M).length) (hevP : ∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RA e'.addr.toNat)
    (hgo : ¬ Stop env p (.run cs))
    (htwo : ∀ evs t', CStep env p (.run cs) evs t' →
      ∃ hl : 1 < evs.length, evs[0].dir ≠ .F ∧ evs[1].dir ≠ .F) :
    k = (pairLs lsP eR eW M).length := by
  refine covers_full hcov hk hgo fun evs t' hs k' hk' ψ hsh hinj => ?_
  obtain ⟨hl, h0, h1⟩ := htwo evs t' hs
  have hpos : ∀ i (hi : i < evs.length), evs[i].dir ≠ .F → ψ (0, i) = (lsP.length, 0) := by
    intro i hi hF
    obtain ⟨hnp, y, hy, -, hly⟩ := hsh i hi hF
    rw [evAt_conv] at hy
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
    have hlt : (ψ (0, i)).1 < k' := by
      obtain ⟨h1, -⟩ := evAt_isSome (show (evAt (evTr ((pairLs lsP eR eW M).take k'))
        ((ψ (0, i)).1, (ψ (0, i)).2)).isSome from by rw [hx]; rfl)
      simp [evTr] at h1; omega
    have hx' := evAt_take_some hx
    by_cases hq : (ψ (0, i)).1 < lsP.length
    · obtain ⟨l, hl', hxl⟩ := posP (j := (ψ (0, i)).1) (kk := (ψ (0, i)).2) hx' hq
      exact absurd (by rw [← hly]; exact hevP l hl' x hxl) hnp
    · rcases posE (j := (ψ (0, i)).1) (kk := (ψ (0, i)).2) hx' (by omega) with
        ⟨e1, e2, -⟩ | ⟨e1, -, -⟩
      · exact Prod.ext e1 e2
      · simp at hk'; omega
  exact hinj 0 1 (by omega) hl (by decide) ((hpos 0 (by omega) h0).trans (hpos 1 hl h1).symm)

/-- **`Realizes` for one compiled thread whose run is private plain accesses, then an exclusive
pair, on the whole run** (`realizes_pair_cov`, `pair_full`). -/
theorem realizes_pair_full {RA : Backend.Proof.RL} {cs : Clif.State} {sA : ArmState}
    (hc : ∀ env p, CompiledLS env p RA cs sA) {lsP : List Lab} {eR eW : Ev} {M : Nat}
    {t' : ArmState × Mon}
    (hr : PRun Policy.arm RA.step (OkPriv RA) (sA, none) (pairLs lsP eR eW M) t')
    (hevP : ∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RA e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR))
    (hkR : eR.k = .acqXR) (hkW : eW.k = .relXW) (ha : eW.addr = eR.addr) (hn : eW.n = eR.n)
    (env : Clif.Env) (p : Clif.Program) (M0 : Bytes) (hgo : ¬ Stop env p (.run cs))
    (htwo : ∀ evs t', CStep env p (.run cs) evs t' →
      ∃ hl : 1 < evs.length, evs[0].dir ≠ .F ∧ evs[1].dir ≠ .F) :
    ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv),
      PC.n = 1 ∧ PC.st 0 0 = .run cs ∧ PC.Runs (CStep env p) ∧
      Realizes (PA1 RA sA (pairLs lsP eR eW M) (pairLs lsP eR eW M).length) (locs1 lsP eR) M0
        (latestW (PA1 RA sA (pairLs lsP eR eW M) (pairLs lsP eR eW M).length) (locs1 lsP eR))
        (coL (PA1 RA sA (pairLs lsP eR eW M) (pairLs lsP eR eW M).length) (locs1 lsP eR))
        (rmwP (pairLs lsP eR eW M) (pairLs lsP eR eW M).length)
        PC [(eR.addr.toNat, eR.n)] M0 φ (fun _ _ _ => True) := by
  obtain ⟨k, hk, hcv, h⟩ := realizes_pair_cov hc hr hevP hkR hkW ha hn env p M0
  obtain rfl := pair_full hcv hk (fun l hl e' he' => (hevP l hl e' he').1) hgo htwo
  exact h

/-- **On the whole run, the `rmw` relates the `ldaxr`'s read to the `stlxr`'s write.** -/
theorem rmw_full {lsP : List Lab} {eR eW : Ev} {M : Nat} (hkR : eR.k = .acqXR)
    (hkW : eW.k = .relXW)
    (hevP : ∀ l ∈ lsP, ∀ e' ∈ l.evs, e'.k = .plainW ∨ e'.k = .plainR) :
    rmwP (pairLs lsP eR eW M) (pairLs lsP eR eW M).length (.thr 0 lsP.length 0)
      (.thr 0 (lsP.length + M + 1) 0) := by
  refine ⟨_, _, _, _, rfl, rfl, ⟨eR, ?_, hkR⟩, ⟨eW, ?_, hkW⟩, .inl (by omega), ?_⟩
  · rw [List.take_length, evTr_append, evAt_append_ge _ _ (by simp [evTr_length])]
    simp [evTr_length, evAt, evTr]
  · rw [List.take_length, evTr_append, evAt_append_ge _ _ (by simp [evTr_length]; omega)]
    simp only [evTr_length, show lsP.length + M + 1 - lsP.length = M + 1 by omega]
    simp [evAt, evTr, List.getElem?_append_right]
  · intro q z h1 h2 hz
    rw [List.take_length] at hz
    by_cases hq : q.1 < lsP.length
    · obtain ⟨l, hl, hzl⟩ := posP (j := q.1) (kk := q.2) hz hq
      rcases hevP l hl z hzl with h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩
    · rcases posE (j := q.1) (kk := q.2) hz (by omega) with ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩
      · rcases h1 with h1 | ⟨-, h1⟩ <;> simp_all
      · rcases h2 with h2 | ⟨-, h2⟩ <;> simp_all

/-- **`Realizes` on the compiled `atomic_rmw` through one successful iteration of its loop**
(module doc): the run of `run_rmw`; every execution of its realized prefix (initial locations
`locs1`, the pair's first; `rmw` the prefix's monitor pairs) is `Realizes`d by a CLIF thread from
`csR`; on the whole run, that `rmw` relates the read to the write. -/
theorem realizes_rmw : ∃ (n : Nat) (lsP : List Lab) (eR eW : Ev) (t' : ArmState × Mon),
    PRun Policy.arm RAR.step (OkPriv RAR) (iterN RAR.step n RAR.s0, none) (pairLs lsP eR eW MR) t' ∧
    eR.k = .acqXR ∧ eW.k = .relXW ∧ eR.addr = 0 ∧ eW.addr = 0 ∧ eR.n = 8 ∧ eW.n = 8 ∧
    (∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RAR e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR)) ∧
    rmwP (pairLs lsP eR eW MR) (pairLs lsP eR eW MR).length (.thr 0 lsP.length 0)
      (.thr 0 (lsP.length + MR + 1) 0) ∧
    ∀ (env : Clif.Env) (p : Clif.Program) (M0 : Bytes), ∃ k ≤ (pairLs lsP eR eW MR).length,
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧ PC.st 0 0 = .run csR ∧
        PC.Runs (CStep env p) ∧
        Realizes (PA1 RAR (iterN RAR.step n RAR.s0) (pairLs lsP eR eW MR) k) (locs1 lsP eR) M0
          (latestW (PA1 RAR (iterN RAR.step n RAR.s0) (pairLs lsP eR eW MR) k) (locs1 lsP eR))
          (coL (PA1 RAR (iterN RAR.step n RAR.s0) (pairLs lsP eR eW MR) k) (locs1 lsP eR))
          (rmwP (pairLs lsP eR eW MR) k) PC [(eR.addr.toNat, eR.n)] M0 φ (fun _ _ _ => True) := by
  obtain ⟨n, lsP, eR, eW, t', hc, hr, hkR, hkW, haR, haW, hnR, hnW, hevP⟩ := run_rmw
  exact ⟨n, lsP, eR, eW, t', hr, hkR, hkW, haR, haW, hnR, hnW, hevP,
    rmw_full hkR hkW fun l hl e he => (hevP l hl e he).2, fun env p M0 =>
    realizes_pair hc hr hevP hkR hkW (haW.trans haR.symm) (hnW.trans hnR.symm) env p M0⟩

/-! ## The whole run -/

theorem bodyR : ∃ st rest, csR.frame.body = st :: rest ∧ st.inst = .atomicRmw .add .i64 {} 0 1 := by
  have h : csR.frame.body.head?.map (·.inst) = some (.atomicRmw .add .i64 {} 0 1) := by
    native_decide
  revert h
  cases csR.frame.body with
  | nil => intro h; cases h
  | cons st rest => intro h; exact ⟨st, rest, rfl, by simpa using h⟩

theorem regR0 : csR.frame.regs 0 = some ⟨.i64, 0⟩ := by native_decide

theorem getR1 : ∃ v, csR.frame.getAs 1 .i64 = .ok v := by
  have h : (match csR.frame.getAs 1 .i64 with | .ok _ => true | _ => false) = true := by
    native_decide
  revert h
  cases csR.frame.getAs 1 .i64 with
  | ok v => intro _; exact ⟨v, rfl⟩
  | _ => intro h; cases h

theorem loadR0 : ∃ old, (withBytes csR (fun _ => some 0)).mem.load {} (Clif.effAddr ⟨.i64, 0⟩ 0)
    Clif.Ty.i64.bytes Clif.Ty.i64.width = .ok old := by
  have h : (match (withBytes csR (fun _ => some 0)).mem.load {} (Clif.effAddr ⟨.i64, 0⟩ 0)
      Clif.Ty.i64.bytes Clif.Ty.i64.width with | .ok _ => true | _ => false) = true := by
    native_decide
  revert h
  cases (withBytes csR (fun _ => some 0)).mem.load {} (Clif.effAddr ⟨.i64, 0⟩ 0)
    Clif.Ty.i64.bytes Clif.Ty.i64.width with
  | ok v => intro _; exact ⟨v, rfl⟩
  | _ => intro h; cases h

theorem stepR0 : (match Clif.step default default (withBytes csR (fun _ => some 0)) with
    | .next _ => true | _ => false) = true := by native_decide

/-- **The CLIF thread from `csR` steps** (its `atomic_rmw`). -/
theorem cstep_csR (env : Clif.Env) (p : Clif.Program) : ∃ evs t', CStep env p (.run csR) evs t' := by
  obtain ⟨st, rest, hb, hi⟩ := bodyR
  obtain ⟨v, hv⟩ := getR1
  obtain ⟨old, hold⟩ := loadR0
  have hb' : (withBytes csR (fun _ => some 0)).frame.body = st :: rest := hb
  obtain ⟨s', hs⟩ := step_next_of_check (env := env) (p := p) hb'
    (fun _ _ h => by rw [hi] at h; cases h) (fun _ _ _ h => by rw [hi] at h; cases h) default
    default stepR0
  exact ⟨_, _, ClifCStep.cstep_atomicRmw hb' hi regR0 hv hold hs⟩

theorem shapeR1 : evShape csR = [[(.scR, 8), (.scW, 8)]] := by
  obtain ⟨st, rest, hb, hi⟩ := bodyR
  simp only [evShape, hb, hi]
  rfl

theorem notStop_csR (env : Clif.Env) (p : Clif.Program) : ¬ Stop env p (.run csR) := by
  obtain ⟨st, rest, hb, hi⟩ := bodyR
  obtain ⟨evs, t', hs⟩ := cstep_csR env p
  rintro (hd | hc)
  · exact hd ⟨evs, t', hs⟩
  · exact not_casRO hb (fun _ _ _ _ _ h => by rw [hi] at h; cases h) hc

/-- **`Realizes` on the compiled `atomic_rmw` through one successful iteration of its loop, on the
whole run** (T2j): the run of `run_rmw`; every execution of all of it (its `rmw` the run's monitor
pairs, which relate the `ldaxr`'s read to the `stlxr`'s write, `rmw_full`) is `Realizes`d by a
CLIF thread from `csR` (`realizes_pair_full`: the CLIF thread steps from `csR` with the
`atomic_rmw`'s read and write). -/
theorem realizes_rmw_full : ∃ (n : Nat) (lsP : List Lab) (eR eW : Ev) (t' : ArmState × Mon),
    PRun Policy.arm RAR.step (OkPriv RAR) (iterN RAR.step n RAR.s0, none) (pairLs lsP eR eW MR) t' ∧
    eR.k = .acqXR ∧ eW.k = .relXW ∧ eR.addr = 0 ∧ eW.addr = 0 ∧ eR.n = 8 ∧ eW.n = 8 ∧
    (∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RAR e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR)) ∧
    rmwP (pairLs lsP eR eW MR) (pairLs lsP eR eW MR).length (.thr 0 lsP.length 0)
      (.thr 0 (lsP.length + MR + 1) 0) ∧
    ∀ (env : Clif.Env) (p : Clif.Program) (M0 : Bytes),
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧ PC.st 0 0 = .run csR ∧
        PC.Runs (CStep env p) ∧
        Realizes (PA1 RAR (iterN RAR.step n RAR.s0) (pairLs lsP eR eW MR)
            (pairLs lsP eR eW MR).length) (locs1 lsP eR) M0
          (latestW (PA1 RAR (iterN RAR.step n RAR.s0) (pairLs lsP eR eW MR)
            (pairLs lsP eR eW MR).length) (locs1 lsP eR))
          (coL (PA1 RAR (iterN RAR.step n RAR.s0) (pairLs lsP eR eW MR)
            (pairLs lsP eR eW MR).length) (locs1 lsP eR))
          (rmwP (pairLs lsP eR eW MR) (pairLs lsP eR eW MR).length) PC [(eR.addr.toNat, eR.n)] M0
          φ (fun _ _ _ => True) := by
  obtain ⟨n, lsP, eR, eW, t', hc, hr, hkR, hkW, haR, haW, hnR, hnW, hevP⟩ := run_rmw
  exact ⟨n, lsP, eR, eW, t', hr, hkR, hkW, haR, haW, hnR, hnW, hevP,
    rmw_full hkR hkW fun l hl e he => (hevP l hl e he).2, fun env p M0 =>
    realizes_pair_full hc hr hevP hkR hkW (haW.trans haR.symm) (hnW.trans hnR.symm) env p M0
      (notStop_csR env p) (fun _ _ hs => nonFence_two shapeR1 (by decide) (by decide) hs)⟩

end Concurrency.RealizeCompiled.WitnessR
