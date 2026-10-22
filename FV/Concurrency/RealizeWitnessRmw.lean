import FV.Concurrency.RealizeWitnessLoad
import FV.Concurrency.ArmAllocLoopFwd
import FV.Concurrency.ArmAllocLoopWitness

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

end Concurrency.RealizeCompiled.WitnessR
