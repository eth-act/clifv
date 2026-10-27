import FV.Concurrency.RealizeWitnessLoad

/-!
# `Realizes` on a run of compiled code through its `stlr` (T2l, #311)

The CLIF function `%st(i64, i64) { atomic_store.i64 v1, v0; return }` (`fS`) as the pipeline
compiles it (`lowerFunction`, `prepare`, `spillAlloc`; the activation as
`ArmAllocThread.Witness.act` loads it): after the 18 saves, the entry `args`, the spill of `x0`,
`x1` to their slots and back, and the `stlr x1, [x0]`. As `RealizeWitnessLoad`:

* `compiled_ofS`: every premise of `RealizeCompiled.Compiled` for the activation, the CLIF entry
  state `csS` (`v0 = v1 = 0`, an 8-byte allocation at address 0) and the Arm state after the
  prologue;
* `realizes_store`: the precise run through the saves, the `args`, the spill moves and the
  `stlr` (one `relW` event of 8 bytes), every earlier event private and plain; every execution
  of its realized prefix (initial locations `locs1`, the `stlr`'s first) is `Realizes`d by a CLIF
  thread from `csS`, for every initial memory.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.RealizeCompiled.WitnessS

open Arm ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine
  ArmAllocThread ThreadCompose E2E ArmInstFoot Code RealizeCompiled.Witness RealizeCompiled.WitnessL

/-! ## `atomic_store`, compiled -/

/-- `atomic_store.i64` of the second argument at the first. -/
def srcS : String := "function %st(i64, i64) {
block0(v0: i64, v1: i64):
    atomic_store.i64 v1, v0
    return
}
"

/-- The parsed function. -/
def fS : Clif.Function :=
  match Clif.parse srcS with
  | .ok p => p.funcs.headD default
  | .error _ => default

/-- Its lowering. -/
def vcS : VCode := match lowerFunction fS with
  | .ok vc => vc
  | .error _ => default

/-- `prepare`'s output. -/
def vcpS : VCode := match Backend.prepare vcS with
  | .ok vcp => vcp
  | .error _ => default

/-- The spill allocation. -/
def rfS : RFunc := spillAlloc vcpS

/-- The activation. -/
abbrev RAS : RL := ArmAllocThread.Witness.act vcpS rfS

theorem checksS : lowerCheck fS vcS = true ∧ IselCheck.threadCheck fS = true ∧
    fS.externs.isEmpty = true ∧ (indSigs fS).isEmpty = true ∧ verifiable fS = true ∧
    IselThread.Witness.isOkB vcS.cfg = true ∧ vcS.outgoing = 0 ∧ prepCheck vcS vcpS = true ∧
    (checkAlloc vcpS rfS).isOk = true ∧ rfS.blocks.size = 1 ∧ (rfS.blocks[0]!).size = 43 := by
  native_decide

theorem allocS : checkAlloc vcpS rfS = .ok () := by
  have h := checksS.2.2.2.2.2.2.2.2.1
  revert h
  cases checkAlloc vcpS rfS with
  | ok u => intro _; rfl
  | error e => intro h; cases h

theorem cfgS : ∃ ss ps, vcS.cfg = .ok (ss, ps) := by
  have hb := checksS.2.2.2.2.2.1
  revert hb
  cases vcS.cfg with
  | ok r => intro _; exact ⟨r.1, r.2, rfl⟩
  | error e => intro h; cases h

theorem factsS : (lowerRFunc vcpS rfS).toBool = true ∧ (emitFunc 0 RAS.af).toBool = true ∧
    RAS.fa.k = 0 ∧ RAS.fa.layout.toBool = true ∧ (labelOffsets RAS.fa.lines).toBool = true ∧
    4 * RAS.fb.words.size ≤ 2 ^ 64 ∧ RAS.af.frameSize ≤ 0x100 ∧ 4 * RAS.fb.words.size ≤ 0x10000 ∧
    (blocksLinesE RAS.ctx RAS.af RAS.af.blocks.toList {}).toBool = true := by
  native_decide

theorem wfRS : RAS.Wf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := factsS
  exact ArmAllocThread.Witness.wf_of allocS h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem codeRS : ∀ k < RAS.fb.words.size,
    Arm.read_mem_bytes 4 (0x10000#64 + BitVec.ofNat 64 (4 * k)) RAS.s0 = RAS.fb.words[k]! := by
  native_decide

theorem entryArgRS : ∀ r, RAS.vc.EntryArg r → r.isArgReg = true := by
  rintro r ⟨vb, ds, h1, h2, v, hv⟩
  have h : entryArgsB vcpS = true := by native_decide
  simp only [entryArgsB, show vcpS = RAS.vc from rfl, h1, h2, List.all_eq_true] at h
  exact h _ hv

/-- The entry world of the body. -/
abbrev w₀S : ArmState := E2E.bodyOf RAS.af RAS.s0

theorem qRS : ∃ n, Q RAS (iterN RAS.step n RAS.s0)
      (MConf.init RAS.rf (locVal RAS.fr (iterN RAS.step n RAS.s0)) w₀S) ∧
    AInv RAS (MConf.init RAS.rf (locVal RAS.fr (iterN RAS.step n RAS.s0)) w₀S) := by
  obtain ⟨n, -, hq, hA, -⟩ := q_init wfRS (ArmAllocThread.Witness.abi_of factsS.2.2.2.2.2.2.2.1 codeRS)
    ((E2E.Binary.bodyEntry_bodyOf RAS.af RAS.s0).w RAS.F entryArgRS)
  exact ⟨n, hq, hA⟩

/-- The memory forms `MemScope` admits, as a check (with `stlr`). -/
def memFormSB (ctx : FnCtx) : MInst → Bool
  | .fence | .args _ | .rets _ => true
  | i@(.storeRelease ..) => FormOk ctx i
  | _ => false

theorem scopeRS : MemScope RAS := by
  have h : RAS.vc.blocks.all (·.insts.all (memFormSB RAS.ctx)) = true := by native_decide
  intro b vb k i hb hi
  obtain ⟨hb', rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨hk', rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  have h1 := (Array.all_eq_true.mp h) b hb'
  have h2 := (Array.all_eq_true.mp h1) k hk'
  revert h2
  generalize RAS.vc.blocks[b].insts[k] = i
  intro h2
  cases i with
  | fence => exact .inr (.inl rfl)
  | args ds => exact .inl (.inr (.inl ⟨ds, rfl⟩))
  | rets us => exact .inl (.inr (.inr (.inl ⟨us, rfl⟩)))
  | storeRelease ty rt rn fl => exact .inr (.inr (.inr ⟨ty, rt, rn, fl, rfl, h2⟩))
  | _ => simp [memFormSB] at h2

/-! ## The CLIF entry -/

/-- The function's entry block. -/
def B0S : Clif.Block := fS.blocks.headD default

/-- The arguments: `0 : i64` twice (`x0`, `x1` at the entry). -/
def argsS : List Clif.Val := [⟨.i64, 0⟩, ⟨.i64, 0⟩]

/-- The entry registers: `v0 = v1 = 0`. -/
def regsS : Clif.Regs := (Clif.Regs.empty.setMany (B0S.params.map (·.1)) argsS).getD Clif.Regs.empty

/-- **The CLIF entry state**: block 0, `v0 = v1 = 0`, no slots, `memL` (8 bytes at 0). -/
def csS : Clif.State :=
  { frame := { func := fS, regs := regsS, slots := [], body := B0S.body, term := B0S.term }
    callers := []
    mem := memL }

/-- The memory relation's parameters. -/
def ΓS : E2E.Rel := ⟨RAS.F, fun _ => none, RAS.ctx.slotBase, 0⟩

theorem shapeS : fS.blocks.isEmpty = false ∧
    (Clif.Regs.empty.setMany (B0S.params.map (·.1)) argsS).isSome = true ∧
    argsS.map (·.ty) = B0S.params.map (·.2) ∧ argsS.map (·.ty) = fS.sig.params.map (·.ty) ∧
    (locsOf fS.sig).all (fun l => match l with | .stack _ => false | _ => true) = true ∧
    (match locsOf fS.sig with | [.reg (.x 0), .reg (.x 1)] => true | _ => false) = true ∧
    (E2E.spv w₀S).toNat % 16 = 0 ∧ regVal RAS.s0 (.x 0) = 0 ∧ regVal RAS.s0 (.x 1) = 0 := by
  native_decide

theorem b0S : fS.blocks[0]? = some B0S := by
  have h := shapeS.1
  unfold B0S
  revert h
  cases fS.blocks with
  | nil => intro h; cases h
  | cons b bs => intro _; rfl

theorem regsS_eq : Clif.Regs.empty.setMany (B0S.params.map (·.1)) argsS = some regsS := by
  have h := shapeS.2.1
  unfold regsS
  revert h
  cases Clif.Regs.empty.setMany (B0S.params.map (·.1)) argsS with
  | none => intro h; cases h
  | some r => intro _; rfl

theorem errW₀S : Arm.r .ERR w₀S = .None := by
  rw [E2E.r_bodyOf _ _ (by simp) (by simp)]
  exact (ArmAllocThread.Witness.abi_of factsS.2.2.2.2.2.2.2.1 codeRS).err

/-- **The first 8 bytes are no frame address.** -/
theorem notF_lowS : ∀ x < 8, ¬ RAS.F (BitVec.ofNat 64 x) := by
  have h : ∀ x < 8, fB RAS (BitVec.ofNat 64 x) = false := by native_decide
  intro x hx hF
  have := h x hx
  rw [fB_of rfl (fun _ h => h) hF] at this
  cases this

theorem relS : E2E.RelW ΓS fS (E2E.spv w₀S) [] memL w₀S := by
  refine ⟨⟨⟨fun a b _ hb => by simp [memL] at hb, fun a n hv => ?_, rfl⟩,
      fun id b h => by simp at h, E2E.outRel_zero _ _ _⟩, rfl, errW₀S⟩
  simp only [Clif.Mem.valid, memL, List.any_cons, List.any_nil, Bool.or_false,
    Clif.Alloc.contains] at hv
  have hv' : a + n ≤ 8 := by
    revert hv; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  exact ⟨by omega, fun k hk => notF_lowS _ (by omega)⟩

theorem locsS : locsOf fS.sig = [.reg (.x 0), .reg (.x 1)] := by
  have h := shapeS.2.2.2.2.2.1
  revert h
  generalize locsOf fS.sig = l
  intro h
  match l, h with
  | [.reg (.x 0), .reg (.x 1)], _ => rfl

theorem argsAtS : ArgsAtEntry RAS.F fS.sig argsS w₀S := by
  intro loc v h
  rw [locsS] at h
  simp only [argsS, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.mem_singleton,
    Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show VHolds _ _
    rw [VHolds, E2E.regVal_bodyOf _ _ (by decide), shapeS.2.2.2.2.2.2.2.1]
    rfl
  · show VHolds _ _
    rw [VHolds, E2E.regVal_bodyOf _ _ (by decide), shapeS.2.2.2.2.2.2.2.2]
    rfl

/-- `Compiled` for the compiled `atomic_store` at every Arm state `Q`-related to its entry
configuration. -/
theorem compiled_ofS {s : ArmState} (hq : Q RAS s (MConf.init RAS.rf (locVal RAS.fr s) w₀S))
    (hA : AInv RAS (MConf.init RAS.rf (locVal RAS.fr s) w₀S)) (env : Clif.Env) (p : Clif.Program) :
    Compiled env p RAS csS s := by
  obtain ⟨hlow, hthr, hext, hind, hv, -, hout, hprep, -⟩ := checksS
  obtain ⟨ctx, st0, R, gn, bl, A, H, hbl⟩ := driverHyp_of (Γ := ΓS) (fctx := RAS.ctx) (X := RAS.X)
    (c := E2E.spv w₀S) (env := env) (p := p) hlow hthr (List.isEmpty_iff.mp hext)
    (List.isEmpty_iff.mp hind) hv cfgS hout rfl (fun _ _ h => by cases h)
  obtain ⟨-, -, hpar, hsig, hlocs, -, hc, -⟩ := shapeS
  exact {
    wf := wfRS
    scope := scopeRS
    gv := rfl
    front := ⟨fS, vcS, ctx, st0, R, gn, bl, A, _, [], ΓS.slotOff, ΓS.syms, B0S, argsS, _, w₀S, H,
      hbl, E2E.memRelOk_relW ΓS fS _, IselRefines.Witness.relW_wf hc,
      VCodeThread.Witness.X0_tls, memRefines_csem RAS.F RAS.ctx _ rfl (fun _ _ h => by cases h),
      E2E.mrStable_relW ΓS fS _,
      (fun off h => by
        have := List.all_eq_true.mp hlocs _ h
        simp at this),
      hprep, allocS, b0S, rfl, rfl, rfl, rfl, rfl, regsS_eq, hpar, hsig, relS, argsAtS, hq, hA⟩ }

/-! ## The run through the `stlr` -/

/-- The spill of `x0`, `x1` to their slots and back. -/
def spillS : List (Loc × Loc) :=
  [(.reg (.x 0), .stack 0 .int), (.reg (.x 1), .stack 1 .int), (.stack 0 .int, .reg (.x 0)),
    (.stack 1 .int, .reg (.x 1))]

/-- The items after the spill moves. -/
def rest2S : List RItem := (rfS.blocks[0]!).toList.drop 23

/-- The code of the items after the spill moves starts with the `stlr` (as a check). -/
def headStB : Bool :=
  match itemsCode RAS.fr vcpS.blocks[0]! rest2S with
  | .ok (.inst (.storeRelease ty (.x 1) (.x 0) fl) :: _) =>
    ty.bits == 64 && (match fl.trapCode with | some .heapOob => true | _ => false)
  | _ => false

/-- The entry `args` (as a check). -/
def argsBS : Bool :=
  match vcpS.blocks[0]? with
  | some vb => (match vb.insts[0]? with
    | some (MInst.args [(Reg.vreg 0 RegClass.int, Reg.x 0), (Reg.vreg 1 RegClass.int, Reg.x 1)]) =>
      true
    | _ => false) && vb.insts.size == 3
  | none => false

theorem checksRunS : (rfS.blocks[0]!).toList = savesL.map (fun p => RItem.move p.1 p.2) ++
      (.op 0 #[.reg (.x 0), .reg (.x 1)] :: (spillS.map (fun p => RItem.move p.1 p.2) ++ rest2S)) ∧
    savesL.all (moveOkB RAS (· == .plainW)) = true ∧
    spillS.all (moveOkB RAS fun K => K == .plainW || K == .plainR) = true ∧ headStB = true ∧
    argsBS = true ∧ 0 < vcpS.blocks.size := by
  native_decide

theorem vb0S : RAS.vc.blocks[0]? = some vcpS.blocks[0]! := by
  show vcpS.blocks[0]? = _
  rw [Array.getElem?_eq_getElem checksRunS.2.2.2.2.2]
  simp [getElem!_def, Array.getElem?_eq_getElem checksRunS.2.2.2.2.2]

theorem argsS0 : (vcpS.blocks[0]!).insts[0]? =
      some (.args [(.vreg 0 .int, .x 0), (.vreg 1 .int, .x 1)]) ∧
    (vcpS.blocks[0]!).insts.size = 3 := by
  have h := checksRunS.2.2.2.2.1
  unfold argsBS at h
  rw [show vcpS.blocks[0]? = some vcpS.blocks[0]! from vb0S] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  revert h1
  generalize (vcpS.blocks[0]!).insts[0]? = oi
  intro h1
  split at h1
  · rfl
  · cases h1

theorem head_stlrS : ∀ vb code, RAS.vc.blocks[0]? = some vb → itemsCode RAS.fr vb rest2S = .ok code →
    ∀ ps ls ps', codeLinesE RAS.ctx RAS.af code ps = .ok (ls, ps') →
      ls.head? = some (.ins (.stlr 64 (.x 1) (.x 0)) (some .heapOob)) := by
  intro vb code hvb hc ps ls ps' hl
  rw [vb0S] at hvb
  obtain rfl := (Option.some.inj hvb).symm
  have h := checksRunS.2.2.2.1
  simp only [headStB, hc] at h
  split at h
  · rename_i ty fl rest e
    cases e
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hty, htc⟩ := h
    have hh := codeLinesE_head_stlr hl
    rw [hty] at hh
    rw [hh]
    revert htc
    cases fl.trapCode with
    | none => intro h; cases h
    | some c => cases c <;> intro h <;> first | rfl | cases h
  · cases h

/-- The entry `args` as a step of the allocated code (no code, the world unchanged; `x0` in the
store gets the world's `x0`). -/
theorem args_stepS (its : List RItem) (m : Loc → CV) (w : ArmState) :
    ∃ m', MStep RAS.vc RAS.sem ckeep RAS.rf (.run ⟨0, .op 0 #[.reg (.x 0), .reg (.x 1)] :: its, m, w⟩)
      (.run ⟨0, its, m', w⟩) ∧ m' (.reg (.x 0)) = regVal w (.x 0) := by
  obtain ⟨hi, hsz⟩ := argsS0
  refine ⟨_, MStep.op vb0S hi (operands_args [(0, .x 0), (1, .x 1)]) rfl rfl
    (by simp [argOps, Operand.isDef]) (HavocOuts.refl _ _ _)
    ⟨fun _ _ => rfl, fun c hc => by cases hc⟩ (MNext.next (by rw [hsz]; decide)), ?_⟩
  simp [writeM, argOps, Operand.isDef, Operand.isLate, Operand.isEarly, Backend.Proof.upd]

/-- **The run of the compiled `atomic_store` through its `stlr`**: after the prologue, a precise
run reading the thread's own bytes whose last step is the `stlr`'s single event (`relW`, 8 bytes
at address 0, the first argument), every earlier event private and plain; `Compiled` at its
start. -/
theorem run_store : ∃ (n : Nat) (lsP : List Lab) (e : Ev) (t' : ArmState × Mon),
    (∀ env p, Compiled env p RAS csS (iterN RAS.step n RAS.s0)) ∧
    PRun Policy.arm RAS.step (OkPriv RAS) (iterN RAS.step n RAS.s0, none) (lsP ++ [⟨[e], false⟩]) t' ∧
    e.k = .relW ∧ e.n = 8 ∧ e.addr = 0 ∧
    (∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RAS e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR)) := by
  obtain ⟨n', hq, hA⟩ := qRS
  have e0 := checksRunS.1
  have hq0 := hq
  have hA0 := hA
  simp only [MConf.init] at hq0 hA0
  rw [show RAS.rf = rfS from rfl, e0] at hq0 hA0
  -- the saves
  obtain ⟨ls1, t1, r1, hq1, hA1, hev1⟩ := moves_fwdA wfRS (fun K => (K == .plainW) = true)
    savesL _ _ _ none hq0 hA0 (moves_kinds checksRunS.2.1) (by simp [savesL, Loc.isSave])
  -- the entry `args`
  obtain ⟨m', hst, hm'⟩ := args_stepS (spillS.map (fun p => RItem.move p.1 p.2) ++ rest2S) _ w₀S
  have hq2 := realizes_args wfRS hq1 hA1 vb0S argsS0.1 hst
  have hA2 := Backend.Proof.aInv_step wfRS hq1 hA1 hst
  -- the spill moves
  obtain ⟨ls2, t2, r2, hq3, -, hev2⟩ := moves_fwdA wfRS
    (fun K => (K == .plainW || K == .plainR) = true) spillS rest2S t1.1 m' t1.2 hq2 hA2
    (moves_kinds checksRunS.2.2.1) (by simp [spillS, Loc.isSave])
  -- the `stlr`
  obtain ⟨j, hj, hpc, hstr⟩ := q_head hq3 rfl head_stlrS
  obtain ⟨t3, ev, r3, -, hk, hn, ha⟩ := excl_step_fwd wfRS hj rfl hstr.prog hpc hstr.err
    (lb := 0) (p := 1) (q := 0) (.inl rfl) (by omega) (by omega) (fun _ => rfl) t2.2
  simp only [show ¬ (0 : Nat) = 1 from by decide, ite_false] at hk
  -- its address: the first argument, `x0 = 0`
  have hx0 : movesM spillS m' (.reg (.x 0)) = regVal w₀S (.x 0) := by
    simp [movesM, spillS, Backend.Proof.upd, hm']
  have hs3 := hstr.store (.reg (.x 0)) (fun r h => by cases h; rfl) trivial
  rw [hx0] at hs3
  have hz : regVal w₀S (.x 0) = 0 := by
    rw [E2E.regVal_bodyOf _ _ (by decide), shapeS.2.2.2.2.2.2.2.1]
  have hr : PRun Policy.arm RAS.step (OkPriv RAS) (iterN RAS.step n' RAS.s0, none)
      ((ls1 ++ ls2) ++ [⟨[ev], false⟩]) t3 := PRun.append (PRun.append r1 r2) r3
  have hevP : ∀ l ∈ ls1 ++ ls2, ∀ e' ∈ l.evs,
      PrivA RAS e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR) := by
    intro l hl e' he'
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨hF, hK⟩ := hev1 l hl e' he'
      exact ⟨privA_addr.2 hF, .inl (by simpa using hK)⟩
    · obtain ⟨hF, hK⟩ := hev2 l hl e' he'
      exact ⟨privA_addr.2 hF, by simpa using hK⟩
  exact ⟨n', ls1 ++ ls2, ev, t3, fun env p => compiled_ofS hq hA env p, hr, hk, hn,
    ha.trans (regVal_x0 hs3 hz), hevP⟩

/-- **`Realizes` on the compiled `atomic_store` through its `stlr`** (module doc). -/
theorem realizes_store : ∃ (n : Nat) (lsP : List Lab) (e : Ev) (t' : ArmState × Mon),
    PRun Policy.arm RAS.step (OkPriv RAS) (iterN RAS.step n RAS.s0, none) (lsP ++ [⟨[e], false⟩]) t' ∧
    e.k = .relW ∧ e.n = 8 ∧ e.addr = 0 ∧
    (∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RAS e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR)) ∧
    ∀ (env : Clif.Env) (p : Clif.Program) (M0 : Bytes), ∃ k ≤ lsP.length + 1,
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧ PC.st 0 0 = .run csS ∧
        PC.Runs (CStep env p) ∧
        Realizes (PA1 RAS (iterN RAS.step n RAS.s0) (lsP ++ [⟨[e], false⟩]) k) (locs1 lsP e) M0
          (latestW (PA1 RAS (iterN RAS.step n RAS.s0) (lsP ++ [⟨[e], false⟩]) k) (locs1 lsP e))
          (coL (PA1 RAS (iterN RAS.step n RAS.s0) (lsP ++ [⟨[e], false⟩]) k) (locs1 lsP e))
          (fun _ _ => False) PC [(e.addr.toNat, e.n)] M0 φ (fun _ _ _ => True) := by
  obtain ⟨n, lsP, e, t', hc, hr, hk, hn, ha, hevP⟩ := run_store
  exact ⟨n, lsP, e, t', hr, hk, hn, ha, hevP, fun env p M0 =>
    realizes_one hc hr hevP (by rw [hk]; decide) env p M0⟩

/-! ## The whole run -/

theorem bodyS : ∃ st rest, csS.frame.body = st :: rest ∧ st.inst = .atomicStore .i64 {} 1 0 := by
  have h : csS.frame.body.head?.map (·.inst) = some (.atomicStore .i64 {} 1 0) := by native_decide
  revert h
  cases csS.frame.body with
  | nil => intro h; cases h
  | cons st rest => intro h; exact ⟨st, rest, rfl, by simpa using h⟩

theorem regS0 : csS.frame.regs 0 = some ⟨.i64, 0⟩ := by native_decide

theorem getS1 : ∃ v, csS.frame.getAs 1 .i64 = .ok v := by
  have h : (match csS.frame.getAs 1 .i64 with | .ok _ => true | _ => false) = true := by
    native_decide
  revert h
  cases csS.frame.getAs 1 .i64 with
  | ok v => intro _; exact ⟨v, rfl⟩
  | _ => intro h; cases h

theorem stepS0 : (match Clif.step default default (withBytes csS (fun _ => some 0)) with
    | .next _ => true | _ => false) = true := by native_decide

/-- **The CLIF thread from `csS` steps** (its `atomic_store`). -/
theorem cstep_csS (env : Clif.Env) (p : Clif.Program) : ∃ evs t', CStep env p (.run csS) evs t' := by
  obtain ⟨st, rest, hb, hi⟩ := bodyS
  obtain ⟨v, hv⟩ := getS1
  have hb' : (withBytes csS (fun _ => some 0)).frame.body = st :: rest := hb
  obtain ⟨s', hs⟩ := step_next_of_check (env := env) (p := p) hb'
    (fun _ _ h => by rw [hi] at h; cases h) (fun _ _ _ h => by rw [hi] at h; cases h) default
    default stepS0
  exact ⟨_, _, ClifCStep.cstep_atomicStore hb' hi regS0 hv hs⟩

theorem shapeS1 : evShape csS = [[(.scW, 8)]] := by
  obtain ⟨st, rest, hb, hi⟩ := bodyS
  simp only [evShape, hb, hi]
  rfl

theorem notStop_csS (env : Clif.Env) (p : Clif.Program) : ¬ Stop env p (.run csS) := by
  obtain ⟨st, rest, hb, hi⟩ := bodyS
  obtain ⟨evs, t', hs⟩ := cstep_csS env p
  rintro (hd | hc)
  · exact hd ⟨evs, t', hs⟩
  · exact not_casRO hb (fun _ _ _ _ _ h => by rw [hi] at h; cases h) hc

/-- **`Realizes` on the compiled `atomic_store` through its `stlr`, on the whole run** (T2j). -/
theorem realizes_store_full : ∃ (n : Nat) (lsP : List Lab) (e : Ev) (t' : ArmState × Mon),
    PRun Policy.arm RAS.step (OkPriv RAS) (iterN RAS.step n RAS.s0, none) (lsP ++ [⟨[e], false⟩]) t' ∧
    e.k = .relW ∧ e.n = 8 ∧ e.addr = 0 ∧
    (∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RAS e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR)) ∧
    ∀ (env : Clif.Env) (p : Clif.Program) (M0 : Bytes),
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧ PC.st 0 0 = .run csS ∧
        PC.Runs (CStep env p) ∧
        Realizes (PA1 RAS (iterN RAS.step n RAS.s0) (lsP ++ [⟨[e], false⟩]) (lsP.length + 1))
          (locs1 lsP e) M0
          (latestW (PA1 RAS (iterN RAS.step n RAS.s0) (lsP ++ [⟨[e], false⟩]) (lsP.length + 1))
            (locs1 lsP e))
          (coL (PA1 RAS (iterN RAS.step n RAS.s0) (lsP ++ [⟨[e], false⟩]) (lsP.length + 1))
            (locs1 lsP e))
          (fun _ _ => False) PC [(e.addr.toNat, e.n)] M0 φ (fun _ _ _ => True) := by
  obtain ⟨n, lsP, e, t', hc, hr, hk, hn, ha, hevP⟩ := run_store
  exact ⟨n, lsP, e, t', hr, hk, hn, ha, hevP, fun env p M0 =>
    realizes_one_full hc hr hevP (by rw [hk]; decide) env p M0 (notStop_csS env p)
      (fun _ _ hs => nonFence_one shapeS1 (by decide) hs)⟩

end Concurrency.RealizeCompiled.WitnessS
