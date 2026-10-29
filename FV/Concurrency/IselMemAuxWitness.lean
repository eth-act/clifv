module

public import FV.Concurrency.IselMemAux
public import FV.Concurrency.SegFootWitness
public import FV.Concurrency.VCodeFrameWitness

@[expose] public section

/-!
# Non-vacuity of `IselMemAux` (T2h, #311, layer 2e)

* exact shapes: `ldar_one_w0` (`cEvs_loadAcquire_one`, `cEvs_straight_one`), `fence_w0`,
  `rmw_shape_w0` (`cEvs_rmw_shape` on a concrete `atomic_rmw add` step),
  `cas_shape_w0` (`cEvs_cas_shape` on a concrete `atomic_cas` step whose expected value differs);
* reached states: `seq1` (the one-instruction segment `ldar` falls through from `w5`),
  `runAt1` (its state after the `ldar`), `runAt1_take`, `runAt1_step`, `runAt1_keep`,
  `runAt1_det`;
* event-free runs: `star_rets` (`star_mem_keep` on the one-step run of `rets []`).
-/

namespace Concurrency.IselMemAux.Witness

open Arm ArmFoot ArmThread ArmInstFoot Backend Backend.Proof VCodeThread VCodeThread.Witness
  VCodeAddr VCodeAddr.Witness IselCover SegFoot SegFoot.Witness

/-! ## Exact shapes -/

theorem ldar_one_w0 :
    ∃ e, cEvs F8 ctx0 iLdar [ofX 0x8000#64] w0 = [e] ∧ e.k = .acqR ∧ e.n = 8 :=
  cEvs_loadAcquire_one (by decide +kernel) _ _

theorem ldar_one_w0' : ∃ e, cEvs F8 ctx0 iLdar [ofX 0x8000#64] w0 = [e] :=
  cEvs_straight_one (n := 8) rfl rfl (fun h => by
    have := ldar_evs_ne
    rw [h] at this
    cases this)

theorem ldar_le_one : (cEvs F8 ctx0 iLdar [ofX 0x8000#64] w0).length ≤ 1 :=
  cEvs_straight_le_one (n := 8) F8 ctx0 rfl rfl _ _

theorem fence_w0 : cEvs F8 ctx0 .fence [] w0 = [dmbEv] := cEvs_fence _ _ _ _

open Classical in
theorem loopSem_eq {F : BitVec 64 → Prop} {ty : CTy} {a : CV} {body : List Line}
    {regs : List Reg} {uses : List CV} {defs : List Reg} {w t' : ArmState}
    (hc : AtomTy ty ∧ Avoids F ty.bytes (lo64 a) ∧ Arm.r .ERR w = .None)
    (hex : execLines env0 body ((regs.zip uses).foldl (fun s p => setReg s p.1 p.2) w) = some t')
    (hok : Arm.r .ERR t' = .None ∧ t'.program = w.program) :
    loopSem F ty a body regs uses defs w =
      some ((defs.take 1).map (regVal t') ++ (defs.drop 1).map (fun _ => ofX 0), t', .next) := by
  unfold loopSem
  rw [ite_eq_left hc, hex]
  simp only [hok, and_self, ite_true]

/-- The world `w0` with the loops' use registers placed. -/
def t2 : ArmState := ([Reg.x 25, .x 26].zip [ofX 0x8000#64, ofX 1#64]).foldl
  (fun s p => setReg s p.1 p.2) w0

def t3 : ArmState := ([Reg.x 25, .x 26, .x 28].zip [ofX 0x8000#64, ofX 1#64, ofX 2#64]).foldl
  (fun s p => setReg s p.1 p.2) w0

/-- The body run of the `atomic_rmw add` loop. -/
def tr : ArmState := (execLines env0 (rmwLoopBody 64 .add {}) t2).getD w0

theorem exec_tr : execLines env0 (rmwLoopBody 64 .add {}) t2 = some tr := by
  have h : (execLines env0 (rmwLoopBody 64 .add {}) t2).isSome = true := by native_decide
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
  rw [ht]; simp only [tr, ht, Option.getD_some]

theorem ok_tr : Arm.r .ERR tr = .None ∧ tr.program = w0.program := by
  have he : (Arm.r .ERR tr == .None) = true := by native_decide
  have hp : @BEq.beq (List (BitVec 64 × BitVec 32)) _ tr.program w0.program = true := by
    native_decide
  exact ⟨by simpa using he, @eq_of_beq (List (BitVec 64 × BitVec 32)) _ _ _ _ hp⟩

/-- `atomic_rmw add` (64 bits) of `1` at `0x8000`. -/
def iRmw : MInst :=
  .atomicRmwLoop (.int 64) .add {} (.vreg 0 .int) (.vreg 1 .int) (.vreg 2 .int) (.vreg 3 .int)
    (.vreg 4 .int)

theorem csem_rmw : ∃ r, csem (fun _ => False) ctx0 X0 iRmw [ofX 0x8000#64, ofX 1#64] w0 = some r := by
  have he : Arm.r .ERR w0 = .None := by decide +kernel
  have e2 := loopSem_eq (F := fun _ => False) (ty := .int 64) (a := ofX 0x8000#64)
    (body := rmwLoopBody (CTy.int 64).bits .add {}) (regs := [.x 25, .x 26])
    (uses := [ofX 0x8000#64, ofX 1#64]) (defs := [.x 27, .x 24, .x 28]) (w := w0)
    ⟨by decide, fun _ _ h => h, he⟩ exec_tr ok_tr
  simp only [iRmw, csem, he, ite_true, e2]
  exact ⟨_, rfl⟩

/-- **`cEvs_rmw_shape` on a concrete step.** -/
theorem rmw_shape_w0 : ∃ wr, cEvs (fun _ => False) ctx0 iRmw [ofX 0x8000#64, ofX 1#64] w0 =
    [⟨.acqXR, lo64 (ofX 0x8000#64), (CTy.int 64).bytes,
      readM (CTy.int 64).bytes (lo64 (ofX 0x8000#64)) w0.mem⟩, wr] ∧
    wr.k = .relXW ∧ wr.addr = lo64 (ofX 0x8000#64) ∧ wr.n = (CTy.int 64).bytes := by
  obtain ⟨r, hr⟩ := csem_rmw
  exact cEvs_rmw_shape (by decide +kernel) hr

/-- The head run of the `atomic_cas` loop. -/
def tc : ArmState := (execLines env0 (casLoopHead 64 {}) t3).getD w0

theorem exec_tc : execLines env0 (casLoopHead 64 {}) t3 = some tc := by
  have h : (execLines env0 (casLoopHead 64 {}) t3).isSome = true := by native_decide
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
  rw [ht]; simp only [tc, ht, Option.getD_some]

theorem ok_tc : Arm.r .ERR tc = .None ∧ tc.program = w0.program ∧
    Arm.ConditionHolds Cond.ne.bits tc = true := by
  have he : (Arm.r .ERR tc == .None) = true := by native_decide
  have hp : @BEq.beq (List (BitVec 64 × BitVec 32)) _ tc.program w0.program = true := by
    native_decide
  have hn : Arm.ConditionHolds Cond.ne.bits tc = true := by native_decide
  exact ⟨by simpa using he, @eq_of_beq (List (BitVec 64 × BitVec 32)) _ _ _ _ hp, hn⟩

/-- `atomic_cas` (64 bits) at `0x8000`, expecting `1` (memory holds `0`), replacing with `2`. -/
def iCas : MInst :=
  .atomicCasLoop (.int 64) {} (.vreg 0 .int) (.vreg 1 .int) (.vreg 2 .int) (.vreg 3 .int)
    (.vreg 4 .int)

theorem csem_cas :
    ∃ r, csem (fun _ => False) ctx0 X0 iCas [ofX 0x8000#64, ofX 1#64, ofX 2#64] w0 = some r := by
  have he : Arm.r .ERR w0 = .None := by decide +kernel
  have e2 := loopSem_eq (F := fun _ => False) (ty := .int 64) (a := ofX 0x8000#64)
    (body := casLoopHead (CTy.int 64).bits {}) (regs := [.x 25, .x 26, .x 28])
    (uses := [ofX 0x8000#64, ofX 1#64, ofX 2#64]) (defs := [.x 27, .x 24]) (w := w0)
    ⟨by decide, fun _ _ h => h, he⟩ exec_tc ⟨ok_tc.1, ok_tc.2.1⟩
  simp only [iCas, csem, he, ite_true, e2, ok_tc.2.2]
  exact ⟨_, rfl⟩

/-- **`cEvs_cas_shape` on a concrete step** (the expected value differs: the read only). -/
theorem cas_shape_w0 :
    (cEvs (fun _ => False) ctx0 iCas [ofX 0x8000#64, ofX 1#64, ofX 2#64] w0 =
        [⟨.acqXR, lo64 (ofX 0x8000#64), (CTy.int 64).bytes,
          readM (CTy.int 64).bytes (lo64 (ofX 0x8000#64)) w0.mem⟩] ∧
      readM (CTy.int 64).bytes (lo64 (ofX 0x8000#64)) w0.mem ≠
        (lo64 (ofX 1#64)).setWidth ((CTy.int 64).bytes * 8)) ∨
    (∃ wr, cEvs (fun _ => False) ctx0 iCas [ofX 0x8000#64, ofX 1#64, ofX 2#64] w0 =
        [⟨.acqXR, lo64 (ofX 0x8000#64), (CTy.int 64).bytes,
          readM (CTy.int 64).bytes (lo64 (ofX 0x8000#64)) w0.mem⟩, wr] ∧
      wr.k = .relXW ∧ wr.addr = lo64 (ofX 0x8000#64) ∧ wr.n = (CTy.int 64).bytes ∧
      readM (CTy.int 64).bytes (lo64 (ofX 0x8000#64)) w0.mem =
        (lo64 (ofX 1#64)).setWidth ((CTy.int 64).bytes * 8)) := by
  obtain ⟨r, hr⟩ := csem_cas
  exact cEvs_cas_shape (by decide +kernel) hr

/-! ## Reached states -/

/-- The one-instruction segment. -/
def seg1 : List MInst := [iLdar]

theorem hs1 : csem (fun _ => False) ctx0 X0 iLdar (vuses ops0 ρ0) w5 =
    some (defVals ops0 (canonRegs ops0) t5, t5, .next) := by
  have hu : vuses ops0 ρ0 = [ofX 0x8000#64] := uses0
  rw [hu]; exact csem_ldar

theorem seq1 : seqRun (csem (fun _ => False) ctx0 X0) seg1 ρ0 w5 = some (.fall ρ1 t5) := by
  have hlen : (defVals ops0 (canonRegs ops0) t5).length =
      (ops0.toList.filter Operand.isDef).length := by decide +kernel
  simp only [seg1, seqRun, ops0_eq, hs1, hlen, ite_true, Option.map_some]
  rfl

theorem runAt1 : RunAt (csem (fun _ => False) ctx0 X0) seg1 ρ0 w5 1 ρ1 t5 :=
  ⟨ops0, _, t5, ops0_eq, hs1, ⟨rfl, rfl⟩⟩

theorem runAt1_take : 1 ≤ seg1.length ∧
    seqRun (csem (fun _ => False) ctx0 X0) (seg1.take 1) ρ0 w5 = some (.fall ρ1 t5) :=
  runAt_take seq1 runAt1

theorem runAt1_step : ∃ outs w2,
    csem (fun _ => False) ctx0 X0 iLdar (vuses ops0 ρ0) w5 = some (outs, w2, .next) :=
  runAt_step seq1 (j := 0) ⟨rfl, rfl⟩ rfl ops0_eq

theorem runAt1_keep : Arm.r .ERR t5 = .None ∧ Arm.CheckSPAlignment t5 :=
  runAt_keep (fun i hi => seg_covered i (by
      simp only [seg1, List.mem_cons, List.not_mem_nil, or_false] at hi
      simp [seg, hi]))
    (by decide +kernel) (by unfold Arm.CheckSPAlignment; decide +kernel) runAt1

theorem runAt1_det {ρ' : Nat → CV} {w' : ArmState}
    (h : RunAt (csem (fun _ => False) ctx0 X0) seg1 ρ0 w5 1 ρ' w') : ρ1 = ρ' ∧ t5 = w' :=
  runAt_det runAt1 h

/-! ## Event-free runs -/

/-- One block: `rets []`. -/
def vc1 : VCode :=
  { name := "r", blocks := #[{ label := 0, insts := #[.rets []] }], classes := #[],
    slotBytes := 0, outgoing := 0, rulesFired := #[] }

def P1 (c : VConf CV ArmState) : Prop := c = .run ⟨0, 0, ρ0, w0⟩

theorem step1 : VStep vc1 (csem (fun _ => False) ctx0 X0) (.run ⟨0, 0, ρ0, w0⟩) (.ret [] w0) :=
  VStep.step (ops := #[]) (outs := []) rfl rfl rfl rfl rfl (.ret rfl)

theorem path1 : IselStep.StarNP (VStep vc1 (csem (fun _ => False) ctx0 X0)) P1 1
    (.run ⟨0, 0, ρ0, w0⟩) (.ret [] w0) :=
  .step rfl step1 (.refl _)

/-- **`star_mem_keep` on a concrete run**: the step of `rets []` keeps the memory, the error flag
and the alignment. -/
theorem star_rets : (SegRun.confW (.ret [] w0)).mem = (SegRun.confW (.run ⟨0, 0, ρ0, w0⟩)).mem ∧
    Arm.r .ERR (SegRun.confW (.ret [] w0)) = .None ∧
    Arm.CheckSPAlignment (SegRun.confW (.ret [] w0)) :=
  star_mem_keep X0_tls (fun c hc => ⟨0, 0, ρ0, w0, _, .rets [], hc, rfl, rfl,
      ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h), .inl rfl⟩, rfl⟩) path1
    (by decide +kernel) (by unfold Arm.CheckSPAlignment; decide +kernel)

end Concurrency.IselMemAux.Witness
