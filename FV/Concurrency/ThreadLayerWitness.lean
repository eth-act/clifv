module

public import FV.Concurrency.VCodeEvents
public import FV.Concurrency.PrivCoh
public import FV.Concurrency.ArmPrecise
public import FV.Concurrency.PrepThread
public import FV.Concurrency.AllocThread
public import FV.Concurrency.VCodeThreadWitness
public import FV.Concurrency.ThreadRefineWitness

@[expose] public section

/-!
# Non-vacuity of the event kinds of VCode, private coherence and precise labels (T2h, #311)

* `instEvs_kinds_ldaxr`, `cEvs_kinds_ldar`, `cEvs_kinds_rmw`, `cEvs_nil_add`: the kinds of
  `VCodeEvents` at an emitted `ldaxr`, at VCode's `ldar` (`acqR`), at the `atomic_rmw` loop's body
  (`acqXR` then `relXW`, its full table entry) and at an `add` (no event);
* `privCoh_own`: `PrivCoh.privCoh_of_consistent` for a thread that writes `x` and reads it back
  (`x` private to it): every premise holds, and its read reads its own write;
* `ret_threads_priv`: `realizes_of_threads_priv` for the two returning threads of
  `ProgWitness`; `ret_ownWrites`: `ownWrites_of_refines` for them;
* `prep_ldar`: `PrepThread.prep_refines_csem` for the one-block VCode of `VCodeThread.Witness`
  (`prepare` keeps it): its run reading the environment's `5` with its `ldar` is realized by a run
  of the original;
* `alloc_ldar`: `AllocThread.alloc_refines` for a two-instruction VCode (`args`, `ldar`) and an
  allocation `checkAlloc` accepts: the allocated code's run, whose `ldar` reads the environment's
  `5`, is realized by a VCode run;
* `precise_ldaxr`: `ArmPrecise.exists_precise_step` at the `ldaxr` of `ArmThread.Witness` with the
  environment's `5` at `0x8000`: the precise label is the read of `5` (`stepEvs_setMem_ldaxr`).
-/

namespace Concurrency.ThreadLayerWitness

open Arm ArmFoot ArmThread ArmInstFoot Backend Backend.Proof VCodeThread VCodeEvents Code
open Rel Prog ClifThread ProgE2E ThreadRefine PrivCoh ArmPrecise
open scoped List

/-! ## Kinds -/

/-- `ldaxr x27, [x25]` (64 bits) at offset 0. -/
theorem instEvs_kinds_ldaxr :
    ∃ ai, (Insn.ldaxr 64 (.x 27) (.x 25)).toArmInst env0 = .ok ai ∧
      (instEvs ai (ArmThread.Witness.st 0x1000#64 0#64)).map (·.k) = [.acqXR] ∧
      (instEvs ai (ArmThread.Witness.st 0x1000#64 0#64)).map (·.k) <+
        (insnKind (.ldaxr 64 (.x 27) (.x 25))).toList := by
  refine ⟨_, rfl, by decide +kernel, instEvs_kinds (env := env0) rfl _⟩

/-- VCode's `ldar`: its event kinds are its table entry `[acqR]`. -/
theorem cEvs_kinds_ldar :
    (cEvs (fun _ => False) VCodeThread.Witness.ctx0 VCodeThread.Witness.iLdar [ofX 0x8000#64]
      VCodeThread.Witness.w0).map (·.k) = akinds VCodeThread.Witness.iLdar ∧
    (cEvs (fun _ => False) VCodeThread.Witness.ctx0 VCodeThread.Witness.iLdar [ofX 0x8000#64]
      VCodeThread.Witness.w0).map (·.k) <+ akinds VCodeThread.Witness.iLdar :=
  ⟨by decide +kernel, cEvs_kinds _ _ _ _ _⟩

/-- The allocated `atomic_rmw add` loop (address `0x8000` in x25, operand `1` in x26). -/
def iRmw : MInst := .atomicRmwLoop (.int 64) .add {} (.x 25) (.x 26) (.x 27) (.x 24) (.x 28)

/-- The loop body's events: its `ldaxr` read and its `stlxr` write, the whole table entry. -/
theorem cEvs_kinds_rmw :
    (cEvs (fun _ => False) VCodeThread.Witness.ctx0 iRmw [ofX 0x8000#64, ofX 1#64]
      VCodeThread.Witness.w0).map (·.k) = akinds iRmw ∧
    (cEvs (fun _ => False) VCodeThread.Witness.ctx0 iRmw [ofX 0x8000#64, ofX 1#64]
      VCodeThread.Witness.w0).map (·.k) <+ akinds iRmw :=
  ⟨by decide +kernel, cEvs_kinds _ _ _ _ _⟩

/-- An `add` has no event. -/
theorem cEvs_nil_add :
    cEvs (fun _ => False) VCodeThread.Witness.ctx0
      (.aluRRR .add .size64 (.vreg 0 .int) (.vreg 1 .int) (.vreg 2 .int)) [ofX 1#64, ofX 2#64]
      VCodeThread.Witness.w0 = [] :=
  cEvs_nil rfl _ _

/-! ## Private coherence: a thread reads its own write -/

abbrev E := Ev SKind BVal

/-- The write of `1` to `x` (address 0) and its read. -/
def wx : E := ⟨.naW, .W, 0, 1, [some 1]⟩
def rx : E := ⟨.naR, .R, 0, 1, [some 1]⟩

/-- One thread: `x = 1; r = x`. -/
def steps : Nat → List (List E)
  | 0 => [[wx], [rx]]
  | _ => []

def Q : Traces (List (List E)) SKind BVal := ⟨1, steps, fun i j => (steps i).drop j⟩

def locs : List (Nat × Nat) := [(0, 1)]

def M0 : Bytes := fun _ => some 0

def rf (a b : PEv) : Prop := a = .thr 0 0 0 ∧ b = .thr 0 1 0

def co (a b : PEv) : Prop := a = .init 0 ∧ b = .thr 0 0 0

def rmw (_ _ : PEv) : Prop := False

abbrev X := Q.exec locs rf co rmw

theorem evAt_cases {i j k : Nat} {x : E} (h : Q.evAt (.thr i j k) = some x) :
    (i = 0 ∧ j = 0 ∧ k = 0 ∧ x = wx) ∨ (i = 0 ∧ j = 1 ∧ k = 0 ∧ x = rx) := by
  rcases i with _ | i <;> rcases j with _ | _ | j <;> rcases k with _ | k <;>
    simp [Traces.evAt, Q, steps] at h <;> simp [h]

def evs : List PEv := [.init 0, .thr 0 0 0, .thr 0 1 0]

theorem mem_evs {e : PEv} (h : X.dir e ≠ .F) : e ∈ evs := by
  cases e with
  | init q =>
    rcases q with _ | q <;> simp [evs]
    simp [Traces.exec, locs] at h
  | thr i j k =>
    rcases hx : Q.evAt (.thr i j k) with _ | x
    · simp [Traces.exec, hx] at h
    · rcases evAt_cases hx with ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩ <;> simp [evs]

theorem wf : X.Wf where
  po_irrefl a := PEv.po_irrefl a
  po_trans _ _ _ := PEv.po_trans
  po_tid _ _ := PEv.po_tid
  po_total _ _ := PEv.po_total
  rf_dir a b h := by obtain ⟨rfl, rfl⟩ := h; decide
  rf_loc a b h := by obtain ⟨rfl, rfl⟩ := h; decide
  rf_func a a' b h1 h2 := by obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, -⟩ := h2; rfl
  rf_total b hb := by
    have := mem_evs (e := b) (by rw [hb]; decide)
    simp only [evs, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl
    all_goals first
      | exact absurd hb (by decide)
      | exact ⟨_, rfl, rfl⟩
  co_dir a b h := by obtain ⟨rfl, rfl⟩ := h; decide
  co_loc a b h := by obtain ⟨rfl, rfl⟩ := h; decide
  co_irrefl a h := by obtain ⟨rfl, h⟩ := h; cases h
  co_trans a b c h1 h2 := by obtain ⟨rfl, rfl⟩ := h1; obtain ⟨h, -⟩ := h2; cases h
  co_total a b ha hb hl hne := by
    have h1 := mem_evs (e := a) (by rw [ha]; decide)
    have h2 := mem_evs (e := b) (by rw [hb]; decide)
    simp only [evs, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hne
      | exact absurd ha (by decide)
      | exact absurd hb (by decide)
      | exact .inl ⟨rfl, rfl⟩
      | exact .inr ⟨rfl, rfl⟩
  rmw_dir _ _ h := h.elim
  rmw_loc _ _ h := h.elim
  rmw_po _ _ h := h.elim
  rmw_imm _ _ _ h := h.elim

def rank : PEv → Nat
  | .init q => q
  | .thr i j _ => 1 + 2 * i + j

theorem sc : X.SC := by
  refine sc_of_rank_on wf (· ∈ evs) rank ?_ ?_ ?_
  · intro a b h
    exact ⟨mem_evs (wf.com_notF h).1, mem_evs (wf.com_notF h).2⟩
  · intro a b ha hb h
    simp only [evs, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp_all [Traces.exec, PEv.po, rank]
  · intro a b h
    rcases h with h | h | ⟨w, h1, h2⟩
    · obtain ⟨rfl, rfl⟩ := h; decide
    · obtain ⟨rfl, rfl⟩ := h; decide
    · obtain ⟨rfl, rfl⟩ := h1; obtain ⟨h, -⟩ := h2; cases h

theorem internal : Acyclic (union X.poLoc X.com) :=
  sc.mono fun _ _ h => by
    rcases h with h | h
    · exact .inl h.1
    · exact .inr h

/-- **Non-vacuity of `privCoh_of_consistent`**: `x` is private to the thread; its read of `x`
reads its own write. -/
theorem privCoh_own : PrivCoh (fun l => l = 0) (fun l n => bytesI.get M0 l n) (Q.tr 0) := by
  have h := privCoh_of_consistent (M0 := M0) (Priv := fun i l => i = 0 ∧ l = 0) wf internal
    (fun w q h => by obtain ⟨-, h⟩ := h; cases h)
    (fun w r h => by obtain ⟨rfl, rfl⟩ := h; rfl)
    (fun a b ha hb => by
      have h1 := mem_evs ha
      have h2 := mem_evs hb
      simp only [evs, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
      rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;> decide)
    (fun i j k x hx _ i' hP => by
      rcases evAt_cases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact hP.1)
    0 (by decide)
  intro p y hy hR hP
  exact h p y hy hR ⟨rfl, hP⟩

/-- The read is the second step's, and `privCoh_own` names the first step's write. -/
theorem privCoh_own_read : evAt (Q.tr 0) (1, 0) = some rx ∧
    ∃ q x, Lt q (1, 0) ∧ evAt (Q.tr 0) q = some x ∧ x.dir = .W ∧ x.val = rx.val := by
  refine ⟨rfl, ?_⟩
  rcases privCoh_own (1, 0) rx rfl rfl rfl with ⟨q, x, hq, hx, hW, -, hv, -⟩ | ⟨h, -⟩
  · exact ⟨q, x, hq, hx, hW, hv⟩
  · exact absurd rfl (h (0, 0) wx (.inl (by decide)) rfl rfl)

/-! ## Per-thread private sets -/

/-- **Non-vacuity of `realizes_of_threads_priv`**: the two returning threads of `ProgWitness`. -/
theorem ret_threads_priv : ∃ (PC' : Traces TState SKind BVal) (φ : PEv → PEv), PC'.n = ProgWitness.PA.n ∧
    (∀ i, PC'.st i 0 = ProgWitness.s0 i) ∧ PC'.Runs (CStep ProgWitness.env0 ProgWitness.p0) ∧
    Realizes ProgWitness.PA [] (fun _ => none) ProgWitness.none2 ProgWitness.none2
      ProgWitness.none2 PC' [] (fun _ => none) φ ProgWitness.Obs :=
  realizes_of_threads_priv (PrivT := fun _ _ => False) (pairT := fun _ _ _ => False)
    ProgWitness.wfA (fun _ _ _ _ => Iff.rfl) (List.prefix_refl _)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun i hi => ⟨[[]], ProgWitness.PC.st i, id, rfl, fun j hj => ProgWitness.runsC i hi j hj,
      ProgWitness.ret_refines i, (fun p x h => by rw [ProgWitness.evAt_ret] at h; cases h), rfl⟩)

/-- **Non-vacuity of `ownWrites_of_refines`**: the two returning threads (every premise holds). -/
theorem ret_ownWrites : ∀ i j k x, ProgWitness.PA.evAt (.thr i j k) = some x → x.dir = .W →
    ∀ i', (fun _ _ => False : Nat → Nat → Prop) i' x.loc → i' = i :=
  ownWrites_of_refines (fun _ _ _ h => h.elim)
    (fun i _ => ⟨[[]], fun _ _ => False, id, ProgWitness.ret_refines i,
      fun p x h => by rw [ProgWitness.evAt_ret] at h; cases h⟩)

/-! ## Precise labels -/

/-- The environment's memory: `5` at `0x8000`. -/
def m5 : Memory := writeM 8 0x8000#64 5#64 (ArmThread.Witness.st 0x1000#64 0#64).mem

/-- The `ldaxr`'s footprint on the environment's memory is the read of `5` (`stepEvs_setMem`). -/
theorem stepEvs_setMem_ldaxr :
    stepEvs (setMem m5 (ArmThread.Witness.st 0x1000#64 0#64)) = [ArmThread.Witness.evRead] ∧
    stepEvs (setMem m5 (ArmThread.Witness.st 0x1000#64 0#64)) =
      reread m5 (stepEvs (ArmThread.Witness.st 0x1000#64 0#64)) :=
  ⟨VCodeThread.Witness.evs_ext (by decide +kernel), stepEvs_setMem _ _⟩

/-- **Non-vacuity of `exists_precise_step`**: the `ldaxr` steps with the precise label that reads
the environment's `5` (its own memory holds `0`). -/
theorem precise_ldaxr : ∃ t', TStep Policy.arm stepi (ArmThread.Witness.st 0x1000#64 0#64, none)
    ⟨[ArmThread.Witness.evRead], false⟩ t' ∧
    Precise (ArmThread.Witness.st 0x1000#64 0#64) ⟨[ArmThread.Witness.evRead], false⟩ := by
  have hcls : cls (ArmThread.Witness.st 0x1000#64 0#64) = .ldx true 25#5 3#2 := by
    unfold cls; rw [ArmThread.Witness.decode_ldaxr]; decide
  obtain ⟨t', h1, h2, -⟩ := exists_precise_step Policy.arm (ArmThread.Witness.st 0x1000#64 0#64)
    none m5 (fun _ _ _ h => by rw [hcls] at h; cases h)
  rw [stepEvs_setMem_ldaxr.1] at h1 h2
  exact ⟨t', h1, h2⟩

/-! ## `prepare` with interference -/

theorem prepCheck_vc0 :
    Driver.prepCheck VCodeThread.Witness.vc0 VCodeThread.Witness.vc0 = true := by
  decide +kernel

/-- **Non-vacuity of `prep_refines_csem`**: the one-block VCode (`ldar`, return), prepared as
itself; its thread run in which the `ldar` reads the environment's `5` is realized by a run of the
original with the same event. -/
theorem prep_ldar : ∃ trS cS ψ c', PrepThread.VTRun VCodeThread.Witness.vc0
    (csem (fun _ => False) VCodeThread.Witness.ctx0 VCodeThread.Witness.X0)
    (cEvs (fun _ => False) VCodeThread.Witness.ctx0)
    (.run ⟨0, 0, VCodeThread.Witness.ρ0, VCodeThread.Witness.w0⟩) trS cS ∧
    Refines (· = ·) (fun _ => False) (StepPair (PrepThread.conv [[VCodeThread.Witness.ev5]]))
      (PrepThread.conv trS) (PrepThread.conv [[VCodeThread.Witness.ev5]]) ψ ∧
    PrepThread.VTRun VCodeThread.Witness.vc0
      (csem (fun _ => False) VCodeThread.Witness.ctx0 VCodeThread.Witness.X0)
      (cEvs (fun _ => False) VCodeThread.Witness.ctx0)
      (.run ⟨0, 0, VCodeThread.Witness.ρ0, VCodeThread.Witness.w0⟩) [[VCodeThread.Witness.ev5]] c' := by
  obtain ⟨c', hst⟩ := VCodeThread.Witness.ldar_vtstep
  have hrun := PrepThread.VTRun.cons hst .nil
  obtain ⟨trS, cS, ψ, hrS, href, -⟩ := PrepThread.prep_refines_csem prepCheck_vc0 hrun
  exact ⟨trS, cS, ψ, c', hrS, href, hrun⟩

/-! ## Register allocation with interference -/

section
open AllocThread VCodeThread.Witness

def iArgs : MInst := .args [(.vreg 1 .int, .x 0)]

/-- `x0` holds the argument `0x8000`, the memory zero. -/
def wA : ArmState := Arm.w (.GPR 0#5) 0x8000#64 ArmState.default

def vcA : VCode :=
  { name := "w", blocks := #[{ label := 0, insts := #[iArgs, iLdar, .rets []] }],
    classes := #[.int, .int], slotBytes := 0, outgoing := 0, rulesFired := #[] }

def rfA : RFunc :=
  { blocks := #[#[.op 0 #[.reg (.x 0)], .op 1 #[.reg (.x 0), .reg (.x 1)], .op 2 #[]]],
    spillSlots := 0, saved := [] }

theorem checkAlloc_A : checkAlloc vcA rfA = .ok () :=
  ok_of_isOkB () (by decide +kernel)

def mA : Loc → CV := fun _ => 0

noncomputable abbrev semA := csem (fun _ => False) ctx0 X0
noncomputable abbrev evA := cEvs (fun _ => False) ctx0

def vbA : VBlock := { label := 0, insts := #[iArgs, iLdar, .rets []] }

def opsArgs : Array Operand := #[⟨1, .int, .def, .late, .fixed (.x 0)⟩]

def opsLdar : Array Operand := #[⟨1, .int, .use, .early, .reg⟩, ⟨0, .int, .def, .late, .reg⟩]

/-- The `ldar` reads the environment's `5` at `0x8000`. -/
def wA5 : ArmState := patch [ev5] (patch [] wA)

def ic5 : MInst := match iLdar.assign (canonRegs opsLdar) with
  | .ok ic => ic
  | .error _ => .fence

theorem ic5_eq : iLdar.assign (canonRegs opsLdar) = .ok ic5 :=
  ok_of_isOkB .fence (by decide +kernel)

def tA : ArmState :=
  (execMInst ctx0 env0 ic5 (placeUses opsLdar (canonRegs opsLdar) [ofX 0x8000#64] wA5)).getD wA5

theorem exec_tA : execMInst ctx0 env0 ic5 (placeUses opsLdar (canonRegs opsLdar) [ofX 0x8000#64] wA5) =
    some tA := by
  have h : (execMInst ctx0 env0 ic5 (placeUses opsLdar (canonRegs opsLdar) [ofX 0x8000#64] wA5)).isSome := by
    decide +kernel
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
  rw [ht]; simp only [tA, ht, Option.getD_some]

theorem csem_ldarA : semA iLdar [ofX 0x8000#64] wA5 =
    some (defVals opsLdar (canonRegs opsLdar) tA, tA, .next) := by
  show csem (fun _ => False) ctx0 X0 iLdar [ofX 0x8000#64] wA5 = _
  rw [csem_of_wf (by decide) (by decide +kernel) (by decide +kernel)
    (by unfold Arm.CheckSPAlignment; decide +kernel)]
  exact straightSem_eq rfl ic5_eq (fun _ _ _ _ h => h) exec_tA (by decide +kernel)
    (by
      have h : @BEq.beq (List (BitVec 64 × BitVec 32)) _ tA.program wA5.program = true := by
        decide +kernel
      exact @eq_of_beq (List (BitVec 64 × BitVec 32)) _ _ _ _ h)

/-- **A run of the allocated code with interference**: `args` (no event), then the `ldar` reading
the environment's `5` at `0x8000`. -/
theorem run_A : ∃ c2, MTRun vcA rfA semA ckeep evA (MConf.init rfA mA wA) [[], [ev5]] c2 := by
  have hev : [ev5] = evA iLdar [ofX 0x8000#64] wA5 := evs_ext (by decide +kernel)
  have huses : itemUses opsLdar #[.reg (.x 0), .reg (.x 1)]
      (Proof.writeM (Proof.writeM mA ((((opsArgs.zip #[Loc.reg (.x 0)]).toList.filter
        (·.1.isDef)).zip [regVal wA (.x 0)]).filter (·.1.1.isEarly)))
        ((((opsArgs.zip #[Loc.reg (.x 0)]).toList.filter (·.1.isDef)).zip
          [regVal wA (.x 0)]).filter (·.1.1.isLate))) = [ofX 0x8000#64] := by
    decide +kernel
  have hfoot : IFoot semA iLdar [ofX 0x8000#64] wA5 [ev5] := by
    rw [hev]
    exact ifoot_csem X0_tls (by decide +kernel) (fun _ h => nomatch h) (fun _ _ h => nomatch h)
      (fun _ => ⟨by decide +kernel, by unfold Arm.CheckSPAlignment; decide +kernel⟩)
  have hsem := csem_ldarA
  rw [← huses] at hev hfoot hsem
  apply Exists.intro
  refine .cons (.op (vb := vbA) (i := iArgs) (ops := opsArgs) rfl rfl rfl rfl
    (ifoot_csem X0_tls (by decide +kernel) (fun _ h => nomatch h) (fun _ _ h => nomatch h)
      (fun h => absurd h (by decide)))
    (.op (outs := [regVal wA (.x 0)]) (outs' := [regVal wA (.x 0)]) rfl rfl rfl rfl rfl
      (by decide +kernel) (HavocOuts.refl _ _ _) ⟨fun _ _ => rfl, fun _ h => nomatch h⟩
      (.next (k := 0) (n := 3) (by decide))))
    (.cons (.op (vb := vbA) (i := iLdar) (ops := opsLdar) rfl rfl rfl hev hfoot
      (.op (outs := defVals opsLdar (canonRegs opsLdar) tA)
        (outs' := defVals opsLdar (canonRegs opsLdar) tA) rfl rfl rfl rfl hsem
        (by decide +kernel) (HavocOuts.refl _ _ _) ⟨fun _ _ => rfl, fun _ h => nomatch h⟩
        (.next (k := 1) (n := 3) (by decide)))) .nil)

/-- **Non-vacuity of `alloc_refines`**: the allocated code's run (the `ldar` reads the
environment's `5` at `0x8000`) is realized by a VCode thread run with the same event. -/
theorem alloc_ldar : ∃ c2 trS cS ψ, MTRun vcA rfA semA ckeep evA (MConf.init rfA mA wA) [[], [ev5]] c2 ∧
    PrepThread.VTRun vcA semA evA (VConf.init (fun _ => 0) wA) trS cS ∧
    Refines (· = ·) (fun _ => False) (StepPair (PrepThread.conv [[], [ev5]])) (PrepThread.conv trS)
      (PrepThread.conv [[], [ev5]]) ψ := by
  obtain ⟨c2, hrun⟩ := run_A
  obtain ⟨trS, cS, ψ, hrS, href, -⟩ := alloc_refines checkAlloc_A (PrepThread.cEvs_len _ _) mA
    (fun _ => 0) wA hrun
  exact ⟨c2, trS, cS, ψ, hrun, hrS, href⟩

end

end Concurrency.ThreadLayerWitness
