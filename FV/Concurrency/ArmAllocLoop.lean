import FV.Concurrency.ArmAllocMem
import FV.Concurrency.ArmLoopRun
import FV.Concurrency.ArmLoopSpec

/-!
# Layer 4b for the LL/SC loops (T2, #311)

The per-item obligation of layer 4b (`ArmAllocThread.ItemSim`, as `OpOut` per item) at the
`atomic_rmw` loop (`atomicRmwLoop`, `l: ldaxr x27, [x25]; …; stlxr w24, …, [x25]; cbnz x24, l`)
and the `atomic_cas` loop (`atomicCasLoop`, `again: ldaxr; cmp; b.ne out; stlxr; cbnz again;
out:`). On the Arm thread a `stlxr` may fail at any time and other threads may write the location
between two iterations, so the run goes round the loop any number of times:

* `LoopInv`: **the loop-head invariant** relative to the item's start `s`: the state differs from
  `s` only in the loop's scratch registers, the flags (when the loop sets them) and the bytes of
  the atomic access (reads of earlier iterations, patched into the thread's memory);
* `rmw_steps`, `rmw_retry`: the `atomic_rmw` loop is a retry loop (`ArmAllocThread.RetryLoop`) on
  the machine `R.step` with heads `LoopInv`; the measure on the Arm run is `retry_run`'s (failed
  iterations take `p + 2` steps);
* `rmw_op`: **the per-item obligation at the `atomic_rmw` loop**: the final iteration's `ldaxr`
  read and successful `stlxr` write are the CLIF atomic's one read-modify-write event (the source
  step `[e, wv]` on the world patched with the final read, `img_pair`: a monitor pair), and the
  states after the item are `Q`-related, whatever the failed iterations read.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot ArmPrecise Backend Backend.Proof AllocThread ThreadRefine
  VCodeThread Code VCodeEvents VCodeAddr ArmLoop IselMemAux

/-! ## The loop-head invariant -/

/-- **The loop-head invariant** relative to the item's start `s`: the same fields but the pc's
line (the loop label is the item's start), the scratch registers `scr` and the flags (when `FW`:
the loop sets them before reading them), the same bytes outside the atomic access of `n` bytes at
x25 (the reads of earlier iterations), the same program. -/
structure LoopInv (s y : ArmState) (scr : List Nat) (FW : Prop) (n : Nat) : Prop where
  pc : Arm.r .PC y = Arm.r .PC s
  frame : ∀ f, f ≠ .PC → (∀ q ∈ scr, f ≠ .GPR (rnum q)) → (∀ g, f ≠ .FLAG g) → Arm.r f y = Arm.r f s
  flags : FW ∨ ∀ g, Arm.r (.FLAG g) y = Arm.r (.FLAG g) s
  mem : ∀ v, writeM n (Arm.r (.GPR 25#5) s) v y.mem = writeM n (Arm.r (.GPR 25#5) s) v s.mem
  prog : y.program = s.program

theorem loopInv_refl (s : ArmState) (scr : List Nat) (FW : Prop) (n : Nat) : LoopInv s s scr FW n :=
  ⟨rfl, fun _ _ _ _ => rfl, .inr fun _ => rfl, fun _ => rfl, rfl⟩

theorem writeM_writeM (n : Nat) (a : BitVec 64) (v v' : BitVec (n * 8)) (m : Memory) (hn : n ≤ 2 ^ 64) :
    writeM n a v (writeM n a v' m) = writeM n a v m := by
  funext x
  by_cases hx : ∃ k < n, x = a + BitVec.ofNat 64 k
  · obtain ⟨k, hk, rfl⟩ := hx
    rw [writeM_apply_in _ _ _ _ _ hn hk, writeM_apply_in _ _ _ _ _ hn hk]
  · have hx' : ∀ k < n, a + BitVec.ofNat 64 k ≠ x := fun k hk e => hx ⟨k, hk, e.symm⟩
    rw [writeM_apply_out _ _ _ _ _ hx', writeM_apply_out _ _ _ _ _ hx', writeM_apply_out _ _ _ _ _ hx']

/-! ## Failed store exclusives -/

theorem r_failState (rs : BitVec 5) (s : ArmState) (f : StateField) (h1 : f ≠ .PC) (h2 : f ≠ .GPR rs) :
    Arm.r f (failState rs s) = Arm.r f s := by
  unfold failState write_gpr_zr
  split
  · simp only [write_pc, write_gpr, Arm.r_of_w_different h1, Arm.r_of_w_different h2]
  · simp only [write_pc, Arm.r_of_w_different h1]

theorem pc_failState (rs : BitVec 5) (s : ArmState) :
    Arm.r .PC (failState rs s) = Arm.r .PC s + 4#64 := by
  unfold failState write_gpr_zr
  split <;> simp [write_pc, read_pc, write_gpr, Arm.r_of_w_same]

theorem mem_failState (rs : BitVec 5) (s : ArmState) : (failState rs s).mem = s.mem := by
  unfold failState write_gpr_zr
  split <;> simp only [write_pc, write_gpr, w_mem]

theorem prog_failState (rs : BitVec 5) (s : ArmState) : (failState rs s).program = s.program := by
  unfold failState write_gpr_zr
  split <;> simp only [write_pc, write_gpr, Arm.w_program]

theorem x24_failState (s : ArmState) : Arm.r (.GPR 24#5) (failState 24#5 s) ≠ 0#64 := by
  unfold failState write_gpr_zr
  simp [write_pc, write_gpr, Arm.r_of_w_same, Arm.r_of_w_different]

theorem applyW_noW : ∀ {E : List Ev}, (∀ e ∈ E, e.k.dir ≠ .W) → ∀ m, applyW E m = m
  | [], _, _ => rfl
  | e :: E, h, m => by
    simp only [applyW, ite_eq_right_iff.mpr (fun hW => absurd hW (h e List.mem_cons_self))]
    exact applyW_noW (fun e' he' => h e' (List.mem_cons_of_mem _ he')) m

/-- A run of lines whose kinds are reads leaves the memory. -/
theorem execLines_mem_of_R {env : Env} {ls : List Line} {s s' : ArmState}
    (h : execLines env ls s = some s') (hk : ∀ k ∈ kinds ls, k.dir ≠ .W) : s'.mem = s.mem := by
  have hf := ofoot_execLines env ls s
  have e := hf.2 s.mem hf.1
  rw [setMem_self, h] at e
  simp only [Option.map_some, Option.some.injEq] at e
  have hW : ∀ ev ∈ linesEvs env ls s, ev.k.dir ≠ .W := fun ev hev =>
    hk _ ((linesEvs_kinds env ls s).subset (List.mem_map_of_mem hev))
  rw [e, setMem_mem, applyW_noW hW]

/-! ## The `atomic_rmw` loop on the machine -/

theorem rmwBody_len (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) :
    (rmwLoopBody bits op fl).length = (rmwLoopMid op bits).length + 2 := by
  simp [rmwLoopBody]

theorem rmwBody_get0 (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) :
    (rmwLoopBody bits op fl)[0]? = some (.ins (.ldaxr bits (.x 27) (.x 25)) fl.trapCode) := by
  simp [rmwLoopBody]

theorem rmwBody_getLast (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) :
    (rmwLoopBody bits op fl)[(rmwLoopMid op bits).length + 1]? =
      some (.ins (.stlxr bits (.x 24) (rmwLoopStored op) (.x 25)) fl.trapCode) := by
  simp [rmwLoopBody]

theorem rmwBody_getMid {bits : Nat} {op : AtomicRmwLoopOp} {fl : Clif.MemFlags} {i : Nat}
    (h0 : 0 < i) (h1 : i < (rmwLoopMid op bits).length + 1) {x : Insn} {tc : Option Clif.TrapCode}
    (h : (rmwLoopBody bits op fl)[i]? = some (.ins x tc)) : insnKind x = none := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  simp only [rmwLoopBody, List.cons_append, List.nil_append, List.getElem?_cons_succ] at h
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_map] at h
  cases hm : (rmwLoopMid op bits)[i]? with
  | none => rw [hm] at h; cases h
  | some y =>
    rw [hm] at h
    simp only [Option.map_some, Option.some.injEq, Line.ins.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact insnKind_rmwLoopMid op bits y (List.mem_of_getElem? hm)

theorem kinds_rmwPrefix (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) :
    kinds ((rmwLoopBody bits op fl).take ((rmwLoopMid op bits).length + 1)) = [.acqXR] := by
  have : (rmwLoopBody bits op fl).take ((rmwLoopMid op bits).length + 1) =
      .ins (.ldaxr bits (.x 27) (.x 25)) fl.trapCode :: (rmwLoopMid op bits).map (fun i => .ins i) := by
    simp [rmwLoopBody]
  rw [this]
  simp only [kinds, List.filterMap_cons, lineKind]
  have := kinds_rmwLoopMid op bits
  simp only [kinds] at this
  rw [this]
  rfl

/-- The line at `j` of a run of lines placed at `j0`. -/
theorem lines_at' {R : RL} {j : Nat} {ls T : List Line} (h : R.L.drop j = ls ++ T) :
    ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln := by
  intro k ln hk
  have := congrArg (·[k]?) h
  simp only [List.getElem?_drop] at this
  show R.L[j + k]? = some ln
  rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
  exact hk

/-- A `cbz`/`cbnz` line: no event, no store exclusive. -/
theorem cbz_noEv {R : RL} (hR : R.Wf) {j : Nat} {nz w : Bool} {r : Reg} {l : Lbl}
    (hj : R.L[j]? = some (.ins (.cbz nz w r l) none)) {u : ArmState}
    (hprog : u.program = R.fb.program R.base) (hpc : Arm.r .PC u = R.pcOf j)
    (herr : Arm.r .ERR u = .None) : stepEvs u = [] ∧ NoStx u := by
  obtain ⟨a, ha, -, hev, hdec⟩ := stepEvs_line (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj
    (by simp [Insn.hooked]) hprog hpc herr
  have hk : insnKind (.cbz nz w r l) = none := rfl
  refine ⟨by rw [hev]; exact VCodeEvents.instEvs_none ha hk _, fun rel rs rn h => ?_⟩
  rw [cls_of_decode hdec, clsOf_none ha hk] at h
  cases h

/-- Two lines defining the same label are at the same address. -/
theorem pcOf_label_eq {R : RL} (hR : R.Wf) {j j' : Nat} {l : Lbl} (hj : R.L[j]? = some (.label l))
    (hj' : R.L[j']? = some (.label l)) : R.pcOf j = R.pcOf j' := by
  have e1 := labelOffsets_label hR.lm (show R.fa.lines.toList[j]? = _ from hj)
  have e2 := labelOffsets_label hR.lm (show R.fa.lines.toList[j']? = _ from hj')
  rw [e1, Option.some.injEq] at e2
  simp only [RL.pcOf, RL.L]; rw [e2]

set_option maxHeartbeats 1000000 in
/-- **The `atomic_rmw` loop's body on the machine**, from a state at its first line (`j0 + 1`): the
`ldaxr` reads the bytes at x25; the steps up to the `stlxr` (at `z`) have no event and no store
exclusive and keep the memory; the `stlxr` writes `rmwNew` at x25 (when it succeeds: then the body
has run, `t'`, and the `cbnz` falls through) and has status register w24; when it fails, the `cbnz`
goes back to the loop label. -/
theorem rmw_steps {R : RL} (hR : R.Wf) {ty : CTy} (hty : AtomTy ty) {op : AtomicRmwLoopOp}
    {fl : Clif.MemFlags} {j0 n : Nat} {T : List Line}
    (hd1 : R.L.drop (j0 + 1) =
      rmwLoopBody ty.bits op fl ++ (.ins (.cbz true true (.x 24) (.loop n)) none :: T))
    (hL0 : R.L[j0]? = some (.label (.loop n)))
    {t : ArmState} (hprog : t.program = R.fb.program R.base) (hpc : Arm.r .PC t = R.pcOf (j0 + 1))
    (herr : Arm.r .ERR t = .None) :
    ∃ t', execLines (R.envOf (j0 + 1)) (rmwLoopBody ty.bits op fl) t = some t' ∧
      R.step (iterN R.step ((rmwLoopMid op ty.bits).length + 1) t) = t' ∧
      (stepEvs t = [⟨.acqXR, Arm.r (.GPR 25#5) t, ty.bytes,
        readM ty.bytes (Arm.r (.GPR 25#5) t) t.mem⟩] ∧ NoStx t) ∧
      (∀ i, 0 < i → i < (rmwLoopMid op ty.bits).length + 1 →
        stepEvs (iterN R.step i t) = [] ∧ NoStx (iterN R.step i t)) ∧
      stepEvs (iterN R.step ((rmwLoopMid op ty.bits).length + 1) t) =
        [⟨.relXW, Arm.r (.GPR 25#5) t, ty.bytes, rmwNew ty op t⟩] ∧
      cls (iterN R.step ((rmwLoopMid op ty.bits).length + 1) t) = .stx true 24#5 25#5 ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 24#5 →
        Arm.r f t' = Arm.r f (iterN R.step ((rmwLoopMid op ty.bits).length + 1) t)) ∧
      Arm.r .ERR (iterN R.step ((rmwLoopMid op ty.bits).length + 1) t) = .None ∧
      (iterN R.step ((rmwLoopMid op ty.bits).length + 1) t).program = t.program ∧
      Arm.r .PC (iterN R.step ((rmwLoopMid op ty.bits).length + 1) t) =
        R.pcOf (j0 + 1 + ((rmwLoopMid op ty.bits).length + 1)) ∧
      (iterN R.step ((rmwLoopMid op ty.bits).length + 1) t).mem = t.mem ∧
      stepEvs t' = [] ∧ NoStx t' ∧
      R.step t' = Arm.w .PC (R.pcOf (j0 + 1 + ((rmwLoopMid op ty.bits).length + 2) + 1)) t' ∧
      stepEvs (failState 24#5 (iterN R.step ((rmwLoopMid op ty.bits).length + 1) t)) = [] ∧
      NoStx (failState 24#5 (iterN R.step ((rmwLoopMid op ty.bits).length + 1) t)) ∧
      R.step (failState 24#5 (iterN R.step ((rmwLoopMid op ty.bits).length + 1) t)) =
        Arm.w .PC (R.pcOf j0) (failState 24#5 (iterN R.step ((rmwLoopMid op ty.bits).length + 1) t)) := by
  have hlen := rmwBody_len ty.bits op fl
  generalize hM : (rmwLoopMid op ty.bits).length = M at hlen ⊢
  generalize hz : iterN R.step (M + 1) t = z
  obtain ⟨t', hrun, hint, -, h24, -, -, hprog'⟩ := rmwBody_spec hty op fl (R.envOf (j0 + 1)) t herr
  have hat := lines_at' hd1
  have hins := rmwBody_ins hty op fl
  have hhook : ∀ i tc, Line.ins i tc ∈ rmwLoopBody ty.bits op fl → i.hooked = false := fun i tc h => by
    obtain ⟨i', t', e, hh⟩ := hins _ h; cases e; exact hh
  have hst : ∀ i < (rmwLoopBody ty.bits op fl).length, ∃ x tc a,
      (rmwLoopBody ty.bits op fl)[i]? = some (.ins x tc) ∧ x.toArmInst (R.envOf (j0 + 1 + i)) = .ok a ∧
      decodeAt (iterN R.step i t) = some a ∧ stepEvs (iterN R.step i t) = instEvs a (iterN R.step i t) ∧
      iterN R.step (i + 1) t = exec_inst a (iterN R.step i t) :=
    step_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hat hhook hprog hpc herr hint hrun
  obtain ⟨hit, hpcs, -, -⟩ := run_ins hR hd1 hins hprog hpc herr hint hrun
  rw [hlen] at hit hpcs
  have hrs : rmwLoopStored op = .x 26 ∨ rmwLoopStored op = .x 28 := by
    cases op <;> simp [rmwLoopStored]
  -- step 0: the `ldaxr`
  obtain ⟨x0, tc0, a0, hl0, ha0, hdec0, hev0, -⟩ := hst 0 (by omega)
  rw [rmwBody_get0] at hl0
  simp only [Option.some.injEq, Line.ins.injEq] at hl0
  obtain ⟨rfl, rfl⟩ := hl0
  have hread : stepEvs t = [⟨.acqXR, Arm.r (.GPR 25#5) t, ty.bytes,
      readM ty.bytes (Arm.r (.GPR 25#5) t) t.mem⟩] ∧ NoStx t := by
    refine ⟨hev0.trans (ldaxr_one hty ha0 t), fun rel rs rn h => ?_⟩
    obtain ⟨sz, hsz⟩ := ldaxr_cls hty ha0
    rw [cls_of_decode (s := t) hdec0, hsz] at h
    cases h
  -- the middle
  have hmid : ∀ i, 0 < i → i < M + 1 → stepEvs (iterN R.step i t) = [] ∧ NoStx (iterN R.step i t) := by
    intro i h0 h1
    obtain ⟨x, tc, a, hl, ha, hdec, hev, -⟩ := hst i (by omega)
    have hk := rmwBody_getMid h0 (by rw [hM]; exact h1) hl
    refine ⟨by rw [hev]; exact VCodeEvents.instEvs_none ha hk _, fun rel rs rn h => ?_⟩
    rw [cls_of_decode hdec, clsOf_none ha hk] at h
    cases h
  -- the `stlxr`
  obtain ⟨xs, tcs, as, hls, has, hdecs, hevs, hnexts⟩ := hst (M + 1) (by omega)
  rw [← hM, rmwBody_getLast] at hls
  simp only [Option.some.injEq, Line.ins.injEq] at hls
  obtain ⟨rfl, rfl⟩ := hls
  rw [hz] at hdecs hevs hnexts
  have hexz : R.step z = Arm.exec_inst as z := by rw [← hnexts, iterN_succ', hz]
  have hstep : R.step z = t' := by
    rw [← hit, show M + 2 = (M + 1) + 1 from rfl, iterN_succ', hz]
  -- the state before the `stlxr`
  obtain ⟨z1, hz1⟩ := execLines_take hrun (M + 1)
  have hz1' : iterN R.step (M + 1) t = z1 := by
    have : iterN R.step ((rmwLoopBody ty.bits op fl).take (M + 1)).length t = z1 := iterN_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit
      ((rmwLoopBody ty.bits op fl).take (M + 1)) (j0 + 1) t z1
      (fun k ln hk => hat k ln (by
        rw [List.getElem?_take] at hk; split at hk
        · exact hk
        · cases hk))
      (fun i' t' hm' => hhook i' t' (List.mem_of_mem_take hm')) hprog hpc herr (interOk_take hint _) hz1
    rwa [List.length_take, Nat.min_eq_left (by omega)] at this
  rw [hz] at hz1'
  subst hz1'
  obtain ⟨herrz, hprogz⟩ := hint (M + 1) (by omega) (by omega) z hz1
  have hmemz : z.mem = t.mem := execLines_mem_of_R hz1 (by
    rw [← hM, kinds_rmwPrefix]; intro k hk; simp at hk; subst hk; decide)
  have hpcz : Arm.r .PC z = R.pcOf (j0 + 1 + (M + 1)) := by
    have : Arm.r .PC (iterN R.step (M + 1) t) = R.pcOf (j0 + 1 + (M + 1)) :=
      iterN_execLines_pc (X := R.X) (H := R.H) hR.layout hR.lm hR.fit _ (j0 + 1) t t' hat hhook
        hprog hpc herr hint hrun (M + 1) (by omega)
    rw [hz] at this; exact this
  -- the `stlxr`'s event
  have hwev : stepEvs z = [⟨.relXW, Arm.r (.GPR 25#5) t, ty.bytes, rmwNew ty op t⟩] := by
    have hseg : (segEvs R.step (rmwLoopBody ty.bits op fl).length t).flatten =
        linesEvs (R.envOf (j0 + 1)) (rmwLoopBody ty.bits op fl) t :=
      segEvs_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit _ (j0 + 1) t t' hat
        hhook hprog hpc herr hint hrun
    rw [hlen, show M + 2 = (M + 1) + 1 from rfl, segEvs_add, segEvs_one, hz,
      rmwBody_evsEq hty op fl _ t herr] at hseg
    have hpre : (segEvs R.step (M + 1) t).flatten = [⟨.acqXR, Arm.r (.GPR 25#5) t, ty.bytes,
        readM ty.bytes (Arm.r (.GPR 25#5) t) t.mem⟩] := by
      simp only [segEvs, List.flatten_cons]
      rw [← hread.1]
      have : (segEvs R.step M (R.step t)).flatten = [] := by
        refine List.flatten_eq_nil_iff.mpr fun x hx => ?_
        obtain ⟨i, hi, rfl⟩ := mem_segEvs hx
        exact (hmid (i + 1) (by omega) (by omega)).1
      rw [this, List.append_nil]
    rw [List.flatten_append, hpre] at hseg
    simpa using hseg
  -- the `cbnz` after the body
  have hLc : R.L[j0 + 1 + (M + 2)]? = some (.ins (.cbz true true (.x 24) (.loop n)) none) := by
    have := congrArg (·[M + 2]?) hd1
    simp only [List.getElem?_drop] at this
    rw [this, List.getElem?_append_right (by omega), hlen]; simp
  have herr' : Arm.r .ERR t' = .None := by
    rw [← hstep, hexz]
    rw [stlxr_frame hty hrs has z herrz .ERR (by simp) (by simp)]; exact herrz
  have hprogt' : t'.program = R.fb.program R.base := by rw [hprog', hprog]
  obtain ⟨hevc, hnsc⟩ := cbz_noEv hR hLc hprogt' hpcs herr'
  obtain ⟨ac, jl, hac, hjl, hstepc⟩ := step_branch hR hLc (.inr (.inr (.inl ⟨true, true, .x 24, rfl⟩)))
    (by simp) hprogt' hpcs herr'
  have hbr : brCond ac t' = false := by
    rw [brCond_cbz (by decide) hac]; simp [rnum, h24]
  rw [hbr] at hstepc
  simp only [Bool.false_eq_true, ite_false] at hstepc
  -- the failed `stlxr`, then the `cbnz` back
  have hLs : R.L[j0 + 1 + (M + 1)]? = some (.ins (.stlxr ty.bits (.x 24) (rmwLoopStored op) (.x 25))
      fl.trapCode) := by
    have := hat (M + 1) _ (by rw [← hM, rmwBody_getLast])
    exact this
  have hpcf : Arm.r .PC (failState 24#5 z) = R.pcOf (j0 + 1 + (M + 2)) := by
    rw [pc_failState, hpcz, show j0 + 1 + (M + 2) = (j0 + 1 + (M + 1)) + 1 by omega,
      RL.pcOf_succ_ins hLs]
  have herrf : Arm.r .ERR (failState 24#5 z) = .None := by
    rw [r_failState _ _ _ (by simp) (by simp)]; exact herrz
  have hprogf : (failState 24#5 z).program = R.fb.program R.base := by
    rw [prog_failState, hprogz, hprog]
  obtain ⟨hevf, hnsf⟩ := cbz_noEv hR hLc hprogf hpcf herrf
  obtain ⟨af, jf, haf, hjf, hstepf⟩ := step_branch hR hLc (.inr (.inr (.inl ⟨true, true, .x 24, rfl⟩)))
    (by simp) hprogf hpcf herrf
  have hbrf : brCond af (failState 24#5 z) = true := by
    rw [brCond_cbz (by decide) haf]
    have := x24_failState z
    simp [rnum, this]
  simp only [hbrf, ite_true] at hstepf
  rw [pcOf_label_eq hR hjf hL0] at hstepf
  refine ⟨t', hrun, hstep, hread, hmid, hwev, ?_, fun f h1 h2 => ?_, herrz, hprogz, hpcz, hmemz, hevc,
    hnsc, hstepc, hevf, hnsf, hstepf⟩
  · rw [cls_of_decode hdecs, stlxr_cls hty hrs has]
  · rw [← hstep, hexz]
    exact stlxr_frame hty hrs has z herrz f h1 h2

/-! ## The `atomic_rmw` loop is a retry loop -/

theorem atomTy_bytes {ty : CTy} (hty : AtomTy ty) : ty.bytes ≤ 2 ^ 64 := by
  rcases hty with rfl | rfl | rfl | rfl <;> decide

/-- The read of an LL/SC loop's `ldaxr` at a head `y` of the loop started at `s`. -/
def loopRd (ty : CTy) (s y : ArmState) : Ev :=
  ⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, readM ty.bytes (Arm.r (.GPR 25#5) s) y.mem⟩

/-- The heads of the `atomic_rmw` loop started at `s`: scratch x24, x27, x28; the flags when the
operation compares. -/
abbrev RmwHd (ty : CTy) (op : AtomicRmwLoopOp) (s y : ArmState) : Prop :=
  LoopInv s y [24, 27, 28] (FlagOp op = true) ty.bytes

theorem LoopInv.r25 {s y : ArmState} {scr : List Nat} {FW : Prop} {n : Nat} (h : LoopInv s y scr FW n)
    (hs : ∀ q ∈ scr, q < 32 ∧ q ≠ 25) : Arm.r (.GPR 25#5) y = Arm.r (.GPR 25#5) s :=
  h.frame (.GPR 25#5) (by simp) (fun q hq e => by
    have e' : rnum 25 = rnum q := by injection e
    exact rnum_ne (by decide) (hs q hq).1 (hs q hq).2.symm e') (by simp)

theorem LoopInv.err {s y : ArmState} {scr : List Nat} {FW : Prop} {n : Nat} (h : LoopInv s y scr FW n) :
    Arm.r .ERR y = Arm.r .ERR s := h.frame _ (by simp) (by simp) (by simp)

/-- The memory of a patched head: the read's bytes at the access, the start's elsewhere. -/
theorem LoopInv.patch_mem {s y : ArmState} {scr : List Nat} {FW : Prop} {n : Nat}
    (h : LoopInv s y scr FW n) (v : BitVec (n * 8)) :
    (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, n, v⟩] y).mem = writeM n (Arm.r (.GPR 25#5) s) v s.mem := by
  simp only [patch, setMem_mem, applyR, show AKind.acqXR.dir = .R from rfl, ite_true]
  exact h.mem v

theorem frame_list {f : StateField} (h : ∀ q ∈ [24, 27, 28], f ≠ .GPR (rnum q)) :
    ∀ r ∈ [24#5, 27#5, 28#5], f ≠ .GPR r := by
  simpa [rnum] using h

/-- **The `atomic_rmw` loop is a retry loop** (`RetryLoop`) on the machine, with heads `RmwHd`:
`p` is the number of lines before the `stlxr`, the status register w24, no exit before it. -/
theorem rmw_retry {R : RL} (hR : R.Wf) {ty : CTy} (hty : AtomTy ty) {op : AtomicRmwLoopOp}
    {fl : Clif.MemFlags} {j0 n : Nat} {T : List Line}
    (hd1 : R.L.drop (j0 + 1) =
      rmwLoopBody ty.bits op fl ++ (.ins (.cbz true true (.x 24) (.loop n)) none :: T))
    (hL0 : R.L[j0]? = some (.label (.loop n)))
    {s : ArmState} (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) :
    RetryLoop R.step (RmwHd ty op s) (loopRd ty s) ((rmwLoopMid op ty.bits).length + 1) 24#5
      (fun _ => False) := by
  have hy0 : ∀ y, RmwHd ty op s y → ∀ E : List Ev,
      (patch E y).program = R.fb.program R.base ∧ Arm.r .PC (patch E y) = R.pcOf (j0 + 1) ∧
        Arm.r .ERR (patch E y) = .None := by
    intro y hy E
    refine ⟨by rw [patch, setMem_program, hy.prog, hprog], ?_, ?_⟩
    · rw [patch, r_setMem, hy.pc, hpc, RL.pcOf_succ_label hL0]
    · rw [patch, r_setMem, hy.err, herr]
  refine ⟨by omega, fun y hy => ?_, fun y hy e he i h0 hi => ?_, fun y hy e he => .inr ⟨id, ?_⟩⟩
  · obtain ⟨hp1, hp2, hp3⟩ := hy0 y hy []
    obtain ⟨t', -, -, ⟨hev, hns⟩, -⟩ := rmw_steps hR hty hd1 hL0 hp1 hp2 hp3
    rw [patch_nil, hy.r25 (by decide)] at hev
    rw [patch_nil] at hns
    exact ⟨rfl, atomTy_bytes hty, hev, hns⟩
  · obtain ⟨hp1, hp2, hp3⟩ := hy0 y hy [e]
    obtain ⟨t', -, -, -, hmid, -⟩ := rmw_steps hR hty hd1 hL0 hp1 hp2 hp3
    exact hmid i h0 hi
  obtain ⟨k, a, n', v⟩ := e
  obtain ⟨h1, h2, h3⟩ := he
  simp only [loopRd] at h1 h2 h3
  subst h1 h2 h3
  obtain ⟨hp1, hp2, hp3⟩ := hy0 y hy [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩]
  obtain ⟨t', hrun, hstep, -, -, hwev, hcls, hfr, herrz, hprogz, -, hmemz, hevc, hnsc, -, hevf, hnsf,
    hstepf⟩ := rmw_steps hR hty hd1 hL0 hp1 hp2 hp3
  obtain ⟨t'', hrun', -, -, -, hlf, -, -⟩ := rmwBody_spec hty op fl (R.envOf (j0 + 1)) _ hp3
  rw [hrun] at hrun'
  cases hrun'
  generalize hz : iterN R.step ((rmwLoopMid op ty.bits).length + 1)
    (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y) = z at *
  refine ⟨⟨true, 25#5, hcls⟩, ⟨_, rfl, hwev⟩, ⟨by rw [hstep]; exact hevc, by rw [hstep]; exact hnsc⟩,
    ⟨hevf, hnsf⟩, ?_⟩
  rw [hstepf]
  have hfz : ∀ f, f ≠ .PC → f ≠ .GPR 24#5 → Arm.r f (Arm.w .PC (R.pcOf j0) (failState 24#5 z)) =
      Arm.r f t' := fun f h1 h2 => by
    rw [Arm.r_of_w_different h1, r_failState _ _ _ h1 h2, hfr f h1 h2]
  refine ⟨by rw [Arm.r_of_w_same, hpc], fun f h1 h2 h3 => ?_, ?_, fun v' => ?_, ?_⟩
  · rw [hfz f h1 (h2 24 (by simp)), hlf f h1 (frame_list h2) h3, patch, r_setMem]
    exact hy.frame f h1 h2 h3
  · by_cases hop : FlagOp op = true
    · exact .inl hop
    · refine .inr fun g => ?_
      rw [hfz _ (by simp) (by simp), rmwBody_keepFlags hty (by simpa using hop) fl _ hrun, patch, r_setMem]
      rcases hy.flags with h | h
      · exact absurd h hop
      · exact h g
  · rw [ArmState.mem_w_eq_mem, mem_failState, hmemz, hy.patch_mem,
      writeM_writeM _ _ _ _ _ (atomTy_bytes hty)]
  · rw [Arm.w_program, prog_failState, hprogz, patch, setMem_program, hy.prog]

/-! ## The per-item obligation at the `atomic_rmw` loop -/

/-- The conclusion of `ItemSim` at one configuration, for precise runs whose steps satisfy `ok`
(`OpOut` is the case `ok = True`). -/
abbrev OpOutG (R : RL) (ok : ArmState → Lab → Prop) (t : ArmState × Mon) (c : MConf CV ArmState)
    (ls : List Lab) : Prop :=
  Done R c ∨
    ItemSimOut Policy.arm R.step ok (SrcStep R) (RelQ R) (PrivA R) (fun c => c.measure) t c ls ∨
    (∃ evs c' φ, SrcStep R c evs c' ∧ Img (PrivA R) evs (evTr ls) φ) ∨ PrivW (PrivA R) (evTr ls)

theorem privA_of_avoid {R : RL} {n : Nat} {a : BitVec 64} (h : Avoids R.F n a) (hn : 0 < n) :
    ¬ PrivA R a.toNat := by
  have := h 0 hn
  simpa [PrivA] using this

set_option maxHeartbeats 4000000 in
/-- **The per-item obligation at the `atomic_rmw` loop** (module doc): every precise Arm run from
`Q`-related states goes through failed iterations (reading any bytes, writing nothing) and ends
before a successful `stlxr` (private writes only: none), or its final iteration's `ldaxr` read `e`
and successful `stlxr` write `wv` are the events of the allocated code's step `[e, wv]` (on the
world patched with `e`; a monitor pair), the states after the `cbnz` related. -/
theorem rmw_op {R : RL} (hR : R.Wf) {ok : ArmState → Lab → Prop} {s : ArmState} {mon : Mon}
    {b k : Nat} {allocs : Array Loc} {its' : List RItem} {m : Loc → CV} {w : ArmState}
    {evs0 : List Ev} {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its' m w)) (hA : AInv R (OpC b k allocs its' m w))
    (hs0 : SrcStep R (OpC b k allocs its' m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i →
      ∃ ty op fl ra ro rd r1 r2, i = .atomicRmwLoop ty op fl ra ro rd r1 r2)
    {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm R.step ok (s, mon) ls t') :
    OpOutG R ok (s, mon) (OpC b k allocs its' m w) ls := by
  cases hs0 with
  | @op _ _ _ _ _ _ vb i ops _ _ hvb hi hops0 hevs0 hfoot0 hst0 =>
  obtain ⟨ty, op, fl, ra, ro, rd, r1, r2, rfl⟩ := hform vb i hvb hi
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hok := ctlCheck_inst hck hvb hi
  simp only [ctlInstOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  obtain ⟨va, rfl⟩ := isVregInt_iff h0
  obtain ⟨vo, rfl⟩ := isVregInt_iff h1
  obtain ⟨vd, rfl⟩ := isVregInt_iff h2
  obtain ⟨v1, rfl⟩ := isVregInt_iff h3
  obtain ⟨v2, rfl⟩ := isVregInt_iff h4
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, hl1, hl2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  rw [hops] at hops0
  cases hops0
  have hops' : ops = #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨vo, .int, .use, .early, .fixed (.x 26)⟩,
      ⟨vd, .int, .def, .late, .fixed (.x 27)⟩, ⟨v1, .int, .def, .late, .fixed (.x 24)⟩,
      ⟨v2, .int, .def, .late, .fixed (.x 28)⟩] := by
    have e : (MInst.atomicRmwLoop ty op fl (.vreg va .int) (.vreg vo .int) (.vreg vd .int)
        (.vreg v1 .int) (.vreg v2 .int)).operands =
        .ok #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨vo, .int, .use, .early, .fixed (.x 26)⟩,
          ⟨vd, .int, .def, .late, .fixed (.x 27)⟩, ⟨v1, .int, .def, .late, .fixed (.x 24)⟩,
          ⟨v2, .int, .def, .late, .fixed (.x 28)⟩] := rfl
    rw [e] at hops; injection hops with h; exact h.symm
  subst hops'
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hstat
  obtain ⟨q0, q1, q2, q3, q4, rfl⟩ := regs5 (by simpa using hsz.symm)
  obtain rfl : q0 = .x 25 := fixed_reg (o := ⟨va, .int, .use, .early, .fixed (.x 25)⟩) hloc (by simp) rfl
  obtain rfl : q1 = .x 26 := fixed_reg (o := ⟨vo, .int, .use, .early, .fixed (.x 26)⟩) hloc (by simp) rfl
  obtain rfl : q2 = .x 27 := fixed_reg (o := ⟨vd, .int, .def, .late, .fixed (.x 27)⟩) hloc (by simp) rfl
  obtain rfl : q3 = .x 24 := fixed_reg (o := ⟨v1, .int, .def, .late, .fixed (.x 24)⟩) hloc (by simp) rfl
  obtain rfl : q4 = .x 28 := fixed_reg (o := ⟨v2, .int, .def, .late, .fixed (.x 28)⟩) hloc (by simp) rfl
  have hasg' : (MInst.atomicRmwLoop ty op fl (.vreg va .int) (.vreg vo .int) (.vreg vd .int)
      (.vreg v1 .int) (.vreg v2 .int)).assign #[.x 25, .x 26, .x 27, .x 24, .x 28] =
      .ok (.atomicRmwLoop ty op fl (.x 25) (.x 26) (.x 27) (.x 24) (.x 28)) := rfl
  rw [hasg'] at hasg; cases hasg
  obtain rfl : c1 = [.inst (.atomicRmwLoop ty op fl (.x 25) (.x 26) (.x 27) (.x 24) (.x 28))] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1' := codeLinesE_single hl1
  simp only [MInst.lines, bne_self_eq_false, Bool.or_false, Bool.and_false, Bool.false_eq_true,
    ite_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1'
  obtain ⟨rfl, rfl⟩ := hl1'
  -- the given step of the allocated code: the access's facts
  have hreg : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
    hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
  have hU : (((#[(⟨va, .int, .use, .early, .fixed (.x 25)⟩ : Operand),
      ⟨vo, .int, .use, .early, .fixed (.x 26)⟩, ⟨vd, .int, .def, .late, .fixed (.x 27)⟩,
      ⟨v1, .int, .def, .late, .fixed (.x 24)⟩, ⟨v2, .int, .def, .late, .fixed (.x 28)⟩].zip
      (#[Reg.x 25, .x 26, .x 27, .x 24, .x 28].map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2)) =
      [regVal s (.x 25), regVal s (.x 26)] := by
    simp [Operand.isUse, hreg (.x 25) rfl, hreg (.x 26) rfl]
  have herrw : Arm.r .ERR w = .None := by
    rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
  have hnc : ∀ info, MInst.atomicRmwLoop ty op fl (.vreg va .int) (.vreg vo .int) (.vreg vd .int)
      (.vreg v1 .int) (.vreg v2 .int) ≠ .call info := fun _ h => by cases h
  have hnt : ∀ info ti, MInst.atomicRmwLoop ty op fl (.vreg va .int) (.vreg vo .int) (.vreg vd .int)
      (.vreg v1 .int) (.vreg v2 .int) ≠ .tryCall info ti := fun _ _ h => by cases h
  obtain ⟨hty, hav, hk⟩ : AtomTy ty ∧ Avoids R.F ty.bytes (Arm.r (.GPR 25#5) s) ∧ k + 1 < vb.insts.size := by
    cases hst0 with
    | @op _ _ _ _ _ _ vb1 i1 ops1 outs outs' w' ctl m2 c' hvb1 hi1 hops1 hsz1 hsem hlen hho hcl hn =>
    rw [hvb] at hvb1; cases hvb1; rw [hi] at hi1; cases hi1; rw [hops] at hops1; cases hops1
    rw [hU, R.sem_eq hnc hnt] at hsem
    have herrp : Arm.r .ERR (patch evs0 w) = .None := by rw [patch, r_setMem]; exact herrw
    simp only [csem, herrp, ite_true] at hsem
    obtain ⟨hty, hav, -, -, rfl⟩ := loopSem_inv hsem
    refine ⟨hty, by rwa [lo64_regVal_x] at hav, ?_⟩
    cases hn with
    | next hk => exact hk
  have hn0 : 0 < ty.bytes := by rcases hty with rfl | rfl | rfl | rfl <;> decide
  have hbytes := atomTy_bytes hty
  -- the lines
  have hdrop' := ftList_rmw hR hty ⟨_, rfl⟩ hdrop
  have hL0 : R.L[j0]? = some (.label (.loop ps1.aloop)) := by
    have := congrArg (·[0]?) hdrop'
    simpa [List.getElem?_drop, rmwLoopLines] using this
  have hd1 : R.L.drop (j0 + 1) = rmwLoopBody ty.bits op fl ++
      (.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none ::
        (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T)) := by
    rw [← List.drop_drop, hdrop']; simp [rmwLoopLines]
  -- the run
  have hloop := rmw_retry hR hty hd1 hL0 hst.prog hpc hst.err
  rcases retry_run (P := Policy.arm) (ok := ok) hloop ls.length ls s mon t' (Nat.le_refl _)
      (loopInv_refl s _ _ _) hr with hnw | ⟨q, y1, e, hF, hX⟩
  · exact .inr (.inr (.inr (privW_of_noW hnw)))
  rcases hX with hfalse | ⟨-, -, hle1, wv, hW, hwv, hseg1, hseg2⟩
  · exact hfalse.elim
  -- the final iteration: its read `e`, its write `wv`
  obtain ⟨k0, a0, n0, v⟩ := e
  obtain ⟨hk1, ha1, hn1⟩ := hF.acc
  simp only [loopRd] at hk1 ha1 hn1
  subst hk1 ha1 hn1
  have hy1 := hF.hd
  have hp1 : (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1).program = R.fb.program R.base := by
    rw [patch, setMem_program, hy1.prog, hst.prog]
  have hp2 : Arm.r .PC (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1) = R.pcOf (j0 + 1) := by
    rw [patch, r_setMem, hy1.pc, hpc, RL.pcOf_succ_label hL0]
  have hp3 : Arm.r .ERR (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1) = .None := by
    rw [patch, r_setMem, hy1.err, hst.err]
  obtain ⟨t'', hrun, hstep, -, -, hwev', -, -, -, -, -, -, -, -, hstepc, -⟩ :=
    rmw_steps hR hty hd1 hL0 hp1 hp2 hp3
  have h25y : Arm.r (.GPR 25#5) (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1) =
      Arm.r (.GPR 25#5) s := by rw [patch, r_setMem, hy1.r25 (by decide)]
  rw [hwev', h25y] at hwv
  simp only [List.cons.injEq, and_true] at hwv
  subst hwv
  -- the allocated code's step on the world patched with the final read
  have hpw : applyR [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩,
      ⟨.relXW, Arm.r (.GPR 25#5) s, ty.bytes, rmwNew ty op
        (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1)⟩] w.mem =
      writeM ty.bytes (Arm.r (.GPR 25#5) s) v w.mem := by
    simp [applyR, AKind.dir]
  generalize hW0 : patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩,
      ⟨.relXW, Arm.r (.GPR 25#5) s, ty.bytes, rmwNew ty op
        (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1)⟩] w = W
  have hWmem : W.mem = writeM ty.bytes (Arm.r (.GPR 25#5) s) v w.mem := by
    rw [← hW0, patch, setMem_mem, hpw]
  have hWerr : Arm.r .ERR W = .None := by rw [← hW0, patch, r_setMem, herrw]
  generalize hWt : ([Reg.x 25, .x 26].zip [regVal s (.x 25), regVal s (.x 26)]).foldl
    (fun s p => setReg s p.1 p.2) W = Wt
  have hWt25 : Arm.r (.GPR 25#5) Wt = Arm.r (.GPR 25#5) s := by
    rw [← hWt, r25_two, lo64_regVal_x]; rfl
  have hWt26 : Arm.r (.GPR 26#5) Wt = Arm.r (.GPR 26#5) s := by
    rw [← hWt]; simp [setReg, rnum, Arm.r_of_w_same, lo64_regVal_x]
  have hWtoth : ∀ f, f ≠ .GPR 25#5 → f ≠ .GPR 26#5 → Arm.r f Wt = Arm.r f W := by
    intro f h1 h2; rw [← hWt]; simp [setReg, rnum, Arm.r_of_w_different h1, Arm.r_of_w_different h2]
  have hWtmem : Wt.mem = W.mem := by rw [← hWt, foldl_setReg_mem]
  have hWtprog : Wt.program = W.program := by rw [← hWt]; simp [setReg, Arm.w_program]
  have hWterr : Arm.r .ERR Wt = .None := by rw [hWtoth _ (by simp) (by simp), hWerr]
  obtain ⟨w'', hrunw, -, -, -, hfrw, hmemw, hprogw⟩ := rmwBody_spec hty op fl env0 Wt hWterr
  have hrd : readM ty.bytes (Arm.r (.GPR 25#5) s) Wt.mem = v := by
    rw [hWtmem, hWmem, readM_writeM _ _ _ _ hbytes]
  have hrdy : readM ty.bytes (Arm.r (.GPR 25#5) s)
      (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1).mem = v := by
    rw [hy1.patch_mem, readM_writeM _ _ _ _ hbytes]
  have h26y : Arm.r (.GPR 26#5) (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1) =
      Arm.r (.GPR 26#5) s := by
    rw [patch, r_setMem]
    exact hy1.frame _ (by simp) (fun q hq e => by
      have e' : rnum 26 = rnum q := by injection e
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> exact absurd e' (by decide)) (by simp)
  have hnew : rmwNew ty op Wt = rmwNew ty op (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1) := by
    unfold rmwNew
    rw [hWt25, hWt26, h25y, h26y, read_mem_bytes_eq, read_mem_bytes_eq, hrd, hrdy]
  have hav' : Avoids R.F ty.bytes (lo64 (regVal s (.x 25))) := by rw [lo64_regVal_x]; exact hav
  have hw''err : Arm.r .ERR w'' = .None := by
    rw [hfrw .ERR (by simp) (by simp) (by simp)]; exact hWterr
  have hsemW : R.sem (.atomicRmwLoop ty op fl (.vreg va .int) (.vreg vo .int) (.vreg vd .int)
      (.vreg v1 .int) (.vreg v2 .int)) [regVal s (.x 25), regVal s (.x 26)] W =
      some ([regVal w'' (.x 27), ofX 0, ofX 0], w'', .next) := by
    rw [R.sem_eq hnc hnt]
    simp only [csem, hWerr, ite_true]
    unfold loopSem
    rw [hWt, ite_eq_left ⟨hty, hav', hWerr⟩, hrunw]
    simp [hw''err, hprogw, hWtprog]
  have hevL : loopEvs (rmwLoopBody ty.bits op fl) [.x 25, .x 26] [regVal s (.x 25), regVal s (.x 26)] W =
      [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩, ⟨.relXW, Arm.r (.GPR 25#5) s, ty.bytes,
        rmwNew ty op (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1)⟩] := by
    unfold loopEvs
    rw [hWt, rmwBody_evsEq hty op fl env0 Wt hWterr, hWt25, hrd, hnew]
  -- the machine after the loop, against the allocated code's world after the step
  obtain ⟨t3, hrun3, -, -, -, hlf, hmemt, hprogt⟩ := rmwBody_spec hty op fl (R.envOf (j0 + 1)) _ hp3
  rw [hrun] at hrun3
  cases hrun3
  have hflW : ∀ g, Arm.r (.FLAG g) W = Arm.r (.FLAG g) s := fun g => by
    rw [← hW0, patch, r_setMem]; exact (hst.world.1 _ (by simp [Masked])).symm
  obtain ⟨hdepF, hdep27⟩ := rmwBody_dep hty op fl (R.envOf (j0 + 1)) env0
    (t1 := patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1) (t2 := Wt)
    (by rw [h25y, hWt25]) (by rw [h26y, hWt26])
    (by rw [hWt25, read_mem_bytes_eq, read_mem_bytes_eq, hrd, hrdy])
    (fun hop g => by
      rw [hWtoth _ (by simp) (by simp), hflW, patch, r_setMem]
      rcases hy1.flags with h | h
      · rw [hop] at h; cases h
      · exact h g) hrun hrunw
  generalize hxF : Arm.w .PC (R.pcOf (j0 + 1 + ((rmwLoopMid op ty.bits).length + 2) + 1)) t'' = xF
    at hstepc
  have hfr2 : ∀ f, f ≠ .PC → (∀ n ∈ [27, 24, 28], f ≠ .GPR (rnum n)) → (∀ g, f ≠ .FLAG g) →
      Arm.r f xF = Arm.r f s := by
    intro f h1 h2 h3
    have h2' : ∀ q ∈ [24, 27, 28], f ≠ .GPR (rnum q) := by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> exact h2 _ (by simp)
    rw [← hxF, Arm.r_of_w_different h1, hlf f h1 (frame_list h2') h3, patch, r_setMem]
    exact hy1.frame f h1 h2' h3
  have hnm : ∀ f, ¬ Masked f → f ≠ .PC ∧ ∀ n ∈ [27, 24, 28], f ≠ .GPR (rnum n) := by
    intro f hf
    refine ⟨fun h => hf (by subst h; simp [Masked]), fun n hn h => hf ?_⟩
    subst h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl <;> simp [Masked, rnum]
  have hsw : SameWorld R.F xF w'' := by
    refine ⟨fun f hf => ?_, fun a ha => ?_, ?_⟩
    · by_cases hfl : ∃ g, f = .FLAG g
      · obtain ⟨g, rfl⟩ := hfl
        rw [← hxF, Arm.r_of_w_different (by simp)]; exact hdepF g
      · have h3 : ∀ g, f ≠ .FLAG g := fun g h => hfl ⟨g, h⟩
        obtain ⟨h1, h2⟩ := hnm f hf
        have h2' : ∀ r ∈ [24#5, 27#5, 28#5], f ≠ .GPR r := by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h2 24 (by simp)
          · exact h2 27 (by simp)
          · exact h2 28 (by simp)
        rw [hfr2 f h1 h2 h3, hst.world.1 f hf, hfrw f h1 h2' h3,
          hWtoth f (fun h => hf (by subst h; simp [Masked])) (fun h => hf (by subst h; simp [Masked])),
          ← hW0, patch, r_setMem]
    · rw [← hxF, ArmState.mem_w_eq_mem, hmemt, hmemw, write_mem_bytes_eq, write_mem_bytes_eq,
        setMem_mem, setMem_mem, h25y, hWt25, hnew, hy1.patch_mem, hWtmem, hWmem]
      exact writeM_pt _ _ _ (writeM_pt _ _ _ (hst.world.2.1 a ha))
    · rw [← hxF, Arm.w_program, hprogt, hprogw, hWtprog, ← hW0, patch, setMem_program, patch,
        setMem_program, hy1.prog]
      exact hst.world.2.2
  have h27 : Arm.r (.GPR 27#5) xF = Arm.r (.GPR 27#5) w'' := by
    rw [← hxF, Arm.r_of_w_different (by simp)]; exact hdep27
  obtain ⟨c'', hm, hQ⟩ : ∃ c'', MStep R.vc R.sem ckeep R.rf
      (.run ⟨b, .op k (#[Reg.x 25, .x 26, .x 27, .x 24, .x 28].map Loc.reg) :: its', m, W⟩) c'' ∧
      Q R xF c'' := by
    refine ⟨_, MStep.op (outs' := [regVal xF (.x 27), regVal xF (.x 24), regVal xF (.x 28)]) (m2 := m)
      hvb hi hops (by simp) (by rw [hU]; exact hsemW) (by simp [Operand.isDef])
      ⟨by simp, fun h => by simp [havocFrom, MInst.keptDefs] at h, fun n h => ?_⟩ ?_
      (MNext.next hk), ?_⟩
    · simp only [havocFrom, MInst.keptDefs, Option.some.injEq] at h
      subst h
      simp [regVal, rnum, h27]
    · refine ⟨fun l _ => ?_, fun c hc => by simp [MInst.clobbers] at hc⟩
      simp [Backend.Proof.writeM, Operand.isDef, Operand.isEarly]
    refine ⟨j0 + (rmwLoopLines ty.bits op fl (.loop ps1.aloop)).length, vb, items,
      pre ++ [.op k (#[Reg.x 25, .x 26, .x 27, .x 24, .x 28].map Loc.reg)], c2, ls2, _, ps2, T,
      hvb, hit, by rw [hsplit]; simp, hchk', hc2, hl2, htr, ?_, ?_, ?_⟩
    · rw [← List.drop_drop, hdrop', List.drop_left]
    · rw [← hxF, Arm.r_of_w_same]
      congr 1
      simp [rmwLoopLines, rmwLoopBody]
      omega
    · refine stRel_after hR hst ?_ ?_ hsw ?_ ?_ ⟨?_, fun a ha => ?_⟩
      · refine store_regs hst [27, 24, 28] (by simp) ?_ ?_ hfr2
        · intro n hn
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
          rcases hn with rfl | rfl | rfl <;>
            simp [Backend.Proof.writeM, upd, Operand.isDef, Operand.isLate]
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
          simp [Backend.Proof.writeM, upd, Operand.isDef, Operand.isLate, hr.1, hr.2.1, hr.2.2]
      · intro l hl
        simp [Backend.Proof.writeM, upd, Operand.isDef, Operand.isLate, hl]
      · rw [hfr2 .ERR (by simp) (by simp) (by simp)]; exact hst.err
      · rw [← hxF, Arm.w_program, hprogt, patch, setMem_program, hy1.prog]
      · simp only [spOf]; exact hfr2 _ (by simp) (by simp [rnum]) (by simp)
      · have hF' := RL.FK_F ha
        have hout : ∀ q < ty.bytes, Arm.r (.GPR 25#5) s + BitVec.ofNat 64 q ≠ a :=
          fun q hq e => hav q hq (by rw [e]; exact hF')
        rw [← hxF, ArmState.mem_w_eq_mem, hmemt, write_mem_bytes_eq, setMem_mem, h25y,
          writeM_apply_out _ _ _ _ _ hout, hy1.patch_mem, writeM_apply_out _ _ _ _ _ hout]
  have hEav : ∀ x ∈ [(⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩ : Ev),
      ⟨.relXW, Arm.r (.GPR 25#5) s, ty.bytes,
        rmwNew ty op (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1)⟩],
      Avoids R.F x.n x.addr := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact hav
  have hAI : AInv R c'' := by
    have := aInv_step hR (q_patch hR hq hEav) (aInv_patch hA _) (by rw [hW0]; exact hm)
    exact this
  have hsrc : SrcStep R (OpC b k (#[Reg.x 25, .x 26, .x 27, .x 24, .x 28].map Loc.reg) its' m w)
      [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩, ⟨.relXW, Arm.r (.GPR 25#5) s, ty.bytes,
        rmwNew ty op (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1)⟩] c'' := by
    refine .op hvb hi hops ?_ ?_ (by rw [hW0]; exact hm)
    · rw [hW0]
      show _ = cEvs R.F R.ctx _ (((_ : Array Operand).zip _).toList.filter (·.1.isUse) |>.map (m ·.2)) W
      rw [hU]
      unfold cEvs
      simp only [MInst.isCtl, ite_true]
      exact hevL.symm
    · rw [hW0]
      show IFoot R.sem _ (((_ : Array Operand).zip _).toList.filter (·.1.isUse) |>.map (m ·.2)) W _
      rw [hU]
      have hf := rmw_foot (F := R.F) (ctx := R.ctx) (X := R.X) (ra := .vreg va .int) (rx := .vreg vo .int)
        (rd := .vreg vd .int) (r1 := .vreg v1 .int) (r2 := .vreg v2 .int)
        (u := regVal s (.x 25)) (x := regVal s (.x 26)) (ty := ty) (op := op) (fl := fl) hWerr
      rw [hevL] at hf
      refine ⟨hf.1, fun m' hm' => ?_⟩
      rw [R.sem_eq hnc hnt, R.sem_eq hnc hnt]
      exact hf.2 m' hm'
  -- the image of the step: the final iteration's `ldaxr` and successful `stlxr`
  have hpos : 0 < (rmwLoopMid op ty.bits).length + 1 := by omega
  have hsh : ∀ x ∈ [(⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩ : Ev),
      ⟨.relXW, Arm.r (.GPR 25#5) s, ty.bytes,
        rmwNew ty op (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1)⟩],
      x.k.dir ≠ .F → ¬ PrivA R x.addr.toNat := by
    intro x hx _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact privA_of_avoid hav hn0
  by_cases h2 : q + ((rmwLoopMid op ty.bits).length + 1) + 2 ≤ ls.length
  · obtain ⟨hs2, mon2, hr2⟩ := hseg2 h2
    rw [hstep, hstepc] at hr2
    refine .inr (.inl ⟨_, _, c'', (xF, mon2), fun j => if j = 0 then ((evTr (ls.take q)).length, 0) else
      ((evTr (ls.take q)).length + ((rmwLoopMid op ty.bits).length + 1), 0), h2, .inl (by omega), hsrc,
      hr2, ⟨hQ, hAI⟩, ?_⟩)
    rw [hs2, List.append_assoc]
    exact img_pair hpos hF.pre rfl rfl hsh (T := [[]]) (by simp)
  · have hls : ls.take (q + ((rmwLoopMid op ty.bits).length + 1) + 1) = ls :=
      List.take_of_length_le (by omega)
    rw [hls] at hseg1
    refine .inr (.inr (.inl ⟨_, c'', fun j => if j = 0 then ((evTr (ls.take q)).length, 0) else
      ((evTr (ls.take q)).length + ((rmwLoopMid op ty.bits).length + 1), 0), hsrc, ?_⟩))
    rw [hseg1, List.append_assoc]
    exact img_pair hpos hF.pre rfl rfl hsh (T := []) (by simp)

/-! ## The `atomic_cas` loop on the machine -/

theorem condHolds_w_pc (c : BitVec 4) (v : BitVec 64) (s : ArmState) :
    Arm.ConditionHolds c (Arm.w .PC v s) = Arm.ConditionHolds c s := by
  exact SameWorld.conditionHolds (SameWorld.w_left (F := fun _ => False) (by simp [Masked])
    (SameWorld.refl _ s)) c

/-- An unhooked line without memory kind: no event, no store exclusive. -/
theorem line_noEv {R : RL} (hR : R.Wf) {j : Nat} {x : Insn} {tc : Option Clif.TrapCode}
    (hj : R.L[j]? = some (.ins x tc)) (hh : x.hooked = false) (hk : insnKind x = none) {u : ArmState}
    (hprog : u.program = R.fb.program R.base) (hpc : Arm.r .PC u = R.pcOf j)
    (herr : Arm.r .ERR u = .None) : stepEvs u = [] ∧ NoStx u := by
  obtain ⟨a, ha, -, hev, hdec⟩ := stepEvs_line (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj hh hprog
    hpc herr
  refine ⟨by rw [hev]; exact VCodeEvents.instEvs_none ha hk _, fun rel rs rn h => ?_⟩
  rw [cls_of_decode hdec, clsOf_none ha hk] at h
  cases h

set_option maxHeartbeats 1000000 in
/-- **The `atomic_cas` loop on the machine**, from a state at its `ldaxr` (line `j0 + 1`): the
`ldaxr` reads at x25, the `cmp` and the `b.ne` have no event and no store exclusive; the `b.ne`
leaves the loop (to the line after it, `j0 + 7`) when `ne` holds, else goes to the `stlxr`, which
writes x28's low bytes at x25 with status register w24; after it, the `cbnz` falls through on
success and goes back to the loop label on failure. -/
theorem cas_steps {R : RL} (hR : R.Wf) {ty : CTy} (hty : AtomTy ty) {fl : Clif.MemFlags}
    {j0 n : Nat} {X : List Line}
    (hdrop : R.L.drop j0 = casLoopLines ty.bits fl (.loop n) (.loop (n + 1)) ++ X)
    {t : ArmState} (hprog : t.program = R.fb.program R.base) (hpc : Arm.r .PC t = R.pcOf (j0 + 1))
    (herr : Arm.r .ERR t = .None) :
    ∃ s1, execLines (R.envOf (j0 + 1)) (casLoopHead ty.bits fl) t = some s1 ∧
      iterN R.step 2 t = s1 ∧
      (stepEvs t = [⟨.acqXR, Arm.r (.GPR 25#5) t, ty.bytes,
        readM ty.bytes (Arm.r (.GPR 25#5) t) t.mem⟩] ∧ NoStx t) ∧
      (stepEvs (R.step t) = [] ∧ NoStx (R.step t)) ∧ (stepEvs s1 = [] ∧ NoStx s1) ∧
      R.step s1 = Arm.w .PC (if Arm.ConditionHolds Cond.ne.bits s1 then R.pcOf (j0 + 7)
        else R.pcOf (j0 + 4)) s1 ∧
      (Arm.ConditionHolds Cond.ne.bits s1 = false →
        ∃ s3, execLines (R.envOf (j0 + 4)) (casStore ty.bits fl) (Arm.w .PC (R.pcOf (j0 + 4)) s1) = some s3 ∧
          R.step (Arm.w .PC (R.pcOf (j0 + 4)) s1) = s3 ∧
          stepEvs (Arm.w .PC (R.pcOf (j0 + 4)) s1) =
            [⟨.relXW, Arm.r (.GPR 25#5) s1, ty.bytes, (Arm.r (.GPR 28#5) s1).setWidth (ty.bytes * 8)⟩] ∧
          cls (Arm.w .PC (R.pcOf (j0 + 4)) s1) = .stx true 24#5 25#5 ∧
          stepEvs s3 = [] ∧ NoStx s3 ∧ R.step s3 = Arm.w .PC (R.pcOf (j0 + 7)) s3 ∧
          stepEvs (failState 24#5 (Arm.w .PC (R.pcOf (j0 + 4)) s1)) = [] ∧
          NoStx (failState 24#5 (Arm.w .PC (R.pcOf (j0 + 4)) s1)) ∧
          R.step (failState 24#5 (Arm.w .PC (R.pcOf (j0 + 4)) s1)) =
            Arm.w .PC (R.pcOf j0) (failState 24#5 (Arm.w .PC (R.pcOf (j0 + 4)) s1))) := by
  have hat : ∀ q ln, (casLoopLines ty.bits fl (.loop n) (.loop (n + 1)))[q]? = some ln →
      R.L[j0 + q]? = some ln := lines_at' hdrop
  have hL0 : R.L[j0]? = some (.label (.loop n)) := hat 0 _ rfl
  have hL3 : R.L[j0 + 3]? = some (.ins (.bcond .ne (.loop (n + 1))) none) := hat 3 _ rfl
  have hL4 : R.L[j0 + 4]? = some (.ins (.stlxr ty.bits (.x 24) (.x 28) (.x 25)) fl.trapCode) :=
    hat 4 _ rfl
  have hL5 : R.L[j0 + 5]? = some (.ins (.cbz true true (.x 24) (.loop n)) none) := hat 5 _ rfl
  have hL6 : R.L[j0 + 6]? = some (.label (.loop (n + 1))) := hat 6 _ rfl
  have hp76 : R.pcOf (j0 + 7) = R.pcOf (j0 + 6) := RL.pcOf_succ_label hL6
  have hd1 : R.L.drop (j0 + 1) = casLoopHead ty.bits fl ++
      (.ins (.bcond .ne (.loop (n + 1))) none :: .ins (.stlxr ty.bits (.x 24) (.x 28) (.x 25)) fl.trapCode ::
        .ins (.cbz true true (.x 24) (.loop n)) none :: .label (.loop (n + 1)) :: X) := by
    rw [← List.drop_drop, hdrop]; simp [casLoopLines, casLoopHead]
  have hd4 : R.L.drop (j0 + 4) = casStore ty.bits fl ++
      (.ins (.cbz true true (.x 24) (.loop n)) none :: .label (.loop (n + 1)) :: X) := by
    rw [← List.drop_drop, hdrop]; simp [casLoopLines, casLoopHead, casStore]
  obtain ⟨s1, hrun1, hint1, -, hfr1, hmem1, hprog1, -⟩ := casHead_spec hty fl (R.envOf (j0 + 1)) t herr
  obtain ⟨hit1, hpcs1, -, -⟩ := run_ins hR hd1 (casHead_ins _ fl) hprog hpc herr hint1 hrun1
  simp only [casLoopHead, List.length_cons, List.length_nil] at hit1 hpcs1
  have hhook : ∀ i tc, Line.ins i tc ∈ casLoopHead ty.bits fl → i.hooked = false := fun i tc h => by
    obtain ⟨i', t', e, hh⟩ := casHead_ins _ fl _ h; cases e; exact hh
  have hst : ∀ i < (casLoopHead ty.bits fl).length, ∃ x tc a,
      (casLoopHead ty.bits fl)[i]? = some (.ins x tc) ∧ x.toArmInst (R.envOf (j0 + 1 + i)) = .ok a ∧
      decodeAt (iterN R.step i t) = some a ∧ stepEvs (iterN R.step i t) = instEvs a (iterN R.step i t) ∧
      iterN R.step (i + 1) t = exec_inst a (iterN R.step i t) :=
    step_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit (lines_at' hd1) hhook hprog hpc herr
      hint1 hrun1
  -- the `ldaxr`
  obtain ⟨x0, tc0, a0, hl0, ha0, hdec0, hev0, -⟩ := hst 0 (by simp [casLoopHead])
  simp only [casLoopHead, List.getElem?_cons_zero, Option.some.injEq, Line.ins.injEq] at hl0
  obtain ⟨rfl, rfl⟩ := hl0
  have hread : stepEvs t = [⟨.acqXR, Arm.r (.GPR 25#5) t, ty.bytes,
      readM ty.bytes (Arm.r (.GPR 25#5) t) t.mem⟩] ∧ NoStx t := by
    refine ⟨hev0.trans (ldaxr_one hty ha0 t), fun rel rs rn h => ?_⟩
    obtain ⟨sz, hsz⟩ := ldaxr_cls hty ha0
    rw [cls_of_decode (s := t) hdec0, hsz] at h
    cases h
  -- the `cmp`
  obtain ⟨x1, tc1, a1, hl1, ha1, hdec1, hev1, -⟩ := hst 1 (by simp [casLoopHead])
  simp only [casLoopHead, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
    Line.ins.injEq] at hl1
  obtain ⟨rfl, rfl⟩ := hl1
  have hcmp : stepEvs (R.step t) = [] ∧ NoStx (R.step t) := by
    refine ⟨hev1.trans (VCodeEvents.instEvs_none ha1 (insnKind_casLoopCmp _) _), fun rel rs rn h => ?_⟩
    rw [cls_of_decode (s := R.step t) hdec1, clsOf_none ha1 (insnKind_casLoopCmp _)] at h
    cases h
  -- the `b.ne`
  have herr1 : Arm.r .ERR s1 = .None := by
    rw [hfr1 .ERR (by simp) (by simp) (by simp)]; exact herr
  have hprog1' : s1.program = R.fb.program R.base := by rw [hprog1, hprog]
  have hpc3 : Arm.r .PC s1 = R.pcOf (j0 + 3) := by rw [hpcs1]
  have hbne := line_noEv hR hL3 rfl rfl hprog1' hpc3 herr1
  obtain ⟨ab, jb, hab, hjb, hstepb⟩ := step_branch hR hL3 (.inr (.inl ⟨.ne, rfl⟩)) (by simp) hprog1'
    hpc3 herr1
  rw [brCond_bcond hab, pcOf_label_eq hR hjb hL6, ← hp76] at hstepb
  refine ⟨s1, hrun1, hit1, hread, hcmp, hbne, hstepb, fun hne => ?_⟩
  -- the `stlxr`
  generalize hz : Arm.w .PC (R.pcOf (j0 + 4)) s1 = z
  have herrz : Arm.r .ERR z = .None := by rw [← hz, Arm.r_of_w_different (by simp)]; exact herr1
  have hprogz : z.program = R.fb.program R.base := by rw [← hz, Arm.w_program]; exact hprog1'
  have hpcz : Arm.r .PC z = R.pcOf (j0 + 4) := by rw [← hz, Arm.r_of_w_same]
  obtain ⟨s3, hrun3, h24, -, -, hprog3⟩ := stlxr_spec hty fl (R.envOf (j0 + 4)) z herrz
  have hint3 : LinesInterOk (R.envOf (j0 + 4)) (casStore ty.bits fl) z :=
    fun q h0 h1 => by simp [casStore] at h1; omega
  obtain ⟨hit3, hpcs3, -, -⟩ := run_ins hR hd4 (by simp [casStore, Insn.hooked]) hprogz hpcz herrz hint3
    hrun3
  simp only [casStore, List.length_cons, List.length_nil, Nat.zero_add] at hit3 hpcs3
  have hseg : (segEvs R.step (casStore ty.bits fl).length z).flatten =
      linesEvs (R.envOf (j0 + 4)) (casStore ty.bits fl) z :=
    segEvs_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit _ (j0 + 4) z s3 (lines_at' hd4)
      (by simp [casStore, Insn.hooked]) hprogz hpcz herrz hint3 hrun3
  rw [casStore_evsEq hty fl] at hseg
  simp only [casStore, List.length_cons, List.length_nil, Nat.zero_add, segEvs_one, List.flatten_cons,
    List.flatten_nil, List.append_nil] at hseg
  obtain ⟨as, has, -, -, hdecs⟩ := stepEvs_line (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hL4 rfl
    hprogz hpcz herrz
  have h25z : Arm.r (.GPR 25#5) z = Arm.r (.GPR 25#5) s1 := by
    rw [← hz, Arm.r_of_w_different (by simp)]
  have h28z : Arm.r (.GPR 28#5) z = Arm.r (.GPR 28#5) s1 := by
    rw [← hz, Arm.r_of_w_different (by simp)]
  rw [h25z, h28z] at hseg
  -- the `cbnz` after a success, after a failure
  have herr3 : Arm.r .ERR s3 = .None := by
    have := stlxr_spec hty fl (R.envOf (j0 + 4)) z herrz
    obtain ⟨s3', h3', -, hfr3, -, -⟩ := this
    rw [hrun3] at h3'; cases h3'
    rw [hfr3 .ERR (by simp) (by simp)]; exact herrz
  have hprog3' : s3.program = R.fb.program R.base := by rw [hprog3, hprogz]
  have hpc5 : Arm.r .PC s3 = R.pcOf (j0 + 5) := by rw [hpcs3]
  obtain ⟨hevc, hnsc⟩ := cbz_noEv hR hL5 hprog3' hpc5 herr3
  obtain ⟨ac, jc, hac, -, hstepc⟩ := step_branch hR hL5 (.inr (.inr (.inl ⟨true, true, .x 24, rfl⟩)))
    (by simp) hprog3' hpc5 herr3
  have hbr : brCond ac s3 = false := by
    rw [brCond_cbz (by decide) hac]; simp [rnum, h24]
  rw [hbr] at hstepc
  simp only [Bool.false_eq_true, ite_false, show j0 + 5 + 1 = j0 + 6 from rfl, ← hp76] at hstepc
  have hpcf : Arm.r .PC (failState 24#5 z) = R.pcOf (j0 + 5) := by
    rw [pc_failState, hpcz, show j0 + 5 = (j0 + 4) + 1 from rfl, RL.pcOf_succ_ins hL4]
  have herrf : Arm.r .ERR (failState 24#5 z) = .None := by
    rw [r_failState _ _ _ (by simp) (by simp)]; exact herrz
  have hprogf : (failState 24#5 z).program = R.fb.program R.base := by
    rw [prog_failState, hprogz]
  obtain ⟨hevf, hnsf⟩ := cbz_noEv hR hL5 hprogf hpcf herrf
  obtain ⟨af, jf, haf, hjf, hstepf⟩ := step_branch hR hL5 (.inr (.inr (.inl ⟨true, true, .x 24, rfl⟩)))
    (by simp) hprogf hpcf herrf
  have hbrf : brCond af (failState 24#5 z) = true := by
    rw [brCond_cbz (by decide) haf]
    have := x24_failState z
    simp [rnum, this]
  simp only [hbrf, ite_true] at hstepf
  rw [pcOf_label_eq hR hjf hL0] at hstepf
  refine ⟨s3, hrun3, by rw [← hit3]; rfl, hseg, ?_, hevc, hnsc, hstepc, hevf, hnsf, hstepf⟩
  rw [cls_of_decode hdecs, stlxr_cls hty (.inr rfl) has]

end Concurrency.ArmAllocThread
