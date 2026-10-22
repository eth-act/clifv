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

end Concurrency.ArmAllocThread
