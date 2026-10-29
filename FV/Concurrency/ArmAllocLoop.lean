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

/-- The `casLoopCmp` comparison is not a `ret`. -/
theorem casLoopCmp_ne_ret (bits : Nat) : casLoopCmp bits ≠ .ret := by
  unfold casLoopCmp; split <;> simp

/-- The `atomic_rmw` loop's middle instructions are not `ret`s. -/
theorem rmwLoopMid_ne_ret {bits : Nat} {op : AtomicRmwLoopOp} {x : Insn}
    (h : x ∈ rmwLoopMid op bits) : x ≠ .ret := by
  unfold rmwLoopMid at h
  split at h
  · simp at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h <;> first
      | (subst h; intro h'; injection h')
      | exact h.elim
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; intro h'; injection h'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; intro h'; injection h'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; intro h'; injection h'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; intro h'; injection h'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; intro h'; injection h'
  · rcases List.mem_append.1 h with h | h
    · exact rmwLoopSext_ne_ret h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with h | h
      · rw [h]; exact rmwLoopCmp_ne_ret _ _
      · subst h; intro h'; injection h'
  · rcases List.mem_append.1 h with h | h
    · exact rmwLoopSext_ne_ret h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with h | h
      · rw [h]; exact rmwLoopCmp_ne_ret _ _
      · subst h; intro h'; injection h'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with h | h
    · rw [h]; exact rmwLoopCmp_ne_ret _ _
    · subst h; intro h'; injection h'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with h | h
    · rw [h]; exact rmwLoopCmp_ne_ret _ _
    · subst h; intro h'; injection h'

/-- Every line of the `atomic_rmw` loop's body is an unhooked instruction other than `ret`. -/
theorem rmwBody_ne_ret {bits : Nat} {op : AtomicRmwLoopOp} {fl : Clif.MemFlags} {x : Insn} {tc}
    (h : Line.ins x tc ∈ rmwLoopBody bits op fl) : x ≠ .ret := by
  have hx : (x = .ldaxr bits (.x 27) (.x 25) ∧ tc = fl.trapCode) ∨
      (∃ a, a ∈ rmwLoopMid op bits ∧ a = x ∧ none = tc) ∨
      (x = .stlxr bits (.x 24) (rmwLoopStored op) (.x 25) ∧ tc = fl.trapCode) := by
    simpa [rmwLoopBody, List.mem_cons, List.mem_append, List.mem_map, Line.ins.injEq] using h
  rcases hx with ⟨h1, -⟩ | ⟨a, ha, h2, -⟩ | ⟨h1, -⟩
  · subst h1; intro h'; injection h'
  · subst h2; exact rmwLoopMid_ne_ret ha
  · subst h1; intro h'; injection h'

/-- The lines and the states of the `atomic_rmw` loop's body, from its first line (`rmw_at` of
`ArmAllocLoopFwd`, here for the runs ending inside the item). -/
theorem rmwBodyAt {R : RL} (hR : R.Wf) {ty : CTy} (hty : AtomTy ty) {op : AtomicRmwLoopOp}
    {fl : Clif.MemFlags} {j0 n : Nat} {T : List Line}
    (hd1 : R.L.drop (j0 + 1) =
      rmwLoopBody ty.bits op fl ++ (.ins (.cbz true true (.x 24) (.loop n)) none :: T))
    {s : ArmState} (hprog : s.program = R.fb.program R.base)
    (hpc : Arm.r .PC s = R.pcOf (j0 + 1))
    (herr : Arm.r .ERR s = .None) (i : Nat) (hi : i < (rmwLoopMid op ty.bits).length + 2) :
    ∃ x tc, R.fa.lines.toList[j0 + 1 + i]? = some (.ins x tc) ∧ x.hooked = false ∧ x ≠ .ret ∧
      (iterN R.step i s).program = R.fb.program R.base ∧
      Arm.r .PC (iterN R.step i s) = R.pcOf (j0 + 1 + i) ∧
      Arm.r .ERR (iterN R.step i s) = .None := by
  have hlen := rmwBody_len ty.bits op fl
  obtain ⟨t', hrun, hint, -⟩ := rmwBody_spec hty op fl (R.envOf (j0 + 1)) s herr
  have hat := lines_at' hd1
  obtain ⟨ln, hln⟩ : ∃ ln, (rmwLoopBody ty.bits op fl)[i]? = some ln :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨x, tc, he, hh⟩ := rmwBody_ins hty op fl _ (List.mem_of_getElem? hln)
  subst he
  refine ⟨x, tc, hat i _ hln, hh, rmwBody_ne_ret (List.mem_of_getElem? hln), ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · exact ⟨hprog, by rw [Nat.add_zero]; exact hpc, herr⟩
  obtain ⟨s1, hs1⟩ := execLines_take hrun i
  have hd' : R.L.drop (j0 + 1) = (rmwLoopBody ty.bits op fl).take i ++
      ((rmwLoopBody ty.bits op fl).drop i ++ (.ins (.cbz true true (.x 24) (.loop n)) none :: T)) := by
    rw [hd1, ← List.append_assoc, List.take_append_drop]
  obtain ⟨hit, hpcs, -, -⟩ := run_ins hR hd'
    (fun l hl => rmwBody_ins hty op fl l (List.mem_of_mem_take hl)) hprog hpc herr
    (interOk_take hint i) hs1
  rw [List.length_take, Nat.min_eq_left (by omega)] at hit hpcs
  obtain ⟨he, hp⟩ := hint i h0 (by omega) s1 hs1
  rw [hit]
  exact ⟨hp.trans hprog, hpcs, he⟩

/-- A trace without writes stays so at its tails. -/
theorem noW_tail {A B : List (List Ev)} (h : NoW (A ++ B)) : NoW B := by
  intro p y hy
  refine h (A.length + p.1, p.2) y ?_
  rw [evAt_append_ge _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact hy

/-- `RetryOut` without its no-write case. -/
abbrev RetryOutR (P : Policy) (f : ArmState → ArmState) (ok : ArmState → Lab → Prop)
    (Hd : ArmState → Prop) (rd : ArmState → Ev) (p : Nat) (rs : BitVec 5) (Ex : ArmState → Prop)
    (t : ArmState × Mon) (ls : List Lab) : Prop :=
  ∃ q y1 e, Final P f ok Hd rd p t ls q y1 e ∧
    (Ex (iterN f p (patch [e] y1)) ∨
      (¬ Ex (iterN f p (patch [e] y1)) ∧ StoreAt f Hd rs (iterN f p (patch [e] y1)) ∧
        q + p + 1 ≤ ls.length ∧
        ∃ wv : Ev, wv.k.dir = .W ∧ stepEvs (iterN f p (patch [e] y1)) = [wv] ∧
          evTr (ls.take (q + p + 1)) = evTr (ls.take q) ++ segR e p ++ [[wv]] ∧
          (q + p + 2 ≤ ls.length →
            evTr (ls.take (q + p + 2)) = evTr (ls.take q) ++ segR e p ++ [[wv], []] ∧
            ∃ mon2, PRun P f ok t (ls.take (q + p + 2))
              (f (f (iterN f p (patch [e] y1))), mon2))))

/-- `retryOut_shift` for `RetryOutR`. -/
theorem retryOutR_shift {P : Policy} {f : ArmState → ArmState} {ok : ArmState → Lab → Prop}
    {Hd : ArmState → Prop} {rd : ArmState → Ev} {p : Nat} {rs : BitVec 5} {Ex : ArmState → Prop}
    {B0 rest : List Lab} {t t0 : ArmState × Mon} (hB : PRun P f ok t B0 t0)
    (hnw : NoW (evTr B0)) (h : RetryOutR P f ok Hd rd p rs Ex t0 rest) :
    RetryOutR P f ok Hd rd p rs Ex t (B0 ++ rest) := by
  obtain ⟨q, y1, e, hF, hX⟩ := h
  have hT : ∀ k, (B0 ++ rest).take (B0.length + k) = B0 ++ rest.take k := take_app B0 rest
  have e1 : B0.length + q + p = B0.length + (q + p) := by omega
  have e2 : B0.length + q + p + 1 = B0.length + (q + p + 1) := by omega
  have e3 : B0.length + q + p + 2 = B0.length + (q + p + 2) := by omega
  refine ⟨B0.length + q, y1, e, ⟨hF.hd, hF.acc, by simp; have := hF.le; omega, ?_, ?_, ?_⟩, ?_⟩
  · rw [hT, evTr_append]; exact noW_append hnw hF.pre
  · rw [e1, hT, hT, evTr_append, evTr_append, hF.seg, List.append_assoc]
  · obtain ⟨mon1, hr1⟩ := hF.run; exact ⟨mon1, by rw [e1, hT]; exact PRun.append hB hr1⟩
  rcases hX with hx | ⟨hnx, hst, hle, wv, hW, hwv, hs1, hs2⟩
  · exact .inl hx
  refine .inr ⟨hnx, hst, by simp; omega, wv, hW, hwv, ?_, fun h2 => ?_⟩
  · rw [e2, hT, hT, evTr_append, evTr_append, hs1]; simp [List.append_assoc]
  · obtain ⟨h3, mon2, hr2⟩ := hs2 (by simp at h2; omega)
    refine ⟨by rw [e3, hT, hT, evTr_append, evTr_append, h3]; simp [List.append_assoc], mon2, ?_⟩
    rw [e3, hT]; exact PRun.append hB hr2

/-- **`retry_run`, with the no-write case's last state at a non-`ret` line**: a precise run of a
retry loop from a head either writes nothing and ends at a state `At`, or has the `RetryOutR`
outcome (a final iteration at the exit or at a successful store exclusive). -/
theorem retry_run_det {P : Policy} {f : ArmState → ArmState} {ok : ArmState → Lab → Prop}
    {Hd : ArmState → Prop} {rd : ArmState → Ev} {p : Nat} {rs : BitVec 5} {Ex : ArmState → Prop}
    {At : ArmState → Prop} (hL : RetryLoop f Hd rd p rs Ex)
    (hhd : ∀ y, Hd y → At y)
    (hpatch : ∀ y e, Hd y → SameAcc e (rd y) → At (patch [e] y))
    (hmid : ∀ y e, Hd y → SameAcc e (rd y) → ∀ i, 0 < i → i < p → At (iterN f i (patch [e] y)))
    (hlast : ∀ y e, Hd y → SameAcc e (rd y) → ¬ Ex (iterN f p (patch [e] y)) →
      At (iterN f p (patch [e] y)))
    (hfail : ∀ y e, Hd y → SameAcc e (rd y) → ¬ Ex (iterN f p (patch [e] y)) →
      At (failState rs (iterN f p (patch [e] y)))) :
    ∀ (N : Nat) (ls : List Lab) (y : ArmState) (mon : Mon) (t' : ArmState × Mon),
      ls.length ≤ N → Hd y → PRun P f ok (y, mon) ls t' →
      (NoW (evTr ls) ∧ At t'.1) ∨ RetryOutR P f ok Hd rd p rs Ex (y, mon) ls := by
  intro N
  induction N with
  | zero =>
    intro ls y mon t' hN hy hr
    obtain rfl : ls = [] := List.eq_nil_of_length_eq_zero (by omega)
    cases hr
    exact .inl ⟨noW_nil, hhd y hy⟩
  | succ N ih =>
  intro ls y mon t' hN hy hr
  obtain ⟨hR, hn, hat, hx0⟩ := hL.read y hy
  obtain ⟨tp, r1, r2⟩ := PRun.split (ls.take p) (ls.drop p) (by rw [List.take_append_drop]; exact hr)
  rcases prun_one_read (N := p) (i0 := 0) hR hn hL.pos (fun i hi => absurd hi (Nat.not_lt_zero _))
      hat hx0 (fun e he i h0 hi => hL.mid y hy e he i h0 hi) r1
      (List.length_take_le p ls) with ⟨hle, -, -⟩ | ⟨e, he, ht1, hevT, hstep⟩
  · have : ls = [] := by
      rcases ls with _ | ⟨l, ls⟩
      · rfl
      · simp at hle; have := hL.pos; omega
    subst this
    cases hr
    exact .inl ⟨noW_nil, hhd y hy⟩
  have heR : e.k.dir = .R := by rw [he.1]; exact hR
  by_cases hlt : ls.length < p
  · refine .inl ⟨?_, ?_⟩
    · have hL' : ls.take p = ls := List.take_of_length_le (by omega)
      rw [hL'] at hevT
      rw [hevT]
      refine noW_of fun x hx y' hy' => ?_
      obtain ⟨i, hi, rfl⟩ := mem_segEvs hx
      rw [hstep i (by omega)] at hy'
      split at hy'
      · simp only [List.mem_singleton] at hy'; subst hy'; rw [heR]; decide
      · cases hy'
    · have hL' : ls.take p = ls := List.take_of_length_le (by omega)
      rw [hL'] at r1 ht1
      obtain rfl := PRun.det r1 hr
      rw [ht1]
      rcases ls with _ | ⟨l, ls⟩
      · exact hpatch y e hy he
      · rw [List.length_cons] at hlt
        exact hmid y e hy he (ls.length + 1) (by omega) (by omega)
  obtain ⟨A, B, rfl, hA⟩ : ∃ A B, ls = A ++ B ∧ A.length = p :=
    ⟨ls.take p, ls.drop p, (List.take_append_drop p ls).symm, by simp; omega⟩
  rw [List.take_left' hA] at r1 ht1 hevT
  rw [List.drop_left' hA] at r2
  rw [hA] at ht1 hevT
  have hsegp : evTr A = segR e p := hevT.trans (segEvs_segR hL.pos fun i hi => hstep i hi)
  obtain ⟨z0, mon1⟩ := tp
  simp only at ht1
  subst ht1
  have hT : ∀ k, (A ++ B).take (A.length + k) = A ++ B.take k := take_app A B
  have hfin : Final P f ok Hd rd p (y, mon) (A ++ B) 0 y e := by
    refine ⟨hy, he, by simp; omega, by simpa [evTr] using noW_nil, ?_, ⟨mon1, ?_⟩⟩
    · rw [Nat.zero_add, List.take_left' hA, List.take_zero]
      exact hsegp
    · rw [Nat.zero_add, List.take_left' hA]; exact r1
  rcases hL.last y hy e he with hex | ⟨hnx, hst⟩
  · exact .inr ⟨0, y, e, hfin, .inl hex⟩
  cases B with
  | nil =>
    cases r2
    refine .inl ⟨?_, hlast y e hy he hnx⟩
    rw [List.append_nil, hsegp]
    exact noW_segR heR p
  | cons l rest =>
  cases r2 with
  | @cons _ t1 _ _ _ hs hp hok r3 =>
  cases hxf : l.xfail with
  | false =>
    obtain ⟨wv, hW, hwv⟩ := hst.wr
    obtain ⟨hl, ht1⟩ := tstep_store hs hp hxf hW hwv
    refine .inr ⟨0, y, e, hfin, .inr ⟨hnx, hst, by simp; omega, wv, hW, hwv, ?_, fun h2 => ?_⟩⟩
    · rw [show 0 + p + 1 = A.length + 1 by omega, hT, List.take_zero, evTr_append, hsegp]
      simp [evTr, hl]
    · cases rest with
      | nil => simp at h2; omega
      | cons l2 rest2 =>
      cases r3 with
      | @cons _ t2 _ _ _ hs2 hp2 hok2 r4 =>
      obtain ⟨s1, mon1'⟩ := t1
      simp only at ht1
      subst ht1
      obtain ⟨h21, hl2, -⟩ := tstep_nil hs2 hp2 hst.next.1 hst.next.2
      obtain ⟨s2, mon2⟩ := t2
      simp only at h21
      subst h21
      refine ⟨?_, mon2, ?_⟩
      · rw [show 0 + p + 2 = A.length + 2 by omega, hT, List.take_zero, evTr_append, hsegp]
        simp [evTr, hl, hl2]
      · rw [show 0 + p + 2 = A.length + 2 by omega, hT]
        simp only [List.take_succ_cons, List.take_zero]
        exact PRun.append r1 (.cons hs hp hok (.cons hs2 hp2 hok2 .nil))
  | true =>
    have hl0 : l.evs = [] := by
      cases hs with
      | exec => cases hxf
      | xfail => rfl
    obtain ⟨rel0, rn0, hc0⟩ := hst.stx
    have ht1 : t1.1 = failState rs (iterN f p (patch [e] y)) := by
      cases hs with
      | exec => cases hxf
      | xfail hc =>
        rw [hc0] at hc
        cases hc
        rfl
    cases rest with
    | nil =>
      refine .inl ⟨?_, ?_⟩
      · rw [evTr_append]
        refine noW_append (hsegp ▸ noW_segR heR p) (noW_nils fun x hx => ?_)
        simp only [evTr, List.map_cons, List.map_nil, List.mem_singleton] at hx
        rw [hx, hl0]
      · cases r3
        rw [ht1]
        exact hfail y e hy he hnx
    | cons l2 rest2 =>
    cases r3 with
    | @cons _ t2 _ _ _ hs2 hp2 hok2 r4 =>
    obtain ⟨s1, mon1'⟩ := t1
    simp only at ht1
    subst ht1
    obtain ⟨h21, hl2, -⟩ := tstep_nil hs2 hp2 hst.fnext.1 hst.fnext.2
    obtain ⟨s2, mon2⟩ := t2
    simp only at h21
    subst h21
    have hnwB : NoW (evTr (A ++ [l, l2])) := by
      rw [evTr_append, hsegp]
      refine noW_append (noW_segR heR p) (noW_nils fun x hx => ?_)
      simp only [evTr, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, hl0, hl2] at hx
      rcases hx with rfl | rfl | hx
      · rfl
      · rfl
      · exact hx.elim
    have hout := ih rest2 _ mon2 t' (by simp at hN; omega) hst.back r4
    rcases hout with ⟨hnw2, hat2⟩ | hout2
    · refine .inl ⟨?_, hat2⟩
      rw [show A ++ l :: l2 :: rest2 = (A ++ [l, l2]) ++ rest2 from by simp [List.append_assoc],
        evTr_append]
      exact noW_append hnwB hnw2
    · refine .inr ?_
      have hres := retryOutR_shift (B0 := A ++ [l, l2])
        (PRun.append r1 (.cons hs hp hok (.cons hs2 hp2 hok2 .nil))) hnwB hout2
      rw [List.append_assoc] at hres
      exact hres

set_option maxHeartbeats 4000000 in
/-- **The per-item obligation at the `atomic_rmw` loop** (module doc): every precise Arm run from
`Q`-related states goes through failed iterations (reading any bytes, writing nothing) and ends
before a successful `stlxr` (private writes only: none), or its final iteration's `ldaxr` read `e`
and successful `stlxr` write `wv` are the events of the allocated code's step `[e, wv]` (on the
world patched with `e`; a monitor pair), the states after the `cbnz` related; a run ending inside
the loop (with no successful `stlxr`) is at a line other than `ret`. -/
theorem rmw_opR {R : RL} (hR : R.Wf) {ok : ArmState → Lab → Prop} {s : ArmState} {mon : Mon}
    {b k : Nat} {allocs : Array Loc} {its' : List RItem} {m : Loc → CV} {w : ArmState}
    {evs0 : List Ev} {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its' m w)) (hA : AInv R (OpC b k allocs its' m w))
    (hs0 : SrcStep R (OpC b k allocs its' m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i →
      ∃ ty op fl ra ro rd r1 r2, i = .atomicRmwLoop ty op fl ra ro rd r1 r2)
    {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm R.step ok (s, mon) ls t') :
    OpOutN R ok (fun c => c.measure) (s, mon) (OpC b k allocs its' m w) ls t' := by
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
  have hk0 : k + 1 < vb.insts.size := lt_size_of_not_term hR hvb hi rfl
  obtain ⟨j0, items, pre, regs, i', c1, c2, X', ls1, ps1, psm, psm', ps2, x, cc, wh, ops, rfl, hit,
    hsplit, hasg, hc1', hops, hstat, hchk', hc2, hl1, hX2, hT2, htr, hdrop, hpc, hst, hx, hsc⟩ :=
    q_op hR hq hvb hi hk0
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
  have hP : ∀ ln ∈ Line.label (.loop ps1.aloop) :: rmwLoopBody ty.bits op fl,
      (∀ x t, ln ≠ .ins (.b x) t) ∧ ∀ c, ln = .ins c none → c.condTarget? = none := by
    rcases hty with rfl | rfl | rfl | rfl <;> cases op <;>
      simp (config := {decide := true}) [rmwLoopBody, rmwLoopMid, rmwLoopStored, rmwLoopSext,
        rmwLoopCmp, CTy.bits, Insn.condTarget?]
  have hloop : relaxLines R.far (rmwLoopLines ty.bits op fl (.loop ps1.aloop)) =
      rmwLoopLines ty.bits op fl (.loop ps1.aloop) := by
    refine relaxLines_loop (fun ln hln c hc => ?_)
    rw [show rmwLoopLines ty.bits op fl (.loop ps1.aloop) = .label (.loop ps1.aloop) ::
        (rmwLoopBody ty.bits op fl ++ [.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none])
        from rfl] at hln
    simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil,
      or_false] at hln
    rcases hln with hln | hln | hln
    · simp [hln] at hc
    · exact .inl ((hP _ (by simp [hln])).2 c hc)
    · subst hln
      injection hc with h9 h10
      subst h9
      exact .inr ⟨_, rfl⟩
  have hdrop' : R.L.drop j0 = rmwLoopLines ty.bits op fl (.loop ps1.aloop) ++
      (relaxLines R.far (X' ++ x.2.1) ++ R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) := by
    rw [hdrop, hloop]
  have hL0 : R.L[j0]? = some (.label (.loop ps1.aloop)) := by
    have := congrArg (·[0]?) hdrop'
    simpa [List.getElem?_drop, rmwLoopLines] using this
  have hd1 : R.L.drop (j0 + 1) = rmwLoopBody ty.bits op fl ++
      (.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none ::
        (relaxLines R.far (X' ++ x.2.1) ++ R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2))) := by
    rw [← List.drop_drop, hdrop']; simp [rmwLoopLines]
  -- the run
  have hloop := rmw_retry hR hty hd1 hL0 hst.prog hpc hst.err
  -- the loop's heads are at unhooked non-`ret` lines (for the runs ending inside the item)
  have hy0 : ∀ y : ArmState, RmwHd ty op s y → ∀ E : List Ev,
      (patch E y).program = R.fb.program R.base ∧ Arm.r .PC (patch E y) = R.pcOf (j0 + 1) ∧
        Arm.r .ERR (patch E y) = .None := by
    intro y hy E
    refine ⟨by rw [patch, setMem_program, hy.prog, hst.prog], ?_, ?_⟩
    · rw [patch, r_setMem, hy.pc, hpc, RL.pcOf_succ_label hL0]
    · rw [patch, r_setMem, hy.err, hst.err]
  have hatb := lines_at' hd1
  have hhk : ∀ x tc, Line.ins x tc ∈ rmwLoopBody ty.bits op fl → x.hooked = false := by
    intro x tc h
    obtain ⟨x', t', e, hh⟩ := rmwBody_ins hty op fl _ h; cases e; exact hh
  have hld : Insn.ldaxr ty.bits (.x 27) (.x 25) ≠ .ret := by simp
  have hhd : ∀ y, RmwHd ty op s y → AtNonRet R y := by
    intro y hy
    obtain ⟨-, hp2, -⟩ := hy0 y hy []
    rw [patch_nil] at hp2
    exact ⟨j0 + 1, .ldaxr ty.bits (.x 27) (.x 25), fl.trapCode, hatb 0 _ (rmwBody_get0 ty.bits op fl), hld,
      hhk _ _ (List.mem_of_getElem? (rmwBody_get0 ty.bits op fl)), hp2⟩
  have hpatchC : ∀ y e, RmwHd ty op s y → SameAcc e (loopRd ty s y) →
      AtNonRet R (patch [e] y) := by
    intro y e hy he
    obtain ⟨-, hp2, -⟩ := hy0 y hy [e]
    exact ⟨j0 + 1, .ldaxr ty.bits (.x 27) (.x 25), fl.trapCode, hatb 0 _ (rmwBody_get0 ty.bits op fl), hld,
      hhk _ _ (List.mem_of_getElem? (rmwBody_get0 ty.bits op fl)), hp2⟩
  have hmidC : ∀ y e, RmwHd ty op s y → SameAcc e (loopRd ty s y) → ∀ i, 0 < i →
      i < (rmwLoopMid op ty.bits).length + 1 →
      AtNonRet R (iterN R.step i (patch [e] y)) := by
    intro y e hy he i h0 hi
    obtain ⟨hp1, hp2, hp3⟩ := hy0 y hy [e]
    obtain ⟨x, tc, hj, hh, hnr, -, hpc, -⟩ := rmwBodyAt (ty := ty) (op := op) hR hty hd1 hp1 hp2 hp3 i (by omega)
    exact ⟨j0 + 1 + i, x, tc, hj, hnr, hh, hpc⟩
  have hlastC : ∀ y e, RmwHd ty op s y → SameAcc e (loopRd ty s y) →
      ¬ (fun _ => False) (iterN R.step ((rmwLoopMid op ty.bits).length + 1) (patch [e] y)) →
      AtNonRet R (iterN R.step ((rmwLoopMid op ty.bits).length + 1) (patch [e] y)) := by
    intro y e hy he _
    obtain ⟨hp1, hp2, hp3⟩ := hy0 y hy [e]
    obtain ⟨x, tc, hj, hh, hnr, -, hpc, -⟩ := rmwBodyAt (ty := ty) (op := op) hR hty hd1 hp1 hp2 hp3 ((rmwLoopMid op ty.bits).length + 1) (by omega)
    exact ⟨j0 + 1 + ((rmwLoopMid op ty.bits).length + 1), x, tc, hj, hnr, hh, hpc⟩
  have hcbz : Insn.cbz true true (.x 24) (.loop ps1.aloop) ≠ .ret := by simp
  have hLcbnz : R.L[j0 + ((rmwLoopMid op ty.bits).length + 3)]? =
      some (.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none) :=
    lines_at' hdrop' ((rmwLoopMid op ty.bits).length + 3) _ (by simp [rmwLoopLines, rmwBody_len])
  have hfailC : ∀ y e, RmwHd ty op s y → SameAcc e (loopRd ty s y) →
      ¬ (fun _ => False) (iterN R.step ((rmwLoopMid op ty.bits).length + 1) (patch [e] y)) →
      AtNonRet R (failState 24#5
        (iterN R.step ((rmwLoopMid op ty.bits).length + 1) (patch [e] y))) := by
    intro y e hy he _
    obtain ⟨hp1, hp2, hp3⟩ := hy0 y hy [e]
    obtain ⟨x, tc, hj, hh, hnr, -, hpc, -⟩ := rmwBodyAt (ty := ty) (op := op) hR hty hd1 hp1 hp2 hp3 ((rmwLoopMid op ty.bits).length + 1) (by omega)
    refine ⟨j0 + ((rmwLoopMid op ty.bits).length + 3),
      .cbz true true (.x 24) (.loop ps1.aloop), none, hLcbnz, hcbz, by simp [Insn.hooked], ?_⟩
    rw [pc_failState, hpc, ← RL.pcOf_succ_ins (hatb ((rmwLoopMid op ty.bits).length + 1) _
      (rmwBody_getLast ty.bits op fl)),
      show (j0 + 1 + ((rmwLoopMid op ty.bits).length + 1)) + 1 =
        j0 + ((rmwLoopMid op ty.bits).length + 3) from by omega]
  rcases retry_run_det (P := Policy.arm) (ok := ok) hloop hhd hpatchC hmidC hlastC hfailC
    ls.length ls s mon t' (Nat.le_refl _)
    (loopInv_refl s _ _ _) hr with ⟨hnw, hat⟩ | ⟨q, y1, e, hF, hX⟩
  · exact .inr (.inr (.inr (And.intro (privW_of_noW hnw) hat)))
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
    refine .inl ⟨j0 + (rmwLoopLines ty.bits op fl (.loop ps1.aloop)).length, vb, items,
      pre ++ [.op k (#[Reg.x 25, .x 26, .x 27, .x 24, .x 28].map Loc.reg)], c2, X', _, psm', ps2,
      x, hvb, hit, by rw [hsplit]; simp, hchk', hc2, hX2, hT2, htr, ?_, ?_, ?_, hx, hsc⟩
    · rw [← List.drop_drop, hdrop', List.drop_left]
    · rw [← hxF, Arm.r_of_w_same]
      congr 1
      simp [rmwLoopLines, rmwLoopBody]
      omega
    · refine stRel_after hR hst ?_ ?_ hsw ?_ ?_ ⟨?_, fun a ha => ?_, ?_⟩
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
      · exact hfr2 _ (by simp) (by simp [rnum]) (by simp)
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
      hr2, .inl ⟨hQ, hAI⟩, ?_⟩)
    rw [hs2, List.append_assoc]
    exact img_pair hpos hF.pre rfl rfl hsh (T := [[]]) (by simp)
  · have hls : ls.take (q + ((rmwLoopMid op ty.bits).length + 1) + 1) = ls :=
      List.take_of_length_le (by omega)
    rw [hls] at hseg1
    have hIMG : Img (PrivA R)
        [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩, ⟨.relXW, Arm.r (.GPR 25#5) s, ty.bytes,
          rmwNew ty op (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1)⟩] (evTr ls)
        (fun j => if j = 0 then ((evTr (ls.take q)).length, 0) else
          ((evTr (ls.take q)).length + ((rmwLoopMid op ty.bits).length + 1), 0)) := by
      rw [hseg1, List.append_assoc]
      exact img_pair hpos hF.pre rfl rfl hsh (T := []) (by simp)
    refine .inr (.inr (.inl (And.intro ⟨_, c'', fun j => if j = 0 then ((evTr (ls.take q)).length, 0) else
      ((evTr (ls.take q)).length + ((rmwLoopMid op ty.bits).length + 1), 0), hsrc, hIMG⟩ ?_)))
    · -- the run ends with the final iteration's successful `stlxr`, at the `cbnz` line
      have hlen1 : ls.length = q + ((rmwLoopMid op ty.bits).length + 1) + 1 := by omega
      obtain ⟨mon1, hr1⟩ := hF.run
      obtain ⟨t0, rA, rB⟩ := PRun.split (ls.take (q + ((rmwLoopMid op ty.bits).length + 1)))
        (ls.drop (q + ((rmwLoopMid op ty.bits).length + 1)))
        (by rw [List.take_append_drop]; exact hr)
      obtain rfl := PRun.det rA hr1
      obtain ⟨l, hdl⟩ : ∃ l, ls.drop (q + ((rmwLoopMid op ty.bits).length + 1)) = [l] := by
        have h1 : (ls.drop (q + ((rmwLoopMid op ty.bits).length + 1))).length = 1 := by
          rw [List.length_drop]; omega
        cases hl : ls.drop (q + ((rmwLoopMid op ty.bits).length + 1)) with
        | nil => rw [hl] at h1; simp at h1
        | cons l t =>
          cases t with
          | nil => exact ⟨l, rfl⟩
          | cons _ _ => rw [hl, List.length_cons, List.length_cons] at h1; omega
      rw [hdl] at rB
      cases rB with
      | @cons _ t1 _ _ _ hsB hpB hokB rB' =>
      cases rB'
      rw [h25y] at hwev'
      have hlev : l.evs = [⟨.relXW, Arm.r (.GPR 25#5) s, ty.bytes,
        rmwNew ty op (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1)⟩] := by
        have e1 : (evTr ls)[q + ((rmwLoopMid op ty.bits).length + 1)]? =
            some [⟨.relXW, Arm.r (.GPR 25#5) s, ty.bytes,
              rmwNew ty op (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1)⟩] := by
          rw [hseg1, List.append_assoc, List.getElem?_append,
            if_neg (by simp only [evTr, List.length_map, List.length_take]; omega),
            show (q + ((rmwLoopMid op ty.bits).length + 1)) - (evTr (ls.take q)).length =
              (rmwLoopMid op ty.bits).length + 1 from by
              simp only [evTr, List.length_map, List.length_take]; omega,
            List.getElem?_append,
            if_neg (by rw [segR_length ⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩ (by omega)]; omega),
            segR_length ⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩ (by omega), Nat.sub_self, List.getElem?_cons_zero]
        have e3 : ls[q + ((rmwLoopMid op ty.bits).length + 1)]? = some l := by
          have h4 : (ls.drop (q + ((rmwLoopMid op ty.bits).length + 1)))[0]? = some l := by
            rw [hdl]; simp
          rw [List.getElem?_drop] at h4
          simpa using h4
        have e2 : (evTr ls)[q + ((rmwLoopMid op ty.bits).length + 1)]? = some l.evs := by
          simp only [evTr, List.getElem?_map]
          rw [e3]
          simp
        rw [e2] at e1
        exact Option.some.inj e1
      have hxfB : l.xfail = false := by
        rcases hpB with hx | ⟨M', hM'⟩
        · have hl0 : l.evs = [] := by cases hsB with | exec => cases hx | xfail => rfl
          rw [hlev] at hl0
          exact absurd hl0 (by simp)
        · rw [ArmPrecise.stepEvs_setMem, hwev'] at hM'
          rw [reread_W hW M' (Arm.r (.GPR 25#5) s) ty.bytes
            (rmwNew ty op (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1))] at hM'
          cases hb : l.xfail with
          | false => rfl
          | true =>
            have hl0 : l.evs = [] := by cases hsB with | exec => cases hb | xfail => rfl
            rw [hl0] at hM'
            injection hM'
      obtain ⟨-, htB⟩ := tstep_store hsB hpB hxfB hW hwev'
      rw [htB]
      obtain ⟨t4, hrun4, hint4, -, -, -, -, -⟩ :=
        rmwBody_spec hty op fl (R.envOf (j0 + 1))
          (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1) hp3
      obtain ⟨hit, hpcs, -, -⟩ := run_ins hR hd1 (rmwBody_ins hty op fl) hp1 hp2 hp3 hint4 hrun
      rw [rmwBody_len] at hpcs
      exact ⟨j0 + ((rmwLoopMid op ty.bits).length + 3),
        .cbz true true (.x 24) (.loop ps1.aloop), none, hLcbnz, hcbz, by simp [Insn.hooked],
        by rw [hstep, hpcs, show j0 + 1 + ((rmwLoopMid op ty.bits).length + 2) =
          j0 + ((rmwLoopMid op ty.bits).length + 3) from by omega]⟩

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
    OpOutG R ok (s, mon) (OpC b k allocs its' m w) ls :=
  (rmw_opR hR hq hA hs0 hform hr).out

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

/-! ## The `atomic_cas` loop is a retry loop -/

/-- The heads of the `atomic_cas` loop started at `s`: scratch x24, x27; the flags (the `cmp` sets
them before the `b.ne` reads them). -/
abbrev CasHd (ty : CTy) (s y : ArmState) : Prop := LoopInv s y [24, 27] True ty.bytes

/-- **The `atomic_cas` loop is a retry loop** (`RetryLoop`) on the machine, with heads `CasHd`:
three lines (`ldaxr; cmp; b.ne`) before the `stlxr`, the status register w24, the exit when `ne`
holds (the values differ). -/
theorem cas_retry {R : RL} (hR : R.Wf) {ty : CTy} (hty : AtomTy ty) {fl : Clif.MemFlags}
    {j0 n : Nat} {X : List Line}
    (hdrop : R.L.drop j0 = casLoopLines ty.bits fl (.loop n) (.loop (n + 1)) ++ X)
    {s : ArmState} (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) :
    RetryLoop R.step (CasHd ty s) (loopRd ty s) 3 24#5
      (fun z => Arm.ConditionHolds Cond.ne.bits z = true) := by
  have hL0 : R.L[j0]? = some (.label (.loop n)) := lines_at' hdrop 0 _ rfl
  have hy0 : ∀ y, CasHd ty s y → ∀ E : List Ev,
      (patch E y).program = R.fb.program R.base ∧ Arm.r .PC (patch E y) = R.pcOf (j0 + 1) ∧
        Arm.r .ERR (patch E y) = .None := by
    intro y hy E
    refine ⟨by rw [patch, setMem_program, hy.prog, hprog], ?_, ?_⟩
    · rw [patch, r_setMem, hy.pc, hpc, RL.pcOf_succ_label hL0]
    · rw [patch, r_setMem, hy.err, herr]
  refine ⟨by omega, fun y hy => ?_, fun y hy e he i h0 hi => ?_, fun y hy e he => ?_⟩
  · obtain ⟨hp1, hp2, hp3⟩ := hy0 y hy []
    obtain ⟨s1, -, -, ⟨hev, hns⟩, -⟩ := cas_steps hR hty hdrop hp1 hp2 hp3
    rw [patch_nil, hy.r25 (by decide)] at hev
    rw [patch_nil] at hns
    exact ⟨rfl, atomTy_bytes hty, hev, hns⟩
  · obtain ⟨hp1, hp2, hp3⟩ := hy0 y hy [e]
    obtain ⟨s1, -, hit, -, hcmp, hbne, -⟩ := cas_steps hR hty hdrop hp1 hp2 hp3
    obtain rfl | rfl : i = 1 ∨ i = 2 := by omega
    · exact hcmp
    · rw [hit]; exact hbne
  obtain ⟨k, a, n', v⟩ := e
  obtain ⟨h1, h2, h3⟩ := he
  simp only [loopRd] at h1 h2 h3
  subst h1 h2 h3
  obtain ⟨hp1, hp2, hp3⟩ := hy0 y hy [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩]
  obtain ⟨s1, hrun1, hit, -, -, -, hstepb, hstore⟩ := cas_steps hR hty hdrop hp1 hp2 hp3
  have hz : iterN R.step 3 (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y) = R.step s1 := by
    rw [show 3 = 2 + 1 from rfl, iterN_succ', hit]
  rw [hz, hstepb]
  by_cases hne : Arm.ConditionHolds Cond.ne.bits s1 = true
  · left; rw [condHolds_w_pc]; exact hne
  have hne' : Arm.ConditionHolds Cond.ne.bits s1 = false := by simpa using hne
  right
  rw [hne', ite_eq_right (by simp)]
  refine ⟨by rw [condHolds_w_pc, hne']; simp, ?_⟩
  obtain ⟨s3, -, hstep3, hwev, hcls, hevc, hnsc, -, hevf, hnsf, hstepf⟩ := hstore hne'
  obtain ⟨-, -, -, hfr1, hmem1, hprog1, -⟩ := casHead_spec hty fl (R.envOf (j0 + 1)) _ hp3
  obtain ⟨s1', hrun1', -, -, hfr1', hmem1', hprog1', -⟩ :=
    casHead_spec hty fl (R.envOf (j0 + 1)) _ hp3
  rw [hrun1] at hrun1'
  cases hrun1'
  refine ⟨⟨true, 25#5, hcls⟩, ⟨_, rfl, hwev⟩, ⟨by rw [hstep3]; exact hevc, by rw [hstep3]; exact hnsc⟩,
    ⟨hevf, hnsf⟩, ?_⟩
  rw [hstepf]
  refine ⟨by rw [Arm.r_of_w_same, hpc], fun f h1 h2 h3 => ?_, .inl trivial, fun v' => ?_, ?_⟩
  · rw [Arm.r_of_w_different h1, r_failState _ _ _ h1 (by simpa [rnum] using h2 24 (by simp)),
      Arm.r_of_w_different h1, hfr1' f h1 (by simpa [rnum] using h2 27 (by simp)) h3, patch, r_setMem]
    exact hy.frame f h1 h2 h3
  · rw [ArmState.mem_w_eq_mem, mem_failState, ArmState.mem_w_eq_mem, hmem1', hy.patch_mem,
      writeM_writeM _ _ _ _ _ (atomTy_bytes hty)]
  · rw [Arm.w_program, prog_failState, Arm.w_program, hprog1', patch, setMem_program, hy.prog]

/-! ## The per-item obligation at the `atomic_cas` loop -/

theorem condHolds_of_flags {a b : ArmState} (h : ∀ g, Arm.r (.FLAG g) a = Arm.r (.FLAG g) b)
    (c : BitVec 4) : Arm.ConditionHolds c a = Arm.ConditionHolds c b := by
  unfold Arm.ConditionHolds Arm.read_flag
  rw [h .N, h .Z, h .C, h .V]

theorem patch_wr (e wv : Ev) (hW : wv.k.dir = .W) (w : ArmState) : patch [e, wv] w = patch [e] w := by
  simp only [patch, applyR, hW, show (Dir.W = Dir.R) = False from by simp, ite_false]

set_option maxHeartbeats 8000000 in
/-- **The per-item obligation at the `atomic_cas` loop** (module doc): every precise Arm run from
`Q`-related states goes through failed iterations (reading any bytes, writing nothing) and ends
before a successful `stlxr` or the exit (no write), or its final iteration's `ldaxr` read `e` is
the event of the allocated code's step `[e]` (the values differ: the `b.ne` exit), or `e` and the
successful `stlxr` write `wv` are the events of its step `[e, wv]` (a monitor pair), on the world
world patched with `e`, the states after the item related; a run ending inside the loop (before
the successful `stlxr`'s `cbnz`) is at a line other than `ret`. -/
theorem cas_opR {R : RL} (hR : R.Wf) {ok : ArmState → Lab → Prop} {s : ArmState} {mon : Mon}
    {b k : Nat} {allocs : Array Loc} {its' : List RItem} {m : Loc → CV} {w : ArmState}
    {evs0 : List Ev} {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its' m w)) (hA : AInv R (OpC b k allocs its' m w))
    (hs0 : SrcStep R (OpC b k allocs its' m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i →
      ∃ ty fl ra re rx rd r1, i = .atomicCasLoop ty fl ra re rx rd r1)
    {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm R.step ok (s, mon) ls t') :
    OpOutN R ok (fun c => c.measure) (s, mon) (OpC b k allocs its' m w) ls t' := by
  cases hs0 with
  | @op _ _ _ _ _ _ vb i ops _ _ hvb hi hops0 hevs0 hfoot0 hst0 =>
  obtain ⟨ty, fl, ra, re, rx, rd, r1, rfl⟩ := hform vb i hvb hi
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hok := ctlCheck_inst hck hvb hi
  simp only [ctlInstOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  obtain ⟨va, rfl⟩ := isVregInt_iff h0
  obtain ⟨ve, rfl⟩ := isVregInt_iff h1
  obtain ⟨vx, rfl⟩ := isVregInt_iff h2
  obtain ⟨vd, rfl⟩ := isVregInt_iff h3
  obtain ⟨v1, rfl⟩ := isVregInt_iff h4
  have hk0 : k + 1 < vb.insts.size := lt_size_of_not_term hR hvb hi rfl
  obtain ⟨j0, items, pre, regs, i', c1, c2, X', ls1, ps1, psm, psm', ps2, x, cc, wh, ops, rfl, hit,
    hsplit, hasg, hc1', hops, hstat, hchk', hc2, hl1, hX2, hT2, htr, hdrop, hpc, hst, hx, hsc⟩ :=
    q_op hR hq hvb hi hk0
  rw [hops] at hops0
  cases hops0
  have hops' : ops = #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨ve, .int, .use, .early, .fixed (.x 26)⟩,
      ⟨vx, .int, .use, .early, .fixed (.x 28)⟩, ⟨vd, .int, .def, .late, .fixed (.x 27)⟩,
      ⟨v1, .int, .def, .late, .fixed (.x 24)⟩] := by
    have e : (MInst.atomicCasLoop ty fl (.vreg va .int) (.vreg ve .int) (.vreg vx .int)
        (.vreg vd .int) (.vreg v1 .int)).operands =
        .ok #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨ve, .int, .use, .early, .fixed (.x 26)⟩,
          ⟨vx, .int, .use, .early, .fixed (.x 28)⟩, ⟨vd, .int, .def, .late, .fixed (.x 27)⟩,
          ⟨v1, .int, .def, .late, .fixed (.x 24)⟩] := rfl
    rw [e] at hops; injection hops with h; exact h.symm
  subst hops'
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hstat
  obtain ⟨q0, q1, q2, q3, q4, rfl⟩ := regs5 (by simpa using hsz.symm)
  obtain rfl : q0 = .x 25 := fixed_reg (o := ⟨va, .int, .use, .early, .fixed (.x 25)⟩) hloc (by simp) rfl
  obtain rfl : q1 = .x 26 := fixed_reg (o := ⟨ve, .int, .use, .early, .fixed (.x 26)⟩) hloc (by simp) rfl
  obtain rfl : q2 = .x 28 := fixed_reg (o := ⟨vx, .int, .use, .early, .fixed (.x 28)⟩) hloc (by simp) rfl
  obtain rfl : q3 = .x 27 := fixed_reg (o := ⟨vd, .int, .def, .late, .fixed (.x 27)⟩) hloc (by simp) rfl
  obtain rfl : q4 = .x 24 := fixed_reg (o := ⟨v1, .int, .def, .late, .fixed (.x 24)⟩) hloc (by simp) rfl
  have hasg' : (MInst.atomicCasLoop ty fl (.vreg va .int) (.vreg ve .int) (.vreg vx .int)
      (.vreg vd .int) (.vreg v1 .int)).assign #[.x 25, .x 26, .x 28, .x 27, .x 24] =
      .ok (.atomicCasLoop ty fl (.x 25) (.x 26) (.x 28) (.x 27) (.x 24)) := rfl
  rw [hasg'] at hasg; cases hasg
  obtain rfl : c1 = [.inst (.atomicCasLoop ty fl (.x 25) (.x 26) (.x 28) (.x 27) (.x 24))] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1' := codeLinesE_single hl1
  simp only [MInst.lines, bne_self_eq_false, Bool.or_false, Bool.false_eq_true,
    ite_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1'
  obtain ⟨rfl, rfl⟩ := hl1'
  have hreg : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
    hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
  have hU : (((#[(⟨va, .int, .use, .early, .fixed (.x 25)⟩ : Operand),
      ⟨ve, .int, .use, .early, .fixed (.x 26)⟩, ⟨vx, .int, .use, .early, .fixed (.x 28)⟩,
      ⟨vd, .int, .def, .late, .fixed (.x 27)⟩, ⟨v1, .int, .def, .late, .fixed (.x 24)⟩].zip
      (#[Reg.x 25, .x 26, .x 28, .x 27, .x 24].map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2)) =
      [regVal s (.x 25), regVal s (.x 26), regVal s (.x 28)] := by
    simp [Operand.isUse, hreg (.x 25) rfl, hreg (.x 26) rfl, hreg (.x 28) rfl]
  have herrw : Arm.r .ERR w = .None := by
    rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
  have hnc : ∀ info, MInst.atomicCasLoop ty fl (.vreg va .int) (.vreg ve .int) (.vreg vx .int)
      (.vreg vd .int) (.vreg v1 .int) ≠ .call info := fun _ h => by cases h
  have hnt : ∀ info ti, MInst.atomicCasLoop ty fl (.vreg va .int) (.vreg ve .int) (.vreg vx .int)
      (.vreg vd .int) (.vreg v1 .int) ≠ .tryCall info ti := fun _ _ h => by cases h
  obtain ⟨hty, hav, hk⟩ : AtomTy ty ∧ Avoids R.F ty.bytes (Arm.r (.GPR 25#5) s) ∧ k + 1 < vb.insts.size := by
    cases hst0 with
    | @op _ _ _ _ _ _ vb1 i1 ops1 outs outs' w' ctl m2 c' hvb1 hi1 hops1 hsz1 hsem hlen hho hcl hn =>
    rw [hvb] at hvb1; cases hvb1; rw [hi] at hi1; cases hi1; rw [hops] at hops1; cases hops1
    rw [hU, R.sem_eq hnc hnt] at hsem
    have herrp : Arm.r .ERR (patch evs0 w) = .None := by rw [patch, r_setMem]; exact herrw
    simp only [csem, herrp, ite_true] at hsem
    split at hsem
    · rename_i outs1 t1 c1 hL
      obtain ⟨hty, hav, -, -, -⟩ := loopSem_inv hL
      refine ⟨hty, by rwa [lo64_regVal_x] at hav, ?_⟩
      have : ctl = .next := by
        split at hsem
        · simp only [Option.some.injEq, Prod.mk.injEq] at hsem; exact hsem.2.2.symm
        · exact (loopSem_inv hsem).2.2.2.2
      subst this
      cases hn with
      | next hk => exact hk
    · cases hsem
  have hn0 : 0 < ty.bytes := by rcases hty with rfl | rfl | rfl | rfl <;> decide
  have hbytes := atomTy_bytes hty
  -- the lines
  have hloopCas : relaxLines R.far (casLoopLines ty.bits fl (.loop ps1.aloop)
      (.loop (ps1.aloop + 1))) =
      casLoopLines ty.bits fl (.loop ps1.aloop) (.loop (ps1.aloop + 1)) := relaxLines_loop (by
    rcases hty with rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [casLoopLines, casLoopHead, casLoopCmp, Insn.condTarget?,
        CTy.bits])
  have hdrop' : R.L.drop j0 = casLoopLines ty.bits fl (.loop ps1.aloop) (.loop (ps1.aloop + 1)) ++
      (relaxLines R.far (X' ++ x.2.1) ++ R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) := by
    rw [hdrop, hloopCas]
  have hL0 : R.L[j0]? = some (.label (.loop ps1.aloop)) := lines_at' hdrop' 0 _ rfl
  -- the run
  have hloop := cas_retry hR hty hdrop' hst.prog hpc hst.err
  -- the loop's heads are at unhooked non-`ret` lines (for the runs ending inside the item)
  have hy0 : ∀ y : ArmState, CasHd ty s y → ∀ E : List Ev,
      (patch E y).program = R.fb.program R.base ∧ Arm.r .PC (patch E y) = R.pcOf (j0 + 1) ∧
        Arm.r .ERR (patch E y) = .None := by
    intro y hy E
    refine ⟨by rw [patch, setMem_program, hy.prog, hst.prog], ?_, ?_⟩
    · rw [patch, r_setMem, hy.pc, hpc, RL.pcOf_succ_label hL0]
    · rw [patch, r_setMem, hy.err, hst.err]
  have hatc := lines_at' hdrop'
  have hL1 : R.L[j0 + 1]? = some (.ins (.ldaxr ty.bits (.x 27) (.x 25)) fl.trapCode) :=
    hatc 1 _ (by simp [casLoopLines, casLoopHead])
  have hL2 : R.L[j0 + 2]? = some (.ins (casLoopCmp ty.bits)) :=
    hatc 2 _ (by simp [casLoopLines, casLoopHead])
  have hL3 : R.L[j0 + 3]? = some (.ins (.bcond .ne (.loop (ps1.aloop + 1))) none) :=
    hatc 3 _ (by simp [casLoopLines, casLoopHead])
  have hL4 : R.L[j0 + 4]? = some (.ins (.stlxr ty.bits (.x 24) (.x 28) (.x 25)) fl.trapCode) :=
    hatc 4 _ (by simp [casLoopLines, casLoopHead])
  have hL5 : R.L[j0 + 5]? = some (.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none) :=
    hatc 5 _ (by simp [casLoopLines, casLoopHead])
  have hpcy : ∀ y, CasHd ty s y → Arm.r .PC y = R.pcOf (j0 + 1) := by
    intro y hy
    obtain ⟨-, hp2, -⟩ := hy0 y hy []
    rw [patch_nil] at hp2
    exact hp2
  have hhd : ∀ y, CasHd ty s y → AtNonRet R y := fun y hy =>
    ⟨j0 + 1, .ldaxr ty.bits (.x 27) (.x 25), fl.trapCode, hL1, by simp, by simp [Insn.hooked],
      hpcy y hy⟩
  have hpatchC : ∀ y e, CasHd ty s y → SameAcc e (loopRd ty s y) → AtNonRet R (patch [e] y) :=
    fun y e hy _ =>
      ⟨j0 + 1, .ldaxr ty.bits (.x 27) (.x 25), fl.trapCode, hL1, by simp, by simp [Insn.hooked],
        (hy0 y hy [e]).2.1⟩
  have hd1' : R.L.drop (j0 + 1) = casLoopHead ty.bits fl ++
      (.ins (.bcond .ne (.loop (ps1.aloop + 1))) none ::
        .ins (.stlxr ty.bits (.x 24) (.x 28) (.x 25)) fl.trapCode ::
        .ins (.cbz true true (.x 24) (.loop ps1.aloop)) none ::
        .label (.loop (ps1.aloop + 1)) ::
          (relaxLines R.far (X' ++ x.2.1) ++
            R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2))) := by
    rw [← List.drop_drop, hdrop']; simp [casLoopLines, casLoopHead]
  have hmidC : ∀ y e, CasHd ty s y → SameAcc e (loopRd ty s y) → ∀ i, 0 < i → i < 3 →
      AtNonRet R (iterN R.step i (patch [e] y)) := by
    intro y e hy he i h0 hi
    obtain ⟨hp1, hp2, hp3⟩ := hy0 y hy [e]
    obtain ⟨s1, hrun1, hint1, -, -, -, -, -⟩ := casHead_spec hty fl (R.envOf (j0 + 1))
      (patch [e] y) hp3
    obtain ⟨hit1, hpcs1, -, -⟩ := run_ins hR hd1' (casHead_ins ty.bits fl) hp1 hp2 hp3 hint1 hrun1
    have hhk1 : ∀ x t, Line.ins x t ∈ casLoopHead ty.bits fl → x.hooked = false := by
      intro x t h
      obtain ⟨x', t', e', hh⟩ := casHead_ins ty.bits fl _ h; cases e'; exact hh
    have hpcI : ∀ j ≤ 2, Arm.r .PC (iterN R.step j (patch [e] y)) = R.pcOf (j0 + 1 + j) :=
      fun j hj => iterN_execLines_pc hR.layout hR.lm hR.fit (casLoopHead ty.bits fl) (j0 + 1)
        (patch [e] y) s1 (lines_at' hd1') hhk1 hp1 hp2 hp3 hint1 hrun1 j hj
    have h12 : i = 1 ∨ i = 2 := by omega
    rcases h12 with rfl | rfl
    · exact ⟨j0 + 2, casLoopCmp ty.bits, none, hL2, casLoopCmp_ne_ret _,
        hhk1 (casLoopCmp ty.bits) none (by simp [casLoopHead]), hpcI 1 (by omega)⟩
    · exact ⟨j0 + 3, .bcond .ne (.loop (ps1.aloop + 1)), none, hL3, by simp,
        by simp [Insn.hooked], hpcI 2 (by omega)⟩
  have hlastC : ∀ y e, CasHd ty s y → SameAcc e (loopRd ty s y) →
      ¬ (fun z => Arm.ConditionHolds Cond.ne.bits z = true)
        (iterN R.step 3 (patch [e] y)) →
      AtNonRet R (iterN R.step 3 (patch [e] y)) := by
    intro y e hy he hnEx
    obtain ⟨hp1, hp2, hp3⟩ := hy0 y hy [e]
    obtain ⟨s1, hrun1, hit1, -, -, -, hstepb, -⟩ := cas_steps hR hty hdrop' hp1 hp2 hp3
    have hz3 : iterN R.step 3 (patch [e] y) = R.step s1 := by
      rw [show 3 = 2 + 1 from rfl, iterN_succ', hit1]
    have hcond : Arm.ConditionHolds Cond.ne.bits s1 = false := by
      rw [hz3, hstepb] at hnEx
      simp only [condHolds_w_pc] at hnEx
      simpa using hnEx
    rw [hz3, hstepb, hcond, if_neg (by simp)]
    exact ⟨j0 + 4, .stlxr ty.bits (.x 24) (.x 28) (.x 25), fl.trapCode, hL4, by simp,
      by simp [Insn.hooked], Arm.r_of_w_same ..⟩
  have hfailC : ∀ y e, CasHd ty s y → SameAcc e (loopRd ty s y) →
      ¬ (fun z => Arm.ConditionHolds Cond.ne.bits z = true)
        (iterN R.step 3 (patch [e] y)) →
      AtNonRet R (failState 24#5 (iterN R.step 3 (patch [e] y))) := by
    intro y e hy he hnEx
    obtain ⟨hp1, hp2, hp3⟩ := hy0 y hy [e]
    obtain ⟨s1, hrun1, hit1, -, -, -, hstepb, -⟩ := cas_steps hR hty hdrop' hp1 hp2 hp3
    have hz3 : iterN R.step 3 (patch [e] y) = R.step s1 := by
      rw [show 3 = 2 + 1 from rfl, iterN_succ', hit1]
    have hcond : Arm.ConditionHolds Cond.ne.bits s1 = false := by
      rw [hz3, hstepb] at hnEx
      simp only [condHolds_w_pc] at hnEx
      simpa using hnEx
    refine ⟨j0 + 5, .cbz true true (.x 24) (.loop ps1.aloop), none, hL5, by simp,
      by simp [Insn.hooked], ?_⟩
    rw [pc_failState, hz3, hstepb, hcond, if_neg (by simp), Arm.r_of_w_same,
      show (j0 + 4) + 1 = j0 + 5 from rfl, RL.pcOf_succ_ins hL4]
  rcases retry_run_det (P := Policy.arm) (ok := ok) hloop hhd hpatchC hmidC hlastC hfailC
    ls.length ls s mon t' (Nat.le_refl _)
    (loopInv_refl s _ _ _) hr with ⟨hnw, hat⟩ | ⟨q, y1, e, hF, hX⟩
  · exact .inr (.inr (.inr (And.intro (privW_of_noW hnw) hat)))
  -- the final iteration: its read `e`
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
  obtain ⟨s1, hrun1, hit1, -, -, -, hstepb, hstore⟩ := cas_steps hR hty hdrop' hp1 hp2 hp3
  obtain ⟨s1', hrun1', -, -, hfr1, hmem1, hprog1, -⟩ := casHead_spec hty fl (R.envOf (j0 + 1)) _ hp3
  rw [hrun1] at hrun1'
  cases hrun1'
  have hz : iterN R.step 3 (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1) = R.step s1 := by
    rw [show 3 = 2 + 1 from rfl, iterN_succ', hit1]
  have hyr : ∀ q, q < 32 → q ≠ 24 → q ≠ 27 →
      Arm.r (.GPR (rnum q)) (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1) =
        Arm.r (.GPR (rnum q)) s := by
    intro q hq h24 h27
    rw [patch, r_setMem]
    exact hy1.frame _ (by simp) (fun q' hq' e => by
      have e' : rnum q = rnum q' := by injection e
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact rnum_ne hq (by decide) h24 e'
      · exact rnum_ne hq (by decide) h27 e') (by simp)
  have hs1r : ∀ q, q < 32 → q ≠ 24 → q ≠ 27 → Arm.r (.GPR (rnum q)) s1 = Arm.r (.GPR (rnum q)) s := by
    intro q hq h24 h27
    rw [hfr1 _ (by simp) (fun r hr e => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      have e' : rnum q = rnum 27 := by injection e
      exact rnum_ne hq (by decide) h27 e') (by simp)]
    exact hyr q hq h24 h27
  -- the allocated code's world patched with the final read
  generalize hW0 : patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] w = W
  have hWmem : W.mem = writeM ty.bytes (Arm.r (.GPR 25#5) s) v w.mem := by
    rw [← hW0]; simp [patch, applyR, AKind.dir]
  have hWerr : Arm.r .ERR W = .None := by rw [← hW0, patch, r_setMem, herrw]
  generalize hWt : ([Reg.x 25, .x 26, .x 28].zip [regVal s (.x 25), regVal s (.x 26), regVal s (.x 28)]).foldl
    (fun s p => setReg s p.1 p.2) W = Wt
  have hWtr : ∀ q, q = 25 ∨ q = 26 ∨ q = 28 → Arm.r (.GPR (rnum q)) Wt = Arm.r (.GPR (rnum q)) s := by
    intro q hq
    rw [← hWt]
    rcases hq with rfl | rfl | rfl <;>
      simp [setReg, rnum, Arm.r_of_w_same, Arm.r_of_w_different, lo64_regVal_x]
  have hWtoth : ∀ f, f ≠ .GPR 25#5 → f ≠ .GPR 26#5 → f ≠ .GPR 28#5 → Arm.r f Wt = Arm.r f W := by
    intro f h1 h2 h3; rw [← hWt]
    simp [setReg, rnum, Arm.r_of_w_different h1, Arm.r_of_w_different h2, Arm.r_of_w_different h3]
  have hWtmem : Wt.mem = W.mem := by rw [← hWt, foldl_setReg_mem]
  have hWtprog : Wt.program = W.program := by rw [← hWt]; simp [setReg, Arm.w_program]
  have hWterr : Arm.r .ERR Wt = .None := by rw [hWtoth _ (by simp) (by simp) (by simp), hWerr]
  obtain ⟨t1, hrunt, -, -, hfrt, hmemt, hprogt, -⟩ := casHead_spec hty fl env0 Wt hWterr
  have hrd : readM ty.bytes (Arm.r (.GPR 25#5) s) Wt.mem = v := by
    rw [hWtmem, hWmem, readM_writeM _ _ _ _ hbytes]
  have hrdy : readM ty.bytes (Arm.r (.GPR 25#5) s)
      (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1).mem = v := by
    rw [hy1.patch_mem, readM_writeM _ _ _ _ hbytes]
  have h25W : Arm.r (.GPR 25#5) Wt = Arm.r (.GPR 25#5) s := hWtr 25 (.inl rfl)
  have h25y : Arm.r (.GPR 25#5) (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1) =
      Arm.r (.GPR 25#5) s := hyr 25 (by decide) (by decide) (by decide)
  have h26W : Arm.r (.GPR 26#5) Wt = Arm.r (.GPR 26#5) s := hWtr 26 (.inr (.inl rfl))
  have h26y : Arm.r (.GPR 26#5) (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1) =
      Arm.r (.GPR 26#5) s := hyr 26 (by decide) (by decide) (by decide)
  have h28W : Arm.r (.GPR 28#5) Wt = Arm.r (.GPR 28#5) s := hWtr 28 (.inr (.inr rfl))
  have h25s1 : Arm.r (.GPR 25#5) s1 = Arm.r (.GPR 25#5) s := hs1r 25 (by decide) (by decide) (by decide)
  have h28s1 : Arm.r (.GPR 28#5) s1 = Arm.r (.GPR 28#5) s := hs1r 28 (by decide) (by decide) (by decide)
  obtain ⟨hflag, h27eq⟩ := casHead_dep hty fl (R.envOf (j0 + 1)) env0
    (t1 := patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1) (t2 := Wt)
    (by rw [h25y, h25W]) (by rw [h26y, h26W])
    (by rw [h25W, read_mem_bytes_eq, read_mem_bytes_eq, hrd, hrdy]) hrun1 hrunt
  have hcond : Arm.ConditionHolds Cond.ne.bits s1 = Arm.ConditionHolds Cond.ne.bits t1 :=
    condHolds_of_flags hflag _
  have hav' : Avoids R.F ty.bytes (lo64 (regVal s (.x 25))) := by rw [lo64_regVal_x]; exact hav
  have ht1err : Arm.r .ERR t1 = .None := by rw [hfrt .ERR (by simp) (by simp) (by simp)]; exact hWterr
  have hsemH : loopSem R.F ty (regVal s (.x 25)) (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28]
      [regVal s (.x 25), regVal s (.x 26), regVal s (.x 28)] [.x 27, .x 24] W =
      some ([regVal t1 (.x 27), ofX 0], t1, .next) := by
    unfold loopSem
    rw [hWt, ite_eq_left ⟨hty, hav', hWerr⟩, hrunt]
    simp [ht1err, hprogt, hWtprog]
  have hevH : loopEvs (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28]
      [regVal s (.x 25), regVal s (.x 26), regVal s (.x 28)] W =
      [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] := by
    unfold loopEvs
    rw [hWt, casHead_shape hty fl env0 Wt hWterr, h25W, hrd]
  -- `Q` at the next item, from a machine state after the loop
  have fin : ∀ (E : List Ev) (sF wF : ArmState) (outsF : List CV), (∀ ev ∈ E, Avoids R.F ev.n ev.addr) →
      patch E w = W →
      R.sem (.atomicCasLoop ty fl (.vreg va .int) (.vreg ve .int) (.vreg vx .int) (.vreg vd .int)
        (.vreg v1 .int)) [regVal s (.x 25), regVal s (.x 26), regVal s (.x 28)] W =
        some (outsF, wF, .next) →
      outsF.length = 2 → [regVal sF (.x 27)] = outsF.take 1 →
      Arm.r .PC sF = R.pcOf (j0 + 7) → SameWorld R.F sF wF →
      (∀ f, f ≠ .PC → (∀ n ∈ [27, 24], f ≠ .GPR (rnum n)) → (∀ g, f ≠ .FLAG g) →
        Arm.r f sF = Arm.r f s) →
      (∀ a, R.F a → sF.mem a = s.mem a) → sF.program = s.program →
      ∃ c'', MStep R.vc R.sem ckeep R.rf
        (.run ⟨b, .op k (#[Reg.x 25, .x 26, .x 28, .x 27, .x 24].map Loc.reg) :: its', m, W⟩) c'' ∧
        Q R sF c'' ∧ AInv R c'' := by
    intro E sF wF outsF hEav hEW hsemF hlen2 h27F hpcF hswF hfrF hmemF hprogF
    obtain ⟨c'', hm, hQ⟩ : ∃ c'', MStep R.vc R.sem ckeep R.rf
        (.run ⟨b, .op k (#[Reg.x 25, .x 26, .x 28, .x 27, .x 24].map Loc.reg) :: its', m, W⟩) c'' ∧
        Q R sF c'' := by
      refine ⟨_, MStep.op (outs' := [regVal sF (.x 27), regVal sF (.x 24)]) (m2 := m) hvb hi hops
        (by simp) (by rw [hU]; exact hsemF) (by rw [hlen2]; simp [Operand.isDef])
        ⟨by simp [hlen2], fun h => by simp [havocFrom, MInst.keptDefs] at h, fun n h => ?_⟩ ?_
        (MNext.next hk), ?_⟩
      · simp only [havocFrom, MInst.keptDefs, Option.some.injEq] at h
        subst h
        simpa using h27F
      · refine ⟨fun l _ => ?_, fun c hc => by simp [MInst.clobbers] at hc⟩
        simp [Backend.Proof.writeM, Operand.isDef, Operand.isEarly]
      refine .inl ⟨j0 + 7, vb, items,
        pre ++ [.op k (#[Reg.x 25, .x 26, .x 28, .x 27, .x 24].map Loc.reg)], c2, X', _, psm', ps2, x,
        hvb, hit, by rw [hsplit]; simp, hchk', hc2, hX2, hT2, htr, ?_, hpcF, ?_, hx, hsc⟩
      · rw [← List.drop_drop, hdrop']
        exact List.drop_left' (by simp [casLoopLines, casLoopHead])
      · refine stRel_after hR hst ?_ ?_ hswF ?_ hprogF ⟨?_, fun a ha => hmemF a (RL.FK_F ha), ?_⟩
        · refine store_regs hst [27, 24] (by simp) ?_ ?_ hfrF
          · intro n hn
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
            rcases hn with rfl | rfl <;> simp [Backend.Proof.writeM, upd, Operand.isDef, Operand.isLate]
          · intro r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
            simp [Backend.Proof.writeM, upd, Operand.isDef, Operand.isLate, hr.1, hr.2]
        · intro l hl
          simp [Backend.Proof.writeM, upd, Operand.isDef, Operand.isLate, hl]
        · rw [hfrF .ERR (by simp) (by simp) (by simp)]; exact hst.err
        · simp only [spOf]; exact hfrF _ (by simp) (by simp [rnum]) (by simp)
        · exact hfrF _ (by simp) (by simp [rnum]) (by simp)
    exact ⟨c'', hm, hQ, aInv_step hR (q_patch hR hq hEav) (aInv_patch hA _) (by rw [hEW]; exact hm)⟩
  -- the machine's fields after the head, against the allocated code's after its head
  have hnm : ∀ f, ¬ Masked f → f ≠ .PC ∧ (∀ n ∈ [27, 24], f ≠ .GPR (rnum n)) ∧
      f ≠ .GPR 25#5 ∧ f ≠ .GPR 26#5 ∧ f ≠ .GPR 28#5 := by
    intro f hf
    refine ⟨fun h => hf (by subst h; simp [Masked]), fun n hn h => hf ?_, fun h => hf (by subst h; simp [Masked]),
      fun h => hf (by subst h; simp [Masked]), fun h => hf (by subst h; simp [Masked])⟩
    subst h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl <;> simp [Masked, rnum]
  have hfs1 : ∀ f, f ≠ .PC → (∀ n ∈ [27, 24], f ≠ .GPR (rnum n)) → (∀ g, f ≠ .FLAG g) →
      Arm.r f s1 = Arm.r f s := by
    intro f h1 h2 h3
    rw [hfr1 f h1 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simpa [rnum] using h2 27 (by simp)) h3, patch,
      r_setMem]
    exact hy1.frame f h1 (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact h2 24 (by simp)
      · exact h2 27 (by simp)) h3
  have hft1 : ∀ f, ¬ Masked f → (∀ g, f ≠ .FLAG g) → Arm.r f t1 = Arm.r f s := by
    intro f hf h3
    obtain ⟨h1, h2, h25, h26, h28⟩ := hnm f hf
    rw [hfrt f h1 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simpa [rnum] using h2 27 (by simp)) h3,
      hWtoth f h25 h26 h28, ← hW0, patch,
      r_setMem]
    exact (hst.world.1 f hf).symm
  have hmems1 : s1.mem = writeM ty.bytes (Arm.r (.GPR 25#5) s) v s.mem := by
    rw [hmem1, hy1.patch_mem]
  have hmemt1 : t1.mem = writeM ty.bytes (Arm.r (.GPR 25#5) s) v w.mem := by
    rw [hmemt, hWtmem, hWmem]
  have hprogs1 : s1.program = s.program := by rw [hprog1, patch, setMem_program, hy1.prog]
  have hprogt1 : t1.program = w.program := by rw [hprogt, hWtprog, ← hW0, patch, setMem_program]
  have hout : ∀ a, R.F a → ∀ q < ty.bytes, Arm.r (.GPR 25#5) s + BitVec.ofNat 64 q ≠ a :=
    fun a ha q hq e => hav q hq (by rw [e]; exact ha)
  have hsh1 : ∀ x ∈ [(⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩ : Ev)],
      x.k.dir ≠ .F → ¬ PrivA R x.addr.toNat := by
    intro x hx _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; exact privA_of_avoid hav hn0
  rcases hX with hex | ⟨hnx, -, hle1, wv, hW, hwv, hseg1, hseg2⟩
  · -- the values differ: the `b.ne` leaves the loop after the head
    rw [hz, hstepb, condHolds_w_pc] at hex
    have hne1 : Arm.ConditionHolds Cond.ne.bits t1 = true := hcond ▸ hex
    have hsemE : R.sem (.atomicCasLoop ty fl (.vreg va .int) (.vreg ve .int) (.vreg vx .int)
        (.vreg vd .int) (.vreg v1 .int)) [regVal s (.x 25), regVal s (.x 26), regVal s (.x 28)] W =
        some ([regVal t1 (.x 27), ofX 0], t1, .next) := by
      rw [R.sem_eq hnc hnt]
      simp only [csem, hWerr, ite_true]
      rw [hsemH]
      simp only [hne1, ite_true]
    have hevE : casEvs R.F ty fl (regVal s (.x 25)) (regVal s (.x 26)) (regVal s (.x 28)) W =
        [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] := by
      unfold casEvs
      rw [hsemH]
      simp only [hne1, ite_true]
      exact hevH
    generalize hzF : Arm.w .PC (R.pcOf (j0 + 7)) s1 = zF
    have hfzF : ∀ f, f ≠ .PC → Arm.r f zF = Arm.r f s1 := fun f h => by rw [← hzF, Arm.r_of_w_different h]
    have hswF : SameWorld R.F zF t1 := by
      refine ⟨fun f hf => ?_, fun a ha => ?_, ?_⟩
      · obtain ⟨h1, h2, -⟩ := hnm f hf
        rw [hfzF f h1]
        by_cases hfl : ∃ g, f = .FLAG g
        · obtain ⟨g, rfl⟩ := hfl; exact hflag g
        · have h3 : ∀ g, f ≠ .FLAG g := fun g h => hfl ⟨g, h⟩
          rw [hfs1 f h1 h2 h3, hft1 f hf h3]
      · rw [← hzF, ArmState.mem_w_eq_mem, hmems1, hmemt1]
        exact writeM_pt _ _ _ (hst.world.2.1 a ha)
      · rw [← hzF, Arm.w_program, hprogs1, hprogt1]; exact hst.world.2.2
    obtain ⟨c'', hm, hQ, hAI⟩ := fin [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] zF t1 _
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; exact hav)
      hW0 hsemE rfl (by
        have h27z : Arm.r (.GPR 27#5) zF = Arm.r (.GPR 27#5) t1 := by
          rw [hfzF _ (by simp)]; exact h27eq
        simp [regVal, rnum, h27z])
      (by rw [← hzF, Arm.r_of_w_same]) hswF
      (fun f h1 h2 h3 => by rw [hfzF f h1]; exact hfs1 f h1 h2 h3)
      (fun a ha => by rw [← hzF, ArmState.mem_w_eq_mem, hmems1, writeM_apply_out _ _ _ _ _ (hout a ha)])
      (by rw [← hzF, Arm.w_program, hprogs1])
    have hsrc : SrcStep R (OpC b k (#[Reg.x 25, .x 26, .x 28, .x 27, .x 24].map Loc.reg) its' m w)
        [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] c'' := by
      refine .op hvb hi hops ?_ ?_ (by rw [hW0]; exact hm)
      · rw [hW0]
        show _ = cEvs R.F R.ctx _ (((_ : Array Operand).zip _).toList.filter (·.1.isUse) |>.map (m ·.2)) W
        rw [hU]
        unfold cEvs
        simp only [MInst.isCtl, ite_true]
        exact hevE.symm
      · rw [hW0]
        show IFoot R.sem _ (((_ : Array Operand).zip _).toList.filter (·.1.isUse) |>.map (m ·.2)) W _
        rw [hU]
        have hf := casEvs_foot (F := R.F) (ctx := R.ctx) (X := R.X) (ra := .vreg va .int)
          (re := .vreg ve .int) (rx := .vreg vx .int) (rd := .vreg vd .int) (rs := .vreg v1 .int)
          (u := regVal s (.x 25)) (e := regVal s (.x 26)) (x := regVal s (.x 28)) (ty := ty) (fl := fl)
          hWerr
        rw [hevE] at hf
        refine ⟨hf.1, fun m' hm' => ?_⟩
        rw [R.sem_eq hnc hnt, R.sem_eq hnc hnt]
        exact hf.2 m' hm'
    obtain ⟨mon1, hr1⟩ := hF.run
    rw [hz, hstepb] at hr1
    simp only [hex, ite_true, hzF] at hr1
    refine .inr (.inl ⟨q + 3, _, c'', (zF, mon1), fun _ => ((evTr (ls.take q)).length, 0), hF.le,
      .inl (by omega), hsrc, hr1, .inl ⟨hQ, hAI⟩, ?_⟩)
    rw [hF.seg]
    exact img_one (by omega) hF.pre rfl (by simp) hsh1
  -- equal values: the `stlxr` succeeds, then the `cbnz` falls through
  simp only [hz, hstepb, condHolds_w_pc] at hnx
  have hne' : Arm.ConditionHolds Cond.ne.bits s1 = false := by simpa using hnx
  have hne1 : Arm.ConditionHolds Cond.ne.bits t1 = false := hcond ▸ hne'
  obtain ⟨s3, hrun3, hstep3, hwevA, -, -, -, hstepc, -⟩ := hstore hne'
  simp only [hz, hstepb, hne', Bool.false_eq_true, ite_false] at hwv
  rw [hwevA, h25s1, h28s1] at hwv
  simp only [List.cons.injEq, and_true] at hwv
  subst hwv
  simp only [hz, hstepb, hne', Bool.false_eq_true, ite_false] at hseg2
  generalize hzS : Arm.w .PC (R.pcOf (j0 + 4)) s1 = zS at hrun3 hstep3 hstepc hseg2
  have hfzS : ∀ f, f ≠ .PC → Arm.r f zS = Arm.r f s1 := fun f h => by rw [← hzS, Arm.r_of_w_different h]
  have herrzS : Arm.r .ERR zS = .None := by
    rw [hfzS _ (by simp), hfs1 _ (by simp) (by simp) (by simp)]; exact hst.err
  obtain ⟨s3', hrun3', -, hfr3, hmem3, hprog3⟩ := stlxr_spec hty fl (R.envOf (j0 + 4)) zS herrzS
  simp only [casStore] at hrun3
  rw [hrun3] at hrun3'
  cases hrun3'
  obtain ⟨w2, hrunw2, -, hfrw2, hmemw2, hprogw2⟩ := stlxr_spec hty fl env0 t1 ht1err
  have hw2err : Arm.r .ERR w2 = .None := by rw [hfrw2 .ERR (by simp) (by simp)]; exact ht1err
  have hsemS : R.sem (.atomicCasLoop ty fl (.vreg va .int) (.vreg ve .int) (.vreg vx .int)
      (.vreg vd .int) (.vreg v1 .int)) [regVal s (.x 25), regVal s (.x 26), regVal s (.x 28)] W =
      some ([regVal w2 (.x 27), ofX 0], w2, .next) := by
    rw [R.sem_eq hnc hnt]
    simp only [csem, hWerr, ite_true]
    rw [hsemH]
    simp only [hne1, Bool.false_eq_true, ite_false]
    unfold loopSem
    rw [ite_eq_left ⟨hty, hav', ht1err⟩]
    simp only [List.zip_nil_left, List.foldl_nil]
    rw [hrunw2]
    simp [hw2err, hprogw2]
  have h25t1 : Arm.r (.GPR 25#5) t1 = Arm.r (.GPR 25#5) s := by
    rw [hfrt _ (by simp) (by simp) (by simp)]; exact h25W
  have h28t1 : Arm.r (.GPR 28#5) t1 = Arm.r (.GPR 28#5) s := by
    rw [hfrt _ (by simp) (by simp) (by simp)]; exact h28W
  have hevS : casEvs R.F ty fl (regVal s (.x 25)) (regVal s (.x 26)) (regVal s (.x 28)) W =
      [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩, ⟨.relXW, Arm.r (.GPR 25#5) s, ty.bytes,
        (Arm.r (.GPR 28#5) s).setWidth (ty.bytes * 8)⟩] := by
    unfold casEvs
    rw [hsemH]
    simp only [hne1, Bool.false_eq_true, ite_false]
    rw [hevH]
    unfold loopEvs
    simp only [List.zip_nil_left, List.foldl_nil]
    rw [casStore_evsEq hty fl, h25t1, h28t1]
    rfl
  -- the machine after the loop
  generalize hxF : Arm.w .PC (R.pcOf (j0 + 7)) s3 = xF at hstepc
  have hfx : ∀ f, f ≠ .PC → f ≠ .GPR 24#5 → Arm.r f xF = Arm.r f s1 := fun f h1 h2 => by
    rw [← hxF, Arm.r_of_w_different h1, hfr3 f h1 h2, hfzS f h1]
  have hfx' : ∀ f, f ≠ .PC → (∀ n ∈ [27, 24], f ≠ .GPR (rnum n)) → (∀ g, f ≠ .FLAG g) →
      Arm.r f xF = Arm.r f s := fun f h1 h2 h3 => by
    rw [hfx f h1 (by simpa [rnum] using h2 24 (by simp))]; exact hfs1 f h1 h2 h3
  have h25zS : Arm.r (.GPR 25#5) zS = Arm.r (.GPR 25#5) s := by rw [hfzS _ (by simp), h25s1]
  have h28zS : Arm.r (.GPR 28#5) zS = Arm.r (.GPR 28#5) s := by rw [hfzS _ (by simp), h28s1]
  have hmemzS : zS.mem = writeM ty.bytes (Arm.r (.GPR 25#5) s) v s.mem := by
    rw [← hzS, ArmState.mem_w_eq_mem, hmems1]
  have hmemx : xF.mem = writeM ty.bytes (Arm.r (.GPR 25#5) s)
      ((Arm.r (.GPR 28#5) s).setWidth (ty.bytes * 8)) (writeM ty.bytes (Arm.r (.GPR 25#5) s) v s.mem) := by
    rw [← hxF, ArmState.mem_w_eq_mem, hmem3, write_mem_bytes_eq, setMem_mem, h25zS, h28zS, hmemzS]
  have hmemw2' : w2.mem = writeM ty.bytes (Arm.r (.GPR 25#5) s)
      ((Arm.r (.GPR 28#5) s).setWidth (ty.bytes * 8)) (writeM ty.bytes (Arm.r (.GPR 25#5) s) v w.mem) := by
    rw [hmemw2, write_mem_bytes_eq, setMem_mem, h25t1, h28t1, hmemt1]
  have hswF : SameWorld R.F xF w2 := by
    refine ⟨fun f hf => ?_, fun a ha => ?_, ?_⟩
    · obtain ⟨h1, h2, -⟩ := hnm f hf
      rw [hfx f h1 (by simpa [rnum] using h2 24 (by simp)),
        hfrw2 f h1 (by simpa [rnum] using h2 24 (by simp))]
      by_cases hfl : ∃ g, f = .FLAG g
      · obtain ⟨g, rfl⟩ := hfl; exact hflag g
      · have h3 : ∀ g, f ≠ .FLAG g := fun g h => hfl ⟨g, h⟩
        rw [hfs1 f h1 h2 h3, hft1 f hf h3]
    · rw [hmemx, hmemw2']
      exact writeM_pt _ _ _ (writeM_pt _ _ _ (hst.world.2.1 a ha))
    · rw [← hxF, Arm.w_program, hprog3, ← hzS, Arm.w_program, hprogs1, hprogw2, hprogt1]
      exact hst.world.2.2
  have hEav : ∀ x ∈ [(⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩ : Ev), ⟨.relXW, Arm.r (.GPR 25#5) s,
      ty.bytes, (Arm.r (.GPR 28#5) s).setWidth (ty.bytes * 8)⟩], Avoids R.F x.n x.addr := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact hav
  have hpw : patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩, ⟨.relXW, Arm.r (.GPR 25#5) s,
      ty.bytes, (Arm.r (.GPR 28#5) s).setWidth (ty.bytes * 8)⟩] w = W := by
    rw [patch_wr _ _ rfl, hW0]
  obtain ⟨c'', hm, hQ, hAI⟩ := fin _ xF w2 _ hEav hpw hsemS rfl (by
      have h27x : Arm.r (.GPR 27#5) xF = Arm.r (.GPR 27#5) w2 := by
        rw [hfx _ (by simp) (by simp), h27eq, hfrw2 _ (by simp) (by simp)]
      simp [regVal, rnum, h27x])
    (by rw [← hxF, Arm.r_of_w_same]) hswF hfx'
    (fun a ha => by
      rw [hmemx, writeM_apply_out _ _ _ _ _ (hout a ha), writeM_apply_out _ _ _ _ _ (hout a ha)])
    (by rw [← hxF, Arm.w_program, hprog3, ← hzS, Arm.w_program, hprogs1])
  have hsrc : SrcStep R (OpC b k (#[Reg.x 25, .x 26, .x 28, .x 27, .x 24].map Loc.reg) its' m w)
      [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩, ⟨.relXW, Arm.r (.GPR 25#5) s,
        ty.bytes, (Arm.r (.GPR 28#5) s).setWidth (ty.bytes * 8)⟩] c'' := by
    refine .op hvb hi hops ?_ ?_ (by rw [hpw]; exact hm)
    · rw [hpw]
      show _ = cEvs R.F R.ctx _ (((_ : Array Operand).zip _).toList.filter (·.1.isUse) |>.map (m ·.2)) W
      rw [hU]
      unfold cEvs
      simp only [MInst.isCtl, ite_true]
      exact hevS.symm
    · rw [hpw]
      show IFoot R.sem _ (((_ : Array Operand).zip _).toList.filter (·.1.isUse) |>.map (m ·.2)) W _
      rw [hU]
      have hf := casEvs_foot (F := R.F) (ctx := R.ctx) (X := R.X) (ra := .vreg va .int)
        (re := .vreg ve .int) (rx := .vreg vx .int) (rd := .vreg vd .int) (rs := .vreg v1 .int)
        (u := regVal s (.x 25)) (e := regVal s (.x 26)) (x := regVal s (.x 28)) (ty := ty) (fl := fl)
        hWerr
      rw [hevS] at hf
      refine ⟨hf.1, fun m' hm' => ?_⟩
      rw [R.sem_eq hnc hnt, R.sem_eq hnc hnt]
      exact hf.2 m' hm'
  have hsh : ∀ x ∈ [(⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩ : Ev), ⟨.relXW, Arm.r (.GPR 25#5) s,
      ty.bytes, (Arm.r (.GPR 28#5) s).setWidth (ty.bytes * 8)⟩],
      x.k.dir ≠ .F → ¬ PrivA R x.addr.toNat := by
    intro x hx _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact privA_of_avoid hav hn0
  by_cases h2 : q + 3 + 2 ≤ ls.length
  · obtain ⟨hs2, mon2, hr2⟩ := hseg2 h2
    rw [hstep3, hstepc] at hr2
    refine .inr (.inl ⟨_, _, c'', (xF, mon2), fun j => if j = 0 then ((evTr (ls.take q)).length, 0) else
      ((evTr (ls.take q)).length + 3, 0), h2, .inl (by omega), hsrc, hr2, .inl ⟨hQ, hAI⟩, ?_⟩)
    rw [hs2, List.append_assoc]
    exact img_pair (by omega) hF.pre rfl rfl hsh (T := [[]]) (by simp)
  · have hls : ls.take (q + 3 + 1) = ls := List.take_of_length_le (by omega)
    rw [hls] at hseg1
    have hIMG : Img (PrivA R)
        [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩, ⟨.relXW, Arm.r (.GPR 25#5) s, ty.bytes,
          (Arm.r (.GPR 28#5) s).setWidth (ty.bytes * 8)⟩] (evTr ls)
        (fun j => if j = 0 then ((evTr (ls.take q)).length, 0) else
          ((evTr (ls.take q)).length + 3, 0)) := by
      rw [hseg1, List.append_assoc]
      exact img_pair (by omega) hF.pre rfl rfl hsh (T := []) (by simp)
    refine .inr (.inr (.inl (And.intro ⟨_, c'', fun j => if j = 0 then ((evTr (ls.take q)).length, 0) else
      ((evTr (ls.take q)).length + 3, 0), hsrc, hIMG⟩ ?_)))
    · -- the run ends with the final iteration's successful `stlxr`, at the `cbnz` line
      have hlen1 : ls.length = q + 3 + 1 := by omega
      obtain ⟨mon1, hr1⟩ := hF.run
      obtain ⟨t0, rA, rB⟩ := PRun.split (ls.take (q + 3)) (ls.drop (q + 3))
        (by rw [List.take_append_drop]; exact hr)
      obtain rfl := PRun.det rA hr1
      obtain ⟨l, hdl⟩ : ∃ l, ls.drop (q + 3) = [l] := by
        have h1 : (ls.drop (q + 3)).length = 1 := by rw [List.length_drop]; omega
        cases hl : ls.drop (q + 3) with
        | nil => rw [hl] at h1; simp at h1
        | cons l t =>
          cases t with
          | nil => exact ⟨l, rfl⟩
          | cons _ _ => rw [hl, List.length_cons, List.length_cons] at h1; omega
      rw [hdl] at rB
      cases rB with
      | @cons _ t1 _ _ _ hsB hpB hokB rB' =>
      cases rB'
      have hz0 : iterN R.step 3 (patch [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩] y1) = zS := by
        rw [hz, hstepb]
        simp only [hne', Bool.false_eq_true, ite_false]
        exact hzS
      rw [hzS] at hwevA
      rw [← hz0, h25s1, h28s1] at hwevA
      have hlev : l.evs = [⟨.relXW, Arm.r (.GPR 25#5) s, ty.bytes,
        (Arm.r (.GPR 28#5) s).setWidth (ty.bytes * 8)⟩] := by
        have e1 : (evTr ls)[q + 3]? = some [⟨.relXW, Arm.r (.GPR 25#5) s, ty.bytes,
          (Arm.r (.GPR 28#5) s).setWidth (ty.bytes * 8)⟩] := by
          rw [hseg1, List.append_assoc, List.getElem?_append,
            if_neg (by simp only [evTr, List.length_map, List.length_take]; omega),
            show (q + 3) - (evTr (ls.take q)).length = 3 from by
              simp only [evTr, List.length_map, List.length_take]; omega,
            List.getElem?_append,
            if_neg (by rw [segR_length ⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩ (by omega)]; omega),
            segR_length ⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes, v⟩ (by omega), Nat.sub_self, List.getElem?_cons_zero]
        have e3 : ls[q + 3]? = some l := by
          have h4 : (ls.drop (q + 3))[0]? = some l := by rw [hdl]; simp
          rw [List.getElem?_drop] at h4
          simpa using h4
        have e2 : (evTr ls)[q + 3]? = some l.evs := by
          simp only [evTr, List.getElem?_map]
          rw [e3]
          simp
        rw [e2] at e1
        exact Option.some.inj e1
      have hxfB : l.xfail = false := by
        rcases hpB with hx | ⟨M', hM'⟩
        · have hl0 : l.evs = [] := by cases hsB with | exec => cases hx | xfail => rfl
          rw [hlev] at hl0
          exact absurd hl0 (by simp)
        · rw [ArmPrecise.stepEvs_setMem, hwevA] at hM'
          rw [reread_W hW M' (Arm.r (.GPR 25#5) s) ty.bytes
            ((Arm.r (.GPR 28#5) s).setWidth (ty.bytes * 8))] at hM'
          cases hb : l.xfail with
          | false => rfl
          | true =>
            have hl0 : l.evs = [] := by cases hsB with | exec => cases hb | xfail => rfl
            rw [hl0] at hM'
            injection hM'
      obtain ⟨-, htB⟩ := tstep_store hsB hpB hxfB hW hwevA
      rw [htB, hz0, hstep3]
      have hd4 : R.L.drop (j0 + 4) = casStore ty.bits fl ++
          (.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none ::
            .label (.loop (ps1.aloop + 1)) ::
              (relaxLines R.far (X' ++ x.2.1) ++
                R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2))) := by
        rw [← List.drop_drop, hdrop']; simp [casLoopLines, casLoopHead, casStore]
      have hint3 : LinesInterOk (R.envOf (j0 + 4)) (casStore ty.bits fl) zS :=
        fun q h0 h1 => by simp [casStore] at h1; omega
      have hprogzS : zS.program = R.fb.program R.base := by
        rw [← hzS, Arm.w_program, hprogs1, hst.prog]
      have hpczS : Arm.r .PC zS = R.pcOf (j0 + 4) := by rw [← hzS, Arm.r_of_w_same]
      obtain ⟨-, hpcs3, -, -⟩ := run_ins hR hd4 (by simp [casStore, Insn.hooked]) hprogzS hpczS
        herrzS hint3 hrun3
      simp only [casStore, List.length_singleton] at hpcs3
      exact ⟨j0 + 5, .cbz true true (.x 24) (.loop ps1.aloop), none, hL5, by simp,
        by simp [Insn.hooked], by rw [hpcs3, show (j0 + 4) + 1 = j0 + 5 from rfl]⟩

/-- **The per-item obligation at the `atomic_cas` loop** (module doc): every precise Arm run from
`Q`-related states goes through failed iterations (reading any bytes, writing nothing) and ends
before a successful `stlxr` or the exit (no write), or its final iteration's `ldaxr` read `e` is
the event of the allocated code's step `[e]` (the values differ: the `b.ne` exit), or `e` and the
successful `stlxr` write `wv` are the events of its step `[e, wv]` (a monitor pair), on the world
patched with `e`, the states after the item related. -/
theorem cas_op {R : RL} (hR : R.Wf) {ok : ArmState → Lab → Prop} {s : ArmState} {mon : Mon}
    {b k : Nat} {allocs : Array Loc} {its' : List RItem} {m : Loc → CV} {w : ArmState}
    {evs0 : List Ev} {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its' m w)) (hA : AInv R (OpC b k allocs its' m w))
    (hs0 : SrcStep R (OpC b k allocs its' m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i →
      ∃ ty fl ra re rx rd r1, i = .atomicCasLoop ty fl ra re rx rd r1)
    {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm R.step ok (s, mon) ls t') :
    OpOutG R ok (s, mon) (OpC b k allocs its' m w) ls :=
  (cas_opR hR hq hA hs0 hform hr).out

end Concurrency.ArmAllocThread
