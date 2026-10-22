import FV.Concurrency.SegFoot
import FV.Concurrency.IselStep

/-!
# Exact footprints, reached states and event-free runs under `csem` (T2h, #311, layer 2e)

* **Exact footprint shapes** (S1):
  - `cEvs_straight_le_one`, `cEvs_straight_one`: a straight-line memory form has at most one
    event, hence exactly one when it has any;
  - `cEvs_loadAcquire_one`, `cEvs_storeRelease_one`: `ldar`/`stlr` have exactly one event
    (`acqR`/`relW`, of the access size);
  - `cEvs_rmw_shape`: the `atomic_rmw` loop's events are its `ldaxr`'s read of the old value
    (`acqXR` at the address use, the bytes of the world) and its `stlxr`'s write (`relXW`);
  - `cEvs_cas_shape`: the `atomic_cas` loop's events are the `ldaxr`'s read, followed, exactly
    when the old value equals the expected one, by the `stlxr`'s write;
  - `cEvs_fence`: `dmb ish` has the barrier event `dmbEv` (address 0, size 0);
* **Reached states** (S3, `IselCover.RunAt`): `runAt_det`, `runAt_take`, `runAt_step`,
  `runAt_keep` (error-free, aligned along a run of covered instructions);
* **Event-free runs** (S4): `star_mem_keep`: a counted `VStep` path through covered instructions
  without memory kinds keeps the memory, the error flag and the alignment.
-/

namespace Concurrency.IselMemAux

open Arm ArmFoot ArmThread ArmInstFoot Backend Backend.Proof VCodeThread VCodeEvents Code VCodeAddr
  IselCover SegFoot

attribute [local csimp_rules] wmb_cast Arm.LDST.exec_reg_exclusive Insn.armFields.exclFields
  CTy.bits Arm.r_of_write_mem_bytes Arm.ldst_read Arm.read_mem_bytes_of_w

/-! ## The exclusive and acquire/release accesses -/

set_option maxHeartbeats 4000000 in
theorem ldaxr_one {ty : CTy} (hty : AtomTy ty) {env : Env} {ai : ArmInst}
    (ha : (Insn.ldaxr ty.bits (.x 27) (.x 25)).toArmInst env = .ok ai) (s : ArmState) :
    instEvs ai s = [⟨.acqXR, Arm.r (.GPR 25#5) s, ty.bytes,
      readM ty.bytes (Arm.r (.GPR 25#5) s) s.mem⟩] := by
  rcases hty with rfl | rfl | rfl | rfl <;>
  · simp (config := {decide := true}) [csimp_rules] at ha
    subst ha
    simp (config := {decide := true}) [instEvs, exclEvs]
    exact ⟨rfl, .rfl⟩

set_option maxHeartbeats 4000000 in
theorem stlxr_one {ty : CTy} (hty : AtomTy ty) {env : Env} {rs : Reg} {ai : ArmInst}
    (hrs : rs = .x 26 ∨ rs = .x 28)
    (ha : (Insn.stlxr ty.bits (.x 24) rs (.x 25)).toArmInst env = .ok ai) (s : ArmState) :
    ∃ e, instEvs ai s = [e] ∧ e.k = .relXW ∧ e.addr = Arm.r (.GPR 25#5) s ∧ e.n = ty.bytes := by
  rcases hty with rfl | rfl | rfl | rfl <;> rcases hrs with rfl | rfl <;>
  · simp (config := {decide := true}) [csimp_rules] at ha
    subst ha
    simp (config := {decide := true}) [instEvs, exclEvs]
    rfl

set_option maxHeartbeats 4000000 in
theorem ldar_one {ty : CTy} (hty : AtomTy ty) (env : Env) (tc : Option Clif.TrapCode)
    (s : ArmState) :
    ∃ e, linesEvs env [.ins (.ldar ty.bits (.x 1) (.x 0)) tc] s = [e] ∧ e.k = .acqR ∧
      e.addr = Arm.r (.GPR 0#5) s ∧ e.n = ty.bytes := by
  rcases hty with rfl | rfl | rfl | rfl <;>
  · simp (config := {decide := true}) [csimp_rules, linesEvs, instEvs, exclEvs]

set_option maxHeartbeats 4000000 in
theorem stlr_one {ty : CTy} (hty : AtomTy ty) (env : Env) (tc : Option Clif.TrapCode)
    (s : ArmState) :
    ∃ e, linesEvs env [.ins (.stlr ty.bits (.x 1) (.x 0)) tc] s = [e] ∧ e.k = .relW ∧
      e.addr = Arm.r (.GPR 0#5) s ∧ e.n = ty.bytes := by
  rcases hty with rfl | rfl | rfl | rfl <;>
  · simp (config := {decide := true}) [csimp_rules, linesEvs, instEvs, exclEvs]

/-! ## The loop bodies -/

/-- **The `atomic_rmw` loop body's events**: the `ldaxr`'s read at x25, then the `stlxr`'s write. -/
theorem rmwBody_shape {ty : CTy} (hty : AtomTy ty) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags)
    (e : Env) (t : ArmState) (herr : Arm.r .ERR t = .None) :
    ∃ wr, linesEvs e (rmwLoopBody ty.bits op fl) t =
        [⟨.acqXR, Arm.r (.GPR 25#5) t, ty.bytes, readM ty.bytes (Arm.r (.GPR 25#5) t) t.mem⟩, wr] ∧
      wr.k = .relXW ∧ wr.addr = Arm.r (.GPR 25#5) t ∧ wr.n = ty.bytes := by
  obtain ⟨t', hrun, -, -, -, hfr, -, -⟩ := rmwBody_spec hty op fl e t herr
  have h25 : Arm.r (.GPR 25#5) t' = Arm.r (.GPR 25#5) t :=
    hfr _ (by simp) (by simp) (by simp)
  unfold rmwLoopBody at hrun ⊢
  simp only [List.cons_append, List.nil_append] at hrun ⊢
  obtain ⟨a1, ha1, -, hr1, he1⟩ := exec_cons hrun
  rw [he1]
  rw [VCodeAddr.execLines_append] at hr1
  cases hm : execLines { e with pc := e.pc + 4 } ((rmwLoopMid op ty.bits).map fun i => .ins i)
      (Arm.exec_inst a1 t) with
  | none => rw [hm] at hr1; cases hr1
  | some s2 =>
    rw [hm] at hr1
    simp only [Option.bind_some] at hr1
    obtain ⟨a2, ha2, -, hr2, he2⟩ := exec_cons hr1
    simp only [execLines, Option.some.injEq] at hr2
    rw [linesEvs_exec _ hm (kinds_rmwLoopMid op ty.bits), he2]
    simp only [linesEvs, List.append_nil]
    have hrs : rmwLoopStored op = .x 26 ∨ rmwLoopStored op = .x 28 := by
      cases op <;> simp [rmwLoopStored]
    obtain ⟨-, hx2⟩ := stlxr_evs hty hrs ha2 s2
    have hs2 : Arm.r (.GPR 25#5) s2 = Arm.r (.GPR 25#5) t := by rw [← hx2, hr2, h25]
    obtain ⟨wr, hw, hk, hwa, hn⟩ := stlxr_one hty hrs ha2 s2
    rw [ldaxr_one hty ha1, hw]
    exact ⟨wr, rfl, hk, hwa.trans hs2, hn⟩

/-- **The `atomic_cas` loop head's event**: the `ldaxr`'s read at x25. -/
theorem casHead_shape {ty : CTy} (hty : AtomTy ty) (fl : Clif.MemFlags) (e : Env) (t : ArmState)
    (herr : Arm.r .ERR t = .None) :
    linesEvs e (casLoopHead ty.bits fl) t =
      [⟨.acqXR, Arm.r (.GPR 25#5) t, ty.bytes, readM ty.bytes (Arm.r (.GPR 25#5) t) t.mem⟩] := by
  obtain ⟨t', hrun, -⟩ := casHead_spec hty fl e t herr
  unfold casLoopHead at hrun ⊢
  obtain ⟨a1, ha1, -, hr1, he1⟩ := exec_cons hrun
  rw [he1]
  have hc := linesEvs_exec ([] : List Line) hr1 (by
    simp only [kinds, List.filterMap_cons, List.filterMap_nil, lineKind, insnKind_casLoopCmp])
  simp only [List.append_nil] at hc
  rw [hc]
  simp only [linesEvs, List.append_nil]
  exact ldaxr_one hty ha1 t

/-- **The `atomic_cas` loop's `stlxr` event**, when it runs: the write at x25. -/
theorem casStore_shape {ty : CTy} (hty : AtomTy ty) (fl : Clif.MemFlags) {e : Env}
    {t t' : ArmState} (hx : execLines e (casStore ty.bits fl) t = some t') :
    ∃ wr, linesEvs e (casStore ty.bits fl) t = [wr] ∧ wr.k = .relXW ∧
      wr.addr = Arm.r (.GPR 25#5) t ∧ wr.n = ty.bytes := by
  unfold casStore at hx ⊢
  obtain ⟨a1, ha1, -, -, he1⟩ := exec_cons hx
  rw [he1]
  simp only [linesEvs, List.append_nil]
  exact stlxr_one hty (.inr rfl) ha1 t

/-! ## `cEvs` of the loops -/

theorem r26_three (u e x : CV) (w : ArmState) :
    Arm.r (.GPR 26#5) (([Reg.x 25, .x 26, .x 28].zip [u, e, x]).foldl
      (fun s p => setReg s p.1 p.2) w) = lo64 e := by
  simp [setReg, rnum, Arm.r_of_w_different, Arm.r_of_w_same]

/-- **The `atomic_rmw` loop's footprint**: the read of the old value at the address use (`acqXR`,
the world's bytes), then the write (`relXW`) there. -/
theorem cEvs_rmw_shape {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {ty : CTy}
    {op : AtomicRmwLoopOp} {fl : Clif.MemFlags} {ra rx rd r1 r2 : Reg} {ua x : CV} {w : ArmState}
    {r : List CV × ArmState × Ctl} (he : Arm.r .ERR w = .None)
    (h : csem F fc X (.atomicRmwLoop ty op fl ra rx rd r1 r2) [ua, x] w = some r) :
    ∃ wr, cEvs F fc (.atomicRmwLoop ty op fl ra rx rd r1 r2) [ua, x] w =
        [⟨.acqXR, lo64 ua, ty.bytes, readM ty.bytes (lo64 ua) w.mem⟩, wr] ∧
      wr.k = .relXW ∧ wr.addr = lo64 ua ∧ wr.n = ty.bytes := by
  simp only [csem, he, ite_true] at h
  obtain ⟨hty, -, -, -⟩ := loopSem_some h
  obtain ⟨wr, hw, hk, ha, hn⟩ := rmwBody_shape hty op fl env0
    (([Reg.x 25, .x 26].zip [ua, x]).foldl (fun s p => setReg s p.1 p.2) w)
    (by rw [err_two]; exact he)
  rw [r25_two, foldl_setReg_mem] at hw
  rw [r25_two] at ha
  refine ⟨wr, ?_, hk, ha, hn⟩
  unfold cEvs loopEvs
  simp only [MInst.isCtl, ite_true]
  exact hw

/-- **The `atomic_cas` loop's footprint**: the read of the old value at the address use
(`acqXR`, the world's bytes), followed — exactly when the old value is the expected one — by the
write (`relXW`) there. -/
theorem cEvs_cas_shape {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {ty : CTy}
    {fl : Clif.MemFlags} {ra re rx ro rs : Reg} {ua ex x : CV} {w : ArmState}
    {r : List CV × ArmState × Ctl} (he : Arm.r .ERR w = .None)
    (h : csem F fc X (.atomicCasLoop ty fl ra re rx ro rs) [ua, ex, x] w = some r) :
    (cEvs F fc (.atomicCasLoop ty fl ra re rx ro rs) [ua, ex, x] w =
        [⟨.acqXR, lo64 ua, ty.bytes, readM ty.bytes (lo64 ua) w.mem⟩] ∧
      readM ty.bytes (lo64 ua) w.mem ≠ (lo64 ex).setWidth (ty.bytes * 8)) ∨
    (∃ wr, cEvs F fc (.atomicCasLoop ty fl ra re rx ro rs) [ua, ex, x] w =
        [⟨.acqXR, lo64 ua, ty.bytes, readM ty.bytes (lo64 ua) w.mem⟩, wr] ∧
      wr.k = .relXW ∧ wr.addr = lo64 ua ∧ wr.n = ty.bytes ∧
      readM ty.bytes (lo64 ua) w.mem = (lo64 ex).setWidth (ty.bytes * 8)) := by
  simp only [csem, he, ite_true] at h
  have hcev : cEvs F fc (.atomicCasLoop ty fl ra re rx ro rs) [ua, ex, x] w =
      casEvs F ty fl ua ex x w := by
    unfold cEvs; simp only [MInst.isCtl, ite_true]
  rw [hcev]
  unfold casEvs
  cases hL : loopSem F ty ua (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [ua, ex, x]
      [.x 27, .x 24] w with
  | none => rw [hL] at h; cases h
  | some r1 =>
    obtain ⟨outs, t1, c1⟩ := r1
    obtain ⟨hty, -, -, hrun⟩ := loopSem_some hL
    simp only at hrun
    rw [hL] at h
    simp only at h ⊢
    have herr0 : Arm.r .ERR (([Reg.x 25, .x 26, .x 28].zip [ua, ex, x]).foldl
        (fun s p => setReg s p.1 p.2) w) = .None := by rw [err_three]; exact he
    have hhead := casHead_shape hty fl env0 _ herr0
    rw [r25_three, foldl_setReg_mem] at hhead
    obtain ⟨t', ht', -, -, hfr, -, -, hne⟩ := casHead_spec hty fl env0 _ herr0
    rw [ht'] at hrun
    simp only [Option.some.injEq] at hrun
    subst hrun
    have hiff : Arm.ConditionHolds Cond.ne.bits t' = true ↔
        readM ty.bytes (lo64 ua) w.mem ≠ (lo64 ex).setWidth (ty.bytes * 8) := by
      rw [hne, read_mem_bytes_eq, r25_three, r26_three, foldl_setReg_mem]
    have hhl : loopEvs (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [ua, ex, x] w =
        [⟨.acqXR, lo64 ua, ty.bytes, readM ty.bytes (lo64 ua) w.mem⟩] := hhead
    by_cases hc : Arm.ConditionHolds Cond.ne.bits t' = true
    · left
      simp only [hc, ite_true]
      exact ⟨hhl, hiff.mp hc⟩
    · right
      simp only [hc, Bool.false_eq_true, ite_false] at h ⊢
      obtain ⟨-, -, -, hrun2⟩ := loopSem_some h
      obtain ⟨wr, hw, hk, ha, hn⟩ := casStore_shape hty fl (t := t') hrun2
      have h25 : Arm.r (.GPR 25#5) t' = lo64 ua := by
        rw [hfr (.GPR 25#5) (by simp) (by simp) (by simp), r25_three]
      refine ⟨wr, ?_, hk, ha.trans h25, hn, ?_⟩
      · rw [hhl]
        have hs : loopEvs (casStore ty.bits fl) [] [] t' = [wr] := hw
        rw [hs]
        rfl
      · exact Classical.byContradiction fun hneq => hc (hiff.mpr hneq)

/-! ## `cEvs` of the straight-line forms -/

theorem straightEvs_one_line {ctx : FnCtx} {i ic : MInst} {uses : List CV} {w : ArmState}
    {ops : Array Operand} {l : Line} (hops : i.operands = .ok ops)
    (hic : i.assign (canonRegs ops) = .ok ic) (hl : ic.lines ctx {} = .ok ([l], {})) :
    straightEvs ctx i uses w = linesEvs env0 [l] (placeUses ops (canonRegs ops) uses w) := by
  unfold straightEvs
  simp only [hops, hic, hl]


/-- **`dmb ish`'s footprint**: the barrier event (address 0, size 0). -/
theorem cEvs_fence (F : BitVec 64 → Prop) (fc : FnCtx) (u : List CV) (w : ArmState) :
    cEvs F fc .fence u w = [dmbEv] := by
  unfold cEvs
  simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
  rw [straightEvs_one_line (ic := .fence) rfl rfl rfl]
  simp (config := {decide := true}) [csimp_rules, linesEvs, instEvs]

theorem dmbEv_addr : dmbEv.addr = 0 ∧ dmbEv.n = 0 := ⟨rfl, rfl⟩

theorem akinds_length {i : MInst} {n : Nat} (hctl : i.isCtl = false)
    (hn : SegShape.memBytes i = some n) : (akinds i).length = 1 := by
  cases i <;> simp_all [SegShape.memBytes, akinds, MInst.isCtl]

/-- **A straight-line memory form has at most one event.** -/
theorem cEvs_straight_le_one (F : BitVec 64 → Prop) (fc : FnCtx) {i : MInst} {n : Nat}
    (hctl : i.isCtl = false) (hn : SegShape.memBytes i = some n) (u : List CV) (w : ArmState) :
    (cEvs F fc i u w).length ≤ 1 := by
  have h := (cEvs_kinds F fc i u w).length_le
  rw [List.length_map, akinds_length hctl hn] at h
  exact h

/-- **A straight-line memory form with an event has exactly one.** -/
theorem cEvs_straight_one {F : BitVec 64 → Prop} {fc : FnCtx} {i : MInst} {n : Nat}
    (hctl : i.isCtl = false) (hn : SegShape.memBytes i = some n) {u : List CV} {w : ArmState}
    (hne : cEvs F fc i u w ≠ []) : ∃ e, cEvs F fc i u w = [e] := by
  have hl := cEvs_straight_le_one F fc hctl hn u w
  rcases hc : cEvs F fc i u w with _ | ⟨e, _ | ⟨e', t⟩⟩
  · exact absurd hc hne
  · exact ⟨e, rfl⟩
  · rw [hc] at hl; simp at hl

/-- **`ldar`'s footprint**: exactly one event, an `acqR` read of the access size. -/
theorem cEvs_loadAcquire_one {F : BitVec 64 → Prop} {fc : FnCtx} {ty : CTy} {rt rn : Reg}
    {fl : Clif.MemFlags} (hfo : FormOk fc (.loadAcquire ty rt rn fl) = true) (u : List CV)
    (w : ArmState) :
    ∃ e, cEvs F fc (.loadAcquire ty rt rn fl) u w = [e] ∧ e.k = .acqR ∧ e.n = ty.bytes := by
  rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  all_goals rcases rn with ⟨a, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, decide_eq_true_eq] at hfo
  unfold cEvs
  simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
  rw [straightEvs_one_line (ic := .loadAcquire ty (.x 1) (.x 0) fl) rfl rfl rfl]
  obtain ⟨e, he, hk, -, hn⟩ := ldar_one hfo env0 _ (placeUses _ _ u w)
  exact ⟨e, he, hk, hn⟩

/-- **`stlr`'s footprint**: exactly one event, a `relW` write of the access size. -/
theorem cEvs_storeRelease_one {F : BitVec 64 → Prop} {fc : FnCtx} {ty : CTy} {rt rn : Reg}
    {fl : Clif.MemFlags} (hfo : FormOk fc (.storeRelease ty rt rn fl) = true) (u : List CV)
    (w : ArmState) :
    ∃ e, cEvs F fc (.storeRelease ty rt rn fl) u w = [e] ∧ e.k = .relW ∧ e.n = ty.bytes := by
  rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  all_goals rcases rn with ⟨a, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, decide_eq_true_eq] at hfo
  unfold cEvs
  simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
  rw [straightEvs_one_line (ic := .storeRelease ty (.x 1) (.x 0) fl) rfl rfl rfl]
  obtain ⟨e, he, hk, -, hn⟩ := stlr_one hfo env0 _ (placeUses _ _ u w)
  exact ⟨e, he, hk, hn⟩

/-! ## Reached states of a straight-line run -/

theorem runAt_zero {sem : Sem} {ms : List MInst} {ρ : Nat → CV} {w : ArmState} {ρj : Nat → CV}
    {wj : ArmState} (h : RunAt sem ms ρ w 0 ρj wj) : ρj = ρ ∧ wj = w := by
  cases ms <;> exact h

/-- **One reached state per index.** -/
theorem runAt_det {sem : Sem} : ∀ {ms : List MInst} {ρ : Nat → CV} {w : ArmState} {j : Nat}
    {ρ1 ρ2 : Nat → CV} {w1 w2 : ArmState}, RunAt sem ms ρ w j ρ1 w1 → RunAt sem ms ρ w j ρ2 w2 →
      ρ1 = ρ2 ∧ w1 = w2
  | _, _, _, 0, _, _, _, _, h1, h2 => by
    obtain ⟨rfl, rfl⟩ := runAt_zero h1
    obtain ⟨rfl, rfl⟩ := runAt_zero h2
    exact ⟨rfl, rfl⟩
  | [], _, _, _ + 1, _, _, _, _, h1, _ => h1.elim
  | i :: ms, ρ, w, j + 1, ρ1, ρ2, w1, w2, h1, h2 => by
    obtain ⟨ops, outs, w', ho, hs, hr⟩ := h1
    obtain ⟨ops2, outs2, w2', ho2, hs2, hr2⟩ := h2
    rw [ho] at ho2; cases ho2
    rw [hs] at hs2
    simp only [Option.some.injEq, Prod.mk.injEq] at hs2
    obtain ⟨rfl, rfl, -⟩ := hs2
    exact runAt_det hr hr2

/-- **A reached state is the end of the run's prefix**, when the whole run falls through. -/
theorem runAt_take {sem : Sem} : ∀ {ms : List MInst} {ρ : Nat → CV} {w : ArmState} {j : Nat}
    {ρj : Nat → CV} {wj : ArmState} {ρ' : Nat → CV} {w' : ArmState},
    seqRun sem ms ρ w = some (.fall ρ' w') → RunAt sem ms ρ w j ρj wj →
      j ≤ ms.length ∧ seqRun sem (ms.take j) ρ w = some (.fall ρj wj)
  | _, _, _, 0, _, _, _, _, _, h => by
    obtain ⟨rfl, rfl⟩ := runAt_zero h
    exact ⟨Nat.zero_le _, rfl⟩
  | [], _, _, _ + 1, _, _, _, _, _, h => h.elim
  | i :: ms, ρ, w, j + 1, ρj, wj, ρ', w', hrun, h => by
    obtain ⟨ops, outs, w1, ho, hs, hr⟩ := h
    obtain ⟨ops', outs', w1', ho', hs', hlen, hrest⟩ := Driver.seqRun_cons_fall hrun
    rw [ho] at ho'; cases ho'
    rw [hs] at hs'
    simp only [Option.some.injEq, Prod.mk.injEq] at hs'
    obtain ⟨rfl, rfl, -⟩ := hs'
    obtain ⟨hj, ht⟩ := runAt_take hrest hr
    refine ⟨by simp; omega, ?_⟩
    simp only [List.take_succ_cons, seqRun, ho, hs, hlen, ite_true, ht, Option.map_some]
    rfl

/-- **The instruction at a reached state steps with control `next`**, when the whole run falls
through. -/
theorem runAt_step {sem : Sem} : ∀ {ms : List MInst} {ρ : Nat → CV} {w : ArmState} {j : Nat}
    {ρj : Nat → CV} {wj : ArmState} {ρ' : Nat → CV} {w' : ArmState} {i : MInst}
    {ops : Array Operand},
    seqRun sem ms ρ w = some (.fall ρ' w') → RunAt sem ms ρ w j ρj wj → ms[j]? = some i →
      i.operands = .ok ops → ∃ outs w2, sem i (vuses ops ρj) wj = some (outs, w2, .next)
  | [], _, _, _, _, _, _, _, _, _, _, _, hi, _ => by simp at hi
  | i' :: ms, ρ, w, 0, ρj, wj, ρ', w', i, ops, hrun, h, hi, hops => by
    obtain ⟨rfl, rfl⟩ := runAt_zero h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    obtain ⟨ops', outs, w1, ho', hs', -, -⟩ := Driver.seqRun_cons_fall hrun
    rw [hops] at ho'; cases ho'
    exact ⟨outs, w1, hs'⟩
  | i' :: ms, ρ, w, j + 1, ρj, wj, ρ', w', i, ops, hrun, h, hi, hops => by
    obtain ⟨ops1, outs, w1, ho, hs, hr⟩ := h
    obtain ⟨ops', outs', w1', ho', hs', -, hrest⟩ := Driver.seqRun_cons_fall hrun
    rw [ho] at ho'; cases ho'
    rw [hs] at hs'
    simp only [Option.some.injEq, Prod.mk.injEq] at hs'
    obtain ⟨rfl, rfl, -⟩ := hs'
    simp only [List.getElem?_cons_succ] at hi
    exact runAt_step hrest hr hi hops

theorem csemWF_vuses {ctx : FnCtx} {i : MInst} {ops : Array Operand} (hfo : FormOk ctx i = true)
    (hops : i.operands = .ok ops) (ρ : Nat → CV) : csemWF ctx i (vuses ops ρ) = true := by
  simp [csemWF, hfo, hops, vuses, useCount]

theorem covered_cov {ctx : FnCtx} {i : MInst} {ops : Array Operand} (hc : Covered ctx i)
    (hops : i.operands = .ok ops) (ρ : Nat → CV) :
    i.isCtl = true ∨ csemWF ctx i (vuses ops ρ) = true := by
  cases hi : i.isCtl
  · rcases hc.2.2 with h | h
    · rw [hi] at h; cases h
    · exact .inr (csemWF_vuses h hops ρ)
  · exact .inl rfl

/-- **Every reached state of a run of covered instructions is error-free and aligned.** -/
theorem runAt_keep {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} :
    ∀ {ms : List MInst} {ρ : Nat → CV} {w : ArmState} {j : Nat} {ρj : Nat → CV} {wj : ArmState},
    (∀ i ∈ ms, Covered fc i) → Arm.r .ERR w = .None → Arm.CheckSPAlignment w →
      RunAt (csem F fc X) ms ρ w j ρj wj → Arm.r .ERR wj = .None ∧ Arm.CheckSPAlignment wj
  | _, _, _, 0, _, _, _, he, hal, h => by
    obtain ⟨rfl, rfl⟩ := runAt_zero h
    exact ⟨he, hal⟩
  | [], _, _, _ + 1, _, _, _, _, _, h => h.elim
  | i :: ms, ρ, w, j + 1, ρj, wj, hms, he, hal, h => by
    obtain ⟨ops, outs, w1, ho, hs, hr⟩ := h
    have hc := hms i List.mem_cons_self
    obtain ⟨he1, hal1, -⟩ := csem_keep hc.1 hc.2.1 (covered_cov hc ho ρ) he hal hs
    exact runAt_keep (fun j hj => hms j (List.mem_cons_of_mem _ hj)) he1 hal1 hr

/-! ## Event-free forward runs -/

theorem loopSem_ctl {F : BitVec 64 → Prop} {ty : CTy} {a : CV} {body : List Line}
    {regs : List Reg} {uses : List CV} {defs : List Reg} {w : ArmState}
    {r : List CV × ArmState × Ctl} (h : loopSem F ty a body regs uses defs w = some r) :
    r.2.2 = .next := by
  unfold loopSem at h
  split at h
  · split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h
  · cases h

/-- A step of a covered instruction with a control other than `next` keeps the world. -/
theorem csem_next_or_same {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    {u : List CV} {w : ArmState} (hcall : ∀ info, i ≠ .call info)
    (htry : ∀ info ti, i ≠ .tryCall info ti) (hcov : i.isCtl = true ∨ csemWF ctx i u = true)
    (he : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w) {o : List CV} {w' : ArmState}
    {c : Ctl} (h : csem F ctx X i u w = some (o, w', c)) : c = .next ∨ w' = w := by
  cases hctl : i.isCtl with
  | false =>
    have hwf : csemWF ctx i u = true := by
      rcases hcov with h' | h'
      · rw [hctl] at h'; cases h'
      · exact h'
    rw [csem_of_wf hctl hwf he hal] at h
    exact .inl (straightSem_some h).1
  | true =>
    cases i <;> (try (simp [MInst.isCtl] at hctl; done))
    case call info => exact absurd rfl (hcall info)
    case tryCall info ti => exact absurd rfl (htry info ti)
    case atomicRmwLoop =>
      simp only [csem, he, ite_true] at h
      split at h
      · exact .inl (loopSem_ctl h)
      · cases h
    case atomicCasLoop =>
      simp only [csem, he, ite_true] at h
      split at h
      · split at h
        · split at h
          · cases h; exact .inl rfl
          · exact .inl (loopSem_ctl h)
        · cases h
      · cases h
    case testBitAndBranch =>
      simp only [csem] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact .inr h.2.1.symm
      · cases h
    case jtSequence =>
      simp only [csem] at h
      split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact .inr h.2.1.symm
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            exact .inr h.2.1.symm
          · cases h
      · cases h
    case elfTlsGetAddr =>
      simp only [csem, Option.some.injEq, Prod.mk.injEq] at h
      exact .inl h.2.2.symm
    all_goals
      simp only [csem, Option.some.injEq, Prod.mk.injEq] at h
      exact .inr h.2.1.symm

/-- **A covered step keeps the error flag and the alignment**, whatever its control. -/
theorem csem_keep_any {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    {u : List CV} {w : ArmState} (hcall : ∀ info, i ≠ .call info)
    (htry : ∀ info ti, i ≠ .tryCall info ti) (hcov : i.isCtl = true ∨ csemWF ctx i u = true)
    (he : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w) {o : List CV} {w' : ArmState}
    {c : Ctl} (h : csem F ctx X i u w = some (o, w', c)) :
    Arm.r .ERR w' = .None ∧ Arm.CheckSPAlignment w' := by
  rcases csem_next_or_same hcall htry hcov he hal h with rfl | rfl
  · exact ⟨(csem_keep hcall htry hcov he hal h).1, (csem_keep hcall htry hcov he hal h).2.1⟩
  · exact ⟨he, hal⟩

theorem vnext_confW {vc : VCode} {b k n : Nat} {i : MInst} {uses : List CV} {ρ : Nat → CV}
    {w : ArmState} {ctl : Ctl} {c' : VConf CV ArmState} (h : VNext vc b k n i uses ρ w ctl c') :
    SegRun.confW c' = w := by
  cases h <;> rfl

/-- **An event-free forward run keeps the memory, the error flag and the alignment**: a counted
`VStep` path whose configurations (but the last) are at covered instructions without memory
kinds. -/
theorem star_mem_keep {vc : VCode} {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    {P : VConf CV ArmState → Prop} (hX : TlsMemFree X)
    (hP : ∀ c, P c → ∃ b k ρ w vb i, c = .run ⟨b, k, ρ, w⟩ ∧ vc.blocks[b]? = some vb ∧
      vb.insts[k]? = some i ∧ Covered fc i ∧ akinds i = []) :
    ∀ {n : Nat} {c c' : VConf CV ArmState}, IselStep.StarNP (VStep vc (csem F fc X)) P n c c' →
      Arm.r .ERR (SegRun.confW c) = .None → Arm.CheckSPAlignment (SegRun.confW c) →
      (SegRun.confW c').mem = (SegRun.confW c).mem ∧ Arm.r .ERR (SegRun.confW c') = .None ∧
        Arm.CheckSPAlignment (SegRun.confW c')
  | _, _, _, .refl _, he, hal => ⟨rfl, he, hal⟩
  | _, _, _, .step hp hst rest, he, hal => by
    obtain ⟨b, k, ρ, w, vb, i, rfl, hb, hi, hc, hk⟩ := hP _ hp
    cases hst with
    | step hb' hi' hops hsem hlen hnx =>
      rw [hb] at hb'; cases hb'
      rw [hi] at hi'; cases hi'
      simp only [SegRun.confW] at he hal ⊢
      have hcov := covered_cov hc hops ρ
      have hfoot := ifoot_csem (F := F) (ctx := fc) (X := X) hX he hc.1 hc.2.1
        (fun hctl => ⟨(hcov.resolve_left (by rw [hctl]; simp)), hal⟩)
      rw [cEvs_nil hk] at hfoot
      have hmem := SegRun.ifoot_nil_mem hfoot hsem
      obtain ⟨he1, hal1⟩ := csem_keep_any hc.1 hc.2.1 hcov he hal hsem
      have hw := vnext_confW hnx
      obtain ⟨h1, h2, h3⟩ := star_mem_keep hX hP rest (by rw [hw]; exact he1) (by rw [hw]; exact hal1)
      refine ⟨?_, h2, h3⟩
      exact h1.trans (by rw [hw]; exact hmem)

end Concurrency.IselMemAux
