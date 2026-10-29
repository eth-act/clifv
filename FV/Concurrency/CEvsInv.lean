module

public import FV.Concurrency.VCodeSize
public import FV.E2E.RegLevelDriverSem
public import FV.Backend.Proof.LowerCover

@[expose] public section

/-!
# Invariances of the footprint `cEvs` (T2h, #311, layer 2e)

* **`cEvs_mapRegs`**: the footprint does not depend on vreg names (`VRenaming`): the canonical
  allocation replaces every vreg (`straightEvs_mapRegs`), and the LL/SC loops' events only read
  the fixed registers x25/x26/x28;
* **`cEvs_setMem_common`**: the events of a memory instruction's footprint on `w` and on `w` with
  any other memory (`setMem M w`) are all at one common address, with the access size
  (`SegShape.memBytes`): the address is a function of the registers (straight-line forms:
  `AMode.addr` of the canonical state, `ldar`/`stlr`: its x0; the LL/SC loops: the address use
  `lo64 u` in x25, for both branches of the CAS loop);
* **`cEvs_setMem_atA`**: hence an address `a` all (at least one) events on `w` have is the
  address of every event on `setMem M w`.
-/

namespace Concurrency.CEvsInv

open Arm ArmFoot ArmThread ArmInstFoot Backend Backend.Proof Backend.Proof.Driver VCodeThread
  VCodeEvents Code VCodeAddr VCodeSize

/-! ## Renaming -/

theorem straightEvs_mapRegs {g : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming g gn) (ctx : FnCtx)
    (i : MInst) : straightEvs ctx (i.mapRegs g) = straightEvs ctx i := by
  funext uses w
  unfold straightEvs
  rw [operands_mapRegs hg]
  cases i.operands with
  | error e => rfl
  | ok ops =>
    simp only [Except.map]
    rw [canonRegs_rn, assign_mapRegs hg]
    have hp : placeUses (ops.map (rnOp gn)) (canonRegs ops) uses w =
        placeUses ops (canonRegs ops) uses w := by
      have hz : ((((ops.map (rnOp gn)).zip (canonRegs ops)).toList.filter
          (fun p => p.1.isUse)).map Prod.snd) =
          (((ops.zip (canonRegs ops)).toList.filter (fun p => p.1.isUse)).map Prod.snd) := by
        simp only [Array.toList_zip, Array.toList_map, zip_map_left]
        rw [filter_map_pair _ Operand.isUse (fun _ => rfl), List.map_map]
        rfl
      unfold placeUses
      rw [hz]
    rw [hp]

/-- **The footprint does not depend on vreg names.** -/
theorem cEvs_mapRegs {g : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming g gn)
    (F : BitVec 64 → Prop) (ctx : FnCtx) (i : MInst) :
    cEvs F ctx (i.mapRegs g) = cEvs F ctx i := by
  funext uses w
  unfold cEvs
  rw [isCtl_mapRegs]
  split
  · cases i <;> (try simp only [MInst.mapRegs]) <;> first
      | rfl
      | (rcases uses with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl)
  · rw [straightEvs_mapRegs hg]

/-! ## Straight-line forms: a common address on every memory -/

/-- A straight-line form whose canonical lines have their events at `A s` (a function of the
registers), on two memories. -/
theorem straight_common {ctx : FnCtx} {i ic : MInst} {uses : List CV} {w : ArmState}
    {ops : Array Operand} {A : ArmState → BitVec 64} {n : Nat}
    (hops : i.operands = .ok ops) (hic : i.assign (canonRegs ops) = .ok ic)
    (hev : ∀ s, CheckSPAlignment s → ∀ ls (ps : Backend.PState), ic.lines ctx {} = .ok (ls, ps) →
      AtA (A s) n (linesEvs env0 ls s))
    (hA : ∀ s M, A (setMem M s) = A s)
    (hc : ∀ r ∈ (canonRegs ops).toList, ∀ k, r = .x k → rnum k ≠ 31#5)
    (hal : CheckSPAlignment w) (M : Memory) :
    ∃ a, AtA a n (straightEvs ctx i uses w) ∧ AtA a n (straightEvs ctx i uses (setMem M w)) := by
  refine ⟨A (placeUses ops (canonRegs ops) uses w), ?_, ?_⟩
  · unfold straightEvs
    simp only [hops, hic]
    split
    · rename_i ls ps hls
      exact hev _ (spAlign_canon _ uses hal hc) ls ps hls
    · exact fun _ h => nomatch h
  · unfold straightEvs
    simp only [hops, hic]
    split
    · rename_i ls ps hls
      have h := hev (placeUses ops (canonRegs ops) uses (setMem M w))
        (spAlign_canon _ uses (w := setMem M w) (by rw [spAlign_setMem]; exact hal) hc) ls ps hls
      rw [placeUses_setMem, hA] at h
      rw [placeUses_setMem]
      exact h
    · exact fun _ h => nomatch h

theorem load_common {ctx : FnCtx} {op : LoadOp} {rd : Reg} {m : AMode} {fl : Clif.MemFlags}
    {uses : List CV} {w : ArmState} (hfo : FormOk ctx (.load op rd m fl) = true)
    (hal : CheckSPAlignment w) (M : Memory) :
    ∃ a, AtA a op.bytes (straightEvs ctx (.load op rd m fl) uses w) ∧
      AtA a op.bytes (straightEvs ctx (.load op rd m fl) uses (setMem M w)) := by
  rcases rd with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hfo
  obtain ⟨hop, hm⟩ := hfo
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm) <;>
  · exact straight_common rfl rfl
      (fun s hs' ls ps hl => (load_lines_evs ctx env0 op hop (d := 0) (by decide) fl
        (by mm_tac) s hs' hl).toA)
      (fun s M => addr_setMem ctx _ _ s M) (by canon_regs) hal M

theorem store_common {ctx : FnCtx} {op : StoreOp} {rd : Reg} {m : AMode} {fl : Clif.MemFlags}
    {uses : List CV} {w : ArmState} (hfo : FormOk ctx (.store op rd m fl) = true)
    (hal : CheckSPAlignment w) (M : Memory) :
    ∃ a, AtA a op.bytes (straightEvs ctx (.store op rd m fl) uses w) ∧
      AtA a op.bytes (straightEvs ctx (.store op rd m fl) uses (setMem M w)) := by
  rcases rd with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hfo
  obtain ⟨hop, hm⟩ := hfo
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm) <;>
  · exact straight_common rfl rfl
      (fun s hs' ls ps hl => (store_lines_evs ctx env0 op hop (d := 0) (by decide) fl
        (by mm_tac) s hs' hl).toA)
      (fun s M => addr_setMem ctx _ _ s M) (by canon_regs) hal M

theorem fpuLoad_common {ctx : FnCtx} {sz : ScalarSize} {rd : Reg} {m : AMode} {fl : Clif.MemFlags}
    {uses : List CV} {w : ArmState} (hfo : FormOk ctx (.fpuLoad sz rd m fl) = true)
    (hal : CheckSPAlignment w) (M : Memory) :
    ∃ a, AtA a sz.bytes (straightEvs ctx (.fpuLoad sz rd m fl) uses w) ∧
      AtA a sz.bytes (straightEvs ctx (.fpuLoad sz rd m fl) uses (setMem M w)) := by
  rcases rd with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, Bool.and_eq_true] at hfo
  obtain ⟨hsz, hm⟩ := hfo
  have hsz := fpSz_of_beq hsz
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm) <;>
  · exact straight_common rfl rfl
      (fun s hs' ls ps hl => (fpuLoad_lines_evs ctx env0 sz hsz (d := 0) (by decide) fl
        (by mm_tac) s hs' hl).toA)
      (fun s M => addr_setMem ctx _ _ s M) (by canon_regs) hal M

theorem fpuStore_common {ctx : FnCtx} {sz : ScalarSize} {rd : Reg} {m : AMode} {fl : Clif.MemFlags}
    {uses : List CV} {w : ArmState} (hfo : FormOk ctx (.fpuStore sz rd m fl) = true)
    (hal : CheckSPAlignment w) (M : Memory) :
    ∃ a, AtA a sz.bytes (straightEvs ctx (.fpuStore sz rd m fl) uses w) ∧
      AtA a sz.bytes (straightEvs ctx (.fpuStore sz rd m fl) uses (setMem M w)) := by
  rcases rd with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, Bool.and_eq_true] at hfo
  obtain ⟨hsz, hm⟩ := hfo
  have hsz := fpSz_of_beq hsz
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm) <;>
  · exact straight_common rfl rfl
      (fun s hs' ls ps hl => (fpuStore_lines_evs ctx env0 sz hsz (d := 0) (by decide) fl
        (by mm_tac) s hs' hl).toA)
      (fun s M => addr_setMem ctx _ _ s M) (by canon_regs) hal M

theorem loadAcquire_common {ctx : FnCtx} {ty : CTy} {rt rn : Reg} {fl : Clif.MemFlags}
    {uses : List CV} {w : ArmState} (hfo : FormOk ctx (.loadAcquire ty rt rn fl) = true)
    (hal : CheckSPAlignment w) (M : Memory) :
    ∃ a, AtA a ty.bytes (straightEvs ctx (.loadAcquire ty rt rn fl) uses w) ∧
      AtA a ty.bytes (straightEvs ctx (.loadAcquire ty rt rn fl) uses (setMem M w)) := by
  rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  all_goals rcases rn with ⟨a, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, decide_eq_true_eq] at hfo
  exact straight_common (ic := .loadAcquire ty (.x 1) (.x 0) fl) rfl rfl
    (fun s _ ls ps hl => by rw [lines_one rfl hl]; exact ldar_evs hfo env0 _ s)
    (fun s M => r_setMem _ M s) (by canon_regs) hal M

theorem storeRelease_common {ctx : FnCtx} {ty : CTy} {rt rn : Reg} {fl : Clif.MemFlags}
    {uses : List CV} {w : ArmState} (hfo : FormOk ctx (.storeRelease ty rt rn fl) = true)
    (hal : CheckSPAlignment w) (M : Memory) :
    ∃ a, AtA a ty.bytes (straightEvs ctx (.storeRelease ty rt rn fl) uses w) ∧
      AtA a ty.bytes (straightEvs ctx (.storeRelease ty rt rn fl) uses (setMem M w)) := by
  rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  all_goals rcases rn with ⟨a, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, decide_eq_true_eq] at hfo
  exact straight_common (ic := .storeRelease ty (.x 1) (.x 0) fl) rfl rfl
    (fun s _ ls ps hl => by rw [lines_one rfl hl]; exact stlr_evs hfo env0 _ s)
    (fun s M => r_setMem _ M s) (by canon_regs) hal M

/-- **The events of a covered straight-line memory form on two memories are at one address.** -/
theorem straightEvs_common {ctx : FnCtx} {i : MInst} {uses : List CV} {w : ArmState} {n : Nat}
    (hfo : FormOk ctx i = true) (hal : CheckSPAlignment w) (hn : SegShape.memBytes i = some n)
    (M : Memory) :
    ∃ a, AtA a n (straightEvs ctx i uses w) ∧ AtA a n (straightEvs ctx i uses (setMem M w)) := by
  cases i with
  | load =>
    simp only [SegShape.memBytes, Option.some.injEq] at hn; subst hn; exact load_common hfo hal M
  | store =>
    simp only [SegShape.memBytes, Option.some.injEq] at hn; subst hn; exact store_common hfo hal M
  | loadAcquire =>
    simp only [SegShape.memBytes, Option.some.injEq] at hn; subst hn
    exact loadAcquire_common hfo hal M
  | storeRelease =>
    simp only [SegShape.memBytes, Option.some.injEq] at hn; subst hn
    exact storeRelease_common hfo hal M
  | fpuLoad =>
    simp only [SegShape.memBytes, Option.some.injEq] at hn; subst hn; exact fpuLoad_common hfo hal M
  | fpuStore =>
    simp only [SegShape.memBytes, Option.some.injEq] at hn; subst hn; exact fpuStore_common hfo hal M
  | atomicRmwLoop => simp [FormOk] at hfo
  | atomicCasLoop => simp [FormOk] at hfo
  | _ => simp [SegShape.memBytes] at hn

/-! ## The LL/SC loops: every event at the address use -/

theorem rmwEvs_at {ty : CTy} (hty : AtomTy ty) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags)
    (u x : CV) {w : ArmState} (he : Arm.r .ERR w = .None) :
    AtA (lo64 u) ty.bytes (loopEvs (rmwLoopBody ty.bits op fl) [.x 25, .x 26] [u, x] w) := by
  have := rmwBody_evs hty op fl env0
    (([Reg.x 25, .x 26].zip [u, x]).foldl (fun s p => setReg s p.1 p.2) w)
    (by rw [err_two]; exact he)
  rwa [r25_two] at this

theorem casEvs_at {F : BitVec 64 → Prop} {ty : CTy} (hty : AtomTy ty) (fl : Clif.MemFlags)
    (u ex x : CV) {w : ArmState} (he : Arm.r .ERR w = .None) :
    AtA (lo64 u) ty.bytes (casEvs F ty fl u ex x w) := by
  have hhead : AtA (lo64 u) ty.bytes (loopEvs (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28]
      [u, ex, x] w) := by
    have := casHead_evs hty fl env0
      (([Reg.x 25, .x 26, .x 28].zip [u, ex, x]).foldl (fun s p => setReg s p.1 p.2) w)
      (by rw [err_three]; exact he)
    rwa [r25_three] at this
  unfold casEvs
  cases hL : loopSem F ty u (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [u, ex, x]
      [.x 27, .x 24] w with
  | none => exact hhead
  | some r1 =>
    obtain ⟨outs, t1, c1⟩ := r1
    obtain ⟨-, -, -, hrun⟩ := loopSem_some hL
    simp only
    split
    · exact hhead
    · intro e hmem
      rcases List.mem_append.mp hmem with h1 | h2
      · exact hhead e h1
      · obtain ⟨t', ht', -, -, hfr, -⟩ := casHead_spec hty fl env0
          (([Reg.x 25, .x 26, .x 28].zip [u, ex, x]).foldl (fun s p => setReg s p.1 p.2) w)
          (by rw [err_three]; exact he)
        rw [ht'] at hrun
        simp only [Option.some.injEq] at hrun
        have h25 : Arm.r (.GPR 25#5) t1 = lo64 u := by
          rw [← hrun, hfr (.GPR 25#5) (by simp) (by simp) (by simp), r25_three]
        have := casStore_evs hty fl env0 t1 e h2
        rwa [h25] at this

/-! ## `csem` -/

theorem common_nil (n : Nat) : ∃ a : BitVec 64, AtA a n [] ∧ AtA a n [] :=
  ⟨0, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩

/-- **The events of a memory instruction's footprint on two memories are at one address**, of
its access size (every instruction but calls; an error-free world; a straight-line form covered
by `csem`'s canonical run on an aligned world; a step on `w`). -/
theorem cEvs_setMem_common {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    {u : List CV} {w : ArmState} {r : List CV × ArmState × Ctl} {n : Nat}
    (he : Arm.r .ERR w = .None)
    (hst : i.isCtl = false → csemWF ctx i u = true ∧ CheckSPAlignment w)
    (h : csem F ctx X i u w = some r) (hn : SegShape.memBytes i = some n) (M : Memory) :
    ∃ a, AtA a n (cEvs F ctx i u w) ∧ AtA a n (cEvs F ctx i u (setMem M w)) := by
  have he' : Arm.r .ERR (setMem M w) = .None := by rw [err_setMem]; exact he
  unfold cEvs
  by_cases hc : i.isCtl = true
  · simp only [hc, ite_true]
    cases i with
    | atomicRmwLoop ty op fl a b c d e =>
      simp only [SegShape.memBytes, Option.some.injEq] at hn
      subst hn
      rcases u with _ | ⟨u, _ | ⟨x, _ | ⟨y, t⟩⟩⟩ <;> try exact common_nil _
      simp only [csem, he, ite_true] at h
      obtain ⟨hty, -⟩ := loopSem_some h
      exact ⟨lo64 u, rmwEvs_at hty op fl u x he, rmwEvs_at hty op fl u x he'⟩
    | atomicCasLoop ty fl a b c d e =>
      simp only [SegShape.memBytes, Option.some.injEq] at hn
      subst hn
      rcases u with _ | ⟨u, _ | ⟨ex, _ | ⟨x, _ | ⟨y, t⟩⟩⟩⟩ <;> try exact common_nil _
      simp only [csem, he, ite_true] at h
      cases hL : loopSem F ty u (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [u, ex, x]
          [.x 27, .x 24] w with
      | none => rw [hL] at h; cases h
      | some r1 =>
        obtain ⟨hty, -⟩ := loopSem_some hL
        exact ⟨lo64 u, casEvs_at hty fl u ex x he, casEvs_at hty fl u ex x he'⟩
    | _ =>
      first
      | exact common_nil n
      | (simp only [MInst.isCtl] at hc; cases hc)
  · have hc' : i.isCtl = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ite_false]
    obtain ⟨hwf, hal⟩ := hst hc'
    have hfo : FormOk ctx i = true := by
      simp only [csemWF, Bool.and_eq_true] at hwf
      exact hwf.1
    exact straightEvs_common hfo hal hn M

/-- **The address of a memory instruction's footprint does not depend on memory**: when the
events on `w` (at least one) are at `a` with the access size, so are the events on `setMem M w`. -/
theorem cEvs_setMem_atA {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    {u : List CV} {w : ArmState} {r : List CV × ArmState × Ctl} {n : Nat} {a : BitVec 64}
    (he : Arm.r .ERR w = .None)
    (hst : i.isCtl = false → csemWF ctx i u = true ∧ CheckSPAlignment w)
    (h : csem F ctx X i u w = some r) (hn : SegShape.memBytes i = some n) (M : Memory)
    (hne : cEvs F ctx i u w ≠ []) (hA : AtA a n (cEvs F ctx i u w)) :
    AtA a n (cEvs F ctx i u (setMem M w)) := by
  obtain ⟨a', h1, h2⟩ := cEvs_setMem_common he hst h hn M
  obtain ⟨e, hmem⟩ := List.exists_mem_of_ne_nil _ hne
  have : a = a' := (hA e hmem).1.symm.trans (h1 e hmem).1
  rw [this]
  exact h2

end Concurrency.CEvsInv
