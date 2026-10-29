module

public import FV.Concurrency.VCodeFrame
public import FV.Concurrency.SegShape
public import FV.Concurrency.IselCover

@[expose] public section

/-!
# The sizes of a VCode instruction's events (T2h, #311, layer 2e)

`VCodeAddr.cEvs_avoid` places the events of `csem`'s precise footprint `cEvs` outside a frame;
this file gives their **size**: every event of a memory instruction's footprint has the
instruction's access size `SegShape.memBytes`, at one address (`OneAcc`):

* straight-line forms (`straightEvs_size`): the canonical run's one event of a load/store (GPR
  and SIMD&FP, every covered addressing mode) has the access size at `AMode.addr`
  (`VCodeAddr.load_lines_evs` …), `ldar`/`stlr` at x0 (`ldar_evs`, `stlr_evs`);
* the LL/SC loops (`cEvs_size`): every event is at x25 with the access size (`rmwBody_evs`,
  `casHead_evs`, `casStore_evs`);
* **`addr_eq_of_oneAcc`**: when the events of one access of `n` bytes cover every byte of an
  access `[a, a + n)` (no wrap-around, `n ≤ 2^63`), every event is at `a` with `n` bytes: with
  `IselCover.cover_of_not_runOut`, the segment's event *is* the CLIF access.
-/

namespace Concurrency.VCodeSize

open Arm ArmFoot ArmThread ArmInstFoot Backend Backend.Proof VCodeThread VCodeEvents Code VCodeAddr

/-- Every event of `evs` is at one address with `n` bytes. -/
def OneAcc (n : Nat) (evs : List Ev) : Prop := ∃ a, AtA a n evs

theorem oneAcc_nil (n : Nat) : OneAcc n [] := ⟨0, fun _ h => nomatch h⟩

theorem oneAcc_append {n : Nat} {a : BitVec 64} {e1 e2 : List Ev} (h1 : AtA a n e1)
    (h2 : AtA a n e2) : OneAcc n (e1 ++ e2) :=
  ⟨a, fun e he => (List.mem_append.mp he).elim (h1 e) (h2 e)⟩

/-! ## Straight-line forms -/

/-- **A straight-line form with one access**: when every run of its canonical allocation's lines
has its events at one address with `n` bytes, so do its `straightEvs`. -/
theorem straight_size_of {ctx : FnCtx} {i ic : MInst} {uses : List CV} {w : ArmState}
    {ops : Array Operand} {A : ArmState → BitVec 64} {n : Nat}
    (hops : i.operands = .ok ops) (hic : i.assign (canonRegs ops) = .ok ic)
    (hev : ∀ s, CheckSPAlignment s → ∀ ls (ps : Backend.PState), ic.lines ctx {} = .ok (ls, ps) →
      AtA (A s) n (linesEvs env0 ls s))
    (hal : CheckSPAlignment (placeUses ops (canonRegs ops) uses w)) :
    OneAcc n (straightEvs ctx i uses w) := by
  unfold straightEvs
  simp only [hops, hic]
  split
  · rename_i ls ps hls
    exact ⟨_, hev _ hal ls ps hls⟩
  · exact oneAcc_nil n

theorem load_size {ctx : FnCtx} {op : LoadOp} {rd : Reg} {m : AMode} {fl : Clif.MemFlags}
    {uses : List CV} {w : ArmState} (hfo : FormOk ctx (.load op rd m fl) = true)
    (hal : CheckSPAlignment w) : OneAcc op.bytes (straightEvs ctx (.load op rd m fl) uses w) := by
  rcases rd with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hfo
  obtain ⟨hop, hm⟩ := hfo
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm) <;>
  · exact straight_size_of rfl rfl
      (fun s hs' ls ps hl => (load_lines_evs ctx env0 op hop (d := 0) (by decide) fl
        (by mm_tac) s hs' hl).toA)
      (spAlign_canon _ uses hal (by canon_regs))

theorem store_size {ctx : FnCtx} {op : StoreOp} {rd : Reg} {m : AMode} {fl : Clif.MemFlags}
    {uses : List CV} {w : ArmState} (hfo : FormOk ctx (.store op rd m fl) = true)
    (hal : CheckSPAlignment w) : OneAcc op.bytes (straightEvs ctx (.store op rd m fl) uses w) := by
  rcases rd with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hfo
  obtain ⟨hop, hm⟩ := hfo
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm) <;>
  · exact straight_size_of rfl rfl
      (fun s hs' ls ps hl => (store_lines_evs ctx env0 op hop (d := 0) (by decide) fl
        (by mm_tac) s hs' hl).toA)
      (spAlign_canon _ uses hal (by canon_regs))

theorem fpuLoad_size {ctx : FnCtx} {sz : ScalarSize} {rd : Reg} {m : AMode} {fl : Clif.MemFlags}
    {uses : List CV} {w : ArmState} (hfo : FormOk ctx (.fpuLoad sz rd m fl) = true)
    (hal : CheckSPAlignment w) : OneAcc sz.bytes (straightEvs ctx (.fpuLoad sz rd m fl) uses w) := by
  rcases rd with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, Bool.and_eq_true] at hfo
  obtain ⟨hsz, hm⟩ := hfo
  have hsz := fpSz_of_beq hsz
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm) <;>
  · exact straight_size_of rfl rfl
      (fun s hs' ls ps hl => (fpuLoad_lines_evs ctx env0 sz hsz (d := 0) (by decide) fl
        (by mm_tac) s hs' hl).toA)
      (spAlign_canon _ uses hal (by canon_regs))

theorem fpuStore_size {ctx : FnCtx} {sz : ScalarSize} {rd : Reg} {m : AMode} {fl : Clif.MemFlags}
    {uses : List CV} {w : ArmState} (hfo : FormOk ctx (.fpuStore sz rd m fl) = true)
    (hal : CheckSPAlignment w) :
    OneAcc sz.bytes (straightEvs ctx (.fpuStore sz rd m fl) uses w) := by
  rcases rd with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, Bool.and_eq_true] at hfo
  obtain ⟨hsz, hm⟩ := hfo
  have hsz := fpSz_of_beq hsz
  unfold memOk at hm
  split at hm <;> (try cases hm) <;> (try simp only [decide_eq_true_eq] at hm) <;>
  · exact straight_size_of rfl rfl
      (fun s hs' ls ps hl => (fpuStore_lines_evs ctx env0 sz hsz (d := 0) (by decide) fl
        (by mm_tac) s hs' hl).toA)
      (spAlign_canon _ uses hal (by canon_regs))

theorem loadAcquire_size {ctx : FnCtx} {ty : CTy} {rt rn : Reg} {fl : Clif.MemFlags}
    {uses : List CV} {w : ArmState} (hfo : FormOk ctx (.loadAcquire ty rt rn fl) = true)
    (hal : CheckSPAlignment w) :
    OneAcc ty.bytes (straightEvs ctx (.loadAcquire ty rt rn fl) uses w) := by
  rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  all_goals rcases rn with ⟨a, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, decide_eq_true_eq] at hfo
  exact straight_size_of (ic := .loadAcquire ty (.x 1) (.x 0) fl) rfl rfl
    (fun s _ ls ps hl => by rw [lines_one rfl hl]; exact ldar_evs hfo env0 _ s)
    (spAlign_canon _ uses hal (by canon_regs))

theorem storeRelease_size {ctx : FnCtx} {ty : CTy} {rt rn : Reg} {fl : Clif.MemFlags}
    {uses : List CV} {w : ArmState} (hfo : FormOk ctx (.storeRelease ty rt rn fl) = true)
    (hal : CheckSPAlignment w) :
    OneAcc ty.bytes (straightEvs ctx (.storeRelease ty rt rn fl) uses w) := by
  rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  all_goals rcases rn with ⟨a, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
  simp only [FormOk, decide_eq_true_eq] at hfo
  exact straight_size_of (ic := .storeRelease ty (.x 1) (.x 0) fl) rfl rfl
    (fun s _ ls ps hl => by rw [lines_one rfl hl]; exact stlr_evs hfo env0 _ s)
    (spAlign_canon _ uses hal (by canon_regs))

/-- **The events of a covered straight-line memory form have its access size** (at one
address). -/
theorem straightEvs_size {ctx : FnCtx} {i : MInst} {uses : List CV} {w : ArmState} {n : Nat}
    (hfo : FormOk ctx i = true) (hal : CheckSPAlignment w) (hn : SegShape.memBytes i = some n) :
    OneAcc n (straightEvs ctx i uses w) := by
  cases i with
  | load => simp only [SegShape.memBytes, Option.some.injEq] at hn; subst hn; exact load_size hfo hal
  | store => simp only [SegShape.memBytes, Option.some.injEq] at hn; subst hn; exact store_size hfo hal
  | loadAcquire =>
    simp only [SegShape.memBytes, Option.some.injEq] at hn; subst hn; exact loadAcquire_size hfo hal
  | storeRelease =>
    simp only [SegShape.memBytes, Option.some.injEq] at hn; subst hn; exact storeRelease_size hfo hal
  | fpuLoad => simp only [SegShape.memBytes, Option.some.injEq] at hn; subst hn; exact fpuLoad_size hfo hal
  | fpuStore =>
    simp only [SegShape.memBytes, Option.some.injEq] at hn; subst hn; exact fpuStore_size hfo hal
  | atomicRmwLoop => simp [FormOk] at hfo
  | atomicCasLoop => simp [FormOk] at hfo
  | _ => simp [SegShape.memBytes] at hn

/-! ## `csem` -/

/-- **The events of a successful `csem` step of a memory instruction have its access size**, at
one address (every instruction but calls; an error-free world; a straight-line form covered by
`csem`'s canonical run on an aligned world, as `ifoot_csem`). -/
theorem cEvs_size {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst} {uses : List CV}
    {w : ArmState} {r : List CV × ArmState × Ctl} {n : Nat} (he : Arm.r .ERR w = .None)
    (hst : i.isCtl = false → csemWF ctx i uses = true ∧ CheckSPAlignment w)
    (h : csem F ctx X i uses w = some r) (hn : SegShape.memBytes i = some n) :
    OneAcc n (cEvs F ctx i uses w) := by
  unfold cEvs
  by_cases hc : i.isCtl = true
  · simp only [hc, ite_true]
    cases i with
    | atomicRmwLoop ty op fl a b c d e =>
      simp only [SegShape.memBytes, Option.some.injEq] at hn
      subst hn
      rcases uses with _ | ⟨u, _ | ⟨x, _ | ⟨y, t⟩⟩⟩ <;> try exact oneAcc_nil _
      simp only [csem, he, ite_true] at h
      obtain ⟨hty, -, herr, -⟩ := loopSem_some h
      refine ⟨lo64 u, ?_⟩
      have := rmwBody_evs hty op fl env0
        (([Reg.x 25, .x 26].zip [u, x]).foldl (fun s p => setReg s p.1 p.2) w)
        (by rw [err_two]; exact herr)
      rwa [r25_two] at this
    | atomicCasLoop ty fl a b c d e =>
      simp only [SegShape.memBytes, Option.some.injEq] at hn
      subst hn
      rcases uses with _ | ⟨u, _ | ⟨ex, _ | ⟨x, _ | ⟨y, t⟩⟩⟩⟩ <;> try exact oneAcc_nil _
      simp only [csem, he, ite_true] at h
      unfold casEvs
      cases hL : loopSem F ty u (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [u, ex, x]
          [.x 27, .x 24] w with
      | none => rw [hL] at h; cases h
      | some r1 =>
        obtain ⟨outs, t1, c1⟩ := r1
        obtain ⟨hty, -, herr, hrun⟩ := loopSem_some hL
        have hhead : AtA (lo64 u) ty.bytes (loopEvs (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28]
            [u, ex, x] w) := by
          have := casHead_evs hty fl env0
            (([Reg.x 25, .x 26, .x 28].zip [u, ex, x]).foldl (fun s p => setReg s p.1 p.2) w)
            (by rw [err_three]; exact herr)
          rwa [r25_three] at this
        simp only [hL]
        by_cases hne : Arm.ConditionHolds Cond.ne.bits t1 = true
        · rw [if_pos hne]; exact ⟨_, hhead⟩
        · rw [if_neg hne]
          refine oneAcc_append hhead ?_
          obtain ⟨t', ht', -, -, hfr, -⟩ := casHead_spec hty fl env0
            (([Reg.x 25, .x 26, .x 28].zip [u, ex, x]).foldl (fun s p => setReg s p.1 p.2) w)
            (by rw [err_three]; exact herr)
          rw [ht'] at hrun
          simp only [Option.some.injEq] at hrun
          have h25 : Arm.r (.GPR 25#5) t1 = lo64 u := by
            rw [← hrun, hfr (.GPR 25#5) (by simp) (by simp) (by simp), r25_three]
          have := casStore_evs hty fl env0 t1
          rw [h25] at this
          exact this
    | _ =>
      first
      | exact oneAcc_nil n
      | (simp only [MInst.isCtl] at hc; cases hc)
  · have hc' : i.isCtl = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ite_false]
    obtain ⟨hwf, hal⟩ := hst hc'
    have hfo : FormOk ctx i = true := by
      simp only [csemWF, Bool.and_eq_true] at hwf
      exact hwf.1
    exact straightEvs_size hfo hal hn

/-! ## The event of a covered access -/

/-- **Events of one access of `n` bytes covering every byte of `[a, a + n)` are that access**:
each is at `a` (no wrap-around: `a + n ≤ 2^64`, `n ≤ 2^63`). -/
theorem addr_eq_of_oneAcc {evs : List Ev} {a n : Nat} (hn : 0 < n) (hn2 : n ≤ 2 ^ 63)
    (ha : a + n ≤ 2 ^ 64) (h1 : OneAcc n evs)
    (hcov : ∀ k < n, ∃ e ∈ evs, ∃ j < e.n, e.addr + BitVec.ofNat 64 j = BitVec.ofNat 64 (a + k)) :
    AtA (BitVec.ofNat 64 a) n evs := by
  obtain ⟨A, hA⟩ := h1
  have hAa : A = BitVec.ofNat 64 a := IselCover.addr_eq_of_cover hn hn2 ha fun k hk => by
    obtain ⟨e, he, j, hj, hx⟩ := hcov k hk
    obtain ⟨h1, h2⟩ := hA e he
    rw [h1] at hx
    exact ⟨j, by omega, hx⟩
  rw [← hAa]
  exact hA

end Concurrency.VCodeSize
