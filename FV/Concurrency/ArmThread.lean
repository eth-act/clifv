module

public import FV.Concurrency.ArmFootprint
public import FV.Concurrency.Armv8

@[expose] public section

/-!
# Per-thread event semantics of the Arm model (T2d, #302)

One thread of the Arm model, run against a memory it shares with other threads. A step of the
thread is a step of a single-core machine `f` (`Arm.stepi`, or the E2E machine `ArmStepX X H fa`)
that reads the bytes of its read events from the environment and writes its write events to it:

* **events** (`Ev`): an access of the kind of the instruction (`AKind` of
  `FV/Concurrency/Armv8.lean`: `ldr`/`str` plain, `ldar` acquire, `stlr` release, `ldaxr`/`stlxr`
  exclusive, `dmb ish`), its address, size and bytes. A read's bytes are chosen by the
  environment (any value; the memory model decides which values are consistent);
* **footprints** (`Footprint f s evs`): the step at `s`, run on *any* memory holding the read
  events' bytes, writes exactly the write events and leaves the same registers. This is the
  semantic condition of footprint-based thread semantics (CompCertTSO-style); it makes the
  semantics sound by construction. Precise footprints: no event for the non-memory instructions
  (`footprint_nonldst`, from `ArmFootprint.stepi_setMem`) and the single access of
  `ldar`/`stlr`/`ldxr`/`ldaxr`/`stxr`/`stlxr` (`footprint_load_excl`, `footprint_store_excl`);
* **the exclusive monitor** (`Mon`): an exclusive load (`ldxr`/`ldaxr`) arms it with its address
  and size; a store exclusive (`stxr`/`stlxr`) and `clrex` disarm it. A store exclusive either
  succeeds (an ordinary step of `f`, `Rs := 0`, a write event), allowed by the policy when the
  monitor is armed, or **fails** (`TStep.xfail`: no memory access, `Rs := 1`, as the Arm ARM's
  `ExclusiveMonitorsPass` false branch), allowed at any time (the global monitor may be lost to
  another core's write, and a failure is architecturally always permitted). Cranelift's LL/SC
  loops retry on failure (`cbnz w24, loop`; `Witness.retry_*`).

The existing single-core model is the special case (`Policy.sc`: a monitor that never fails, every
store exclusive succeeds) against a sequentially consistent memory (every read returns the bytes of
the current memory, `SCRun`): `step_sc` (such a step *is* the step of `f`), `run_sc` (such a run is
`f` iterated: `Arm.run` for `f = stepi`), and conversely `exists_step_sc`/`exists_run_sc` (every run
of `f` is one). Under the Arm policy `Policy.arm` a store exclusive can fail
(`Witness.retry_xfail`), which the single-core model cannot (`no_xfail_sc`). Plan:
`docs/plans/atomics.md` (T2d).
-/

namespace Concurrency.ArmThread

open Arm ArmFoot

/-! ## Events and footprints -/

/-- A memory event of a step: its kind, address, size in bytes and bytes (`dmb`: no bytes). -/
structure Ev where
  k : AKind
  addr : BitVec 64
  n : Nat
  val : BitVec (n * 8)

/-- The memory `m` holds the bytes of the read events. -/
def Agrees (evs : List Ev) (m : Memory) : Prop :=
  ∀ e ∈ evs, e.k.dir = .R → readM e.n e.addr m = e.val

/-- The write events applied to `m`, in order. -/
def applyW : List Ev → Memory → Memory
  | [], m => m
  | e :: es, m => applyW es (if e.k.dir = .W then writeM e.n e.addr e.val m else m)

/-- The read events' bytes stored in `m` (the memory the thread reads from). -/
def applyR : List Ev → Memory → Memory
  | [], m => m
  | e :: es, m => applyR es (if e.k.dir = .R then writeM e.n e.addr e.val m else m)

/-- **The footprint of the step of `f` at `s`**: on every memory holding the read events' bytes,
the step writes exactly the write events and leaves the registers of the step from the memory
`applyR evs s.mem`. -/
def Footprint (f : ArmState → ArmState) (s : ArmState) (evs : List Ev) : Prop :=
  ∀ m, Agrees evs m → f (setMem m s) = setMem (applyW evs m) (f (setMem (applyR evs s.mem) s))

theorem applyR_of_agrees : ∀ {evs : List Ev} {m : Memory}, Agrees evs m → applyR evs m = m
  | [], _, _ => rfl
  | e :: es, m, h => by
    simp only [applyR]
    have h' : Agrees es m := fun e' he' => h e' (List.mem_cons_of_mem _ he')
    split
    · rename_i hr
      rw [← h e List.mem_cons_self hr, writeM_readM, applyR_of_agrees h']
    · exact applyR_of_agrees h'

/-! ## Instruction classes and the exclusive monitor -/

/-- What the instruction at the pc is for the memory model. -/
inductive Cls where
  /-- any other instruction: plain accesses or none -/
  | plain
  /-- `ldar` -/
  | ldar
  /-- `stlr` -/
  | stlr
  /-- `ldxr` (`acq = false`) / `ldaxr` (`acq = true`) of `2 ^ size` bytes at `[Rn]` -/
  | ldx (acq : Bool) (rn : BitVec 5) (size : BitVec 2)
  /-- `stxr` / `stlxr` with status register `rs` -/
  | stx (rel : Bool) (rs rn : BitVec 5)
  /-- `dmb`/`dsb` over all access types (`CRm<1:0> = 11`): a full barrier -/
  | dmb
  /-- `clrex` -/
  | clrex
  deriving DecidableEq

/-- The class of the instruction at the pc of `s`. -/
def cls (s : ArmState) : Cls :=
  match decodeAt s with
  | some (.LDST (.Reg_exclusive i)) =>
    if i.ord = 1#1 then (if i.L = 1#1 then .ldar else .stlr)
    else if i.L = 1#1 then .ldx (i.o0 = 1#1) i.Rn i.size
    else .stx (i.o0 = 1#1) i.Rs i.Rn
  | some (.BR (.Barrier i)) =>
    if (i.op2 = 0b101#3 ∨ i.op2 = 0b100#3) ∧ i.CRm.extractLsb' 0 2 = 0b11#2 then .dmb
    else if i.op2 = 0b010#3 then .clrex
    else .plain
  | _ => .plain

/-- The kind of an event of direction `d` of an instruction of class `c` (`none`: not allowed). -/
def Cls.kind : Cls → Dir → Option AKind
  | .ldar, .R => some .acqR
  | .stlr, .W => some .relW
  | .ldx true _ _, .R => some .acqXR
  | .stx true _ _, .W => some .relXW
  | .dmb, .F => some .dmb
  | _, .R => some .plainR
  | _, .W => some .plainW
  | _, .F => none

/-- The events have the kinds of the class (a full barrier has its `dmb` event). -/
def KindsOk (c : Cls) (evs : List Ev) : Prop :=
  (∀ e ∈ evs, c.kind e.k.dir = some e.k) ∧ (c = .dmb → ∃ e ∈ evs, e.k = .dmb)

/-- The local exclusive monitor: armed with an address and a size, or open. -/
abbrev Mon := Option (BitVec 64 × Nat)

/-- The monitor after a non-failing step of class `c` from `s`. -/
def monAfter (c : Cls) (s : ArmState) (mon : Mon) : Mon :=
  match c with
  | .ldx _ rn size => some (read_gpr 64 rn s, 2 ^ size.toNat)
  | .stx .. | .clrex => none
  | _ => mon

/-- When a store exclusive may succeed and when it may fail. -/
structure Policy where
  succ : Mon → Prop
  fail : Mon → Prop

/-- **The Arm policy**: success needs an armed monitor (Arm ARM: a store exclusive with the local
monitor in the Open Access state fails); failure is always possible. -/
def Policy.arm : Policy := ⟨fun mon => mon.isSome, fun _ => True⟩

/-- **The single-core policy**: a monitor that never fails (`Arm.stepi`'s store exclusive always
succeeds). -/
def Policy.sc : Policy := ⟨fun _ => True, fun _ => False⟩

/-- The state after a failed store exclusive: `Rs := 1`, next instruction. -/
def failState (rs : BitVec 5) (s : ArmState) : ArmState :=
  write_pc (read_pc s + 4#64) (write_gpr_zr 32 rs 1#32 s)

/-- A label of a thread step: its events and whether it is a failed store exclusive. -/
structure Lab where
  evs : List Ev
  xfail : Bool

/-- **One step of the thread** running the machine `f` under the monitor policy `P`. -/
inductive TStep (P : Policy) (f : ArmState → ArmState) : ArmState × Mon → Lab → ArmState × Mon → Prop
  /-- an instruction with the events `evs` (a store exclusive: a successful one) -/
  | exec {s : ArmState} {mon : Mon} {evs : List Ev} :
      KindsOk (cls s) evs → Agrees evs (applyR evs s.mem) → Footprint f s evs →
      (∀ rel rs rn, cls s = .stx rel rs rn → P.succ mon) →
      TStep P f (s, mon) ⟨evs, false⟩ (f (setMem (applyR evs s.mem) s), monAfter (cls s) s mon)
  /-- a failing store exclusive: no access, `Rs := 1` -/
  | xfail {s : ArmState} {mon : Mon} {rel : Bool} {rs rn : BitVec 5} :
      cls s = .stx rel rs rn → P.fail mon → read_err s = .None →
      ¬ (rn = 31#5 ∧ ¬ CheckSPAlignment s) →
      TStep P f (s, mon) ⟨[], true⟩ (failState rs s, none)

/-- A run of the thread: its steps' labels in program order. -/
inductive TRun (P : Policy) (f : ArmState → ArmState) : ArmState × Mon → List Lab → ArmState × Mon → Prop
  | nil {t} : TRun P f t [] t
  | cons {t t' t'' l ls} : TStep P f t l t' → TRun P f t' ls t'' → TRun P f t (l :: ls) t''

/-- A run against a sequentially consistent memory: every read returns the bytes of the memory
of the moment (the thread's own memory, which only it writes). -/
inductive SCRun (P : Policy) (f : ArmState → ArmState) : ArmState × Mon → List Lab → ArmState × Mon → Prop
  | nil {t} : SCRun P f t [] t
  | cons {t t' t'' l ls} : TStep P f t l t' → Agrees l.evs t.1.mem → SCRun P f t' ls t'' →
      SCRun P f t (l :: ls) t''

/-! ## The single-core model is the special case -/

/-- `f` iterated `n` times (the shape of `Arm.run` and `E2E.runX`). -/
def iter (f : ArmState → ArmState) : Nat → ArmState → ArmState
  | 0, s => s
  | n + 1, s => iter f n (f s)

/-- **A step against SC memory that is not a failing store exclusive is the step of `f`.** -/
theorem step_sc {P : Policy} {f : ArmState → ArmState} {t t' : ArmState × Mon} {l : Lab}
    (h : TStep P f t l t') (hag : Agrees l.evs t.1.mem) (hx : l.xfail = false) : t'.1 = f t.1 := by
  cases h with
  | exec _ _ _ _ =>
    show f (setMem (applyR _ _) _) = _
    rw [applyR_of_agrees hag, setMem_self]
  | xfail => cases hx

/-- **The memory after a step is the memory before with the write events applied.** -/
theorem step_mem {P : Policy} {f : ArmState → ArmState} {t t' : ArmState × Mon} {l : Lab}
    (h : TStep P f t l t') (hag : Agrees l.evs t.1.mem) : t'.1.mem = applyW l.evs t.1.mem := by
  cases h with
  | @exec s _ evs _ _ hfp _ =>
    show (f (setMem (applyR evs s.mem) s)).mem = _
    rw [applyR_of_agrees hag, setMem_self]
    have := congrArg ArmState.mem (hfp s.mem hag)
    rwa [setMem_self, setMem_mem] at this
  | xfail =>
    show (failState _ _).mem = _
    simp only [failState, write_pc, write_gpr_zr, write_gpr]
    split <;> simp only [w_mem] <;> rfl

/-- The single-core monitor never fails. -/
theorem no_xfail_sc {f : ArmState → ArmState} {t t' : ArmState × Mon} {l : Lab}
    (h : TStep Policy.sc f t l t') : l.xfail = false := by
  cases h with
  | exec => rfl
  | xfail _ hf => exact absurd hf id

/-- **A run against SC memory under the never-failing monitor is the iterated single-core
step.** -/
theorem run_sc {f : ArmState → ArmState} {t t' : ArmState × Mon} {ls : List Lab}
    (h : SCRun Policy.sc f t ls t') : t'.1 = iter f ls.length t.1 := by
  induction h with
  | nil => rfl
  | cons hs hag _ ih =>
    rw [ih, step_sc hs hag (no_xfail_sc hs)]
    simp only [List.length_cons, iter]

/-- `Arm.run` is `stepi` iterated. -/
theorem run_eq_iter (n : Nat) (s : ArmState) : run n s = iter stepi n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [run, ih, iter]

/-- **The single-core Arm model is the thread semantics against SC memory with a never-failing
monitor** (`f = stepi`). -/
theorem run_sc_stepi {t t' : ArmState × Mon} {ls : List Lab}
    (h : SCRun Policy.sc stepi t ls t') : t'.1 = run ls.length t.1 := by
  rw [run_eq_iter]; exact run_sc h

/-! ## Every single-core step is a step of the thread -/

/-- The read event of the whole memory, of kind `k` (the coarse footprint). -/
def Ev.full (k : AKind) (m : Memory) : Ev := ⟨k, 0, 2 ^ 64, readM (2 ^ 64) 0 m⟩

/-- The coarse events of a step from `s` to `s'`: read the whole memory, write the whole memory
(and the barrier event of a `dmb`). -/
def coarse (c : Cls) (s s' : ArmState) : List Ev :=
  [Ev.full ((c.kind .R).getD .plainR) s.mem, Ev.full ((c.kind .W).getD .plainW) s'.mem] ++
    (if c = .dmb then [⟨.dmb, 0, 0, 0#0⟩] else [])

theorem kind_R (c : Cls) : ∃ k, c.kind .R = some k ∧ k.dir = .R := by
  cases c <;> simp only [Cls.kind] <;> (try rename_i b _ _; cases b) <;> simp [AKind.dir]

theorem kind_W (c : Cls) : ∃ k, c.kind .W = some k ∧ k.dir = .W := by
  cases c <;> simp only [Cls.kind] <;> (try rename_i b _ _; cases b) <;> simp [AKind.dir]

theorem coarse_dirR (c : Cls) : ((c.kind .R).getD .plainR).dir = .R := by
  obtain ⟨k, hk, hd⟩ := kind_R c; rw [hk]; exact hd

theorem coarse_dirW (c : Cls) : ((c.kind .W).getD .plainW).dir = .W := by
  obtain ⟨k, hk, hd⟩ := kind_W c; rw [hk]; exact hd

theorem coarse_kinds (c : Cls) (s s' : ArmState) : KindsOk c (coarse c s s') := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [coarse, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with (rfl | rfl) | he
    · simp only [Ev.full, coarse_dirR]; obtain ⟨k, hk, -⟩ := kind_R c; rw [hk]; rfl
    · simp only [Ev.full, coarse_dirW]; obtain ⟨k, hk, -⟩ := kind_W c; rw [hk]; rfl
    · split at he
      · subst c; simp only [List.mem_singleton] at he; subst he; rfl
      · simp at he
  · intro hc; subst hc
    exact ⟨⟨.dmb, 0, 0, 0#0⟩, by simp [coarse], rfl⟩

theorem coarse_agrees (c : Cls) (s s' : ArmState) : Agrees (coarse c s s') s.mem := by
  intro e he hr
  simp only [coarse, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with (rfl | rfl) | he
  · rfl
  · simp only [Ev.full, coarse_dirW] at hr; cases hr
  · split at he
    · simp only [List.mem_singleton] at he; subst he; cases hr
    · simp at he

theorem applyW_coarse (c : Cls) (s s' : ArmState) (m : Memory) :
    applyW (coarse c s s') m = s'.mem := by
  simp only [coarse, List.cons_append, List.nil_append, applyW, Ev.full, coarse_dirR, coarse_dirW]
  simp only [show (Dir.R = Dir.W) = False from by simp, ite_false, ite_true]
  rw [writeM_full _ _ m s'.mem, writeM_readM]
  split
  · simp only [applyW, AKind.dir]; rfl
  · rfl

/-- **Every step of `f` is a step of the thread against SC memory** (with the coarse footprint;
under the never-failing monitor). -/
theorem exists_step_sc (f : ArmState → ArmState) (s : ArmState) (mon : Mon) :
    ∃ l, Agrees l.evs s.mem ∧ l.xfail = false ∧
      TStep Policy.sc f (s, mon) l (f s, monAfter (cls s) s mon) := by
  have hag := coarse_agrees (cls s) s (f s)
  refine ⟨⟨coarse (cls s) s (f s), false⟩, hag, rfl, ?_⟩
  have e : f s = f (setMem (applyR (coarse (cls s) s (f s)) s.mem) s) := by
    rw [applyR_of_agrees hag, setMem_self]
  conv => rhs; rw [e]
  refine TStep.exec (coarse_kinds _ _ _) (by rw [applyR_of_agrees hag]; exact hag) ?_
    (fun _ _ _ _ => trivial)
  intro m hm
  have hm' : m = s.mem := by
    have h0 := hm (Ev.full (((cls s).kind .R).getD .plainR) s.mem) (by simp [coarse])
      (by simp only [Ev.full, coarse_dirR])
    exact readM_full_inj h0
  subst hm'
  rw [applyR_of_agrees hag, setMem_self, applyW_coarse, setMem_self]

/-- **Every run of `f` is a run of the thread against SC memory under the never-failing
monitor.** -/
theorem exists_run_sc (f : ArmState → ArmState) :
    ∀ (n : Nat) (s : ArmState) (mon : Mon), ∃ ls mon', ls.length = n ∧
      SCRun Policy.sc f (s, mon) ls (iter f n s, mon')
  | 0, s, mon => ⟨[], mon, rfl, .nil⟩
  | n + 1, s, mon => by
    obtain ⟨l, hag, -, hs⟩ := exists_step_sc f s mon
    obtain ⟨ls, mon', hl, hr⟩ := exists_run_sc f n (f s) (monAfter (cls s) s mon)
    exact ⟨l :: ls, mon', by simp [hl], .cons hs hag hr⟩

/-! ## Precise footprints -/

/-- **A non-memory instruction has no event.** -/
theorem footprint_nonldst {s : ArmState}
    (h : ∀ ai, decodeAt s = some ai → ArmInst.isLDST ai = false) : Footprint stepi s [] := by
  intro m _
  simp only [applyR, applyW, setMem_self]
  exact stepi_setMem m s h

/-- A `dmb` event only: no access. -/
theorem footprint_dmb {s : ArmState}
    (h : ∀ ai, decodeAt s = some ai → ArmInst.isLDST ai = false) :
    Footprint stepi s [⟨.dmb, 0, 0, 0#0⟩] := by
  intro m _
  simp only [applyR, applyW, AKind.dir]
  simp only [show (Dir.F = Dir.R) = False from by simp, show (Dir.F = Dir.W) = False from by simp,
    ite_false]
  exact stepi_setMem m s h

theorem stepi_of_decodeAt {s : ArmState} {ai : ArmInst} (herr : read_err s = .None)
    (h : decodeAt s = some ai) : stepi s = exec_inst ai s := by
  unfold stepi
  simp only [herr]
  unfold decodeAt at h
  simp only [read_pc]
  split at h
  · rename_i w hw; rw [hw]; simp only [h]
  · cases h

theorem read_gpr_setMem (n : Nat) (i : BitVec 5) (m : Memory) (s : ArmState) :
    read_gpr n i (setMem m s) = read_gpr n i s := by
  simp only [read_gpr, r_setMem]

/-- The bytes an exclusive / acquire-release access of size field `size` transfers. -/
def exclBytes (size : BitVec 2) : Nat := (8 <<< size.toNat) / 8

theorem exclBytes_mul (size : BitVec 2) : exclBytes size * 8 = 8 <<< size.toNat := by
  unfold exclBytes; simp only [Nat.shiftLeft_eq]; omega

/-- **An exclusive or acquire load (`ldxr`, `ldaxr`, `ldar`) reads its `2 ^ size` bytes at
`[Rn]`**, any bytes `v` the environment supplies. -/
theorem footprint_load_excl {s : ArmState} {i : Reg_exclusive_cls} (k : AKind) (hk : k.dir = .R)
    (herr : read_err s = .None) (hd : decodeAt s = some (.LDST (.Reg_exclusive i)))
    (hL : i.L = 1#1) (hsp : ¬ (i.Rn = 31#5 ∧ ¬ CheckSPAlignment s))
    (v : BitVec (exclBytes i.size * 8)) :
    Footprint stepi s [⟨k, read_gpr 64 i.Rn s, exclBytes i.size, v⟩] := by
  intro m hm
  have hv : readM (exclBytes i.size) (read_gpr 64 i.Rn s) m = v := hm _ List.mem_cons_self hk
  have herr' : ∀ m', read_err (setMem m' s) = .None := fun m' => by
    simp only [read_err, r_setMem]; exact herr
  have hd' : ∀ m', decodeAt (setMem m' s) = some (.LDST (.Reg_exclusive i)) := fun m' => by
    rw [decodeAt_setMem]; exact hd
  rw [stepi_of_decodeAt (herr' _) (hd' _), stepi_of_decodeAt (herr' _) (hd' _)]
  simp only [exec_inst, LDST.exec_reg_exclusive, hL, ite_true]
  have hsp' : ∀ m', ¬ (i.Rn = 31#5 ∧ ¬ CheckSPAlignment (setMem m' s)) := fun m' => by
    simp only [CheckSPAlignment, read_gpr, r_setMem]; exact hsp
  simp only [hsp', ite_false]
  simp only [read_gpr_setMem, read_mem_bytes_eq, setMem_mem, write_gpr_zr, write_gpr,
    write_pc, read_pc, w_setMem, applyR, applyW, hk]
  simp only [show (Dir.R = Dir.W) = False from by simp, ite_false, ite_true]
  have hv' : readM (8 <<< i.size.toNat / 8) (read_gpr 64 i.Rn s) m = v := hv
  have hv'' : readM (8 <<< i.size.toNat / 8) (read_gpr 64 i.Rn s)
      (writeM (exclBytes i.size) (read_gpr 64 i.Rn s) v s.mem) = v :=
    readM_writeM _ _ _ _ (by
      show (8 <<< i.size.toNat) / 8 ≤ 2 ^ 64
      have h3 : 2 ^ i.size.toNat ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by have := i.size.isLt; omega)
      simp only [Nat.shiftLeft_eq]; omega)
  rw [hv', hv'']
  split <;> simp only [w_setMem, setMem_setMem, r_setMem]

/-- **An exclusive or release store (`stxr`, `stlxr`, `stlr`) writes its `2 ^ size` bytes at
`[Rn]`**: the bytes of `Rt`. -/
theorem footprint_store_excl {s : ArmState} {i : Reg_exclusive_cls} (k : AKind) (hk : k.dir = .W)
    (herr : read_err s = .None) (hd : decodeAt s = some (.LDST (.Reg_exclusive i)))
    (hL : i.L = 0#1) (hsp : ¬ (i.Rn = 31#5 ∧ ¬ CheckSPAlignment s)) :
    Footprint stepi s [⟨k, read_gpr 64 i.Rn s, exclBytes i.size,
      BitVec.cast (exclBytes_mul i.size).symm (ldst_read false (8 <<< i.size.toNat) i.Rt s)⟩] := by
  intro m _
  have herr' : ∀ m', read_err (setMem m' s) = .None := fun m' => by
    simp only [read_err, r_setMem]; exact herr
  have hd' : ∀ m', decodeAt (setMem m' s) = some (.LDST (.Reg_exclusive i)) := fun m' => by
    rw [decodeAt_setMem]; exact hd
  rw [stepi_of_decodeAt (herr' _) (hd' _), stepi_of_decodeAt (herr' _) (hd' _)]
  simp only [exec_inst, LDST.exec_reg_exclusive, hL, show ((0#1 : BitVec 1) = 1#1) = False from by
    decide, ite_false]
  have hsp' : ∀ m', ¬ (i.Rn = 31#5 ∧ ¬ CheckSPAlignment (setMem m' s)) := fun m' => by
    simp only [CheckSPAlignment, read_gpr, r_setMem]; exact hsp
  simp only [hsp', ite_false]
  simp only [applyR, applyW, hk, show (Dir.W = Dir.R) = False from by simp, ite_false, ite_true]
  simp only [ldst_read, read_gpr_zr, read_gpr_setMem, write_mem_bytes_eq, setMem_mem,
    setMem_setMem, write_gpr_zr, write_gpr, write_pc, read_pc, w_setMem]
  split <;> simp only [w_setMem, setMem_setMem, r_setMem, Bool.false_eq_true, ite_false] <;> rfl

end Concurrency.ArmThread
