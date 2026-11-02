import FV.Unw.Dwarf
import FV.E2E.Statement
import FV.E2E.RegLevelMachine

/-!
# The outside contract: the DWARF unwinder and Rust's personality routine (S10d, #231)

`docs/plans/unwinding.md`, "The outside contract". Trusted by design, as std is: a model,
**generic over the tables it reads** (not over our compiler), of what phase 2 of the Itanium
C++ ABI's `_Unwind_RaiseException` (§1.6) does to one frame, with libgcc's / libunwind's DWARF
unwinder (`uw_update_context`, `uw_install_context`) and Rust's `rust_eh_personality`
(`library/std/src/sys/personality/gcc.rs` `rust_eh_personality_impl`, `dwarf/eh.rs`
`find_eh_action`). The compiler's tables are proven to make it do the right thing
(`FV/Backend/Proof/UnwindTables.lean`, `restore_frame` here).

* `restore row s`: the frame described by `row` is unwound: CFA := the row's CFA rule
  evaluated in `s`; every register with an `offset` rule := the 8 bytes at CFA + offset
  (the low 64 bits of v8–v15, DWARF 72–79); sp := CFA; pc := x30 as restored (the return
  address column). Registers without a rule keep their value (the AArch64 ABI's "same value"
  for the callee-saved registers). Caller-saved registers are not constrained by any theorem
  after a call (the allocated code treats them as clobbered by every call), so the model's
  choice for them (unchanged) is immaterial.
* `personality lsda off`: Rust's personality in the cleanup phase for the call whose return
  offset − 1 from the function start is `off`: no LSDA (the FDE has no personality) or an
  entry with landing pad 0: continue unwinding; an entry with a landing pad: install it
  (cleanup and catch alike), x0 := the exception object, x1 := 0; no entry: terminate (Rust
  aborts, `EHAction::Terminate`). `lookup` takes the first entry containing `off`, as
  `find_eh_action`'s scan of the sorted table does.
* `ArmStepU X H U T fa`: the Arm machine of `ArmStepX X H fa`, except that a call whose callee
  raises (`U.raise d s = some (obj, t)`: the callee and every frame below it were unwound, `t`
  is the state at our call as the unwinder restored it) continues as the personality decides
  for the function's tables `T` (decoded from the bytes the compiler emitted): at the landing
  pad, or with our frame unwound (`restore`; the exception object kept in x0 — a convention
  of the model: the unwinder carries it in its context, and x0 is caller-saved).
-/

namespace Unw

open Backend Backend.Proof

/-- The 8 bytes at `a` (little-endian). -/
def ld64 (a : BitVec 64) (s : Arm.ArmState) : BitVec 64 := Arm.read_mem_bytes 8 a s

/-- The value of DWARF register `r` (x0–x30, sp = 31) in `s`. -/
def regVal? (s : Arm.ArmState) (r : Nat) : Option (BitVec 64) :=
  if r < 32 then some (Arm.r (.GPR (BitVec.ofNat 5 r)) s) else none

/-- The CFA of `row` in state `s`. -/
def Row.cfa? (row : Row) (s : Arm.ArmState) : Option (BitVec 64) :=
  (regVal? s row.cfaReg).map (· + BitVec.ofNat 64 row.cfaOff)

/-- Set DWARF register `d` to the saved value `v` (x0–x30; the low 64 bits of v0–v31; other
numbers are not restored). -/
def setReg (d : Nat) (v : BitVec 64) (t : Arm.ArmState) : Arm.ArmState :=
  if d < 31 then Arm.w (.GPR (BitVec.ofNat 5 d)) v t
  else if 64 ≤ d ∧ d < 96 then Arm.w (.SFP (BitVec.ofNat 5 (d - 64))) (v.setWidth 128) t
  else t

/-- Unwind the frame described by `row` (`none`: the CFA register is not x0–x30/sp). The
saved values are read from `s`'s memory; the latest rule of a register wins (`saved` is
latest first, so the fold applies the oldest first). -/
def restore (row : Row) (s : Arm.ArmState) : Option Arm.ArmState :=
  (row.cfa? s).map fun cfa =>
    let t := row.saved.foldr (fun (d, off) t => setReg d (ld64 (cfa + BitVec.ofInt 64 off) s) t) s
    Arm.w .PC (Arm.r (.GPR 30#5) t) (Arm.w (.GPR 31#5) cfa t)

/-- What the personality does for one frame in the cleanup phase. -/
inductive Action where
  /-- Install the landing pad at this offset from the function start. -/
  | install (pad : Nat)
  /-- Unwind the frame and continue with its caller. -/
  | continue
  /-- No call-site entry: the process aborts. -/
  | terminate
  deriving DecidableEq, Repr

/-- Rust's personality for the call at return offset − 1 `off` of a function with LSDA call-site
table `lsda` (`none`: the function has no LSDA, its CIE no personality). -/
def personality : Option (List CallSiteEntry) → Nat → Action
  | none, _ => .continue
  | some sites, off =>
    match lookup sites off with
    | none => .terminate
    | some e => if e.pad = 0 then .continue else .install e.pad

/-- The unwind tables of a function as the unwinder decodes them: the CIE's initial
instructions, the FDE's instructions (code offsets from the function start, the FDE's
`pc_begin`), and the LSDA's call-site table if the FDE has one. -/
structure FnTables where
  cie : List CfaInsn
  fde : List CfaInsn
  lsda : Option (List CallSiteEntry)

/-- The error state of the model when the unwinder leaves it (no row, or Rust aborts). -/
def stop (msg : String) (t : Arm.ArmState) : Arm.ArmState := Arm.w .ERR (.Other msg) t

/-- Phase 2 at our call at address `pc` (function start `start`) whose callee raised the
exception object `obj`, the unwinder having restored our call's state `t`. -/
def unwindAt (T : FnTables) (start pc obj : BitVec 64) (t : Arm.ArmState) : Arm.ArmState :=
  let off := (pc + 4 - 1 - start).toNat
  match personality T.lsda off with
  | .install pad =>
    Arm.w .PC (start + BitVec.ofNat 64 pad) (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t))
  | .continue =>
    match restore (rowAt T.cie T.fde off) t with
    | some t' => Arm.w (.GPR 0#5) obj t'
    | none => stop "unwind: no CFA rule" t
  | .terminate => stop "unwind: no call-site entry (abort)" t

/-- The raising callees: `raise d s = some (obj, t)`: the callee of `bl name` (`some name`) /
`blr` (`none`) entered from `s` raised exception object `obj`, and the unwinder restored our
call's state `t` (the callee's frame and every frame below it unwound). `none`: the callee
returns normally (`ArmHooks.call`). -/
structure UnwHooks where
  raise : Option String → Arm.ArmState → Option (BitVec 64 × Arm.ArmState)

/-- No callee raises. -/
def UnwHooks.none : UnwHooks := ⟨fun _ _ => Option.none⟩

/-- **The Arm machine with unwinding.** -/
noncomputable def ArmStepU (X : ExtSem) (H : ArmHooks) (U : UnwHooks) (T : FnTables) (fa : FnAsm)
    (s : Arm.ArmState) : Arm.ArmState :=
  let pc := Arm.r .PC s
  match insnAt fa (progBase s) pc with
  | some (.bl n) =>
    match U.raise (some n) s with
    | some (obj, t) => unwindAt T (progBase s) pc obj t
    | Option.none => H.call (some n) s
  | some (.blr _) =>
    match U.raise Option.none s with
    | some (obj, t) => unwindAt T (progBase s) pc obj t
    | Option.none => H.call Option.none s
  | _ => ArmStepX X H fa s

/-- Without raising callees the machine is `ArmStepX`. -/
theorem armStepU_none (X : ExtSem) (H : ArmHooks) (T : FnTables) (fa : FnAsm) :
    ArmStepU X H UnwHooks.none T fa = ArmStepX X H fa := by
  funext s
  unfold ArmStepU
  simp only [UnwHooks.none]
  split
  · rename_i heq; unfold ArmStepX; simp only [heq]
  · rename_i heq; unfold ArmStepX; simp only [heq]
  · rfl

/-! ## Restoring a frame -/

/-- The value DWARF register `d` (a GPR) has after `restore` with CFA `cfa`, from `t`. -/
def restoredX (row : Row) (cfa : BitVec 64) (t : Arm.ArmState) (n : Nat) : BitVec 64 :=
  match row.rule n with
  | some off => ld64 (cfa + BitVec.ofInt 64 off) t
  | Option.none => E2E.xreg n t

/-- The low 64 bits of `v n` after `restore` with CFA `cfa`, from `t`. -/
def restoredV (row : Row) (cfa : BitVec 64) (t : Arm.ArmState) (n : Nat) : BitVec 64 :=
  match row.rule (64 + n) with
  | some off => ld64 (cfa + BitVec.ofInt 64 off) t
  | Option.none => (Arm.r (.SFP (BitVec.ofNat 5 n)) t).setWidth 64

theorem ofNat5_ne {a b : Nat} (ha : a < 32) (hb : b < 32) (h : a ≠ b) :
    BitVec.ofNat 5 a ≠ BitVec.ofNat 5 b := by
  intro he
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat] at this
  omega

/-- The restoring fold of `restore`. -/
def restoreFold (cfa : BitVec 64) (s : Arm.ArmState) (L : List (Nat × Int)) : Arm.ArmState :=
  L.foldr (fun (d, off) t => setReg d (ld64 (cfa + BitVec.ofInt 64 off) s) t) s

theorem r_gpr_setReg {n : Nat} (hn : n < 31) (d : Nat) (v : BitVec 64) (t : Arm.ArmState) :
    Arm.r (.GPR (BitVec.ofNat 5 n)) (setReg d v t) =
      if n = d then v else Arm.r (.GPR (BitVec.ofNat 5 n)) t := by
  unfold setReg
  by_cases hd : n = d
  · subst hd; simp [hn, Arm.r_of_w_same]
  · rw [if_neg hd]
    split
    · rw [Arm.r_of_w_different (by
        simp only [ne_eq, Arm.StateField.GPR.injEq]; exact ofNat5_ne (by omega) (by omega) hd)]
    · split
      · rw [Arm.r_of_w_different (by simp)]
      · rfl

theorem r_sfp_setReg {n : Nat} (hn : n < 32) (d : Nat) (v : BitVec 64) (t : Arm.ArmState) :
    (Arm.r (.SFP (BitVec.ofNat 5 n)) (setReg d v t)).setWidth 64 =
      if 64 + n = d then v else (Arm.r (.SFP (BitVec.ofNat 5 n)) t).setWidth 64 := by
  unfold setReg
  by_cases hd : 64 + n = d
  · subst hd
    rw [if_pos rfl, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left, Arm.r_of_w_same]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := v.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg hd]
    split
    · rw [Arm.r_of_w_different (by simp)]
    · split
      · rw [Arm.r_of_w_different (by
          simp only [ne_eq, Arm.StateField.SFP.injEq]
          exact ofNat5_ne (by omega) (by omega) (by omega))]
      · rfl

theorem r_other_setReg (fld : Arm.StateField) (hg : ∀ i, fld ≠ .GPR i) (hv : ∀ i, fld ≠ .SFP i)
    (d : Nat) (v : BitVec 64) (t : Arm.ArmState) : Arm.r fld (setReg d v t) = Arm.r fld t := by
  unfold setReg
  split
  · rw [Arm.r_of_w_different (hg _)]
  · split
    · rw [Arm.r_of_w_different (hv _)]
    · rfl

theorem setReg_program (d : Nat) (v : BitVec 64) (t : Arm.ArmState) :
    (setReg d v t).program = t.program ∧ (setReg d v t).mem = t.mem := by
  unfold setReg
  split
  · exact ⟨Arm.w_program, Arm.mem_w_of_mem_eq rfl _ _⟩
  · split
    · exact ⟨Arm.w_program, Arm.mem_w_of_mem_eq rfl _ _⟩
    · exact ⟨rfl, rfl⟩

theorem restoreFold_gpr (cfa : BitVec 64) (s : Arm.ArmState) {n : Nat} (hn : n < 31) :
    ∀ L : List (Nat × Int), Arm.r (.GPR (BitVec.ofNat 5 n)) (restoreFold cfa s L) =
      match L.lookup n with
      | some off => ld64 (cfa + BitVec.ofInt 64 off) s
      | Option.none => Arm.r (.GPR (BitVec.ofNat 5 n)) s
  | [] => rfl
  | (d, off) :: L => by
    have ih := restoreFold_gpr cfa s hn L
    simp only [restoreFold, List.foldr_cons] at ih ⊢
    rw [r_gpr_setReg hn, List.lookup_cons]
    by_cases hd : n = d
    · subst hd; rw [if_pos rfl, beq_self_eq_true]
    · rw [if_neg hd, ih, show (n == d) = false by simpa using hd]

theorem restoreFold_sfp (cfa : BitVec 64) (s : Arm.ArmState) {n : Nat} (hn : n < 32) :
    ∀ L : List (Nat × Int), (Arm.r (.SFP (BitVec.ofNat 5 n)) (restoreFold cfa s L)).setWidth 64 =
      match L.lookup (64 + n) with
      | some off => ld64 (cfa + BitVec.ofInt 64 off) s
      | Option.none => (Arm.r (.SFP (BitVec.ofNat 5 n)) s).setWidth 64
  | [] => rfl
  | (d, off) :: L => by
    have ih := restoreFold_sfp cfa s hn L
    simp only [restoreFold, List.foldr_cons] at ih ⊢
    rw [r_sfp_setReg hn, List.lookup_cons]
    by_cases hd : 64 + n = d
    · subst hd; rw [if_pos rfl, beq_self_eq_true]
    · rw [if_neg hd, ih, show (64 + n == d) = false by simpa using hd]

theorem restoreFold_other (cfa : BitVec 64) (s : Arm.ArmState) (fld : Arm.StateField)
    (hg : ∀ i, fld ≠ .GPR i) (hv : ∀ i, fld ≠ .SFP i) :
    ∀ L : List (Nat × Int), Arm.r fld (restoreFold cfa s L) = Arm.r fld s
  | [] => rfl
  | (d, off) :: L => by
    have ih := restoreFold_other cfa s fld hg hv L
    simp only [restoreFold, List.foldr_cons] at ih ⊢
    rw [r_other_setReg fld hg hv, ih]

theorem restoreFold_program (cfa : BitVec 64) (s : Arm.ArmState) :
    ∀ L : List (Nat × Int), (restoreFold cfa s L).program = s.program ∧
      (restoreFold cfa s L).mem = s.mem
  | [] => ⟨rfl, rfl⟩
  | (d, off) :: L => by
    have ih := restoreFold_program cfa s L
    simp only [restoreFold, List.foldr_cons] at ih ⊢
    obtain ⟨h1, h2⟩ := setReg_program d (ld64 (cfa + BitVec.ofInt 64 off) s)
      (List.foldr (fun x t => setReg x.1 (ld64 (cfa + BitVec.ofInt 64 x.2) s) t) s L)
    exact ⟨h1.trans ih.1, h2.trans ih.2⟩

/-- **What `restore` does**, register by register: sp := CFA, pc := the restored x30, every
GPR x0–x30 and the low 64 bits of every v register as its rule says (`restoredX`,
`restoredV`), memory, program and error as before. -/
theorem restore_spec {row : Row} {t : Arm.ArmState} {cfa : BitVec 64} (hc : row.cfa? t = some cfa) :
    ∃ t', restore row t = some t' ∧ E2E.spv t' = cfa ∧
      Arm.r .PC t' = restoredX row cfa t 30 ∧
      (∀ n < 31, E2E.xreg n t' = restoredX row cfa t n) ∧
      (∀ n < 32, (Arm.r (.SFP (BitVec.ofNat 5 n)) t').setWidth 64 = restoredV row cfa t n) ∧
      Arm.r .ERR t' = Arm.r .ERR t ∧ t'.program = t.program ∧ t'.mem = t.mem := by
  refine ⟨_, by simp [restore, hc]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [E2E.spv]
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_same]
  · rw [Arm.r_of_w_same]
    exact restoreFold_gpr cfa t (by omega) row.saved
  · intro n hn
    simp only [E2E.xreg]
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by
      simp only [ne_eq, Arm.StateField.GPR.injEq]
      exact ofNat5_ne (by omega) (by omega) (by omega))]
    exact restoreFold_gpr cfa t hn row.saved
  · intro n hn
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
    exact restoreFold_sfp cfa t hn row.saved
  · rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
    exact restoreFold_other cfa t .ERR (by simp) (by simp) row.saved
  · simp only [Arm.w, Arm.write_base_pc, Arm.write_base_gpr]
    exact (restoreFold_program cfa t row.saved).1
  · simp only [Arm.w, Arm.write_base_pc, Arm.write_base_gpr]
    exact (restoreFold_program cfa t row.saved).2

/-- **The frame invariant at a call** of an activation entered in `s0`, for the frame row
`row`: the row's CFA is the entry sp, and every register the ABI's return condition names —
x19–x29, x30 (the return address) and the low 64 bits of v8–v15 — is where the row says: at
its save slot if the row has a rule for it, otherwise unchanged. -/
structure FrameAt (row : Row) (s0 t : Arm.ArmState) : Prop where
  cfa : row.cfa? t = some (E2E.spv s0)
  regs : ∀ n ∈ 30 :: E2E.calleeSavedX, restoredX row (E2E.spv s0) t n = E2E.xreg n s0
  vregs : ∀ n, 8 ≤ n → n < 16 →
    restoredV row (E2E.spv s0) t n = (Arm.r (.SFP (BitVec.ofNat 5 n)) s0).setWidth 64

/-- **`restore_frame`**: unwinding a frame that satisfies the frame invariant with its row
returns as the ABI requires (`ArmRet`): at the return address (x30 at entry), with the entry
sp and the entry values of the callee-saved registers. -/
theorem restore_frame {row : Row} {s0 t : Arm.ArmState} (h : FrameAt row s0 t)
    (herr : Arm.r .ERR t = .None) :
    ∃ t', restore row t = some t' ∧ E2E.ArmRet (E2E.xreg 30 s0) s0 t' ∧
      t'.program = t.program ∧ t'.mem = t.mem := by
  obtain ⟨t', hr, hsp, hpc, hx, hv, he, hp, hm⟩ := restore_spec h.cfa
  refine ⟨t', hr, ⟨?_, ?_, hsp, ?_, ?_⟩, hp, hm⟩
  · rw [hpc]; exact h.regs 30 (by simp)
  · rw [he, herr]
  · intro n hn
    have hn' : n < 31 := by
      simp only [E2E.calleeSavedX, List.mem_map, List.mem_range] at hn; omega
    rw [hx n hn']
    exact h.regs n (List.mem_cons_of_mem _ hn)
  · intro n h8 h16
    rw [hv n (by omega)]
    exact h.vregs n h8 h16

/-! ## One frame of phase 2 -/

/-- A call whose callee raises steps to `unwindAt`. -/
theorem armStepU_raise {X : ExtSem} {H : ArmHooks} {U : UnwHooks} {T : FnTables} {fa : FnAsm}
    {s : Arm.ArmState} {i : Insn} {d : Option String} {obj : BitVec 64} {t : Arm.ArmState}
    (hi : insnAt fa (progBase s) (Arm.r .PC s) = some i)
    (hd : (∃ n, i = .bl n ∧ d = some n) ∨ (∃ r, i = .blr r ∧ d = Option.none))
    (hr : U.raise d s = some (obj, t)) :
    ArmStepU X H U T fa s = unwindAt T (progBase s) (Arm.r .PC s) obj t := by
  unfold ArmStepU
  rcases hd with ⟨n, rfl, rfl⟩ | ⟨r, rfl, rfl⟩
  · simp only [hi, hr]
  · simp only [hi, hr]

/-- A call whose callee returns normally steps as `ArmStepX`. -/
theorem armStepU_noRaise {X : ExtSem} {H : ArmHooks} {U : UnwHooks} {T : FnTables} {fa : FnAsm}
    {s : Arm.ArmState} (h : ∀ d, U.raise d s = Option.none) :
    ArmStepU X H U T fa s = ArmStepX X H fa s := by
  unfold ArmStepU
  simp only [h]
  split
  · rename_i heq; unfold ArmStepX; simp only [heq]
  · rename_i heq; unfold ArmStepX; simp only [heq]
  · rfl

/-- The personality installs a landing pad: control at `start + pad`, x0 = the exception
object, x1 = 0, everything else as the unwinder restored it. -/
theorem unwindAt_install {T : FnTables} {start pc obj : BitVec 64} {t : Arm.ArmState} {pad : Nat}
    (hp : personality T.lsda (pc + 4 - 1 - start).toNat = .install pad) :
    unwindAt T start pc obj t =
      Arm.w .PC (start + BitVec.ofNat 64 pad) (Arm.w (.GPR 1#5) 0 (Arm.w (.GPR 0#5) obj t)) := by
  simp only [unwindAt, hp]

/-- The personality continues: the frame is unwound by its row (`restore_frame` gives the ABI
return when the frame invariant holds), the exception object in x0. -/
theorem unwindAt_continue {T : FnTables} {start pc obj : BitVec 64} {s0 t : Arm.ArmState}
    (hp : personality T.lsda (pc + 4 - 1 - start).toNat = .continue)
    (hfr : FrameAt (rowAt T.cie T.fde (pc + 4 - 1 - start).toNat) s0 t)
    (herr : Arm.r .ERR t = .None) :
    ∃ t', unwindAt T start pc obj t = Arm.w (.GPR 0#5) obj t' ∧
      E2E.ArmRet (E2E.xreg 30 s0) s0 t' ∧ t'.program = t.program ∧ t'.mem = t.mem := by
  obtain ⟨t', hr, hret, hp', hm⟩ := restore_frame hfr herr
  exact ⟨t', by simp only [unwindAt, hp, hr], hret, hp', hm⟩

/-- Writing the exception object into x0 keeps the ABI return condition (x0 is caller-saved). -/
theorem armRet_x0 {ra : BitVec 64} {s0 t : Arm.ArmState} (h : E2E.ArmRet ra s0 t) (v : BitVec 64) :
    E2E.ArmRet ra s0 (Arm.w (.GPR 0#5) v t) where
  pc := by rw [Arm.r_of_w_different (by simp)]; exact h.pc
  err := by rw [Arm.r_of_w_different (by simp)]; exact h.err
  sp := by
    simp only [E2E.spv]
    rw [Arm.r_of_w_different (by simp only [ne_eq, Arm.StateField.GPR.injEq]; decide)]
    exact h.sp
  savedX := by
    intro n hn
    have hn' : 19 ≤ n ∧ n < 30 := by
      simp only [E2E.calleeSavedX, List.mem_map, List.mem_range] at hn; omega
    simp only [E2E.xreg]
    rw [Arm.r_of_w_different (by
      simp only [ne_eq, Arm.StateField.GPR.injEq]
      exact ofNat5_ne (a := n) (b := 0) (by omega) (by omega) (by omega))]
    exact h.savedX n hn
  savedV := by
    intro n h8 h16
    rw [Arm.r_of_w_different (by simp)]
    exact h.savedV n h8 h16

/-- **The raising callees' register contract** (the register part of `CalleeUnwOk`,
`docs/plans/unwinding.md`; the world part comes with `ExtSem.raise`, S10e): a callee entered
from an error-free, aligned call state `s` that raises leaves our call's state `t` as the
unwinder restored it — error-free, with `s`'s sp, callee-saved registers and program. -/
structure CalleeUnwRegs (U : UnwHooks) : Prop where
  raise : ∀ d s obj t, Arm.r .ERR s = .None → Arm.CheckSPAlignment s → U.raise d s = some (obj, t) →
    Arm.r .ERR t = .None ∧ E2E.spv t = E2E.spv s ∧
    (∀ n ∈ E2E.calleeSavedX, E2E.xreg n t = E2E.xreg n s) ∧
    (∀ n, 8 ≤ n → n < 16 → (Arm.r (.SFP (BitVec.ofNat 5 n)) t).setWidth 64 =
      (Arm.r (.SFP (BitVec.ofNat 5 n)) s).setWidth 64) ∧
    t.program = s.program

/-- No callee raising satisfies the contract. -/
theorem calleeUnwRegs_none : CalleeUnwRegs UnwHooks.none := ⟨fun _ _ _ _ _ _ h => by cases h⟩

end Unw
