import FV.E2E.Statement
import FV.E2E.RegLevelEmit
import FV.E2E.RegLevelMachine
import FV.E2E.RegLevelPlan
import FV.Backend.Proof.RegallocLayout
import FV.Backend.Proof.AssignOk
import FV.Backend.Proof.RegallocFrame

/-!
# The register-level simulation relation (M6)

The Arm machine `ArmStepX` running the laid-out function realises the allocated code
(`MStep`) item by item. `Q R s c` relates an Arm state `s` to an allocated-code configuration
`c` of the activation `R`:

* **position**: the pc is at line `j` of the final line list, and the lines from `j` on are the
  relaxation of the remaining items' lines with the block's last instruction's lines replaced by
  its final lines in the emission plan (`Qs`); or the configuration is at the entry of a block
  reached through forwarding blocks (a single `jump`, without machine steps, `QE`);
* **store**: every valid location (allocatable register, spill/save slot) holds in `s` what the
  store `m` says (`locVal`);
* **world**: `s` has the world `w` (`SameWorld (R.F)`: equal outside allocatable registers,
  x16/x17, the pc and the addresses `R.F` — the frame addresses `R.FK` and the callees' dead
  stack `[sp_body - K, sp_body)`), no error, the function's program, `sp` at the body's frame,
  fp/lr saved at the top of the frame.

Returns and traps are the last step of a run and are treated separately (their `Q` is `True`).
-/

namespace Backend.Proof

open Backend E2E

/-- The frame addresses of the activation entered in `s` (`lo`, `hi` = the frame's `intBase`,
`size`): the spill and float-move slots `[sp_body + lo, sp_body + hi)`, the clobber area the
prologue pushes the saved registers into and fp/lr above the CLIF slots
`[sp_body + frameSize - clobberBytes, sp_entry)` (the explicit CLIF slots in between belong to
the world; empty without a frame), and the code words (read as data by jump tables; the
program never accesses them). -/
def frameF (lo hi : Nat) (af : AFunc) (s : Arm.ArmState) (a : BitVec 64) : Prop :=
  (lo ≤ (a - (spv s - BitVec.ofNat 64 (frameDrop af))).toNat ∧
    (a - (spv s - BitVec.ofNat 64 (frameDrop af))).toNat < hi) ∨
  (af.frameSize - clobberBytes af.saves ≤ (a - (spv s - BitVec.ofNat 64 (frameDrop af))).toNat ∧
    (a - (spv s - BitVec.ofNat 64 (frameDrop af))).toNat < frameDrop af) ∨
  CodeAddr s a

/-- The `K` bytes below `sp` (`[sp - K, sp)`, without wrapping: `[0, sp)` when `sp < K`). -/
def StackBelow (K : Nat) (sp a : BitVec 64) : Prop :=
  a.toNat < sp.toNat ∧ sp.toNat ≤ a.toNat + K

/-- The addresses outside the world of the activation entered in `s` (`lo`, `hi` as in
`frameF`): its frame addresses `frameF`, and the callees' dead stack: the `K` bytes below the
body's `sp` (`StackBelow`), where every callee builds its frame (the saved return address and
callee-saved registers, spills: bytes that depend on more than the caller's world). No live
CLIF byte is there (`MemRel.valid`), and a call leaves them unspecified (`CalleeOk`). With
`K = 0` this is `frameF`. -/
def frameW (K lo hi : Nat) (af : AFunc) (s : Arm.ArmState) (a : BitVec 64) : Prop :=
  frameF lo hi af s a ∨ StackBelow K (spv s - BitVec.ofNat 64 (frameDrop af)) a

/-- `frameW` and addresses `G` that the activation keeps (its callers' frames, the program's
code; `RL.G`): the addresses outside the world of an activation inside a linked program. -/
def frameWG (K lo hi : Nat) (af : AFunc) (G : BitVec 64 → Prop) (s : Arm.ArmState)
    (a : BitVec 64) : Prop :=
  frameW K lo hi af s a ∨ G a

/-- Without kept addresses `frameWG` is `frameW`. -/
theorem frameWG_false (K lo hi : Nat) (af : AFunc) (s : Arm.ArmState) :
    frameWG K lo hi af (fun _ => False) s = frameW K lo hi af s :=
  funext fun _ => or_false _

theorem frameDrop_le (af : AFunc) : frameDrop af ≤ af.frameSize + 16 := by
  unfold frameDrop; split <;> omega

/-- The body's `sp` (`sp_entry - frameDrop`) does not wrap, and the callees' budget `K` fits
below it. -/
theorem spBody_toNat {K : Nat} {af : AFunc} {s : Arm.ArmState} (hst : StackAvail K af s) :
    (spv s - BitVec.ofNat 64 (frameDrop af)).toNat = (spv s).toNat - frameDrop af ∧
      frameDrop af + K ≤ (spv s).toNat := by
  have h1 := hst.1
  have h2 := frameDrop_le af
  have hlt := (spv s).isLt
  refine ⟨?_, by omega⟩
  rw [BitVec.toNat_sub_of_le] <;>
    simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : frameDrop af < 2 ^ 64)]
  omega

/-- **The frame addresses are not in the dead stack**: with enough stack (`StackAvail K`) and
the allocator's slots inside the dropped frame (`hi ≤ frameDrop`), no frame address — slot,
fp/lr, code — lies in the `K` bytes below the body's `sp`. -/
theorem frameF_not_below {K lo hi : Nat} {af : AFunc} {s : Arm.ArmState} (hst : StackAvail K af s)
    (hhi : hi ≤ frameDrop af) {a : BitVec 64} (ha : frameF lo hi af s a) :
    ¬ StackBelow K (spv s - BitVec.ofNat 64 (frameDrop af)) a := by
  obtain ⟨hB, hK⟩ := spBody_toNat hst
  rintro ⟨hlt, hle⟩
  have hsp := (spv s).isLt
  have hfd := frameDrop_le af
  rcases ha with ⟨-, h⟩ | ⟨-, h⟩ | hc
  · rw [BitVec.toNat_sub, hB] at h
    have := a.isLt
    rw [hB] at hlt
    have e : (2 ^ 64 - ((spv s).toNat - frameDrop af) + a.toNat) % 2 ^ 64 =
        2 ^ 64 - ((spv s).toNat - frameDrop af) + a.toNat := Nat.mod_eq_of_lt (by omega)
    rw [e] at h
    omega
  · rw [BitVec.toNat_sub, hB] at h
    have := a.isLt
    rw [hB] at hlt
    have e : (2 ^ 64 - ((spv s).toNat - frameDrop af) + a.toNat) % 2 ^ 64 =
        2 ^ 64 - ((spv s).toNat - frameDrop af) + a.toNat := Nat.mod_eq_of_lt (by omega)
    rw [e] at h
    omega
  · have h := hst.2 a hc
    have h1 := hst.1
    rw [hB] at hlt hle
    have hn : (spv s - BitVec.ofNat 64 (af.frameSize + 16 + K)).toNat =
        (spv s).toNat - (af.frameSize + 16 + K) := by
      rw [BitVec.toNat_sub_of_le] <;>
        simp only [BitVec.le_def, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : af.frameSize + 16 + K < 2 ^ 64)]
      omega
    rw [BitVec.toNat_sub, hn] at h
    have := a.isLt
    have e : (2 ^ 64 - ((spv s).toNat - (af.frameSize + 16 + K)) + a.toNat) % 2 ^ 64 =
        a.toNat - ((spv s).toNat - (af.frameSize + 16 + K)) := by
      rw [show 2 ^ 64 - ((spv s).toNat - (af.frameSize + 16 + K)) + a.toNat =
        (a.toNat - ((spv s).toNat - (af.frameSize + 16 + K))) + 2 ^ 64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e] at h
    omega

/-- **The operand-view obligation of a call with a dead stack of `K` bytes**: at every state
whose `K` bytes below `sp` fit (`K ≤ sp`) and lie outside the world (in `F`: the caller holds
nothing live there), the emitted call satisfies `OperandsSoundCtl`, keeping the frame `F` only
outside that dead stack (the callee builds its frame there). -/
def CallSoundCtl (F : BitVec 64 → Prop) (K : Nat) (exec : MInst → Arm.ArmState → Option Arm.ArmState)
    (sem : ISem CV Arm.ArmState) (i : MInst) (ctl : Ctl) : Prop :=
  ∀ s, K ≤ (spOf s).toNat → (∀ a, StackBelow K (spOf s) a → F a) →
    OperandsSoundCtlAt F (fun a => F a ∧ ¬ StackBelow K (spOf s) a) exec sem i ctl s

/-- `OperandsSoundCtlAt` for the allocated instructions `i'` that satisfy `P` (e.g. the one whose
code is at the pc of the state, `CallAt`). -/
def OperandsSoundCtlAtI (F FK : BitVec 64 → Prop) (P : MInst → Prop)
    (exec : MInst → Arm.ArmState → Option Arm.ArmState)
    (sem : ISem CV Arm.ArmState) (i : MInst) (ctl : Ctl) (s : Arm.ArmState) : Prop :=
  ∀ (c : CheckCtx) (wh : String) (ops : Array Operand) (regs : Array Reg) (i' : MInst)
    (w : Arm.ArmState) (outs : List CV) (w' : Arm.ArmState),
    i.operands = .ok ops →
    c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () →
    i.assign regs = .ok i' → P i' →
    SameWorld F s w → Arm.CheckSPAlignment s → Arm.r .ERR s = .None →
    sem i (useVals ops regs s) w = some (outs, w', ctl) →
    ∃ s', exec i' s = some s' ∧ SameWorld F s' w' ∧ FrameKeep FK s s' ∧
      (∀ p ∈ defRegs ops regs outs, regVal s' p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ i.clobbers → regVal s' r = regVal s r) ∧
      (∀ r ∈ i.clobbers, r ∈ calleeSaved → ckeep r (regVal s' r) = ckeep r (regVal s r))

theorem OperandsSoundCtlAt.toI {F FK : BitVec 64 → Prop}
    {exec : MInst → Arm.ArmState → Option Arm.ArmState} {sem : ISem CV Arm.ArmState} {i : MInst}
    {ctl : Ctl} {s : Arm.ArmState} (h : OperandsSoundCtlAt F FK exec sem i ctl s)
    (P : MInst → Prop) : OperandsSoundCtlAtI F FK P exec sem i ctl s :=
  fun c wh ops regs i' w outs w' hops hst hasg _ hw hal herr hsem =>
    h c wh ops regs i' w outs w' hops hst hasg hw hal herr hsem

theorem OperandsSoundCtlAtI.mono {F FK FK' : BitVec 64 → Prop} {P P' : MInst → Prop}
    {exec : MInst → Arm.ArmState → Option Arm.ArmState} {sem : ISem CV Arm.ArmState} {i : MInst}
    {ctl : Ctl} {s : Arm.ArmState} (h : OperandsSoundCtlAtI F FK P exec sem i ctl s)
    (hP : ∀ i', P' i' → P i') (hFK : ∀ a, FK' a → FK a) :
    OperandsSoundCtlAtI F FK' P' exec sem i ctl s := by
  intro c wh ops regs i' w outs w' hops hst hasg hp hw hal herr hsem
  obtain ⟨s', hex, hW, hK, hd, ho, hc⟩ := h c wh ops regs i' w outs w' hops hst hasg (hP i' hp) hw hal
    herr hsem
  exact ⟨s', hex, hW, ⟨hK.1, fun a ha => hK.2.1 a (hFK a ha), hK.2.2⟩, hd, ho, hc⟩

/-- `CallSoundCtl` at the states whose memory at `G` is `s0`'s: the callee may assume that the
addresses `G` the calling activation keeps (`RL.G`: e.g. its callers' frames and the program's
code) hold what they held at the activation's entry `s0`, and that the allocated call `i'` is the
instruction at the pc (`Pc pc i'`, `CallAt`: e.g. a `blr` reads the target from the register the
allocation gave it). -/
def CallSoundCtlG (F : BitVec 64 → Prop) (K : Nat) (G : BitVec 64 → Prop) (s0 : Arm.ArmState)
    (Pc : BitVec 64 → MInst → Prop)
    (exec : MInst → Arm.ArmState → Option Arm.ArmState) (sem : ISem CV Arm.ArmState) (i : MInst)
    (ctl : Ctl) : Prop :=
  ∀ s, K ≤ (spOf s).toNat → (∀ a, StackBelow K (spOf s) a → F a) →
    (∀ a, G a → s.mem a = s0.mem a) →
    OperandsSoundCtlAtI F (fun a => F a ∧ ¬ StackBelow K (spOf s) a) (Pc (Arm.r .PC s)) exec sem i
      ctl s

theorem CallSoundCtl.g {F : BitVec 64 → Prop} {K : Nat} {exec : MInst → Arm.ArmState → Option Arm.ArmState}
    {sem : ISem CV Arm.ArmState} {i : MInst} {ctl : Ctl} (h : CallSoundCtl F K exec sem i ctl)
    (G : BitVec 64 → Prop) (s0 : Arm.ArmState) (Pc : BitVec 64 → MInst → Prop) :
    CallSoundCtlG F K G s0 Pc exec sem i ctl :=
  fun s h1 h2 _ => (h s h1 h2).toI _

/-- `pc` is the address of a call instruction (`bl`, `blr`) of the laid-out function `fa` loaded
at `base`. -/
def CallPc (fa : FnAsm) (base pc : BitVec 64) : Prop :=
  ∃ j i t, fa.lines.toList[j]? = some (.ins i t) ∧ ((∃ n, i = .bl n) ∨ (∃ r, i = .blr r)) ∧
    pc = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j)

/-- The call instruction an allocated `call`/`try_call` emits first (`bl name`, `blr reg`). -/
def _root_.Backend.MInst.callInsn? : MInst → Option Insn
  | .call info | .tryCall info _ => some (match info.dest with
    | .sym n => .bl n
    | .reg r => .blr r)
  | _ => none

/-- **The allocated call `i'` is the instruction at `pc`** of the laid-out function `fa` loaded at
`base`: the states and instructions `CallSoundCtlG` is required at (`Pc := CallAt fa base`). -/
def CallAt (fa : FnAsm) (base pc : BitVec 64) (i' : MInst) : Prop :=
  ∃ j x t, fa.lines.toList[j]? = some (.ins x t) ∧ i'.callInsn? = some x ∧
    pc = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j)

theorem CallAt.callPc {fa : FnAsm} {base pc : BitVec 64} {i' : MInst} (h : CallAt fa base pc i') :
    CallPc fa base pc := by
  obtain ⟨j, x, t, hj, hx, hpc⟩ := h
  refine ⟨j, x, t, hj, ?_, hpc⟩
  unfold MInst.callInsn? at hx
  split at hx
  all_goals first
    | (simp only [Option.some.injEq] at hx; subst hx; split <;> simp)
    | cases hx

/-- The registers the entry `Args` of `vc` (instruction 0 of block 0) reads. -/
def _root_.Backend.VCode.EntryArg (vc : VCode) (r : Reg) : Prop :=
  ∃ vb ds, vc.blocks[0]? = some vb ∧ vb.insts[0]? = some (.args ds) ∧ ∃ v, (v, r) ∈ ds

/-- `BodyEntry` relative to the addresses `F` outside the world and the argument registers `A`
the body reads: the body-entry world `w₀` agrees with the entry state `s` on the memory outside
`F` and on the registers `A` (`BodyEntry` fixes all memory and x0–x8, v0–v7). -/
structure BodyEntryW (F : BitVec 64 → Prop) (A : Reg → Prop) (af : AFunc) (s w₀ : Arm.ArmState) :
    Prop where
  sp : spv w₀ = spv s - BitVec.ofNat 64 (frameDrop af)
  fp : xreg 29 w₀ = if af.frame then spv s - 16#64 else xreg 29 s
  args : ∀ r, A r → regVal w₀ r = regVal s r
  other : ∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f w₀ = Arm.r f s
  mem : ∀ a, ¬ F a → w₀.mem a = s.mem a
  program : w₀.program = s.program

/-- `BodyEntry` gives `BodyEntryW` for every `F` and every set of argument registers. -/
theorem _root_.E2E.BodyEntry.w {af : AFunc} {s w₀ : Arm.ArmState} (h : BodyEntry af s w₀)
    (F : BitVec 64 → Prop) {A : Reg → Prop} (hA : ∀ r, A r → r.isArgReg = true) :
    BodyEntryW F A af s w₀ := by
  refine ⟨h.sp, h.fp, fun r hr => ?_, h.other, fun a _ => by rw [h.mem], h.program⟩
  have := hA r hr
  cases r with
  | x n =>
    simp only [Reg.isArgReg, decide_eq_true_eq] at this
    have e := h.args n (by omega)
    simp only [xreg] at e
    simp only [regVal, rnum, e]
  | v n =>
    simp only [Reg.isArgReg, decide_eq_true_eq] at this
    exact h.argsV n this
  | _ => simp [Reg.isArgReg] at this

/-! ## Calls through the GOT: the target the VCode run gives them -/

/-- The guard of a call of `csemV gv`: when the call's target is the vreg `t` (its first use
operand), and `gv t n` (`t` holds the GOT entry of `n` at every call through it: `E2E.GotV`),
the target value (the first use) is `n`'s link-time address. -/
def gotGuard (gv : Nat → String → Prop) (X : ExtSem) (info : CallInfo) (uses : List CV) : Prop :=
  ∀ t n ops, info.dest = .reg (.vreg t .int) → gv t n → (MInst.call info).operands = .ok ops →
    ((ops.toList.filter Operand.isUse).head?).map Operand.vreg = some t →
    uses.head?.map lo64 = some (X.sym n 0)

open Classical in
/-- **`csem` with the calls through the GOT pinned to their symbol** (`gv`): a `call`/`try_call`
whose target vreg `t` has `gv t n` is defined only when the target value is `n`'s address
(`gotGuard`); everything else is `csem`. The VCode run reaches only such calls when `gv` is the
static GOT analysis of the code (`E2E.GotV`, `E2E.vReturns_gotV`), so the callee contract at a
GOT site needs to hold only for the GOT symbol's callee. `gv := fun _ _ => False` is `csem`. -/
noncomputable def csemV (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    ISem CV Arm.ArmState := fun i uses w =>
  match i with
  | .call info | .tryCall info _ => if gotGuard gv X info uses then csem F ctx X i uses w else none
  | _ => csem F ctx X i uses w

theorem csemV_sub {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {i : MInst} {uses : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : csemV gv F ctx X i uses w = some r) : csem F ctx X i uses w = some r := by
  unfold csemV at h
  split at h
  all_goals first | exact h | (split at h; exact h; cases h)

theorem csemV_guard {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {info : CallInfo} {uses : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : csemV gv F ctx X (.call info) uses w = some r) : gotGuard gv X info uses := by
  simp only [csemV] at h
  split at h
  · assumption
  · cases h

theorem csemV_guard_try {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {X : ExtSem} {info : CallInfo} {ti : TryInfo} {uses : List CV} {w : Arm.ArmState}
    {r : List CV × Arm.ArmState × Ctl}
    (h : csemV gv F ctx X (.tryCall info ti) uses w = some r) : gotGuard gv X info uses := by
  simp only [csemV] at h
  split at h
  · assumption
  · cases h

/-- `csemV` is `csem` where the guard of the calls holds. -/
theorem csemV_eq {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {i : MInst} {uses : List CV} {w : Arm.ArmState}
    (h : ∀ info, (i = .call info ∨ ∃ ti, i = .tryCall info ti) → gotGuard gv X info uses) :
    csemV gv F ctx X i uses w = csem F ctx X i uses w := by
  unfold csemV
  split
  · simp only [h _ (.inl rfl), ↓reduceIte]
  · simp only [h _ (.inr ⟨_, rfl⟩), ↓reduceIte]
  · rfl

theorem csemV_bot (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    csemV (fun _ _ => False) F ctx X = csem F ctx X := by
  funext i uses w
  exact csemV_eq fun _ _ _ _ _ _ h => h.elim

/-- The operand-view obligation of `csem` gives that of `csemV gv` (a guarded semantics). -/
theorem OperandsSoundCtlAtI.v {F F' FK : BitVec 64 → Prop} {P : MInst → Prop}
    {exec : MInst → Arm.ArmState → Option Arm.ArmState} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    {ctl : Ctl} {s : Arm.ArmState} (h : OperandsSoundCtlAtI F FK P exec (csem F' ctx X) i ctl s)
    (gv : Nat → String → Prop) : OperandsSoundCtlAtI F FK P exec (csemV gv F' ctx X) i ctl s :=
  fun c wh ops regs i' w outs w' hops hst hasg hp hw hal herr hsem =>
    h c wh ops regs i' w outs w' hops hst hasg hp hw hal herr (csemV_sub hsem)

/-- The fixed data of one activation. -/
structure RL where
  vc : VCode
  rf : RFunc
  af : AFunc
  fa : FnAsm
  fb : FnBin
  lm : Std.HashMap Lbl Nat
  base : BitVec 64
  /-- the ABI entry state -/
  s0 : Arm.ArmState
  X : ExtSem
  H : ArmHooks
  /-- the emitter's final state (trap table) -/
  psF : PState
  /-- the callees' stack budget below the body's `sp` (the dead stack of the calls) -/
  K : Nat
  /-- addresses the activation keeps and leaves outside its world (its callers' frames, the
  program's code; `fun _ => False` for the per-function theorems) -/
  G : BitVec 64 → Prop
  /-- the calls through the GOT: the target vreg `t` holds `n`'s address at every call through
  it (`csemV`; `fun _ _ => False` for the per-function theorems) -/
  gv : Nat → String → Prop

namespace RL
variable (R : RL)

def fr : RAFrame := RAFrame.compute R.vc R.rf
def L : List Line := R.fa.lines.toList
def ctx : FnCtx := ⟨R.fa.k, R.af.slotBase⟩
/-- The far labels the emitter relaxed the branches to (`emitFar`). -/
def far : Lbl → Bool := emitFar R.ctx R.af
/-- `sp` in the body. -/
def spB : BitVec 64 := spv R.s0 - BitVec.ofNat 64 (frameDrop R.af)
/-- The frame addresses and the kept addresses `G` (kept by every step of the body). -/
def FK : BitVec 64 → Prop := fun a => frameF R.fr.intBase R.fr.size R.af R.s0 a ∨ R.G a
/-- The addresses outside the world: the frame, the callees' dead stack below `spB` and `G`. -/
def F : BitVec 64 → Prop := frameWG R.K R.fr.intBase R.fr.size R.af R.G R.s0
/-- Address of line `j`. -/
def pcOf (j : Nat) : BitVec 64 := R.base + BitVec.ofNat 64 (lineOffset R.L j)
/-- The encoder's environment at line `j`. -/
def envOf (j : Nat) : Env := ⟨lineOffset R.L j, (R.lm[·]?)⟩
/-- The instruction semantics of the activation (`csem`, the calls through the GOT pinned). -/
noncomputable def sem : ISem CV Arm.ArmState := csemV R.gv R.F R.ctx R.X

theorem sem_csem {i : MInst} {uses : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : R.sem i uses w = some r) : csem R.F R.ctx R.X i uses w = some r := csemV_sub h

/-- Off the calls, `sem` is `csem`. -/
theorem sem_eq {i : MInst} (hc : ∀ info, i ≠ .call info) (ht : ∀ info ti, i ≠ .tryCall info ti)
    (uses : List CV) (w : Arm.ArmState) : R.sem i uses w = csem R.F R.ctx R.X i uses w :=
  csemV_eq fun info h => by
    rcases h with rfl | ⟨ti, rfl⟩
    · exact absurd rfl (hc info)
    · exact absurd rfl (ht info ti)

/-- The machine. -/
noncomputable def step : Arm.ArmState → Arm.ArmState := ArmStepX R.X R.H R.fa

/-- The bytes the prologue writes below the entry `sp`: fp/lr and the clobber area. -/
def topN : Nat := 16 + clobberBytes R.af.saves

/-- The lowest of them: the bottom of the clobber area. -/
def topB : BitVec 64 := spv R.s0 - BitVec.ofNat 64 R.topN

/-- The state after the prologue. -/
noncomputable def sP : Arm.ArmState := iterN R.step (prologueLines R.af.saves R.af.frameSize).length R.s0

/-- What the prologue leaves in fp/lr and the clobber area. -/
noncomputable def topImg : BitVec (R.topN * 8) := Arm.read_mem_bytes R.topN R.topB R.sP

end RL

/-- `pc` is the address after a call instruction (`bl`, `blr`) of the laid-out function `fa`
loaded at `base`: where a call of the function returns to. -/
def PostCall (fa : FnAsm) (base pc : BitVec 64) : Prop := ∃ q, CallPc fa base q ∧ pc = q + 4

/-- **A state of the activation that is no return into its own code**: at an address after one
of its calls only with the body's `sp`. Every state of a run of the activation before its return
satisfies it (`regLevelCorrect_world`), which tells the linked call of a function calling itself
(one copy of the code) where the callee returns. -/
def RL.Good (R : RL) (u : Arm.ArmState) : Prop :=
  ¬ PostCall R.fa R.base (Arm.r .PC u) ∨ spOf u = R.spB

/-- The Arm state `s` represents store `m` and world `w`. -/
structure StRel (R : RL) (s : Arm.ArmState) (m : Loc → CV) (w : Arm.ArmState) : Prop where
  store : ∀ l, ValidLoc l → Live R.rf l → m l = locVal R.fr s l
  world : SameWorld R.F s w
  err : Arm.r .ERR s = .None
  prog : s.program = R.fb.program R.base
  sp : spOf s = R.spB
  align : Arm.CheckSPAlignment s
  /-- fp/lr and the clobber area as pushed by the prologue -/
  fplr : R.af.frame = true → Arm.read_mem_bytes R.topN R.topB s = R.topImg
  /-- the code words are readable as data -/
  code : ∀ k w, R.fb.words[k]? = some w →
    Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) s = w
  /-- the kept addresses hold what they held at entry -/
  gkeep : ∀ a, R.G a → s.mem a = R.s0.mem a
  /-- the frame pointer as the prologue set it: x29 = entry sp − 16 (Cranelift's unwind rows
  define the CFA from x29; the body never writes x29, the callees keep it) -/
  fp : R.af.frame = true → xreg 29 s = spv R.s0 - 16#64

/-- x29 is part of the world: two states with the same world agree on it. -/
theorem xreg29_sw {F : BitVec 64 → Prop} {s s' w : Arm.ArmState} (h : SameWorld F s w)
    (h' : SameWorld F s' w) : xreg 29 s' = xreg 29 s := by
  show Arm.r (.GPR 29#5) s' = Arm.r (.GPR 29#5) s
  rw [h'.1 _ (by simp [Masked]), ← h.1 _ (by simp [Masked])]

/-- The checker accepts the remaining items of block `vb` (from VCode index `k`). -/
def ItemsChecked (R : RL) (vb : VBlock) (its : List RItem) : Prop :=
  ∃ (c : CheckCtx) (k : Nat) (a out : AState), c.rf = R.rf ∧ c.vc = R.vc ∧ c.runItems vb k its a = .ok out

/-- **The simulation relation inside a block** (`b`, remaining items `its`, their code `code`):
the lines of `code` but its last instruction's are `X`, those of the last instruction are the
block's segment's (`x.1.term`, `x` = the block's segment in the emission plan, `segX`); the lines
from `j` on are the relaxation of `X` and the segment's final lines (`x.2.1`), then the lines from
the one after them (`x.2.2`) on; the segment passes the branch check (`SegChecked`). -/
def Qs (R : RL) (s : Arm.ArmState) (b : Nat) (its : List RItem) (m : Loc → CV)
    (w : Arm.ArmState) : Prop :=
  ∃ j vb items pre code X ps1 psm ps2 x,
    R.vc.blocks[b]? = some vb ∧ R.rf.blocks[b]? = some items ∧ items.toList = pre ++ its ∧
    ItemsChecked R vb its ∧
    itemsCode R.fr vb its = .ok code ∧
    codeLinesE R.ctx R.af code.dropLast ps1 = .ok (X, psm) ∧
    codeLinesE R.ctx R.af code.getLast?.toList psm = .ok (x.1.term, ps2) ∧
    ps2.traps.toList <+: R.psF.traps.toList ∧
    R.L.drop j = relaxLines R.far (X ++ x.2.1) ++ R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2) ∧
    Arm.r .PC s = R.pcOf j ∧ StRel R s m w ∧
    segX R.fa.k R.af b = some x ∧ SegChecked R.fa.k R.af b

/-- **Entering block `b`** with store `m` and world `w` in state `s`: at its first item
(`Qs`), or `b` forwards (`fwd?`: its items are one `op` of its only instruction, a `jump`, whose
`b` the emission may have removed or aliased) to its successor `bx`, entered so, without a
machine step. -/
inductive QE (R : RL) (s : Arm.ArmState) (m : Loc → CV) (w : Arm.ArmState) : Nat → Prop
  | std {b : Nat} {items : Array RItem} : R.rf.blocks[b]? = some items →
      Qs R s b items.toList m w → QE R s m w b
  | fwd {b bx : Nat} {vb vbx : VBlock} {x : Label} {items : Array RItem} {allocs : Array Loc}
      {regs : Array Reg} {i : MInst} : R.vc.blocks[b]? = some vb →
      R.af.fwd? vb.label = some x → R.rf.blocks[b]? = some items →
      items.toList = [.op 0 allocs] → allocs = regs.map Loc.reg → vb.insts = #[i] →
      i.assign regs = .ok (.jump x) → succOf R.vc b 0 = some bx →
      R.vc.blocks[bx]? = some vbx → vbx.label = x → QE R s m w bx → QE R s m w b

/-- **The simulation relation**: inside a block (`Qs`), or at the entry of a block entered
through forwarding blocks (`QE`). -/
def Q (R : RL) (s : Arm.ArmState) : MConf CV Arm.ArmState → Prop
  | .run ⟨b, its, m, w⟩ =>
    Qs R s b its m w ∨ ∃ items, R.rf.blocks[b]? = some items ∧ its = items.toList ∧ QE R s m w b
  | _ => True

/-- A block entered (`QE`) has items. -/
theorem QE.items {R : RL} {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState} {b : Nat}
    (h : QE R s m w b) : ∃ items, R.rf.blocks[b]? = some items := by
  cases h with
  | std hit _ => exact ⟨_, hit⟩
  | fwd _ _ hit _ _ _ _ _ _ _ _ => exact ⟨_, hit⟩

/-- **`Q` at an item**: inside a block (`Qs`), or the item is the only one of a forwarding
block (an `op` of its only instruction, a `jump` to its successor `bx`, entered by `Q`). -/
theorem Q.cases {R : RL} {s : Arm.ArmState} {b : Nat} {it : RItem} {its : List RItem}
    {m : Loc → CV} {w : Arm.ArmState} (h : Q R s (.run ⟨b, it :: its, m, w⟩)) :
    Qs R s b (it :: its) m w ∨ ∃ vb allocs regs i x bx, R.vc.blocks[b]? = some vb ∧
      it = .op 0 allocs ∧ its = [] ∧ allocs = regs.map Loc.reg ∧ vb.insts = #[i] ∧
      i.assign regs = .ok (.jump x) ∧ succOf R.vc b 0 = some bx ∧
      ∃ itx, R.rf.blocks[bx]? = some itx ∧ Q R s (.run ⟨bx, itx.toList, m, w⟩) := by
  rcases h with hs | ⟨items, hit, hits, hqe⟩
  · exact .inl hs
  cases hqe with
  | std hit' hq =>
    rw [hit] at hit'
    cases hit'
    rw [hits]
    exact .inl hq
  | fwd hvb _ hit' hil hal hins hasg hsucc _ _ hq =>
    rw [hit] at hit'
    cases hit'
    rw [hil] at hits
    simp only [List.cons.injEq] at hits
    obtain ⟨rfl, rfl⟩ := hits
    obtain ⟨itx, hitx⟩ := hq.items
    exact .inr ⟨_, _, _, _, _, _, hvb, rfl, rfl, hal, hins, hasg, hsucc, itx, hitx,
      .inr ⟨itx, hitx, rfl, hq⟩⟩

/-- `Q` at an item that is no `op` of instruction 0 is `Qs`. -/
theorem Q.qs {R : RL} {s : Arm.ArmState} {b : Nat} {it : RItem} {its : List RItem}
    {m : Loc → CV} {w : Arm.ArmState} (h : Q R s (.run ⟨b, it :: its, m, w⟩))
    (hit : ∀ allocs, it ≠ .op 0 allocs) : Qs R s b (it :: its) m w := by
  rcases Q.cases h with h | ⟨_, allocs, _, _, _, _, -, he, -⟩
  · exact h
  · exact (hit allocs he).elim

/-- Every successful run of `x` ends with a value meeting `P`. -/
def VPost {α : Type} (P : α → Prop) (x : StateT Nat (Except String) α) : Prop :=
  ∀ s a s', x.run s = .ok (a, s') → P a

theorem vpost_pure {α : Type} {P : α → Prop} {a : α} (h : P a) :
    VPost P (pure a : StateT Nat (Except String) α) := by
  intro s a' s' h'
  cases h'
  exact h

theorem vpost_bind {α β : Type} {P : β → Prop} {x : StateT Nat (Except String) α}
    {g : α → StateT Nat (Except String) β} (h : ∀ a, VPost P (g a)) : VPost P (x >>= g) := by
  intro s b s' h'
  rw [StateT.run_bind] at h'
  cases hx : x.run s with
  | error e => rw [hx] at h'; cases h'
  | ok p => rw [hx] at h'; exact h p.1 p.2 b s' h'

/-- Visiting the operands keeps the branch targets and the `Args` form. -/
theorem visit_shape (f : OpSpec → Reg → StateT Nat (Except String) Reg) (i : MInst) :
    VPost (fun r => r.targets = i.targets ∧ ((∃ ds, r = .args ds) → ∃ ds, i = .args ds))
      (MInst.visitOperands f i) := by
  cases i <;> simp only [MInst.visitOperands] <;>
    repeat' (first
      | exact vpost_pure ⟨rfl, fun _ => ⟨_, rfl⟩⟩
      | exact vpost_pure ⟨rfl, fun ⟨_, h⟩ => by cases h⟩
      | refine vpost_bind fun _ => ?_
      | split)

/-- Substituting an allocation keeps the branch targets and the `Args` form. -/
theorem assign_shape {i i' : MInst} {regs : Array Reg} (h : i.assign regs = .ok i') :
    i'.targets = i.targets ∧ ((∃ ds, i' = .args ds) → ∃ ds, i = .args ds) := by
  rw [assign_eq] at h
  simp only [bind, Except.bind] at h
  cases hr : (MInst.visitOperands (putOp regs) i).run 0 with
  | error e => rw [hr] at h; cases h
  | ok p =>
    rw [hr] at h
    obtain ⟨i1, k⟩ := p
    simp only at h
    split at h
    · cases h
    · cases h
      exact visit_shape _ i 0 i' k hr

/-- `Q` at an `op` whose instruction branches nowhere is `Qs`. -/
theorem Q.qs_op {R : RL} {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem}
    {m : Loc → CV} {w : Arm.ArmState} (h : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (ht : i.targets = []) : Qs R s b (.op k allocs :: its) m w := by
  rcases Q.cases h with h | ⟨vb', _, regs, i', x, -, hvb', he, -, -, hins, hasg, -⟩
  · exact h
  · rw [hvb] at hvb'
    cases hvb'
    simp only [RItem.op.injEq] at he
    obtain ⟨rfl, -⟩ := he
    rw [hins] at hi
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    have := (assign_shape hasg).1
    rw [ht] at this
    cases this

/-- `Q` at an `op` of an instruction before the block's last is `Qs`. -/
theorem Q.qs_lt {R : RL} {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem}
    {m : Loc → CV} {w : Arm.ArmState} (h : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} (hvb : R.vc.blocks[b]? = some vb) (hk : k + 1 < vb.insts.size) :
    Qs R s b (.op k allocs :: its) m w := by
  rcases Q.cases h with h | ⟨vb', _, _, i', _, _, hvb', he, -, -, hins, -⟩
  · exact h
  · rw [hvb] at hvb'
    cases hvb'
    simp only [RItem.op.injEq] at he
    obtain ⟨rfl, -⟩ := he
    rw [hins] at hk
    simp at hk

/-- Checked items after an `op` of an instruction before the block's last are not empty. -/
theorem ItemsChecked.tail_ne {R : RL} {vb : VBlock} {k : Nat} {allocs : Array Loc}
    {its : List RItem} (h : ItemsChecked R vb (.op k allocs :: its)) (hk : k + 1 < vb.insts.size) :
    its ≠ [] := by
  obtain ⟨c, k0, a, out, -, -, hrun⟩ := h
  obtain ⟨-, rfl, _, _, _, _, _, _, h'⟩ := runItems_op hrun
  rintro rfl
  have := (runItems_nil h').1
  omega

/-- Under `Q`, the remaining items are a suffix of the block's items. -/
theorem Q.split {R : RL} {s : Arm.ArmState} {b : Nat} {its : List RItem} {m : Loc → CV}
    {w : Arm.ArmState} (h : Q R s (.run ⟨b, its, m, w⟩)) :
    ∃ items pre, R.rf.blocks[b]? = some items ∧ items.toList = pre ++ its := by
  rcases h with ⟨_, _, items, pre, _, _, _, _, _, _, -, hit, hsplit, -⟩ | ⟨items, hit, rfl, -⟩
  · exact ⟨items, pre, hit, hsplit⟩
  · exact ⟨items, [], hit, rfl⟩

end Backend.Proof

namespace Backend.Proof

open Backend E2E

/-! ## Code bookkeeping -/

theorem mem_wordsAt {base : BitVec 64} :
    ∀ (ws : List (BitVec 32)) (k0 k : Nat) (w : BitVec 32), ws[k]? = some w →
      List.Mem (base + BitVec.ofNat 64 (4 * (k0 + k)), w) (wordsAt base k0 ws)
  | [], _, _, _, h => by simp at h
  | w' :: ws, k0, 0, w, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact List.Mem.head _
  | w' :: ws, k0, k + 1, w, h => by
    simp only [List.getElem?_cons_succ] at h
    have := mem_wordsAt (base := base) ws (k0 + 1) k w h
    rw [show k0 + 1 + k = k0 + (k + 1) by omega] at this
    exact List.Mem.tail _ this

/-- The bytes of code word `k` are code addresses of a state holding the function's program. -/
theorem codeAddr_word {s : Arm.ArmState} {base : BitVec 64} {fb : FnBin}
    (hp : s.program = fb.program base) {k : Nat} {w : BitVec 32} (hk : fb.words[k]? = some w)
    {i : Nat} (hi : i < 4) : CodeAddr s (base + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 i) := by
  refine ⟨(base + BitVec.ofNat 64 (4 * k), w), ?_, ?_⟩
  · rw [hp]
    have := mem_wordsAt (base := base) fb.words.toList 0 k w (by simpa using hk)
    rw [Nat.zero_add] at this
    exact this
  · simp only
    rw [show base + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 i - (base + BitVec.ofNat 64 (4 * k)) =
      BitVec.ofNat 64 i by bv_omega]
    simp only [BitVec.toNat_ofNat]
    omega

/-- The code words are kept by a step that keeps the memory at code addresses. -/
theorem code_keep {s0 s s' : Arm.ArmState} {base : BitVec 64} {fb : FnBin}
    (hp : s0.program = fb.program base)
    (hc : ∀ k w, fb.words[k]? = some w → Arm.read_mem_bytes 4 (base + BitVec.ofNat 64 (4 * k)) s = w)
    (hm : ∀ a, CodeAddr s0 a → s'.mem a = s.mem a) :
    ∀ k w, fb.words[k]? = some w → Arm.read_mem_bytes 4 (base + BitVec.ofNat 64 (4 * k)) s' = w := by
  intro k w hk
  rw [← hc k w hk]
  exact read_mem_bytes_congr _ _ fun i hi => hm _ (codeAddr_word hp hk hi)

theorem codeLinesE_append {c : FnCtx} {af : AFunc} :
    ∀ (A B : List AInst) (ps ps' : PState) (ls : List Line),
      codeLinesE c af (A ++ B) ps = .ok (ls, ps') →
      ∃ ls1 ls2 psm, codeLinesE c af A ps = .ok (ls1, psm) ∧
        codeLinesE c af B psm = .ok (ls2, ps') ∧ ls = ls1 ++ ls2
  | [], B, ps, ps', ls, h => ⟨[], ls, ps, rfl, by simpa using h, by simp⟩
  | a :: A, B, ps, ps', ls, h => by
    simp only [List.cons_append, codeLinesE, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i r2 hr2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ls1, ls2, psm, h1, h2, h3⟩ := codeLinesE_append A B r.2 r2.2 r2.1 hr2
        refine ⟨r.1 ++ ls1, ls2, psm, ?_, h2, ?_⟩
        · simp [codeLinesE, bind, Except.bind, hr, h1, pure, Except.pure]
        · rw [h3]; simp

theorem itemsCode_cons {fr : RAFrame} {vb : VBlock} {it : RItem} {its : List RItem}
    {code : List AInst} (h : itemsCode fr vb (it :: its) = .ok code) :
    ∃ c1 c2, itemCode fr vb it = .ok c1 ∧ itemsCode fr vb its = .ok c2 ∧ code = c1 ++ c2 := by
  simp only [itemsCode, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i c1 h1
    split at h
    · cases h
    · rename_i c2 h2
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨c1, c2, h1, h2, h.symm⟩

theorem execLines_pc : ∀ {env : Env} {ls : List Line} {s s' : Arm.ArmState},
    execLines env ls s = some s' → Arm.r .PC s' = Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length)
  | _, [], s, s', h => by simp [execLines] at h; subst h; simp
  | _, .label _ :: _, _, _, h => by simp [execLines] at h
  | _, .word _ _ :: _, _, _, h => by simp [execLines] at h
  | env, .ins i t :: ls, s, s', h => by
    simp only [execLines] at h
    split at h
    · split at h
      · rename_i hpc
        rw [execLines_pc h, hpc, BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]
        omega
      · cases h
    · cases h

/-- Lines of instructions only: each is 4 bytes. -/
theorem lineOffset_drop_ins {L : List Line} {j : Nat} {ls T : List Line}
    (hd : L.drop j = ls ++ T) (hins : ∀ ln ∈ ls, ∃ i t, ln = .ins i t) :
    lineOffset L (j + ls.length) = lineOffset L j + 4 * ls.length := by
  induction ls generalizing j with
  | nil => simp
  | cons ln ls ih =>
    obtain ⟨i, t, rfl⟩ := hins ln (by simp)
    have hj : L[j]? = some (.ins i t) := by
      have := congrArg (·[0]?) hd
      simpa [List.getElem?_drop] using this
    have hd' : L.drop (j + 1) = ls ++ T := by
      rw [← List.drop_drop, hd]; rfl
    have := ih hd' (fun x hx => hins x (by simp [hx]))
    have h1 := lineOffset_succ L j _ hj
    simp only [Line.size] at h1
    simp only [List.length_cons]
    rw [show j + (ls.length + 1) = j + 1 + ls.length by omega, this, h1]
    omega

theorem list_mapM_ok {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → l'.length = l.length ∧
      ∀ (i : Nat) x, l[i]? = some x → ∃ y, f x = .ok y ∧ l'[i]? = some y
  | [], l', h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i y hy
    split at h
    · cases h
    rename_i ys hys
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hl, hi⟩ := list_mapM_ok hys
    refine ⟨by simp [hl], fun i x hx => ?_⟩
    cases i with
    | zero => simp at hx; subst hx; exact ⟨y, hy, rfl⟩
    | succ i =>
      simp at hx
      obtain ⟨y', h1, h2⟩ := hi i x hx
      exact ⟨y', h1, by simpa using h2⟩

theorem array_mapM_ok {ε α β : Type} {f : α → Except ε β} {as : Array α} {bs : Array β}
    (h : as.mapM f = .ok bs) : bs.size = as.size ∧
      ∀ (i : Nat) x, as[i]? = some x → ∃ y, f x = .ok y ∧ bs[i]? = some y := by
  have e := Array.toList_mapM (xs := as) (f := f)
  rw [h] at e
  simp only [Functor.map, Except.map] at e
  obtain ⟨hl, hi⟩ := list_mapM_ok e.symm
  refine ⟨by simpa using hl, fun i x hx => ?_⟩
  obtain ⟨y, h1, h2⟩ := hi i x (by simpa using hx)
  exact ⟨y, h1, by rw [← Array.getElem?_toList]; exact h2⟩

def locReg : Loc → Except String Reg
  | Loc.reg r => pure r
  | l => throw (toString "operand in " ++ toString (repr l))

theorem mapM_locReg : ∀ (L : List Loc) (R : List Reg), L.mapM locReg = .ok R → L = R.map .reg
  | [], R, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | l :: L, R, h => by
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i r hr
    split at h
    · cases h
    rename_i rs hrs
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [mapM_locReg L rs hrs]
    cases l <;> simp [locReg, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hr
    subst hr; rfl

theorem arr_mapM_locReg {allocs : Array Loc} {regs : Array Reg}
    (h : allocs.mapM locReg = .ok regs) : allocs = regs.map .reg := by
  have e := Array.toList_mapM (xs := allocs) (f := locReg)
  rw [h] at e
  simp only [Functor.map, Except.map] at e
  apply Array.toList_inj.1
  rw [Array.toList_map]
  exact mapM_locReg _ _ e.symm

theorem itemCode_op {fr : RAFrame} {vb : VBlock} {k : Nat} {allocs : Array Loc} {c1 : List AInst}
    (h : itemCode fr vb (.op k allocs) = .ok c1) :
    ∃ regs i i', allocs = regs.map Loc.reg ∧ vb.insts[k]? = some i ∧ i.assign regs = .ok i' ∧
      ((c1 = [AInst.inst i'] ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us)) ∨ (∃ ds, i' = .args ds ∧ c1 = []) ∨
        (∃ us, i' = .rets us ∧ c1 = [AInst.epilogueRet])) := by
  unfold itemCode itemStep at h
  dsimp only at h
  simp only [bind, Except.bind, Functor.map, Except.map] at h
  split at h
  · cases h
  rename_i arr harr
  simp only [Except.ok.injEq] at h
  subst h
  split at harr
  · cases harr
  rename_i regs hregs
  split at harr
  · rename_i i hi
    split at harr
    · cases harr
    rename_i i' hi'
    refine ⟨regs, i, i', arr_mapM_locReg (by exact hregs), hi, hi', ?_⟩
    cases i' <;> simp only [pure, Except.pure, Except.ok.injEq] at harr <;> subst harr <;> simp
  · simp [throw, throwThe, MonadExceptOf.throw] at harr


/-- The last instruction of a block of a VCode with a CFG is a terminator. -/
theorem cfg_back {vc : VCode} {ss ps : Array (Array Nat)} (h : vc.cfg = .ok (ss, ps)) {b : Nat}
    {vb : VBlock} (hvb : vc.blocks[b]? = some vb) :
    ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true := by
  unfold VCode.cfg at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i succs hsuccs
  obtain ⟨-, hel⟩ := array_mapM_ok hsuccs
  obtain ⟨ts, hts, -⟩ := hel b vb hvb
  split at hts
  · rename_i t ht
    split at hts
    · simp [throw, throwThe, MonadExceptOf.throw] at hts
    · rename_i hterm
      exact ⟨t, ht, by simpa using hterm⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at hts

/-- A checked item list that is not empty has an `op` of the block's last instruction. -/
theorem runItems_last {c : CheckCtx} {vb : VBlock} :
    ∀ {its : List RItem} {k : Nat} {a out : AState}, c.runItems vb k its a = .ok out → its ≠ [] →
      ∃ allocs, RItem.op (vb.insts.size - 1) allocs ∈ its
  | [], _, _, _, _, hne => absurd rfl hne
  | .move src dst :: rest, k, a, out, h, _ => by
    obtain ⟨hk, h'⟩ := runItems_move h
    cases rest with
    | nil => exact absurd (runItems_nil h').1 hk
    | cons r rest =>
      obtain ⟨al, hm⟩ := runItems_last h' (by simp)
      exact ⟨al, List.mem_cons_of_mem _ hm⟩
  | .op k' allocs :: rest, k, a, out, h, _ => by
    obtain ⟨hk, hkk, _, _, _, _, _, _, h'⟩ := runItems_op h
    cases rest with
    | nil =>
      have := (runItems_nil h').1
      exact ⟨allocs, by rw [show vb.insts.size - 1 = k' by omega]; simp⟩
    | cons r rest =>
      obtain ⟨al, hm⟩ := runItems_last h' (by simp)
      exact ⟨al, List.mem_cons_of_mem _ hm⟩

theorem itemsCode_mem {fr : RAFrame} {vb : VBlock} :
    ∀ {its : List RItem} {c : List AInst} {it : RItem}, itemsCode fr vb its = .ok c → it ∈ its →
      ∃ c1, itemCode fr vb it = .ok c1 ∧ c1 <:+: c
  | [], _, _, _, hm => by simp at hm
  | it' :: its, c, it, h, hm => by
    obtain ⟨c1, c2, h1, h2, rfl⟩ := itemsCode_cons h
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨c1, h1, (List.prefix_append c1 c2).isInfix⟩
    · obtain ⟨c', h', hi⟩ := itemsCode_mem h2 hm
      exact ⟨c', h', hi.trans (List.suffix_append c1 c2).isInfix⟩

/-- **The code of a checked item list that is not empty is not empty** (its last item is an
`op` of the block's terminator). -/
theorem itemsCode_ne_nil {vc : VCode} {ss ps : Array (Array Nat)} (hcfg : vc.cfg = .ok (ss, ps))
    {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {cc : CheckCtx} {k : Nat}
    {a out : AState} {its : List RItem} (hrun : cc.runItems vb k its a = .ok out) (hne : its ≠ [])
    {fr : RAFrame} {c : List AInst} (hc : itemsCode fr vb its = .ok c) : c ≠ [] := by
  obtain ⟨allocs, hm⟩ := runItems_last hrun hne
  obtain ⟨t, hback, hterm⟩ := cfg_back hcfg hvb
  obtain ⟨c1, hc1, hsub⟩ := itemsCode_mem hc hm
  obtain ⟨regs, i, i', -, hi, hasg, hcase⟩ := itemCode_op hc1
  rw [Array.back?_eq_getElem?, hi] at hback
  cases hback
  intro hcn
  subst hcn
  have h0 : c1 = [] := List.infix_nil.mp hsub
  rcases hcase with ⟨rfl, -⟩ | ⟨ds, rfl, -⟩ | ⟨us, -, rfl⟩
  · cases h0
  · obtain ⟨ds', rfl⟩ := (assign_shape hasg).2 ⟨ds, rfl⟩
    simp [MInst.isTerminator, MInst.isBranch, MInst.isRet] at hterm
  · cases h0

end Backend.Proof
