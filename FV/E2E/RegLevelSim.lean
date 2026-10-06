import FV.E2E.RegLevelMachine
import FV.Backend.Proof.RegallocLayout

/-!
# The register-level simulation relation (M6)

The Arm machine `ArmStepX` running the laid-out function realises the allocated code
(`MStep`) item by item. `Q R s c` relates an Arm state `s` to an allocated-code configuration
`c` of the activation `R`:

* **position**: the pc is at line `j` of the final line list, and the lines from `j` on are the
  `fallthrough` of the remaining items' lines (followed by the next block's label);
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
`size`): the spill, save and float-move slots `[sp_body + lo, sp_body + hi)`, the padding and
fp/lr above the CLIF slots `[sp_body + frameSize, sp_entry)` (the explicit CLIF slots in between
belong to the world; empty without a frame), and the code words (read as data by jump tables;
the program never accesses them). -/
def frameF (lo hi : Nat) (af : AFunc) (s : Arm.ArmState) (a : BitVec 64) : Prop :=
  (lo ≤ (a - (spv s - BitVec.ofNat 64 (frameDrop af))).toNat ∧
    (a - (spv s - BitVec.ofNat 64 (frameDrop af))).toNat < hi) ∨
  (af.frameSize ≤ (a - (spv s - BitVec.ofNat 64 (frameDrop af))).toNat ∧
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
  exact ⟨s', hex, hW, ⟨hK.1, fun a ha => hK.2 a (hFK a ha)⟩, hd, ho, hc⟩

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
  /-- fp/lr as pushed by the prologue -/
  fplr : R.af.frame = true →
    Arm.read_mem_bytes 16 (spv R.s0 - 16#64) s = xreg 30 R.s0 ++ xreg 29 R.s0
  /-- the code words are readable as data -/
  code : ∀ k w, R.fb.words[k]? = some w →
    Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) s = w
  /-- the kept addresses hold what they held at entry -/
  gkeep : ∀ a, R.G a → s.mem a = R.s0.mem a

/-- The checker accepts the remaining items of block `vb` (from VCode index `k`). -/
def ItemsChecked (R : RL) (vb : VBlock) (its : List RItem) : Prop :=
  ∃ (c : CheckCtx) (k : Nat) (a out : AState), c.rf = R.rf ∧ c.vc = R.vc ∧ c.runItems vb k its a = .ok out

/-- **The simulation relation.** -/
def Q (R : RL) (s : Arm.ArmState) : MConf CV Arm.ArmState → Prop
  | .run ⟨b, its, m, w⟩ =>
    ∃ j vb items pre code ls ps1 ps2 T,
      R.vc.blocks[b]? = some vb ∧ R.rf.blocks[b]? = some items ∧ items.toList = pre ++ its ∧
      ItemsChecked R vb its ∧
      itemsCode R.fr vb its = .ok code ∧
      codeLinesE R.ctx R.af code ps1 = .ok (ls, ps2) ∧
      ps2.traps.toList <+: R.psF.traps.toList ∧
      R.L.drop j = relaxLines R.far (ftList (ls ++ nxtOf R.af b)) ++ T ∧
      Arm.r .PC s = R.pcOf j ∧ StRel R s m w
  | _ => True

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

end Backend.Proof
