import FV.Backend
import FV.Backend.Proof.RegallocSound
import FV.Backend.Proof.RegallocOperands
import FV.Backend.Proof.EncodeStep
import FV.Backend.Proof.LowerSim
import FV.Backend.Proof.DriverCheck
import FV.Backend.Proof.PrepareCheck
import FV.Compile.Subset

/-!
# M7: the end-to-end statement (`docs/contracts/e2e.md`)

For an in-subset CLIF function `f` of a program `p` and the Lean backend's compiled code
(`Compiled`: `lowerFunction` → `prepare` → `checkAlloc` → `lowerRFunc` → `emitFunc` →
`FnAsm.layout`, and the validators `lowerCheck`/`prepCheck` accepted), loaded at `base`: an Arm execution from an ABI-conformant entry state refines
the CLIF execution (`Clif.runLoop` from the matching CLIF entry state):

* CLIF returns `vals` with memory `cm` ⇒ the Arm run reaches the return address with `vals` in
  x0.. (low bits, `XHolds`), sp / callee-saved registers restored, and memory agreeing with `cm`
  on every live CLIF allocation;
* CLIF traps with code `c` ⇒ the Arm run reaches a trap site of the function's trap table with
  code `c`;
* `stuck` (a violated CLIF precondition) and `outOfFuel`: no claim.

The three layers and who proves them:

```
Clif.runLoop  ──(IselSim: M7 driver + lowerCheck, from M4's rules)──▶  VStep vc sem
VStep vc sem  ──(PrepareCorrect: M7, prepCheck)─────────────────────▶  VStep (prepare vc) sem
VStep vcp sem ──(RegLevelCorrect: M6 + M5)──────────────────────────▶  Arm run (astep^n)
```

`sem s : Sem` is the VCode-level per-`MInst` semantics of the activation entered in `s`, shared
by M4 and M6 (M6's `csem (F s)`; values `CV` = 128-bit registers, world = the Arm state).
Everything is stated for an abstract `sem`, Arm machine `astep` and frame-address set `F`; they
are instantiated by M6's definitions.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-! ## Values: the width convention

`Sem` (the VCode-level instruction semantics, M6's `csem` is the instance), `VHolds` (a CLIF
value of type `ty` is the low `ty.width` bits of a register value, upper bits unspecified,
PLAN.md §3.4) and `AllHold` are the driver's (`Backend.Proof.Driver`, shared with M4). -/

/-- `VHolds` for a 64-bit X register. For the subset's types (width ≤ 64) this is
`x.setWidth v.ty.width = v.bits` (`XHolds_iff`). -/
def XHolds (v : Clif.Val) (x : BitVec 64) : Prop := VHolds v (ofX x)

theorem XHolds_iff {v : Clif.Val} {x : BitVec 64} (h : v.ty.width ≤ 64) :
    XHolds v x ↔ x.setWidth v.ty.width = v.bits := by
  simp only [XHolds, VHolds, ofX]
  rw [BitVec.setWidth_setWidth_of_le _ (by omega)]

/-- Number of the Arm register `x n`. -/
def xreg (n : Nat) (s : Arm.ArmState) : BitVec 64 := Arm.r (.GPR (BitVec.ofNat 5 n)) s

/-- Arm stack pointer. -/
def spv (s : Arm.ArmState) : BitVec 64 := Arm.r (.GPR 31#5) s

/-! ## The subset -/

/-- The CLIF functions the theorem covers: clif-subset-v2 E (`Compile.functionE`), plus the
current restrictions of the proof (e2e.md, "Remaining"): parameters passed in registers,
calls only to externs (calls between compiled functions compose by induction on the call
depth, not done yet; for indirect calls this is the run premise `TrapsExplicit.indirect`),
externs and indirect calls with at most 8 (register) parameters (no stack-passed call
arguments), and signatures (the function's, its externs' and its indirect calls') with `normal`
parameters and returns plus at most one `sret` struct-return pointer (`sigAbiOk`: in x8,
returned in x0, no other returns); other special-purpose parameters are compiled and flagged
unverified. -/
structure InSubset (p : Clif.Program) (f : Clif.Function) : Prop where
  func : p.func? f.name = some f
  subsetE : Compile.functionE f = true
  regParams : f.sig.params.length ≤ 8
  externCalls : ∀ b ∈ f.blocks, ∀ st ∈ b.body, ∀ fn args, st.inst = .call fn args →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  /-- a `try_call` calls an extern, like `externCalls` -/
  tryExterns : ∀ b ∈ f.blocks, ∀ fn args et, b.term = .tryCall fn args et →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  callRegArgs : ∀ e ∈ f.externs, e.2.sig.params.length ≤ 8
  abiSigs : sigAbiOk f.sig = true ∧ ∀ e ∈ f.externs, sigAbiOk e.2.sig = true
  /-- the signatures of the indirect calls (`call_indirect`, `try_call_indirect`) take at most
  8 (register) parameters and pass `sigAbiOk` (`Backend.indSigsOk`) -/
  indSigs : ∀ s ∈ indSigs f, s.params.length ≤ 8 ∧ sigAbiOk s = true

/-- A function without indirect calls has no indirect-call signatures. -/
theorem indSigs_eq_nil {f : Clif.Function}
    (hci : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ sig callee args, st.inst ≠ .callIndirect sig callee args)
    (htci : ∀ B ∈ f.blocks, ∀ callee args et, B.term ≠ .tryCallIndirect callee args et) :
    indSigs f = [] := by
  unfold indSigs
  rw [List.flatMap_eq_nil_iff]
  intro B hB
  rw [List.append_eq_nil_iff, List.filterMap_eq_nil_iff]
  refine ⟨fun st hst => ?_, ?_⟩
  · cases h : st.inst with
    | callIndirect sig callee args => exact absurd h (hci B hB st hst sig callee args)
    | _ => rfl
  · cases h : B.term with
    | tryCallIndirect callee args et => exact absurd h (htci B hB callee args et)
    | _ => rfl

/-- **Specialisation**: for a function without indirect calls, `InSubset` is the former subset
(the same fields, without `indSigs`, which is vacuous: `indSigs_eq_nil`). -/
theorem InSubset.of_indirectFree {p : Clif.Program} {f : Clif.Function}
    (hfunc : p.func? f.name = some f) (hE : Compile.functionE f = true)
    (hreg : f.sig.params.length ≤ 8)
    (hext : ∀ b ∈ f.blocks, ∀ st ∈ b.body, ∀ fn args, st.inst = .call fn args →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (htry : ∀ b ∈ f.blocks, ∀ fn args et, b.term = .tryCall fn args et →
      ∀ e, f.extern? fn = some e → p.func? e.name = none)
    (hcra : ∀ e ∈ f.externs, e.2.sig.params.length ≤ 8)
    (habi : sigAbiOk f.sig = true ∧ ∀ e ∈ f.externs, sigAbiOk e.2.sig = true)
    (hci : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ sig callee args, st.inst ≠ .callIndirect sig callee args)
    (htci : ∀ B ∈ f.blocks, ∀ callee args et, B.term ≠ .tryCallIndirect callee args et) :
    InSubset p f :=
  ⟨hfunc, hE, hreg, hext, htry, hcra, habi, by rw [indSigs_eq_nil hci htci]; simp⟩

/-! ## The compiled code -/

/-- The backend's pipeline succeeded on `f` (`Backend.compileFileWith` with the regalloc2
allocator; `rf` is whatever the untrusted allocator returned and the checker accepted), and
M7's validators accepted the lowering (`lowerCheck`: the VCode is the recorded lowering of `f`
with an SSA availability certificate) and `prepare` (`prepCheck`). -/
structure Compiled (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheck f vc = true
  prepare : prepare vc = .ok vcp
  prepOk : prepCheck vc vcp = true
  check : checkAlloc vcp rf = .ok ()
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

/-! ## CLIF side: entry state and memory relation -/

/-- `cs` is an initial CLIF state of `f` on `args`: `Clif.initState` except that the stack
slot addresses (`cs.frame.slots`) and the memory are left free. CLIF does not specify slot
addresses; `Clif.run`'s bump allocator picks one choice (`clifEntry_initState`), the Arm frame
another, and the theorem is stated for the Arm frame's (`SlotsAt`). -/
structure ClifEntry (f : Clif.Function) (args : List Clif.Val) (cs : Clif.State) : Prop where
  callers : cs.callers = []
  func : cs.frame.func = f
  sig : args.map (·.ty) = f.sig.params.map (·.ty)
  entry : ∃ b, f.entry? = some b ∧ cs.frame.body = b.body ∧ cs.frame.term = b.term ∧
    b.params.map (·.2) = args.map (·.ty) ∧
    Clif.Regs.empty.setMany (b.params.map (·.1)) args = some cs.frame.regs
  slotIds : cs.frame.slots.map (·.1) = f.slots.map (·.1)

/-- CLIF memory ↔ Arm memory, same addresses: initialised bytes of live CLIF allocations are
the Arm bytes, every address of a live CLIF allocation is a 64-bit address outside the frame addresses `F` (the
allocator-private part of the frame: spill and save slots, fp/lr), and `symbol_value`
addresses are the link-time ones `syms`. -/
structure MemRel (F : BitVec 64 → Prop) (syms : String → Option Nat) (cm : Clif.Mem)
    (s : Arm.ArmState) : Prop where
  bytes : ∀ a b, cm.valid a 1 = true → cm.bytes a = some b → Arm.read_mem (BitVec.ofNat 64 a) s = b
  valid : ∀ a n, cm.valid a n = true → a + n ≤ 2 ^ 64 ∧ ∀ k < n, ¬ F (BitVec.ofNat 64 (a + k))
  symbols : cm.symbols = syms

/-- The relation parameters of the CLIF ↔ VCode relation: frame addresses `F`, link-time
symbol addresses `syms`, and `slotOff`: the explicit stack-slot region is at `sp + slotOff` of
the VCode world (M6: the allocated frame's `slotBase`). -/
structure Rel where
  F : BitVec 64 → Prop
  syms : String → Option Nat
  slotOff : Nat

/-- Address of the stack-slot region in world `w`. -/
def Rel.slotReg (Γ : Rel) (w : Arm.ArmState) : Nat := (spv w).toNat + Γ.slotOff

/-- The stack slots of an activation are at the frame's slot region. -/
def SlotRel (f : Clif.Function) (base : Nat) (slots : List (Clif.SlotId × Nat)) : Prop :=
  ∀ id b, slots.lookup id = some b →
    ∃ off, (slotLayout f.slots).1.lookup id = some off ∧ b = base + off

/-- The CLIF memory/slots ↔ VCode world relation M4's rule statements are relative to. -/
def Rel.holds (Γ : Rel) (f : Clif.Function) (slots : List (Clif.SlotId × Nat)) (cm : Clif.Mem)
    (w : Arm.ArmState) : Prop :=
  MemRel Γ.F Γ.syms cm w ∧ SlotRel f (Γ.slotReg w) slots

/-- Live CLIF memory agrees with the Arm memory (the observable memory at return). -/
def MemAgree (cm : Clif.Mem) (s : Arm.ArmState) : Prop :=
  ∀ a b, cm.valid a 1 = true → cm.bytes a = some b → Arm.read_mem (BitVec.ofNat 64 a) s = b

/-- The run premises: every trap of the CLIF run is explicit, a `trap` terminator or a division
(whose lowering checks and traps); memory-access traps (`heap_oob`) and traps inside externs are
excluded (the Arm model has no memory faults and callees are outside the theorem; for DSL
output this holds trivially, traps are unreachable, PLAN.md §3.2). And an indirect call of the
entered function calls an extern: no function of `p` is at its callee address (calls between
the program's functions are outside the theorem, as for `call`: `InSubset.externCalls`). -/
structure TrapsExplicit (env : Clif.Env) (p : Clif.Program) (cs : Clif.State) : Prop where
  /-- a statement traps only if it is an explicitly trapping instruction -/
  stmt : ∀ s c st rest, Reach env p cs s → Clif.step env p s = .trapped c →
    s.frame.body = st :: rest → explicitTrapInst st.inst = true
  /-- the callee of a `try_call` terminator of the entered function does not trap (its step
  continues at the normal return; `Clif.run` has no unwinding) -/
  tryCall : ∀ s c fn args et, Reach env p cs s → Clif.step env p s = .trapped c →
    s.frame.body = [] → s.frame.term = .tryCall fn args et →
    ∀ B ∈ cs.frame.func.blocks, B.term ≠ .tryCall fn args et
  /-- the same for a `try_call_indirect` terminator -/
  tryCallInd : ∀ s c callee args et, Reach env p cs s → Clif.step env p s = .trapped c →
    s.frame.body = [] → s.frame.term = .tryCallIndirect callee args et →
    ∀ B ∈ cs.frame.func.blocks, B.term ≠ .tryCallIndirect callee args et
  /-- a `call_indirect` statement of the entered function calls an extern: no function of `p`
  is at the callee address (`Clif.stepCallIndirect` would enter it) -/
  indirect : ∀ s st rest sig callee args, Reach env p cs s → s.frame.body = st :: rest →
    st.inst = .callIndirect sig callee args → (∃ B ∈ cs.frame.func.blocks, st ∈ B.body) → ∀ cv,
    s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat
  /-- the same for a `try_call_indirect` terminator of the entered function -/
  tryIndirect : ∀ s callee args et, Reach env p cs s → s.frame.body = [] →
    s.frame.term = .tryCallIndirect callee args et →
    (∃ B ∈ cs.frame.func.blocks, B.term = .tryCallIndirect callee args et) → ∀ cv,
    s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat

/-- **Specialisation**: for an entered function without indirect calls (no `call_indirect`
statement, no `try_call_indirect` terminator), `TrapsExplicit` is its former two clauses (the
statement and `try_call` trap clauses); the indirect-call clauses are vacuous. -/
theorem TrapsExplicit.of_indirectFree {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    (hci : ∀ B ∈ cs.frame.func.blocks, ∀ st ∈ B.body, ∀ sig callee args,
      st.inst ≠ .callIndirect sig callee args)
    (htci : ∀ B ∈ cs.frame.func.blocks, ∀ callee args et, B.term ≠ .tryCallIndirect callee args et)
    (h : ∀ s c st rest, Reach env p cs s → Clif.step env p s = .trapped c →
      s.frame.body = st :: rest → explicitTrapInst st.inst = true)
    (ht : ∀ s c fn args et, Reach env p cs s → Clif.step env p s = .trapped c →
      s.frame.body = [] → s.frame.term = .tryCall fn args et →
      ∀ B ∈ cs.frame.func.blocks, B.term ≠ .tryCall fn args et) :
    TrapsExplicit env p cs :=
  ⟨h, ht, fun _ _ callee args et _ _ _ _ B hB e => htci B hB callee args et e,
    fun _ st _ sig callee args _ _ hi ⟨B, hB, hst⟩ => absurd hi (hci B hB st hst sig callee args),
    fun _ callee args et _ _ _ ⟨B, hB, e⟩ => absurd e (htci B hB callee args et)⟩

/-- For an entered function without `try_call`/`try_call_indirect` terminators and without
`call_indirect` statements, `TrapsExplicit` is its statement clause. -/
theorem TrapsExplicit.of_tryFree {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    (hf : ∀ B ∈ cs.frame.func.blocks, B.term.isTry = false)
    (hci : ∀ B ∈ cs.frame.func.blocks, ∀ st ∈ B.body, ∀ sig callee args,
      st.inst ≠ .callIndirect sig callee args)
    (h : ∀ s c st rest, Reach env p cs s → Clif.step env p s = .trapped c →
      s.frame.body = st :: rest → explicitTrapInst st.inst = true) :
    TrapsExplicit env p cs :=
  .of_indirectFree hci (fun B hB callee args et e => by have := hf B hB; rw [e] at this; cases this)
    h (fun _ _ fn args et _ _ _ _ B hB e => by have := hf B hB; rw [e] at this; cases this)

/-! ## Arm side: entry, return, trap -/

/-- `n` steps of the Arm machine `astep` (M6's `ArmStepX ext`: `stepi`, except that calls and
relocated address computations run the external hooks). -/
def runX (astep : Arm.ArmState → Arm.ArmState) : Nat → Arm.ArmState → Arm.ArmState
  | 0, s => s
  | n + 1, s => runX astep n (astep s)

/-- `a` is a byte of a code word of the program loaded in `s`. -/
def CodeAddr (s : Arm.ArmState) (a : BitVec 64) : Prop :=
  ∃ p : BitVec 64 × BitVec 32, List.Mem p s.program ∧ (a - p.1).toNat < 4

/-- ABI (AAPCS64) entry: the function's words are loaded at `base` (as the model's program and
as data in memory: jump tables are read from the code), pc at the entry, return address `ra` in
x30 outside the code, sp 16-aligned, no model error. -/
structure AbiEntry (fb : FnBin) (base ra : BitVec 64) (s : Arm.ArmState) : Prop where
  program : s.program = fb.program base
  code : ∀ k w, fb.words[k]? = some w → Arm.read_mem_bytes 4 (base + BitVec.ofNat 64 (4 * k)) s = w
  pc : Arm.r .PC s = base
  err : Arm.r .ERR s = .None
  lr : xreg 30 s = ra
  raOutside : ∀ k < fb.words.size, ra ≠ base + BitVec.ofNat 64 (4 * k)
  spAligned : (spv s).toNat % 16 = 0
  fits : base.toNat + 4 * fb.words.size ≤ 2 ^ 64

/-- The arguments in their AAPCS64 registers (register parameters only, `InSubset.regParams`):
parameter `i` of signature `sig` in `x (argIdx sig i)` — x0.. in order, an `sret` struct-return
pointer in x8 (`sigArgLocs`). Without an `sret` parameter, argument `i` is in `x i`. -/
def ArgsIn (sig : Clif.Signature) (args : List Clif.Val) (s : Arm.ArmState) : Prop :=
  ∀ i v, args[i]? = some v → XHolds v (xreg (argIdx sig i) s)

/-- For a signature without `sret` parameter, `ArgsIn` is "argument `i` in `x i`". -/
theorem argsIn_iff_of_noSret {sig : Clif.Signature} {args : List Clif.Val} {s : Arm.ArmState}
    (h : sig.params.any (·.purpose == .sret) = false) :
    ArgsIn sig args s ↔ ∀ i v, args[i]? = some v → XHolds v (xreg i s) := by
  simp only [ArgsIn, argIdx_of_noSret h]

/-- **Resource precondition**: the frame (fp/lr pair and `frameSize` bytes) fits below sp
without wrapping, and does not overlap the code. Stack used by callees is part of the callee
contract. -/
def StackAvail (af : AFunc) (s : Arm.ArmState) : Prop :=
  af.frameSize + 16 ≤ (spv s).toNat ∧
    ∀ a, CodeAddr s a →
      af.frameSize + 16 ≤ (a - (spv s - BitVec.ofNat 64 (af.frameSize + 16))).toNat

/-- The state the function body starts in, relative to the ABI entry state `s`: the prologue
(when `af.frame`) pushed fp/lr and set up the frame: `sp` lowered by `16 + frameSize`, `x29` the
frame pointer `sp_entry - 16`; x0–x8 and v0–v7 (arguments; x8 is preserved by the
prologue — for `sret` functions it carries the hidden struct-return pointer), memory, the program and every field outside
the allocatable/temporary registers (x18, x30, flags, …) as at entry. -/
def frameDrop (af : AFunc) : Nat := if af.frame then af.frameSize + 16 else 0

structure BodyEntry (af : AFunc) (s w₀ : Arm.ArmState) : Prop where
  sp : spv w₀ = spv s - BitVec.ofNat 64 (frameDrop af)
  fp : xreg 29 w₀ = if af.frame then spv s - 16#64 else xreg 29 s
  args : ∀ i < 9, xreg i w₀ = xreg i s
  argsV : ∀ i < 8, Arm.r (.SFP (BitVec.ofNat 5 i)) w₀ = Arm.r (.SFP (BitVec.ofNat 5 i)) s
  other : ∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f w₀ = Arm.r f s
  mem : w₀.mem = s.mem
  program : w₀.program = s.program

/-- Callee-saved X registers (AAPCS64: x19–x28, and the frame pointer x29). -/
def calleeSavedX : List Nat := (List.range 11).map (19 + ·)

/-- An AAPCS64 return from the activation entered in `s`: at the return address, sp and the
callee-saved registers (x19–x29, low 64 bits of v8–v15) as at entry. -/
structure ArmRet (ra : BitVec 64) (s s' : Arm.ArmState) : Prop where
  pc : Arm.r .PC s' = ra
  err : Arm.r .ERR s' = .None
  sp : spv s' = spv s
  savedX : ∀ n ∈ calleeSavedX, xreg n s' = xreg n s
  savedV : ∀ n, 8 ≤ n → n < 16 →
    (Arm.r (.SFP (BitVec.ofNat 5 n)) s').setWidth 64 = (Arm.r (.SFP (BitVec.ofNat 5 n)) s).setWidth 64

/-- The Arm run stopped at a trap site of the function with code `c`: the word there is a
`udf` (the model's next step errors) or a trapping access whose fault the OS reports (trusted). -/
structure TrapAt (fb : FnBin) (base : BitVec 64) (c : Clif.TrapCode) (s : Arm.ArmState) : Prop where
  err : Arm.r .ERR s = .None
  site : ∃ t ∈ fb.traps, t.code = c ∧ Arm.r .PC s = base + BitVec.ofNat 64 t.offset

/-! ## VCode observables -/

/-- The VCode run from the entry executes `rets us` (use values `vals`), final world `w`. -/
def VReturns (vc : VCode) (sem : Sem) (ρ₀ : Nat → CV) (w₀ : Arm.ArmState)
    (us : List (Reg × Reg)) (vals : List CV) (w : Arm.ArmState) : Prop :=
  VRetFrom vc sem ⟨0, 0, ρ₀, w₀⟩ us vals w

/-- The VCode run from the entry reaches an instruction that halts with trap code `c`. -/
def VTraps (vc : VCode) (sem : Sem) (ρ₀ : Nat → CV) (w₀ : Arm.ArmState) (c : Clif.TrapCode) :
    Prop :=
  VTrapFrom vc sem ⟨0, 0, ρ₀, w₀⟩ c

/-! ## The layer statements -/

/-- **CLIF → VCode (M7 driver).** The VCode of `f` simulates complete CLIF runs of `f` (entered
at an entry state whose slots/memory are related to the VCode entry world `w₀`). -/
def IselSim (sem : Sem) (Γ : Rel) (env : Clif.Env) (p : Clif.Program) (f : Clif.Function)
    (vc : VCode) : Prop :=
  ∀ args cs w₀ (ρ₀ : Nat → CV), ClifEntry f args cs → Γ.holds f cs.frame.slots cs.mem w₀ →
    ArgsIn f.sig args w₀ → TrapsExplicit env p cs → ∀ fuel,
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VReturns vc sem ρ₀ w₀ us outs w ∧
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel Γ.F Γ.syms cm w) ∧
    (∀ c, Clif.runLoop env p fuel cs = .trapped c → VTraps vc sem ρ₀ w₀ c)

/-- **`prepare` (M7).** Unreachable-block removal, critical-edge splitting and the RPO
reordering preserve returns and traps. Discharged by `prepCheck` (`prepareCorrect_of_check`). -/
def PrepareCorrect (sem : Sem) (vc vcp : VCode) : Prop :=
  ∀ ρ₀ w₀, (∀ us vals w, VReturns vc sem ρ₀ w₀ us vals w → VReturns vcp sem ρ₀ w₀ us vals w) ∧
    (∀ c, VTraps vc sem ρ₀ w₀ c → VTraps vcp sem ρ₀ w₀ c)

/-- **VCode → Arm (M6 + M5, agent M6Rest).** For the prepared VCode `vcp`, allocated and laid
out as `af`/`fb`, loaded at `base`, from an ABI entry state `s` with enough stack: VCode runs of
the activation's semantics `sem s` from a body-entry world `w₀` (`BodyEntry`: after the
prologue) are realised by the Arm machine `astep` from `s`. `F s` is the frame-address set of
the activation entered in `s` (allocator-private slots, fp/lr). -/
def RegLevelCorrect (sem : Arm.ArmState → Sem) (F : Arm.ArmState → BitVec 64 → Prop)
    (astep : Arm.ArmState → Arm.ArmState) (vcp : VCode) (af : AFunc) (fb : FnBin) : Prop :=
  ∀ base ra s, AbiEntry fb base ra s → StackAvail af s → ∀ w₀, BodyEntry af s w₀ →
    ∀ ρ₀ : Nat → CV,
    (∀ us vals w, VReturns vcp (sem s) ρ₀ w₀ us vals w →
      ∃ n, ArmRet ra s (runX astep n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x → regVal (runX astep n s) p = x) ∧
        ∀ a, ¬ F s a → (runX astep n s).mem a = w.mem a) ∧
    (∀ c, VTraps vcp (sem s) ρ₀ w₀ c → ∃ n, TrapAt fb base c (runX astep n s))

/-- **M7's lowering obligations**: the VCode has the structure `lowerFunction` builds
(`LowerShape`, incl. `CtxInv`), and an SSA availability certificate exists (`Cert`).
Discharged by `lowerCheck` (`loweringObligations_of_check`). -/
def LoweringObligations (f : Clif.Function) (vc : VCode) : Prop :=
  ∃ ctx st0 R gn bl A, LowerShape f vc ctx st0 R gn bl ∧ Cert f ctx st0 gn bl A ∧
    ∀ B ∈ f.blocks, BrIdxTyped ctx B.term

/-! ## The theorem's conclusion -/

/-- What the Arm run does for a CLIF outcome (`stuck`/`outOfFuel`: no claim). -/
def ArmRefines (fb : FnBin) (base ra : BitVec 64) (astep : Arm.ArmState → Arm.ArmState)
    (s : Arm.ArmState) : Clif.Outcome → Prop
  | .returned vals cm => ∃ n, ArmRet ra s (runX astep n s) ∧
      (∀ (j : Nat) v, vals[j]? = some v → XHolds v (xreg j (runX astep n s))) ∧
      MemAgree cm (runX astep n s)
  | .trapped c => ∃ n, TrapAt fb base c (runX astep n s)
  | .stuck _ | .outOfFuel => True

end E2E
