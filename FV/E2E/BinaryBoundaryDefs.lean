import FV.E2E.SemanticStackBound
import FV.E2E.ProductionCheck
import FV.E2E.ProductionChecksWith

/-! # The binary-level theorem (M9, docs/contracts/e2e.md, "Binary level (M9)")

`crate_correct` (`FV/E2E/LinkCheck.lean`) is `backend_correct_program` for every function of a
crate's linked program, with the per-run premises of an Arm entry state `s`, a body-entry world
`w₀` and a CLIF entry state `cs`. Here those premises are stated as a **boundary contract** on
the real machine state `r` in which code outside the program (std's `lang_start`, a fallback
function, a callback) enters a function `f` of the program:

* `OutsideCall I roB f N r args cm` — what the outside caller guarantees at the call: the AAPCS64
  entry (pc at `f`'s link address, return address outside the program's code, `sp` 16-aligned),
  `N` bytes of free stack below `sp` that hold no code, the arguments where AAPCS64 puts them,
  and the CLIF-visible memory `cm` related to `r` (its live bytes are `r`'s, none of them in the
  code or in the free stack except `f`'s own CLIF slot region, the symbol table the CLIF image's).
* `ClifRun I B f r args cs` — the choice of the reference CLIF run (not an obligation on the
  outside code): `cs` is an entry state of `f` on `args`, its stack slots where the compiled frame
  puts them, and (with slotted program callees) the slot-placement oracle at the body's `sp`.
  CLIF leaves slot addresses unspecified; this picks the run the compiled code realises.
* the model state `modelOf I f r`: `r` with the machine's program `f`'s compiled words and the
  memory at the program's code addresses the compiled image (`LinkSys.withImg`). The compiled
  image holds relocated instructions with zero relocation fields, which the model machine runs by
  their link-map semantics (`ArmStepX`); the binary checks (`FV/E2E/BinCheck.lean`) show the
  executable differs from it only there, holding the resolved encodings.

Every other premise of `backend_correct_program` is discharged here: `AbiEntry` (program, code
words, pc, error, return address, alignment, fits), the stack premises (`StackAvail`, the world
complement `F`, the code outside the stack, `hgfree`), `himg`, `BodyEntry` (the body-entry world
is `bodyOf af s`), `ArgsIn` and `StackArgsAvoid` (from `OutsideCall.args` on `r`), and
`Rel.holds`' memory part, `OutRel` (the outgoing area is free stack). `TrapsExplicit` (the CLIF
run traps only explicitly) stays a premise about the CLIF run; `BaseOk` (the contracts of the code
outside the program) stays as in `crate_correct`.

`binary_correct_depth` uses `crate_correct` (a stack of `frameDrop + D * M` bytes for runs of
depth `M`: the statement for recursive programs); `binary_correct` uses the stack bound of a
non-recursive program (`FV/E2E/SemanticStackBound.lean`) and the executable's checks.
-/

set_option autoImplicit false
namespace E2E.SemanticBinary

open Backend Backend.Proof E2E.LinkCheck

/-! ## The compiled program of an input -/

/-- The program of the input (`SemanticStackBound.ofInput`'s `P`). -/
abbrev prog (I : SemanticStackBound.CompilerInput) : Clif.Program := progOf I.results

/-- The compiled image of `f` (`SemanticStackBound.ofInput`'s `A f`). -/
abbrev art (I : SemanticStackBound.CompilerInput) (f : Clif.Function) : Art := artOf I.results f

/-- The program's code addresses (`SemanticStackBound.ofInput`'s `Img`). -/
abbrev img (I : SemanticStackBound.CompilerInput) : BitVec 64 → Prop := ImgT (tabOf I.results)

/-- The program's compiled code bytes (`SemanticStackBound.ofInput`'s `imgMem`). -/
abbrev imgMem (I : SemanticStackBound.CompilerInput) : Arm.Memory := memT (tabOf I.results)

/-- The linked system with no addresses outside the world (`F` only enters premises; `mach`,
`NeedSlots`, `PlaceAt`, `base`, `P` do not depend on it). -/
abbrev sys (I : SemanticStackBound.CompilerInput) (B : BaseEnv) : LinkSys := SemanticStackBound.ofInput I B fun _ => False

/-- The body's stack pointer of an activation of a function with frame `af` entered in `r`. -/
def spBody (af : AFunc) (r : Arm.ArmState) : BitVec 64 := spv r - BitVec.ofNat 64 (frameDrop af)

/-- `a` is in the CLIF stack-slot region of the frame of `af` entered in `r`
(`[sp_body + slotBase, sp_body + frameSize − clobberBytes)`: the slots lie below Cranelift's
clobber area, #479). -/
def SlotArea (af : AFunc) (r : Arm.ArmState) (a : BitVec 64) : Prop :=
  af.slotBase ≤ (a - spBody af r).toNat ∧
    (a - spBody af r).toNat < af.frameSize - clobberBytes af.saves

/-- The arguments `args` of a call with signature `sig` where AAPCS64 puts them in `r`: a
register parameter in its register, a stack parameter in the caller's outgoing area at
`sp + off` (inside the address space, outside the code `G`, holding its bits). -/
def ArgsOut (G : BitVec 64 → Prop) (sig : Clif.Signature) (args : List Clif.Val)
    (r : Arm.ArmState) : Prop :=
  ∀ loc v, (loc, v) ∈ (locsOf sig).zip args → match loc with
    | .reg x => VHolds v (regVal r x)
    | .stack off => (spv r).toNat + off + v.ty.bytes ≤ 2 ^ 64 ∧
        Avoids G v.ty.bytes (spv r + BitVec.ofNat 64 off) ∧
        (Arm.read_mem_bytes v.ty.bytes (spv r + BitVec.ofNat 64 off) r).setWidth v.ty.width = v.bits

/-- **The boundary contract**: what code outside the program guarantees when it calls the
function `f` of the program in the machine state `r`, with arguments `args`, its CLIF-visible
memory being `cm`, and `N` bytes of stack. `roB a = some b`: the executable holds the byte `b` of
the CLIF image's read-only data at `a` (`fun _ => none`: no data facts, every live CLIF byte is
required of the caller). -/
structure OutsideCall (I : SemanticStackBound.CompilerInput) (roB : BitVec 64 → Option (BitVec 8)) (f : Clif.Function)
    (N : Nat) (r : Arm.ArmState)
    (args : List Clif.Val) (cm : Clif.Mem) : Prop where
  /-- the pc is `f`'s address (its link-map address) -/
  pc : Arm.r .PC r = (art I f).base
  /-- no model error -/
  err : Arm.r .ERR r = .None
  /-- the return address (x30) is outside the program's code: the caller is outside code -/
  ra : ¬ img I (xreg 30 r)
  /-- AAPCS64: `sp` is 16-aligned -/
  spAligned : (spv r).toNat % 16 = 0
  /-- `N` bytes below `sp` without wrapping -/
  stack : N ≤ (spv r).toNat
  /-- none of them is code -/
  stackFree : ∀ a, img I a → ¬ StackBelow N (spv r) a
  /-- the arguments where AAPCS64 puts them (stack arguments outside the code) -/
  args : ArgsOut (img I) f.sig args r
  /-- the live CLIF bytes outside the executable's read-only CLIF data (`roB`) are the
  machine's -/
  bytes : ∀ a b, cm.valid a 1 = true → cm.bytes a = some b → roB (BitVec.ofNat 64 a) = none →
    Arm.read_mem (BitVec.ofNat 64 a) r = b
  /-- the live CLIF bytes at the read-only CLIF data are the CLIF image's (a CLIF-level fact: a
  store into read-only data is stuck) -/
  image : ∀ a b b', cm.valid a 1 = true → cm.bytes a = some b → roB (BitVec.ofNat 64 a) = some b' →
    b = b'
  /-- the live CLIF allocations fit the address space, hold no code, and lie in the free stack
  only in `f`'s CLIF slot region -/
  valid : ∀ a n, cm.valid a n = true → a + n ≤ 2 ^ 64 ∧ ∀ k < n,
    ¬ img I (BitVec.ofNat 64 (a + k)) ∧
    (StackBelow N (spv r) (BitVec.ofNat 64 (a + k)) → SlotArea (art I f).af r (BitVec.ofNat 64 (a + k)))
  /-- the CLIF symbol table is the CLIF image's -/
  symbols : cm.symbols = fun n => I.syms.lookup n

/-- **The reference CLIF run** of an outside call of `f` in `r` (a choice, not an obligation of
the outside code): an entry state of `f` on `args` whose stack slots are where the compiled frame
puts them, and whose slot-placement oracle (needed only with slotted program callees) is at the
body's `sp` with the program's compiled frames. -/
structure ClifRun (I : SemanticStackBound.CompilerInput) (B : BaseEnv) (f : Clif.Function) (r : Arm.ArmState)
    (args : List Clif.Val) (cs : Clif.State) : Prop where
  entry : ClifEntry f args cs
  slots : SlotRel f ((spBody (art I f).af r).toNat + (art I f).af.slotBase) cs.frame.slots
  place : (sys I B).NeedSlots → (sys I B).PlaceAt cs.mem (spBody (art I f).af r)

open Classical in
/-- **The model state** of the machine state `r` entering `f`: `r` with the machine's program
`f`'s compiled words and the compiled code bytes at the program's code addresses. -/
noncomputable def modelOf (I : SemanticStackBound.CompilerInput) (f : Clif.Function) (r : Arm.ArmState) : Arm.ArmState :=
  Arm.set_program (setMem r fun a => if img I a then imgMem I a else r.mem a)
    ((art I f).fb.program (art I f).base)

theorem r_modelOf (I : SemanticStackBound.CompilerInput) (f : Clif.Function) (r : Arm.ArmState) (fld : Arm.StateField) :
    Arm.r fld (modelOf I f r) = Arm.r fld r := by
  simp only [modelOf]
  rw [r_set_program, r_setMem]

theorem spv_modelOf (I : SemanticStackBound.CompilerInput) (f : Clif.Function) (r : Arm.ArmState) :
    spv (modelOf I f r) = spv r := r_modelOf I f r _

theorem regVal_modelOf (I : SemanticStackBound.CompilerInput) (f : Clif.Function) (r : Arm.ArmState) (x : Reg) :
    regVal (modelOf I f r) x = regVal r x := by
  cases x <;> simp only [regVal, r_modelOf]

open Classical in
theorem mem_modelOf (I : SemanticStackBound.CompilerInput) (f : Clif.Function) (r : Arm.ArmState) (a : BitVec 64) :
    (modelOf I f r).mem a = if img I a then imgMem I a else r.mem a := by
  simp only [modelOf, mem_set_program, mem_setMem]

theorem mem_modelOf_img {I : SemanticStackBound.CompilerInput} {f : Clif.Function} {r : Arm.ArmState} {a : BitVec 64}
    (h : img I a) : (modelOf I f r).mem a = imgMem I a := by
  rw [mem_modelOf]; simp [h]

theorem mem_modelOf_not {I : SemanticStackBound.CompilerInput} {f : Clif.Function} {r : Arm.ArmState} {a : BitVec 64}
    (h : ¬ img I a) : (modelOf I f r).mem a = r.mem a := by
  rw [mem_modelOf]; simp [h]

@[simp] theorem program_modelOf (I : SemanticStackBound.CompilerInput) (f : Clif.Function) (r : Arm.ArmState) :
    (modelOf I f r).program = (art I f).fb.program (art I f).base := by
  simp only [modelOf, program_set_program]

/-- The body-entry world `bodyOf af s` is a body entry of `s`. -/
theorem bodyEntry_bodyOf (af : AFunc) (s : Arm.ArmState) : BodyEntry af s (bodyOf af s) where
  sp := spv_bodyOf af s
  fp := x29_bodyOf af s
  args := fun i hi => r_bodyOf af s
    (fun e => by
      have := congrArg (fun f => match f with | Arm.StateField.GPR j => j.toNat | _ => 0) e
      simp at this; omega)
    (fun e => by
      have := congrArg (fun f => match f with | Arm.StateField.GPR j => j.toNat | _ => 0) e
      simp at this; omega)
  argsV := fun i _ => r_bodyOf af s (by simp) (by simp)
  other := fun _ _ h29 h31 => r_bodyOf af s h29 h31
  mem := mem_bodyOf af s
  program := program_bodyOf af s

/-- `BaseOk` does not depend on the addresses `F` outside the world. -/
theorem baseOk_F {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {F F' : BitVec 64 → Prop}
    (h : BaseOk (SemanticStackBound.ofInput I B F)) : BaseOk (SemanticStackBound.ofInput I B F') :=
  ⟨h.baseNoAlloc, h.keepSyms, h.aliasSyms, h.baseOs, h.basePc, h.baseExt, h.baseX, h.baseXI,
    h.baseTls, h.baseTry, h.baseNI, h.baseTlsNI, h.baseKeepsPlace, h.baseKeepsAllocs⟩

/-- **The addresses outside the entry activation's world** with callees' budget `K`
(`backend_correct_program`'s `hF`): the frame-private addresses, the callees' dead stack and the
program's code. -/
def worldF (I : SemanticStackBound.CompilerInput) (f : Clif.Function) (K : Nat) (r : Arm.ArmState) : BitVec 64 → Prop :=
  frameWG K (RAFrame.compute (art I f).vcp (art I f).rf).intBase
    (RAFrame.compute (art I f).vcp (art I f).rf).size (art I f).af (img I) (modelOf I f r)


end E2E.SemanticBinary
