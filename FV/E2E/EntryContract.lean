import FV.E2E.DeadCleanupBinary

/-!
# The entry contract at the level of the written ELF (A5, #411)

`DeadCleanupBinary.OutsideCall` states the outside caller's contract partly in terms of the
compiled program (`img I`: "not code") and splits the caller's CLIF memory into the bytes outside
the read-only CLIF data (`bytes`) and those inside (`image`). Several of its fields follow from
facts about the written executable and a loader contract stated on the file:

* `stackFree` (no code in the free stack) and the stack arguments' "not code": the program's code
  is in read-only `PT_LOAD` segments of the file (`DeadCleanupBinCheck.img_bytes`), and the stack
  is writable memory, so it is in no read-only segment (`Loader.stackRw`, `ArgsRw`);
* `image` (the live CLIF bytes at the read-only CLIF data are the image's): the file holds the
  read-only CLIF data objects in read-only or RELRO segments (`BinCheck.roByte_sound`), the loader
  keeps those bytes (`Image.Intact`), and the caller's CLIF memory agrees with the machine on every
  live byte (`ClifView.bytes`, one uniform agreement replacing `bytes` and `image`).

The contract is split by who guarantees what:

* `Loader file N r` — the OS loader and runtime: the kept bytes (`Image.Intact`), `N` bytes of
  stack below `sp`, writable (in no read-only segment of `file`);
* `Caller I file f r args` — the outside caller (AAPCS64): `pc` at `f`'s link-map address, no
  model error, the return address outside the program's code, `sp` 16-aligned, the arguments where
  AAPCS64 puts them (stack arguments in writable memory);
* `ClifView I B f N r args cs` — **not an obligation**: the choice of the CLIF state `cs` that
  models `r` (its live bytes are `r`'s, its allocations hold no code and lie in the free stack only
  in `f`'s slot region, its symbol table is the link map, and the reference run `ClifRun`).

`outsideCall_of` derives `OutsideCall I (BinCheck.roByte I D) f N r args cs.mem` from them and the
checks (`okBCleanup`, `DeadCleanupBinCheck.BinOk`). The executable theorems over this contract are
`Front.bundle_correct_raw_contract{,_peak}` (`FV/Front/RawExeContract.lean`).
-/

namespace E2E.EntryContract
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary

/-- **The loader's contract** for the executable `file` in the machine state `r` (TO-PROVE §1.3,
the OS loader and runtime): the machine holds the file's read-only and RELRO bytes
(`Image.Intact`); `N` bytes of stack lie below `sp` without wrapping, and they are writable memory:
in no read-only `PT_LOAD` segment of the file (`Elf.ro`). -/
structure Loader (file : ByteArray) (N : Nat) (r : Arm.ArmState) : Prop where
  /-- the read-only segments and `PT_GNU_RELRO` hold the file's bytes -/
  intact : (imageOf file).Intact r
  /-- `N` bytes of stack below `sp` -/
  stack : N ≤ (spv r).toNat
  /-- the stack is writable: none of its bytes is in a read-only segment of the file -/
  stackRw : ∀ a, StackBelow N (spv r) a → ¬ Elf.ro file a

/-- The arguments `args` of a call with signature `sig` where AAPCS64 puts them in `r`: a register
parameter in its register, a stack parameter in the caller's outgoing area at `sp + off` (inside the
address space, in writable memory: in no read-only segment of `file`, holding its bits). -/
def ArgsRw (file : ByteArray) (sig : Clif.Signature) (args : List Clif.Val) (r : Arm.ArmState) :
    Prop :=
  ∀ loc v, (loc, v) ∈ (locsOf sig).zip args → match loc with
    | .reg x => VHolds v (regVal r x)
    | .stack off => (spv r).toNat + off + v.ty.bytes ≤ 2 ^ 64 ∧
        Avoids (Elf.ro file) v.ty.bytes (spv r + BitVec.ofNat 64 off) ∧
        (Arm.read_mem_bytes v.ty.bytes (spv r + BitVec.ofNat 64 off) r).setWidth v.ty.width = v.bits

/-- **The outside caller's contract** (AAPCS64; TO-PROVE §1.3, code outside the program) when it
calls the function `f` of the program in `r` with the arguments `args`. -/
structure Caller (I : LinkInput) (file : ByteArray) (f : Clif.Function) (r : Arm.ArmState)
    (args : List Clif.Val) : Prop where
  /-- the pc is `f`'s address (its link-map address) -/
  pc : Arm.r .PC r = (art I f).base
  /-- no model error -/
  err : Arm.r .ERR r = .None
  /-- the return address (x30) is outside the program's code: the caller is outside code -/
  ra : ¬ img I (xreg 30 r)
  /-- `sp` is 16-aligned -/
  spAligned : (spv r).toNat % 16 = 0
  /-- the arguments where AAPCS64 puts them (stack arguments in writable memory) -/
  args : ArgsRw file f.sig args r

/-- **The CLIF view of the machine state** (a choice, not an obligation of the outside code): the
CLIF state `cs` whose run the theorems are about agrees with `r` on every live byte after `f`'s
prologue stack probes (`probeMem`, #581: the body starts after them; `r`'s own bytes for a
function without probes), its live
allocations fit the address space, hold no code and lie in the free stack (`N` bytes) only in `f`'s
CLIF slot region, its symbol table is the CLIF image's (the link map, which `SymsOk` ties to the
file's symbols), and it is a reference entry state of `f` (`ClifRun`). -/
structure ClifView (I : LinkInput) (B : BaseEnv) (f : Clif.Function) (N : Nat) (r : Arm.ArmState)
    (args : List Clif.Val) (cs : Clif.State) : Prop where
  /-- the live CLIF bytes are the machine's after `f`'s stack probes -/
  bytes : ∀ a b, cs.mem.valid a 1 = true → cs.mem.bytes a = some b →
    probeMem (art I f).af r (BitVec.ofNat 64 a) = b
  /-- the live CLIF allocations fit the address space, hold no code, and lie in the free stack
  only in `f`'s CLIF slot region -/
  valid : ∀ a n, cs.mem.valid a n = true → a + n ≤ 2 ^ 64 ∧ ∀ k < n,
    ¬ img I (BitVec.ofNat 64 (a + k)) ∧
    (StackBelow N (spv r) (BitVec.ofNat 64 (a + k)) → SlotArea (art I f).af r (BitVec.ofNat 64 (a + k)))
  /-- the CLIF symbol table is the CLIF image's -/
  symbols : cs.mem.symbols = fun n => I.syms.lookup n
  /-- the reference CLIF run -/
  run : ClifRun I B f r args cs

/-- The program's code is in read-only segments of a checked file. -/
theorem ro_of_img {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okBCleanup I = true) (hbin : DeadCleanupBinCheck.BinOk I D file) {a : BitVec 64}
    (ha : img I a) : Elf.ro file a :=
  (DeadCleanupBinCheck.img_bytes hbin hI ha).1

/-- **`OutsideCall.stackFree` from the loader's contract**: the free stack is writable, the code
read-only. -/
theorem stackFree_of {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okBCleanup I = true) (hbin : DeadCleanupBinCheck.BinOk I D file) {N : Nat}
    {r : Arm.ArmState} (hl : Loader file N r) : ∀ a, img I a → ¬ StackBelow N (spv r) a :=
  fun a ha hb => hl.stackRw a hb (ro_of_img hI hbin ha)

/-- **`OutsideCall.args` from the caller's contract**: stack arguments in writable memory are not
code. -/
theorem argsOut_of {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okBCleanup I = true) (hbin : DeadCleanupBinCheck.BinOk I D file) {sig : Clif.Signature}
    {args : List Clif.Val} {r : Arm.ArmState} (h : ArgsRw file sig args r) :
    ArgsOut (img I) sig args r := by
  intro loc v hm
  have h' := h loc v hm
  cases loc with
  | reg x => exact h'
  | stack off =>
    obtain ⟨hfit, hav, hby⟩ := h'
    exact ⟨hfit, fun k hk hc => hav k hk (ro_of_img hI hbin hc), hby⟩

/-- **`OutsideCall.image` from the loader's contract**: a live CLIF byte at a read-only CLIF data
object is the machine's (`ClifView.bytes`), which is the file's (`Image.Intact`), which is the
object's (`BinCheck.roByte_sound`). -/
theorem image_of {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hbin : DeadCleanupBinCheck.BinOk I D file) {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    {f : Clif.Function} {cm : Clif.Mem}
    (hb : ∀ a b, cm.valid a 1 = true → cm.bytes a = some b →
      probeMem (art I f).af r (BitVec.ofNat 64 a) = b) :
    ∀ a b b', cm.valid a 1 = true → cm.bytes a = some b →
      BinCheck.roByte I D (BitVec.ofNat 64 a) = some b' →
      probeHit (art I f).af (spv r) (BitVec.ofNat 64 a) = false → b = b' := by
  intro a b b' hv hby hro hnp
  have hs := BinCheck.roByte_sound hbin.data hro
  have hm : r.mem (BitVec.ofNat 64 a) = b' := hX _ _ hs.2 hs.1
  rw [← hb a b hv hby, probeMem_of_not hnp, hm]

/-- **The boundary contract `OutsideCall` from the loader's and the caller's contracts** and the
CLIF view, for an input that passes the crate checker and a file that passes the binary checks. -/
theorem outsideCall_of {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okBCleanup I = true) (hbin : DeadCleanupBinCheck.BinOk I D file) {B : BaseEnv}
    {f : Clif.Function} {N : Nat} {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hl : Loader file N r) (hc : Caller I file f r args) (hv : ClifView I B f N r args cs) :
    OutsideCall I (BinCheck.roByte I D) f N r args cs.mem where
  pc := hc.pc
  err := hc.err
  ra := hc.ra
  spAligned := hc.spAligned
  stack := hl.stack
  stackFree := stackFree_of hI hbin hl
  args := argsOut_of hI hbin hc.args
  bytes := hv.bytes
  image := image_of hbin hl.intact hv.bytes
  valid := hv.valid
  symbols := hv.symbols

end E2E.EntryContract
