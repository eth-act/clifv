import FV.E2E.SretCopyHeapBoundary
import FV.E2E.Elf

namespace E2E.SretExecBoundary
open Backend Backend.Proof Backend.Proof.Driver E2E.SretHeapBoundary
set_option autoImplicit false
set_option Elab.async false

/-- Finite segment bounds imply a bound for every byte supplied by the actual ELF loader. -/
theorem loaded_bound {file : ByteArray} {segments : List Elf.Phdr} {limit : Nat}
    (headers : Elf.phdrs (Elf.fileRd file) = some segments)
    (bounds : ∀ segment ∈ segments,segment.type = 1 → segment.vaddr+segment.memsz ≤ limit)
    {a : BitVec 64} {byte : BitVec 8} (loaded : Elf.loadMem file a = some byte) : a.toNat < limit := by
  simp only [Elf.loadMem,headers,Option.bind_some] at loaded
  unfold Elf.loadIn at loaded
  cases selected : Elf.segIn segments a.toNat with
  | none => rw [selected] at loaded; cases loaded
  | some segment =>
    have member := List.mem_of_find?_eq_some selected
    have inside := List.find?_some selected
    simp only [Elf.isLoad,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at inside
    have upper := bounds segment member inside.1.1
    exact Nat.lt_of_lt_of_le inside.2 upper

/-- The two source heap regions are outside a compact executable image. -/
theorem heap_unmapped {file : ByteArray} {segments : List Elf.Phdr}
    (headers : Elf.phdrs (Elf.fileRd file) = some segments)
    (bounds : ∀ segment ∈ segments,segment.type = 1 → segment.vaddr+segment.memsz ≤ 0x300000)
    {a : BitVec 64} (above : 0x400000 ≤ a.toNat) : Elf.loadMem file a = none := by
  cases loaded : Elf.loadMem file a with
  | none => rfl
  | some byte => have := loaded_bound headers bounds loaded; omega

theorem r_world (contents : Nat → BitVec 8) (initial : Arm.ArmState) (field : Arm.StateField) :
    Arm.r field (world contents initial) = Arm.r field initial := by
  cases field <;> simp [Arm.r,world,Arm.read_base_gpr,Arm.read_base_sfp,Arm.read_base_pc,Arm.read_base_flag,Arm.read_base_error]

def machine (contents : Nat → BitVec 8) (base : BitVec 64)
    (memory : BitVec 64 → BitVec 8) : Arm.ArmState :=
  Caller.machine contents (Arm.w .PC base (Arm.w (.GPR 31#5) 0x1000000#64
    (Arm.w (.GPR 30#5) 0x8000000#64 {Arm.ArmState.default with mem := memory})))

theorem pc (contents : Nat → BitVec 8) (base : BitVec 64) (memory : BitVec 64 → BitVec 8) :
    Arm.r .PC (machine contents base memory) = base := by
  simp [machine,Caller.machine,r_world,Arm.r_of_w_same,Arm.r_of_w_different]

theorem stack_pointer (contents : Nat → BitVec 8) (base : BitVec 64) (memory : BitVec 64 → BitVec 8) :
    spv (machine contents base memory) = 0x1000000#64 := by
  simp [spv,machine,Caller.machine,r_world,Arm.r_of_w_same,Arm.r_of_w_different]

theorem return_address (contents : Nat → BitVec 8) (base : BitVec 64) (memory : BitVec 64 → BitVec 8) :
    xreg 30 (machine contents base memory) = 0x8000000#64 := by
  simp [xreg,machine,Caller.machine,r_world,Arm.r_of_w_same,Arm.r_of_w_different]

theorem no_error (contents : Nat → BitVec 8) (base : BitVec 64) (memory : BitVec 64 → BitVec 8) :
    Arm.r .ERR (machine contents base memory) = .None := by
  have unchanged : Arm.r .ERR (machine contents base memory) =
      Arm.r .ERR {Arm.ArmState.default with mem := memory} := by
    simp [machine,Caller.machine,r_world,Arm.r_of_w_different]
  rw [unchanged]
  simp [Arm.r,Arm.read_base_error,Arm.ArmState.default]

theorem memory_relation (contents : Nat → BitVec 8) (base : BitVec 64)
    (memory : BitVec 64 → BitVec 8) (syms : String → Option Nat) :
    MemRel reserved syms (heap contents syms) (machine contents base memory) :=
  Caller.machine_memory_relation contents syms _

theorem reserved_bytes (contents : Nat → BitVec 8) (base : BitVec 64)
    (memory : BitVec 64 → BitVec 8) {a : BitVec 64} (outside : reserved a) :
    (machine contents base memory).mem a = memory a := by
  simpa only [machine,Caller.machine,Arm.ArmState.mem_w_eq_mem] using
    protected_bytes contents (Arm.w .PC base (Arm.w (.GPR 31#5) 0x1000000#64
      (Arm.w (.GPR 30#5) 0x8000000#64 {Arm.ArmState.default with mem := memory}))) outside


theorem entry_arguments (contents : Nat → BitVec 8) (base : BitVec 64)
    (memory : BitVec 64 → BitVec 8) :
    ArgsAtEntry reserved Caller.signature arguments (machine contents base memory) :=
  Caller.entry_arguments contents _

/-- Adding arbitrary source bytes leaves every originally loaded ELF byte exact. -/
theorem loaded_bytes {file : ByteArray} {segments : List Elf.Phdr}
    (headers : Elf.phdrs (Elf.fileRd file) = some segments)
    (bounds : ∀ segment ∈ segments,segment.type = 1 → segment.vaddr+segment.memsz ≤ 0x300000)
    (contents : Nat → BitVec 8) (base : BitVec 64) {a : BitVec 64} {byte : BitVec 8}
    (loaded : Elf.loadMem file a = some byte) :
    (machine contents base (fun address => (Elf.loadMem file address).getD 0)).mem a = byte := by
  have outside : reserved a := Or.inl (loaded_bound headers bounds loaded)
  rw [reserved_bytes contents base _ outside]
  rw [loaded]
  rfl

end E2E.SretExecBoundary


