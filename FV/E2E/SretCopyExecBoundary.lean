import FV.E2E.SretCopyExecEntry
import FV.E2E.SemanticBinary

namespace E2E.SretExecBoundary
open Backend Backend.Proof Backend.Proof.Driver E2E.SemanticBinary E2E.SretHeapBoundary
set_option autoImplicit false
set_option Elab.async false

theorem arguments_out (contents : Nat → BitVec 8) (base : BitVec 64)
    (memory : BitVec 64 → BitVec 8) (image : BitVec 64 → Prop) :
    ArgsOut image Caller.signature arguments (machine contents base memory) := by
  intro loc value member
  change (loc,value) ∈ [(ArgLoc.reg (.x 0),⟨.i64,0x400000#64⟩),
    (ArgLoc.reg (.x 1),⟨.i64,0x500000#64⟩)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal
  all_goals cases equal
  all_goals simp [machine,Caller.machine,regVal,rnum,VHolds,Clif.Ty.width,Arm.r_of_w_same,Arm.r_of_w_different]

theorem stack_reserved (contents : Nat → BitVec 8) (base : BitVec 64)
    (memory : BitVec 64 → BitVec 8) {N : Nat} (budget : N ≤ 4096) {a : BitVec 64}
    (below : StackBelow N (spv (machine contents base memory)) a) : reserved a := by
  rw [stack_pointer] at below
  change a.toNat < 0x1000000 ∧ 0x1000000 ≤ a.toNat+N at below
  right
  omega

/-- The symbolic heap supplies the existing executable entry contract, including its live bytes. -/
theorem outside_call {I : SemanticStackBound.CompilerInput} {f : Clif.Function} {N : Nat}
    {readOnly : BitVec 64 → Option (BitVec 8)}
    (signature : f.sig = Caller.signature) (budget : N ≤ 4096)
    (imageBound : ∀ a,img I a → a.toNat < 0x300000)
    (readOnlyFree : ∀ a,0x400000 ≤ a.toNat ∧ a.toNat < 0x500010 → readOnly a = none)
    (contents : Nat → BitVec 8) (memory : BitVec 64 → BitVec 8) :
    OutsideCall I readOnly f N (machine contents (art I f).base memory) arguments
      (heap contents (fun name => I.syms.lookup name)) where
  pc := pc contents _ memory
  err := no_error contents _ memory
  ra := by
    intro code
    have bound := imageBound _ code
    rw [return_address] at bound
    change 0x8000000 < 0x300000 at bound
    omega
  spAligned := by rw [stack_pointer]; decide
  stack := by rw [stack_pointer]; change N ≤ 0x1000000; omega
  stackFree := by
    intro a code below
    have low := imageBound a code
    rw [stack_pointer] at below
    change a.toNat < 0x1000000 ∧ 0x1000000 ≤ a.toNat+N at below
    omega
  args := by rw [signature]; exact arguments_out contents _ memory _
  bytes := by
    intro a value valid initialized
    -- the heap lies far below the stack probes (#581: at most three probes below `sp - 16`)
    have bounds := valid_bounds contents (fun name => I.syms.lookup name) valid
    have small : a < 2^64 := by rcases bounds with bounds | bounds <;> omega
    have range : a < 0x500010 := by rcases bounds with bounds | bounds <;> omega
    have hsp : (spv (machine contents (art I f).base memory)).toNat = 0x1000000 := by
      rw [stack_pointer]; rfl
    have hc := probeCount_le_three (probeTotal (art I f).af.frameSize (art I f).af.isCaller)
    rw [probeMem_of_not]
    · exact (memory_relation contents (art I f).base memory _).bytes a value valid initialized
    · cases hp : probeHit (art I f).af (spv (machine contents (art I f).base memory)) (BitVec.ofNat 64 a) with
      | false => rfl
      | true =>
        obtain ⟨-, i, hi, k, hk, e⟩ := probeHit_toNat hp (by rw [hsp]; omega)
        rw [hsp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at e
        omega
  image := by
    intro a value other valid initialized placed
    have bounds := valid_bounds contents (fun name => I.syms.lookup name) valid
    have small : a < 2^64 := by rcases bounds with bounds | bounds <;> omega
    have range : 0x400000 ≤ a ∧ a < 0x500010 := by rcases bounds with bounds | bounds <;> omega
    have excluded := readOnlyFree (BitVec.ofNat 64 a)
      (by simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] using range)
    rw [excluded] at placed
    cases placed
  valid := by
    intro a n valid
    have related := (memory_relation contents (art I f).base memory _).valid a n valid
    refine ⟨related.1,?_⟩
    intro k below
    refine ⟨?_,?_⟩
    · intro code
      exact (related.2 k below) (Or.inl (imageBound _ code))
    · intro onStack
      exact False.elim ((related.2 k below) (stack_reserved contents (art I f).base memory budget onStack))
  symbols := rfl

/-- Slot-free original functions need no supplied placement oracle. -/
theorem clif_run (I : SemanticStackBound.CompilerInput) (B : LinkCheck.BaseEnv)
    (noSlots : ∀ f ∈ (prog I).funcs,f.slots = [])
    (contents : Nat → BitVec 8) (memory : BitVec 64 → BitVec 8) :
    ClifRun I B Caller.function (machine contents (art I Caller.function).base memory) arguments
      (entryState Caller.function Caller.first (heap contents (fun name => I.syms.lookup name))) where
  entry := Caller.entry contents _
  slots := by intro id address found; cases found
  place := by
    rintro ⟨g,member,f,callee,slots⟩
    have present := LinkSys.callee_mem (sys I B) callee
    change f ∈ (prog I).funcs at present
    exact (slots (noSlots f present)).elim

/-- The original loader premise holds for all kept bytes of the actual file. -/
theorem image_intact {file : ByteArray} {segments : List Elf.Phdr}
    (headers : Elf.phdrs (Elf.fileRd file) = some segments)
    (bounds : ∀ segment ∈ segments,segment.type = 1 → segment.vaddr+segment.memsz ≤ 0x300000)
    (contents : Nat → BitVec 8) (base : BitVec 64) :
    (imageOf file).Intact (machine contents base (fun a => (Elf.loadMem file a).getD 0)) := by
  intro a byte _ loaded
  exact loaded_bytes headers bounds contents base loaded

end E2E.SretExecBoundary
