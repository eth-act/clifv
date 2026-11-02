import FV.Backend.Proof.IselMemArm
import FV.E2E.Statement

namespace E2E.SretHeapBoundary
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The two original sixteen-byte regions lie between the image and the stack. -/
def reserved (a : BitVec 64) : Prop := a.toNat < 0x300000 ∨ 0xf00000 ≤ a.toNat

def heap (contents : Nat → BitVec 8) (syms : String → Option Nat) : Clif.Mem := {
  allocs := [{base := 0x400000,size := 16},{base := 0x500000,size := 16}]
  bytes := fun a => if 0x500000 ≤ a ∧ a < 0x500010 then some (contents (a-0x500000)) else none
  next := 0x600000
  symbols := syms }

def world (contents : Nat → BitVec 8) (initial : Arm.ArmState) : Arm.ArmState :=
  {initial with mem := fun a =>
    if 0x500000 ≤ a.toNat ∧ a.toNat < 0x500010 then contents (a.toNat-0x500000)
    else initial.mem a}

theorem valid_bounds (contents : Nat → BitVec 8) (syms : String → Option Nat) {a n : Nat}
    (valid : (heap contents syms).valid a n = true) :
    (0x400000 ≤ a ∧ a+n ≤ 0x400010) ∨ (0x500000 ≤ a ∧ a+n ≤ 0x500010) := by
  simpa [heap,Clif.Mem.valid,Clif.Alloc.contains] using valid

/-- Arbitrary source bytes inhabit the same original CLIF/ARM memory relation. -/
theorem memory_relation (contents : Nat → BitVec 8) (syms : String → Option Nat)
    (initial : Arm.ArmState) : MemRel reserved syms (heap contents syms) (world contents initial) where
  bytes := by
    intro a value valid initialized
    change (if 0x500000 ≤ a ∧ a < 0x500010 then some (contents (a-0x500000)) else none) = some value at initialized
    split at initialized
    · rename_i inside
      have small : a < 2^64 := by omega
      have same := Option.some.inj initialized
      simp only [Arm.read_mem,Arm.read_store,world,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
      rw [if_pos inside,same]
    · cases initialized
  valid := by
    intro a n valid
    have bounds := valid_bounds contents syms valid
    constructor
    · rcases bounds with bounds | bounds <;> omega
    · intro k below
      have small : a+k < 2^64 := by rcases bounds with bounds | bounds <;> omega
      simp only [reserved,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
      rcases bounds with bounds | bounds <;> omega
  symbols := rfl

theorem source_byte (contents : Nat → BitVec 8) (initial : Arm.ArmState) {k : Nat} (bound : k < 16) :
    Arm.read_mem (BitVec.ofNat 64 (0x500000+k)) (world contents initial) = contents k := by
  have small : 0x500000+k < 2^64 := by omega
  simp only [Arm.read_mem,Arm.read_store,world,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have inside : 0x500000 ≤ 0x500000+k ∧ 0x500000+k < 0x500010 := by omega
  rw [if_pos inside]
  have offset : 0x500000+k-0x500000 = k := by omega
  exact congrArg contents offset

/-- The symbolic heap leaves every ELF and stack byte at its original value. -/
theorem protected_bytes (contents : Nat → BitVec 8) (initial : Arm.ArmState) {a : BitVec 64}
    (outside : reserved a) : (world contents initial).mem a = initial.mem a := by
  change (if 0x500000 ≤ a.toNat ∧ a.toNat < 0x500010 then _ else _) = _
  have excluded : ¬ (0x500000 ≤ a.toNat ∧ a.toNat < 0x500010) := by
    unfold reserved at outside
    omega
  rw [if_neg excluded]


def signature : Clif.Signature := {
  params := [⟨.i64,.none,.sret⟩,⟨.i64,.none,.normal⟩]
  callConv := some .systemV }

def arguments : List Clif.Val := [⟨.i64,0x400000#64⟩,⟨.i64,0x500000#64⟩]

def machine (contents : Nat → BitVec 8) (initial : Arm.ArmState) : Arm.ArmState :=
  Arm.w (.GPR 8#5) 0x400000#64 (Arm.w (.GPR 0#5) 0x500000#64 (world contents initial))

theorem machine_memory_relation (contents : Nat → BitVec 8) (syms : String → Option Nat)
    (initial : Arm.ArmState) : MemRel reserved syms (heap contents syms) (machine contents initial) := by
  have related := memory_relation contents syms initial
  refine ⟨?_,related.valid,related.symbols⟩
  intro a value valid initialized
  simpa only [machine,Arm.read_mem,Arm.ArmState.mem_w_eq_mem] using related.bytes a value valid initialized

theorem entry_arguments (contents : Nat → BitVec 8) (initial : Arm.ArmState) :
    ArgsAtEntry reserved signature arguments (machine contents initial) := by
  intro loc value member
  change (loc,value) ∈ [(ArgLoc.reg (.x 8),⟨.i64,0x400000#64⟩),
    (ArgLoc.reg (.x 0),⟨.i64,0x500000#64⟩)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal
  all_goals cases equal
  all_goals simp [machine,regVal,rnum,VHolds,Clif.Ty.width,Arm.r_of_w_same,Arm.r_of_w_different]


/-- A live symbolic heap and both original ABI arguments exist for every source byte function. -/
theorem symbolic_entry (contents : Nat → BitVec 8) (syms : String → Option Nat)
    (initial : Arm.ArmState) :
    ∃ (cm : Clif.Mem) (w : Arm.ArmState),
      MemRel reserved syms cm w ∧ ArgsAtEntry reserved signature arguments w ∧
      cm.valid 0x400000 16 = true ∧ cm.valid 0x500000 16 = true ∧
      (∀ k < 16, Arm.read_mem (BitVec.ofNat 64 (0x500000+k)) w = contents k) ∧
      (∀ a, reserved a → w.mem a = initial.mem a) := by
  refine ⟨heap contents syms,machine contents initial,machine_memory_relation contents syms initial,
    entry_arguments contents initial,rfl,rfl,?_,?_⟩
  · intro k bound
    simpa only [machine,Arm.read_mem,Arm.ArmState.mem_w_eq_mem] using source_byte contents initial bound
  · intro a outside
    simpa only [machine,Arm.ArmState.mem_w_eq_mem] using protected_bytes contents initial outside


def entryState (f : Clif.Function) (block : Clif.Block) (cm : Clif.Mem) : Clif.State :=
  ⟨⟨f,(Clif.Regs.empty.set 0 ⟨.i64,0x400000#64⟩).set 1 ⟨.i64,0x500000#64⟩,
    [],block.body,block.term⟩,[],cm⟩

/-- Original source entry needs no execution certificate or heap acceptance guard. -/
theorem source_entry {f : Clif.Function} {block : Clif.Block}
    (sig : f.sig = signature) (entry : f.entry? = some block)
    (params : block.params = [(0,.i64),(1,.i64)]) (slots : f.slots = []) (cm : Clif.Mem) :
    ClifEntry f arguments (entryState f block cm) where
  callers := rfl
  func := rfl
  sig := by rw [sig]; rfl
  entry := by
    refine ⟨block,entry,rfl,rfl,?_,?_⟩
    · rw [params]; rfl
    · rw [params]; rfl
  slotIds := by rw [slots]; rfl

/-- The source entry, heap relation and ABI arguments are jointly inhabited. -/
theorem source_entry_heap {f : Clif.Function} {block : Clif.Block}
    (sig : f.sig = signature) (entry : f.entry? = some block)
    (params : block.params = [(0,.i64),(1,.i64)]) (slots : f.slots = [])
    (contents : Nat → BitVec 8) (syms : String → Option Nat) (initial : Arm.ArmState) :
    ∃ (cs : Clif.State) (w : Arm.ArmState), ClifEntry f arguments cs ∧
      MemRel reserved syms cs.mem w ∧ ArgsAtEntry reserved f.sig arguments w ∧
      cs.mem.valid 0x400000 16 = true ∧ cs.mem.valid 0x500000 16 = true := by
  refine ⟨entryState f block (heap contents syms),machine contents initial,
    source_entry sig entry params slots _,machine_memory_relation contents syms initial,?_,rfl,rfl⟩
  rw [sig]
  exact entry_arguments contents initial



/-- Little-endian loading retains each original byte in its eight-bit lane. -/
theorem loaded_byte {cm : Clif.Mem} {address : Nat} {word : BitVec 64}
    (loaded : cm.readBits false address 8 64 = some word) {k : Nat} (bound : k < 8) :
    cm.bytes (address+k) = some (word.extractLsb' (8*k) 8) := by
  obtain ⟨byte,initialized⟩ := Option.isSome_iff_exists.mp ((readBits_spec loaded).1 k bound)
  have equal : word.extractLsb' (8*k) 8 = byte := by
    apply BitVec.eq_of_getLsbD_eq
    intro i below
    simp only [BitVec.getLsbD_extractLsb',below,decide_true,Bool.true_and]
    rw [(readBits_spec loaded).2]
    have bits : 8*k+i < 64 := by omega
    have quotient : (8*k+i)/8 = k := by omega
    have remainder : (8*k+i)%8 = i := by omega
    simp [bits,quotient,remainder,bound,initialized]
  rw [equal]
  exact initialized


theorem heap_source_byte (contents : Nat → BitVec 8) (syms : String → Option Nat)
    {k : Nat} (bound : k < 16) : (heap contents syms).bytes (0x500000+k) = some (contents k) := by
  change (if 0x500000 ≤ 0x500000+k ∧ 0x500000+k < 0x500010 then _ else _) = _
  rw [if_pos (by omega)]
  have offset : 0x500000+k-0x500000 = k := by omega
  rw [offset]

namespace Source

def flags : Clif.MemFlags := {trapCode := none}
def first : Clif.Block := {
  id := 0,params := [(0,.i64),(1,.i64)],body := [⟨[],.nop⟩],term := .jump ⟨1,[]⟩ }
def middle : Clif.Block := {
  id := 1,body := [⟨[],.nop⟩,⟨[2],.load .load .i64 flags 1 0⟩,
    ⟨[3],.load .load .i64 flags 1 8⟩,⟨[],.store .store .i64 flags 2 0 0⟩,
    ⟨[],.store .store .i64 flags 3 0 8⟩],term := .jump ⟨2,[]⟩ }
def last : Clif.Block := {id := 2,body := [⟨[],.nop⟩],term := .ret []}

/-- The original three-block copy shape, parameterized only by its source name. -/
def function (name : String) : Clif.Function := {name,sig := signature,blocks := [first,middle,last]}

theorem entry (name : String) (contents : Nat → BitVec 8) (syms : String → Option Nat) :
    ClifEntry (function name) arguments (entryState (function name) first (heap contents syms)) :=
  source_entry rfl rfl rfl rfl _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- Both loads and stores execute for arbitrary source bytes. -/
theorem returns (name : String) (contents : Nat → BitVec 8) (syms : String → Option Nat)
    (env : Clif.Env) (program : Clif.Program) :
    ∃ cm, Clif.runLoop env program 12 (entryState (function name) first (heap contents syms)) =
      .returned [] cm := by
  exact ⟨_,rfl⟩


def low (contents : Nat → BitVec 8) (syms : String → Option Nat) : BitVec 64 :=
  ((heap contents syms).readBits false 0x500000 8 64).getD 0

def high (contents : Nat → BitVec 8) (syms : String → Option Nat) : BitVec 64 :=
  ((heap contents syms).readBits false 0x500008 8 64).getD 0

def copied (contents : Nat → BitVec 8) (syms : String → Option Nat) : Clif.Mem :=
  (((heap contents syms).writeBits false 0x400000 8 (low contents syms)).writeBits false
    0x400008 8 (high contents syms)).free [] |>.leave

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem returns_exact (name : String) (contents : Nat → BitVec 8) (syms : String → Option Nat)
    (env : Clif.Env) (program : Clif.Program) :
    Clif.runLoop env program 12 (entryState (function name) first (heap contents syms)) =
      .returned [] (copied contents syms) := by
  rfl


theorem low_loaded (contents : Nat → BitVec 8) (syms : String → Option Nat) :
    (heap contents syms).readBits false 0x500000 8 64 = some (low contents syms) := rfl

theorem high_loaded (contents : Nat → BitVec 8) (syms : String → Option Nat) :
    (heap contents syms).readBits false 0x500008 8 64 = some (high contents syms) := rfl


theorem copied_other (contents : Nat → BitVec 8) (syms : String → Option Nat) {a : Nat}
    (outside : a < 0x400000 ∨ 0x400010 ≤ a) :
    (copied contents syms).bytes a = (heap contents syms).bytes a := by
  change (if 0x400008 ≤ a ∧ a < 0x400010 then _ else
    if 0x400000 ≤ a ∧ a < 0x400008 then _ else _) = _
  rw [if_neg (by omega),if_neg (by omega)]

theorem copied_byte (contents : Nat → BitVec 8) (syms : String → Option Nat) {k : Nat}
    (bound : k < 16) : (copied contents syms).bytes (0x400000+k) = some (contents k) := by
  change (if 0x400008 ≤ 0x400000+k ∧ 0x400000+k < 0x400010 then _ else
    if 0x400000 ≤ 0x400000+k ∧ 0x400000+k < 0x400008 then _ else _) = _
  by_cases firstHalf : k < 8
  · rw [if_neg (by omega),if_pos (by omega)]
    have offset : 0x400000+k-0x400000 = k := by omega
    rw [offset]
    exact (loaded_byte (low_loaded contents syms) firstHalf).symm.trans
      (heap_source_byte contents syms bound)
  · rw [if_pos (by omega)]
    have offset : 0x400000+k-0x400008 = k-8 := by omega
    rw [offset]
    have loaded := loaded_byte (high_loaded contents syms) (k := k-8) (by omega)
    have sourceOffset : 0x500008+(k-8) = 0x500000+k := by omega
    rw [sourceOffset] at loaded
    exact loaded.symm.trans (heap_source_byte contents syms bound)

theorem copied_source_byte (contents : Nat → BitVec 8) (syms : String → Option Nat) {k : Nat}
    (bound : k < 16) : (copied contents syms).bytes (0x500000+k) = some (contents k) := by
  rw [copied_other contents syms (Or.inr (by omega))]
  exact heap_source_byte contents syms bound

/-- The full source execution copies every arbitrary byte and preserves every source byte. -/
theorem returns_bytes (name : String) (contents : Nat → BitVec 8) (syms : String → Option Nat)
    (env : Clif.Env) (program : Clif.Program) :
    ∃ cm, Clif.runLoop env program 12 (entryState (function name) first (heap contents syms)) =
      .returned [] cm ∧
      (∀ k < 16,cm.bytes (0x400000+k) = some (contents k)) ∧
      (∀ k < 16,cm.bytes (0x500000+k) = some (contents k)) :=
  ⟨copied contents syms,returns_exact name contents syms env program,
    fun _ bound => copied_byte contents syms bound,
    fun _ bound => copied_source_byte contents syms bound⟩

end Source


namespace Caller

def calleeName : String := "_RNxC7fv_demo11HawPMC3YC2b"
def signature : Clif.Signature := {
  params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
  callConv := some .systemV }
def first : Clif.Block := {
  id := 0,params := [(0,.i64),(1,.i64)],body := [⟨[],.call 0 [0,1]⟩],term := .ret [] }
def function : Clif.Function := {
  name := "sret_caller",sig := signature,
  externs := [(0,⟨calleeName,SretHeapBoundary.signature,true⟩)],blocks := [first] }
def program : Clif.Program := {funcs := [Source.function calleeName,function]}

theorem entry (contents : Nat → BitVec 8) (syms : String → Option Nat) :
    ClifEntry function arguments (entryState function first (heap contents syms)) :=
  ⟨rfl,rfl,rfl,⟨first,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The complete original caller/callee shape executes on arbitrary source contents. -/
theorem returns_exact (contents : Nat → BitVec 8) (syms : String → Option Nat) (env : Clif.Env) :
    Clif.runLoop env program 16 (entryState function first (heap contents syms)) =
      .returned [] (Source.copied contents syms) := by
  rfl

theorem returns_bytes (contents : Nat → BitVec 8) (syms : String → Option Nat) (env : Clif.Env) :
    ∃ cm, Clif.runLoop env program 16 (entryState function first (heap contents syms)) =
      .returned [] cm ∧
      (∀ k < 16,cm.bytes (0x400000+k) = some (contents k)) ∧
      (∀ k < 16,cm.bytes (0x500000+k) = some (contents k)) :=
  ⟨Source.copied contents syms,returns_exact contents syms env,
    fun _ bound => Source.copied_byte contents syms bound,
    fun _ bound => Source.copied_source_byte contents syms bound⟩


def machine (contents : Nat → BitVec 8) (initial : Arm.ArmState) : Arm.ArmState :=
  Arm.w (.GPR 0#5) 0x400000#64 (Arm.w (.GPR 1#5) 0x500000#64 (world contents initial))

theorem machine_memory_relation (contents : Nat → BitVec 8) (syms : String → Option Nat)
    (initial : Arm.ArmState) : MemRel reserved syms (heap contents syms) (machine contents initial) := by
  have related := SretHeapBoundary.memory_relation contents syms initial
  refine ⟨?_,related.valid,related.symbols⟩
  intro a value valid initialized
  simpa only [machine,Arm.read_mem,Arm.ArmState.mem_w_eq_mem] using related.bytes a value valid initialized

theorem entry_arguments (contents : Nat → BitVec 8) (initial : Arm.ArmState) :
    ArgsAtEntry reserved signature arguments (machine contents initial) := by
  intro loc value member
  change (loc,value) ∈ [(ArgLoc.reg (.x 0),⟨.i64,0x400000#64⟩),
    (ArgLoc.reg (.x 1),⟨.i64,0x500000#64⟩)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal
  all_goals cases equal
  all_goals simp [machine,regVal,rnum,VHolds,Clif.Ty.width,Arm.r_of_w_same,Arm.r_of_w_different]

/-- Source entry, ordinary caller arguments, and the complete copy outcome exist jointly. -/
theorem symbolic_entry (contents : Nat → BitVec 8) (syms : String → Option Nat)
    (initial : Arm.ArmState) (env : Clif.Env) :
    ∃ (cs : Clif.State) (w : Arm.ArmState) (cm : Clif.Mem),
      ClifEntry function arguments cs ∧ MemRel reserved syms cs.mem w ∧
      ArgsAtEntry reserved signature arguments w ∧
      Clif.runLoop env program 16 cs = .returned [] cm ∧
      (∀ k < 16,cm.bytes (0x400000+k) = some (contents k)) ∧
      (∀ k < 16,cm.bytes (0x500000+k) = some (contents k)) :=
  ⟨entryState function first (heap contents syms),machine contents initial,Source.copied contents syms,
    entry contents syms,machine_memory_relation contents syms initial,entry_arguments contents initial,
    returns_exact contents syms env,fun _ bound => Source.copied_byte contents syms bound,
    fun _ bound => Source.copied_source_byte contents syms bound⟩


def programWith (header : List String) (data : List Clif.DataObject) : Clif.Program :=
  {program with header,data}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- Source execution retains every supplied program header and data object. -/
theorem returns_exact_with (header : List String) (data : List Clif.DataObject)
    (contents : Nat → BitVec 8) (syms : String → Option Nat) (env : Clif.Env) :
    Clif.runLoop env (programWith header data) 16 (entryState function first (heap contents syms)) =
      .returned [] (Source.copied contents syms) := by
  rfl

theorem symbolic_entry_with (header : List String) (data : List Clif.DataObject)
    (contents : Nat → BitVec 8) (syms : String → Option Nat) (initial : Arm.ArmState) (env : Clif.Env) :
    ∃ (cs : Clif.State) (w : Arm.ArmState) (cm : Clif.Mem),
      ClifEntry function arguments cs ∧ MemRel reserved syms cs.mem w ∧
      ArgsAtEntry reserved signature arguments w ∧
      Clif.runLoop env (programWith header data) 16 cs = .returned [] cm ∧
      (∀ k < 16,cm.bytes (0x400000+k) = some (contents k)) ∧
      (∀ k < 16,cm.bytes (0x500000+k) = some (contents k)) :=
  ⟨entryState function first (heap contents syms),machine contents initial,Source.copied contents syms,
    entry contents syms,machine_memory_relation contents syms initial,entry_arguments contents initial,
    returns_exact_with header data contents syms env,fun _ bound => Source.copied_byte contents syms bound,
    fun _ bound => Source.copied_source_byte contents syms bound⟩

end Caller

end E2E.SretHeapBoundary











