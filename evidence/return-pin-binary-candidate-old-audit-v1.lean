import FV.E2E.BinaryBoundaryFacts

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

/-- The model state's code addresses are the program's. -/
theorem img_of_codeAddr {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    (hL : (SemanticStackBound.ofInput I B F).OkSemanticNI) {f : Clif.Function} (hf : f ∈ (prog I).funcs)
    {r : Arm.ArmState} {a : BitVec 64} (h : CodeAddr (modelOf I f r) a) : img I a := by
  exact BinaryBoundaryFacts.img_of_codeAddr (BinaryBoundaryFacts.of_semantic hL) hf h

/-- The frame facts of a compiled function. -/
theorem frame_facts {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    (hL : (SemanticStackBound.ofInput I B F).OkSemanticNI) {f : Clif.Function} (hf : f ∈ (prog I).funcs) :
    frameDrop (art I f).af = (art I f).af.frameSize + 16 ∧
    (art I f).af.slotBase = (RAFrame.compute (art I f).vcp (art I f).rf).size ∧
    (RAFrame.compute (art I f).vcp (art I f).rf).intBase ≤
      (RAFrame.compute (art I f).vcp (art I f).rf).size ∧
    (RAFrame.compute (art I f).vcp (art I f).rf).size ≤
      (art I f).af.frameSize - clobberBytes (art I f).af.saves := by
  exact BinaryBoundaryFacts.frame_facts (BinaryBoundaryFacts.of_semantic hL) hf

/-- A byte of the free stack outside the slot region, or of the code, is outside the world; a
byte that is neither is not. -/
theorem not_worldF {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    (hL : (SemanticStackBound.ofInput I B F).OkSemanticNI) {f : Clif.Function} (hf : f ∈ (prog I).funcs)
    {K : Nat} {r : Arm.ArmState} (hN : frameDrop (art I f).af + K ≤ (spv r).toNat)
    {x : BitVec 64} (hx : ¬ img I x)
    (hs : StackBelow (frameDrop (art I f).af + K) (spv r) x → SlotArea (art I f).af r x) :
    ¬ worldF I f K r x := by
  exact BinaryBoundaryFacts.not_worldF (BinaryBoundaryFacts.of_semantic hL) hf hN hx hs

/-- A byte of the outgoing-argument area `[sp_body, sp_body + intBase)` that is not code is in
the world. -/
theorem not_worldF_out {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    (hL : (SemanticStackBound.ofInput I B F).OkSemanticNI) {f : Clif.Function} (hf : f ∈ (prog I).funcs)
    {K : Nat} {r : Arm.ArmState} (hN : frameDrop (art I f).af + K ≤ (spv r).toNat)
    {j : Nat} (hj : j < (RAFrame.compute (art I f).vcp (art I f).rf).intBase)
    (hx : ¬ img I (spBody (art I f).af r + BitVec.ofNat 64 j)) :
    ¬ worldF I f K r (spBody (art I f).af r + BitVec.ofNat 64 j) := by
  exact BinaryBoundaryFacts.not_worldF_out (BinaryBoundaryFacts.of_semantic hL) hf hN hj hx

/-- **The per-run premises of `backend_correct_program` from the boundary contract**, for the
model state `s = modelOf I f r`, the body-entry world `bodyOf af s`, the callees' budget `K` and
the addresses outside the world `worldF I f K r`. -/
theorem premises {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {f : Clif.Function} {K : Nat} {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State}
    (hL : (SemanticStackBound.ofInput I B (worldF I f K r)).OkSemanticNI) (hf : f ∈ (prog I).funcs)
    {roB : BitVec 64 → Option (BitVec 8)} (hro : ∀ a b, roB a = some b → r.mem a = b)
    (ho : OutsideCall I roB f (frameDrop (art I f).af + K) r args cs.mem)
    (hr : ClifRun I B f r args cs) :
    AbiEntry (art I f).fb (art I f).base (xreg 30 r) (modelOf I f r) ∧
    StackAvail K (art I f).af (modelOf I f r) ∧
    (∀ a, img I a → ¬ StackBelow (frameDrop (art I f).af + K) (spv (modelOf I f r)) a) ∧
    (∀ a, img I a → (modelOf I f r).mem a = imgMem I a) ∧
    BodyEntry (art I f).af (modelOf I f r) (bodyOf (art I f).af (modelOf I f r)) ∧
    ArgsIn f.sig args (modelOf I f r) ∧ StackArgsAvoid (img I) f.sig args (modelOf I f r) ∧
    Rel.holds ⟨worldF I f K r, fun n => I.syms.lookup n, (art I f).af.slotBase,
      (RAFrame.compute (art I f).vcp (art I f).rf).intBase⟩ f cs.frame.slots cs.mem
      (bodyOf (art I f).af (modelOf I f r)) ∧
    ((sys I B).NeedSlots → (sys I B).PlaceAt cs.mem (spv (bodyOf (art I f).af (modelOf I f r)))) := by
  exact BinaryBoundaryFacts.premises (BinaryBoundaryFacts.of_semantic hL) hf hro ho hr
/-- The linked machine does not depend on the addresses `F` outside the world. -/
theorem hooks_F (I : SemanticStackBound.CompilerInput) (B : BaseEnv) (F F' : BitVec 64 → Prop) :
    ∀ M, (SemanticStackBound.ofInput I B F).hooks M = (SemanticStackBound.ofInput I B F').hooks M
  | 0 => rfl
  | M + 1 => by
    simp only [LinkSys.hooks]
    rw [hooks_F I B F F' M]
    rfl

theorem mach_F (I : SemanticStackBound.CompilerInput) (B : BaseEnv) (F F' : BitVec 64 → Prop) (M : Nat)
    (f : Clif.Function) : (SemanticStackBound.ofInput I B F).mach M f = (SemanticStackBound.ofInput I B F').mach M f := by
  simp only [LinkSys.mach]
  rw [hooks_F I B F F' M]
  rfl

/-! ## The binary-level theorems -/

/-- **The binary-level theorem at depth `M`** (any program, recursive ones included: the stack
premise is `frameDrop + D * M` bytes, `backend_correct_program`'s budget): for a crate input that
passes the checker, a function `f` of the program called by outside code that meets the boundary
contract `OutsideCall` in the machine state `r`, the linked machine of depth `M` from the model
state of `r` refines the whole-program CLIF run of at most `M + 1` steps from the reference entry
state `cs` (`ClifRun`), returning to the caller's return address (x30 of `r`). The premises left:
the base environment's contracts (`BaseOk`) and the CLIF run's explicit traps (`TrapsExplicit`). -/
theorem binary_correct_depth {I : SemanticStackBound.CompilerInput} (hI : SemanticStackBound.okB I = true) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (ho : OutsideCall I (fun _ => none) f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hB' : BaseOk (SemanticStackBound.ofInput I B (worldF I f (I.D * M) r)) := baseOk_F hB
  have himgF : ∀ a, (SemanticStackBound.ofInput I B (worldF I f (I.D * M) r)).Img a →
      worldF I f (I.D * M) r a := fun _ h => .inr h
  have hL := SemanticStackBound.okB_sound hI hB' himgF
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
    premises hL (Clif.Program.func?_some hf).1 (fun _ _ h => by cases h) ho hr
  rw [mach_F I B (fun _ => False) (worldF I f (I.D * M) r)]
  exact backend_correct_program_semantic _ hL (Clif.Program.func?_some hf).1 M hent hres rfl hgfree himg hbe hargs hr.entry hsav hrel hpl htr

/-- A contract with more stack gives one with less. -/
theorem OutsideCall.mono {I : SemanticStackBound.CompilerInput} {roB : BitVec 64 → Option (BitVec 8)} {f : Clif.Function}
    {N N' : Nat} {r : Arm.ArmState} {args : List Clif.Val} {cm : Clif.Mem}
    (h : OutsideCall I roB f N' r args cm) (hN : N ≤ N') : OutsideCall I roB f N r args cm where
  pc := h.pc
  err := h.err
  ra := h.ra
  spAligned := h.spAligned
  stack := Nat.le_trans hN h.stack
  stackFree := fun a ha hb => h.stackFree a ha ⟨hb.1, by have := hb.2; omega⟩
  args := h.args
  bytes := h.bytes
  image := h.image
  valid := fun a n hv => ⟨(h.valid a n hv).1, fun k hk => ⟨((h.valid a n hv).2 k hk).1,
    fun hb => ((h.valid a n hv).2 k hk).2 ⟨hb.1, by have := hb.2; omega⟩⟩⟩
  symbols := h.symbols

/-- A returning whole-program CLIF run of `f` satisfies `TrapsExplicit` (as in
`backend_correct_program_returned`): the premise is needed only for trapping runs. -/
theorem trapsExplicit_of_run {L : LinkSys} (hL : L.OkSemanticNI) {f : Clif.Function} (hf : f ∈ L.P.funcs)
    {M : Nat} {args : List Clif.Val} {cs : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (hcs : ClifEntry f args cs) (hsym : cs.mem.symbols = L.syms)
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs := by
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf)
    (E := Clif.linkEnvN L.P L.base M) rfl rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
    (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hsym) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  exact trapsExplicit_of_returned hm

/-- `trapsExplicit_of_run` for the environment of the run's peak call depth: a returning
whole-program CLIF run of `f` of at most `F + 1` steps and call depth at most `d`
(`Clif.DepthLe`) satisfies `TrapsExplicit` under `Clif.linkEnvD` (`Clif.runLoop_linkD`). -/
theorem trapsExplicit_of_runD {L : LinkSys} (hL : L.OkSemanticNI) {f : Clif.Function} (hf : f ∈ L.P.funcs)
    {F d : Nat} {args : List Clif.Val} {cs : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (hcs : ClifEntry f args cs) (hsym : cs.mem.symbols = L.syms)
    (hd : Clif.DepthLe L.base L.P d cs)
    (hrun : Clif.runLoop L.base L.P (F + 1) cs = .returned vals cm) :
    TrapsExplicit (Clif.linkEnvD L.P L.base F d) L.P.bare cs := by
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkD (base := L.base) (syms := L.syms) F d hL.names hf hL.free
    (hL.indScope f hf)
    (E := Clif.linkEnvD L.P L.base F d) rfl rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
    (F + 1) cs (Nat.le_refl _) hd (runInv_entry hf hcs) hIf
    (fun _ => hsym) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  exact trapsExplicit_of_returned hm

/-! ## The binary facts -/

/-- **The executable's loaded segments** as the binary checks read them: the byte at each loaded
address (`mem`), and the addresses nothing writes after loading (`kept`: the read-only segments;
the relocation-read-only data, `PT_GNU_RELRO`). -/
structure Image where
  mem : BitVec 64 → Option (BitVec 8)
  kept : BitVec 64 → Prop

/-- **The loader premise**: the machine state `r` holds the executable's kept bytes (the OS maps
the segments at their link addresses; read-only segments are never written, and no code writes
the relocation-read-only data). -/
def Image.Intact (X : Image) (r : Arm.ArmState) : Prop :=
  ∀ a b, X.kept a → X.mem a = some b → r.mem a = b

/-- **The binary facts** of an executable `X` for a crate input `I` (what the binary checks
establish, `binary_correct_of_checks`): the input passes the crate checker (`SemanticStackBound.okB`); the program's
code bytes are kept bytes of the executable, equal to the compiled image except at the bytes `R`
of relocated instructions (which hold the resolved encodings, `FV/E2E/BinCheck.lean`); the CLIF
image's read-only data `roB` are kept bytes of the executable. -/
structure BinFacts (I : SemanticStackBound.CompilerInput) (X : Image) (R : BitVec 64 → Prop)
    (roB : BitVec 64 → Option (BitVec 8)) : Prop where
  ok : SemanticStackBound.okB I = true
  code : ∀ a, img I a → X.kept a ∧ (X.mem a = some (imgMem I a) ∨ R a)
  data : ∀ a b, roB a = some b → X.kept a ∧ X.mem a = some b

/-- **The binary-level theorem** (`docs/contracts/e2e.md`, "Binary level (M9)"): for an
executable with the binary facts of a crate input (`BinFacts`), whose loaded kept bytes the
machine state `r` holds (`Image.Intact`), a function `f` of the program whose calls reach no call
cycle (`goodN`, the stack check of `FV/E2E/SemanticStackBound.lean`) called by outside code that meets
the boundary contract (`OutsideCall`, with `f`'s stack bound `stackFn I f`), the linked machine
(at every depth `M`) from the model state of `r` refines the whole-program CLIF run of at most
`M + 1` steps from the reference entry state (`ClifRun`), returning to the caller's return
address; and the model state differs from `r` only at the relocated instruction bytes `R`. The
premises left: the base environment's contracts (`BaseOk`) and the CLIF run's explicit traps
(`TrapsExplicit`). -/
theorem binary_correct {I : SemanticStackBound.CompilerInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} (hn : SemanticStackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    ∀ a, (modelOf I f r).mem a ≠ r.mem a → R a := by
  refine ⟨?_, fun a hne => ?_⟩
  · have hB' : BaseOk (SemanticStackBound.ofInput I B (worldF I f (SemanticStackBound.bud I f) r)) := baseOk_F hB
    have himgF : ∀ a, (SemanticStackBound.ofInput I B (worldF I f (SemanticStackBound.bud I f) r)).Img a →
        worldF I f (SemanticStackBound.bud I f) r a := fun _ h => .inr h
    have hL := SemanticStackBound.okB_sound hbin.ok hB' himgF
    have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h =>
      hX a b (hbin.data a b h).1 (hbin.data a b h).2
    obtain ⟨hent, -, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
      premises hL (Clif.Program.func?_some hf).1 hro ho hr
    rw [mach_F I B (fun _ => False) (worldF I f (SemanticStackBound.bud I f) r)]
    exact SemanticStackBound.crate_correct_stackN hbin.ok hn B _ hB' himgF f hf M _ _ _ args cs hent
      (by rw [spv_modelOf]; exact ho.stack) hgfree rfl himg hbe hargs hr.entry hsav hrel hpl htr
  · by_cases hi : img I a
    · rw [mem_modelOf_img hi] at hne
      rcases (hbin.code a hi).2 with h | h
      · exact absurd (hX a _ (hbin.code a hi).1 h).symm hne
      · exact h
    · exact absurd (mem_modelOf_not hi) hne

/-- **`binary_correct` for a non-recursive program** (`stackB I = some S`): every function, with
`S` bytes of stack. -/
theorem binary_correct_bound {I : SemanticStackBound.CompilerInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) {S : Nat}
    (hS : SemanticStackBound.stackB I = some S) (B : BaseEnv) (hB : BaseOk (sys I B)) {n : String}
    {f : Clif.Function} (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f S r args cs.mem) (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    ∀ a, (modelOf I f r).mem a ≠ r.mem a → R a := by
  have hn : SemanticStackBound.goodN I n = true := by
    unfold SemanticStackBound.goodN; rw [show (progOf I.results).func? n = some f from hf]
    exact (SemanticStackBound.stackB_some hS).1 f (Clif.Program.func?_some hf).1
  exact binary_correct hbin B hB hn hf M hX
    (ho.mono (SemanticStackBound.stackFn_le hS (Clif.Program.func?_some hf).1)) hr htr

/-! ## The binary checks -/

/-- **The loaded image of an ELF file** (`FV/E2E/Elf.lean`): its bytes, and the addresses nothing
writes after loading (the read-only segments; the relocation-read-only data). -/
def imageOf (file : ByteArray) : Image := ⟨Elf.loadMem file, fun a => Elf.ro file a ∨ Elf.relro file a⟩

/-- **The binary facts from the checks**: an input that passes the crate checker and an
executable file that passes the binary checks (`BinCheck.BinOk`: its code is the compiled code
with resolved relocations, its CLIF data objects and symbols are the input's). -/
theorem binFacts_of_checks {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : SemanticStackBound.okB I = true) (hB : BinCheck.BinOkWithResults I I.results D file) :
    BinFacts I (imageOf file) (BinCheck.RelocAtWithResults I I.results) (BinCheck.roByte I D) where
  ok := hI
  code := fun _ ha =>
    have himg : imgB (tabOf I.results) = true :=
      okRSemanticNI_global I.stage hI ("imgCode: the image reads back",imgB (tabOf I.results))
        (by simp [globalChks])
    have h := BinCheck.img_bytesWithResults hB himg ha
    ⟨.inl h.1, h.2⟩
  data := fun _ _ h =>
    have h' := BinCheck.roByte_sound hB.data h
    ⟨h'.2, h'.1⟩

/-- **The binary-level theorem for an executable file** that passes the checks (`SemanticStackBound.okB` on the
crate input `I`, `BinOk` on the file with the CLIF data objects `D`): `binary_correct` with the
executable's loaded image (`imageOf file`), its relocated instruction bytes `RelocAt I` and its
read-only CLIF data `roByte I D`. -/
theorem binary_correct_of_checks {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : SemanticStackBound.okB I = true) (hbin : BinCheck.BinOkWithResults I I.results D file) (B : BaseEnv) (hB : BaseOk (sys I B))
    {n : String} (hn : SemanticStackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    ∀ a, (modelOf I f r).mem a ≠ r.mem a → BinCheck.RelocAtWithResults I I.results a :=
  binary_correct (binFacts_of_checks hI hbin) B hB hn hf M hX ho hr htr

/-- **`binary_correct_of_checks` from the input condition**: the stack premise `goodN` replaced by
what it decides (`SemanticStackBound.goodN_iff`): no call cycle of the program's call graph
(`SemanticStackBound.Calls`) is reachable from `f`. Recursive functions (a cycle reachable) keep the
depth-indexed theorem. -/
theorem binary_correct_of_checks_acyclic {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : SemanticStackBound.okB I = true) (hbin : BinCheck.BinOkWithResults I I.results D file) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls I I.results) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    ∀ a, (modelOf I f r).mem a ≠ r.mem a → BinCheck.RelocAtWithResults I I.results a :=
  binary_correct_of_checks hI hbin B hB ((SemanticStackBound.goodN_iff hI).2 ⟨f, hf, hc⟩) hf M hX ho hr htr

end E2E.SemanticBinary

#print axioms E2E.SemanticBinary.r_modelOf
#print axioms E2E.SemanticBinary.spv_modelOf
#print axioms E2E.SemanticBinary.regVal_modelOf
#print axioms E2E.SemanticBinary.mem_modelOf
#print axioms E2E.SemanticBinary.mem_modelOf_img
#print axioms E2E.SemanticBinary.mem_modelOf_not
#print axioms E2E.SemanticBinary.program_modelOf
#print axioms E2E.SemanticBinary.bodyEntry_bodyOf
#print axioms E2E.SemanticBinary.baseOk_F
#print axioms E2E.SemanticBinary.img_of_codeAddr
#print axioms E2E.SemanticBinary.frame_facts
#print axioms E2E.SemanticBinary.not_worldF
#print axioms E2E.SemanticBinary.not_worldF_out
#print axioms E2E.SemanticBinary.premises
#print axioms E2E.SemanticBinary.hooks_F
#print axioms E2E.SemanticBinary.mach_F
#print axioms E2E.SemanticBinary.binary_correct_depth
#print axioms E2E.SemanticBinary.OutsideCall.mono
#print axioms E2E.SemanticBinary.trapsExplicit_of_run
#print axioms E2E.SemanticBinary.trapsExplicit_of_runD
#print axioms E2E.SemanticBinary.binary_correct
#print axioms E2E.SemanticBinary.binary_correct_bound
#print axioms E2E.SemanticBinary.binFacts_of_checks
#print axioms E2E.SemanticBinary.binary_correct_of_checks
#print axioms E2E.SemanticBinary.binary_correct_of_checks_acyclic
