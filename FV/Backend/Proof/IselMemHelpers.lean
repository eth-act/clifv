import FV.Backend.Proof.IselMemAmodeTop

/-!
# Memory family (M4Mem2): the memory helper terms

`aarch64_{u,s}load*` (529–535: a fresh destination and one load), `aarch64_store*` (541–544:
the store as a `SideEffectNoResult`), `compute_stack_addr` (643: `LoadAddr` of the slot's
`SlotOffset`), `load_ext_name_got` (571) and `load_ext_name` (570; the non-PIC rules never
apply since `is_pic` is true): the GOT load, plus the offset through `imm` and `add`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Decoding the emitted instructions -/

theorem ofV_uload8' (rd : Reg) (amv : V) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 10 [.reg rd, amv, .op (.memFlags fl)]) =
      amv.amode?.bind fun am => some (.load .uload8 rd am fl) := rfl

theorem ofV_sload8' (rd : Reg) (amv : V) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 11 [.reg rd, amv, .op (.memFlags fl)]) =
      amv.amode?.bind fun am => some (.load .sload8 rd am fl) := rfl

theorem ofV_uload16' (rd : Reg) (amv : V) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 12 [.reg rd, amv, .op (.memFlags fl)]) =
      amv.amode?.bind fun am => some (.load .uload16 rd am fl) := rfl

theorem ofV_sload16' (rd : Reg) (amv : V) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 13 [.reg rd, amv, .op (.memFlags fl)]) =
      amv.amode?.bind fun am => some (.load .sload16 rd am fl) := rfl

theorem ofV_uload32' (rd : Reg) (amv : V) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 14 [.reg rd, amv, .op (.memFlags fl)]) =
      amv.amode?.bind fun am => some (.load .uload32 rd am fl) := rfl

theorem ofV_sload32' (rd : Reg) (amv : V) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 15 [.reg rd, amv, .op (.memFlags fl)]) =
      amv.amode?.bind fun am => some (.load .sload32 rd am fl) := rfl

theorem ofV_uload64' (rd : Reg) (amv : V) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 16 [.reg rd, amv, .op (.memFlags fl)]) =
      amv.amode?.bind fun am => some (.load .uload64 rd am fl) := rfl

theorem ofV_store8' (rd : Reg) (amv : V) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 17 [.reg rd, amv, .op (.memFlags fl)]) =
      amv.amode?.bind fun am => some (.store .store8 rd am fl) := rfl

theorem ofV_store16' (rd : Reg) (amv : V) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 18 [.reg rd, amv, .op (.memFlags fl)]) =
      amv.amode?.bind fun am => some (.store .store16 rd am fl) := rfl

theorem ofV_store32' (rd : Reg) (amv : V) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 19 [.reg rd, amv, .op (.memFlags fl)]) =
      amv.amode?.bind fun am => some (.store .store32 rd am fl) := rfl

theorem ofV_store64' (rd : Reg) (amv : V) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 20 [.reg rd, amv, .op (.memFlags fl)]) =
      amv.amode?.bind fun am => some (.store .store64 rd am fl) := rfl

theorem ofV_loadAddr_slot (rd : Reg) (o : Int) :
    MInst.ofV (.data tyMInst VIdx.MInst.LoadAddr [.reg rd, .data tyAMode VIdx.AMode.SlotOffset [.int o]]) =
      some (.loadAddr rd (.slotOffset o)) := rfl

theorem ofV_loadExtNameGot (rd : Reg) (nm : String) :
    MInst.ofV (.data 58 129 [.reg rd, .op (.extName nm)]) = some (.loadExtNameGot rd nm) := rfl

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

/-! ## Loads and stores -/

include hp hc in
/-- **`aarch64_uload8`**: a fresh destination and the load. -/
theorem uload8_helper_ok {n : Nat} (hn : 40 ≤ n) {amv flv : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 529 [amv, flv] s v s') :
    ∃ m, MInst.ofV (.data 58 10 [.reg (s.1.fresh .int).1, amv, flv]) = some m ∧
      v = .reg (s.1.fresh .int).1 ∧ s'.1 = (s.1.fresh .int).2.emit m := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 529
  mem_inv hp [] at hm he
  first | exact ⟨_, ‹_›, rfl, rfl⟩ | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›⟩

include hp hc in
/-- **`aarch64_sload8`**: a fresh destination and the load. -/
theorem sload8_helper_ok {n : Nat} (hn : 40 ≤ n) {amv flv : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 530 [amv, flv] s v s') :
    ∃ m, MInst.ofV (.data 58 11 [.reg (s.1.fresh .int).1, amv, flv]) = some m ∧
      v = .reg (s.1.fresh .int).1 ∧ s'.1 = (s.1.fresh .int).2.emit m := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 530
  mem_inv hp [] at hm he
  first | exact ⟨_, ‹_›, rfl, rfl⟩ | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›⟩

include hp hc in
/-- **`aarch64_uload16`**: a fresh destination and the load. -/
theorem uload16_helper_ok {n : Nat} (hn : 40 ≤ n) {amv flv : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 531 [amv, flv] s v s') :
    ∃ m, MInst.ofV (.data 58 12 [.reg (s.1.fresh .int).1, amv, flv]) = some m ∧
      v = .reg (s.1.fresh .int).1 ∧ s'.1 = (s.1.fresh .int).2.emit m := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 531
  mem_inv hp [] at hm he
  first | exact ⟨_, ‹_›, rfl, rfl⟩ | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›⟩

include hp hc in
/-- **`aarch64_sload16`**: a fresh destination and the load. -/
theorem sload16_helper_ok {n : Nat} (hn : 40 ≤ n) {amv flv : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 532 [amv, flv] s v s') :
    ∃ m, MInst.ofV (.data 58 13 [.reg (s.1.fresh .int).1, amv, flv]) = some m ∧
      v = .reg (s.1.fresh .int).1 ∧ s'.1 = (s.1.fresh .int).2.emit m := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 532
  mem_inv hp [] at hm he
  first | exact ⟨_, ‹_›, rfl, rfl⟩ | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›⟩

include hp hc in
/-- **`aarch64_uload32`**: a fresh destination and the load. -/
theorem uload32_helper_ok {n : Nat} (hn : 40 ≤ n) {amv flv : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 533 [amv, flv] s v s') :
    ∃ m, MInst.ofV (.data 58 14 [.reg (s.1.fresh .int).1, amv, flv]) = some m ∧
      v = .reg (s.1.fresh .int).1 ∧ s'.1 = (s.1.fresh .int).2.emit m := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 533
  mem_inv hp [] at hm he
  first | exact ⟨_, ‹_›, rfl, rfl⟩ | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›⟩

include hp hc in
/-- **`aarch64_sload32`**: a fresh destination and the load. -/
theorem sload32_helper_ok {n : Nat} (hn : 40 ≤ n) {amv flv : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 534 [amv, flv] s v s') :
    ∃ m, MInst.ofV (.data 58 15 [.reg (s.1.fresh .int).1, amv, flv]) = some m ∧
      v = .reg (s.1.fresh .int).1 ∧ s'.1 = (s.1.fresh .int).2.emit m := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 534
  mem_inv hp [] at hm he
  first | exact ⟨_, ‹_›, rfl, rfl⟩ | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›⟩

include hp hc in
/-- **`aarch64_uload64`**: a fresh destination and the load. -/
theorem uload64_helper_ok {n : Nat} (hn : 40 ≤ n) {amv flv : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 535 [amv, flv] s v s') :
    ∃ m, MInst.ofV (.data 58 16 [.reg (s.1.fresh .int).1, amv, flv]) = some m ∧
      v = .reg (s.1.fresh .int).1 ∧ s'.1 = (s.1.fresh .int).2.emit m := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 535
  mem_inv hp [] at hm he
  first | exact ⟨_, ‹_›, rfl, rfl⟩ | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›⟩

include hp hc in
/-- **`aarch64_store8`**: the store as a side effect. -/
theorem store8_helper_ok {n : Nat} (hn : 40 ≤ n) {amv flv r : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 46 541 [amv, flv, r] s v s') :
    v = .data 46 0 [.data 58 17 [r, amv, flv]] ∧ s'.1 = s.1 := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 541
  mem_inv hp [] at hm he

include hp hc in
/-- **`aarch64_store16`**: the store as a side effect. -/
theorem store16_helper_ok {n : Nat} (hn : 40 ≤ n) {amv flv r : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 46 542 [amv, flv, r] s v s') :
    v = .data 46 0 [.data 58 18 [r, amv, flv]] ∧ s'.1 = s.1 := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 542
  mem_inv hp [] at hm he

include hp hc in
/-- **`aarch64_store32`**: the store as a side effect. -/
theorem store32_helper_ok {n : Nat} (hn : 40 ≤ n) {amv flv r : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 46 543 [amv, flv, r] s v s') :
    v = .data 46 0 [.data 58 19 [r, amv, flv]] ∧ s'.1 = s.1 := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 543
  mem_inv hp [] at hm he

include hp hc in
/-- **`aarch64_store64`**: the store as a side effect. -/
theorem store64_helper_ok {n : Nat} (hn : 40 ≤ n) {amv flv r : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 46 544 [amv, flv, r] s v s') :
    v = .data 46 0 [.data 58 20 [r, amv, flv]] ∧ s'.1 = s.1 := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 544
  mem_inv hp [] at hm he

/-! ## Stack-slot addresses and symbols -/

include hp hc in
/-- **`compute_stack_addr slot off`**: `LoadAddr` of the slot's `SlotOffset`. -/
theorem compute_stack_addr_ok {n : Nat} (hn : 40 ≤ n) {sl : Nat} {off : Int}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 643 [.op (.stackSlot sl), .int off] s v s') :
    ∃ base, ctx.slotOff.lookup sl = some base ∧ v = .reg (s.1.fresh .int).1 ∧
      s'.1 = (s.1.fresh .int).2.emit (.loadAddr (s.1.fresh .int).1 (.slotOffset (base + off))) := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 643
  mem_inv hp [] at hm he
  rw [ofV_loadAddr_slot] at *
  simp only [Option.some.injEq] at *
  subst_vars
  first | exact ⟨_, ‹_›, rfl, rfl⟩ | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›⟩

include hp hc in
/-- **`load_ext_name_got name`**: a fresh destination and the GOT load. -/
theorem load_ext_name_got_ok {n : Nat} (hn : 40 ≤ n) {nm : String}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 571 [.op (.extName nm)] s v s') :
    v = .reg (s.1.fresh .int).1 ∧
      s'.1 = (s.1.fresh .int).2.emit (.loadExtNameGot (s.1.fresh .int).1 nm) := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 571
  mem_inv hp [] at hm he
  rw [ofV_loadExtNameGot] at *
  simp only [Option.some.injEq] at *
  subst_vars
  first | exact ⟨rfl, rfl⟩ | rfl | trivial

/-! ## `load_ext_name` -/

section Sym
variable {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {isem : Sem}

theorem mem_lo64_ofX (r : BitVec 64) : lo64 (ofX r) = r := by
  simp [lo64, ofX, BitVec.setWidth_setWidth_of_le]

theorem operands_loadExtNameGot (d : Nat) (nm : String) :
    (MInst.loadExtNameGot (.vreg d .int) nm).operands = .ok #[⟨d, .int, .def, .late, .reg⟩] := rfl

/-- The GOT load of a linked symbol (`MemRefines`). -/
theorem runs_got {sb : Nat} {syms : String → Option Nat} (hM : MemRefinesR Rd F sb syms isem) {d : Nat}
    {nm : String} {b : Nat} (hb : syms nm = some b) (ρ : Nat → CV) (w : Arm.ArmState) :
    Runs F isem [.loadExtNameGot (.vreg d .int) nm] ρ w
      (fun ρ' _ => ρ' = upd ρ d (ofX (BitVec.ofNat 64 b))) := by
  obtain ⟨w', hs, hsw⟩ := hM.2.2.2.1 d nm b w hb
  exact ⟨_, w', seqRun_isem_one (operands_loadExtNameGot d nm) hs rfl, hsw.toNF, rfl⟩

/-- What `load_ext_name name off _` produced: code defining fresh vregs and reading only fresh
vregs, whose result `d` holds the symbol's address plus `off`. -/
structure SymOk (F : BitVec 64 → Prop) (isem : Sem) (syms : String → Option Nat) (st st' : LState)
    (ms : List MInst) (d : Nat) (nm : String) (off : Int) : Prop where
  frag : Frag st st' ms
  res : st.nextVreg ≤ d
  uses : ∀ m ∈ ms, ∀ u ∈ vuseNums m, st.nextVreg ≤ u
  run : ∀ b ρ w, syms nm = some b → Runs F isem ms ρ w
    (fun ρ' _ => lo64 (ρ' d) = BitVec.ofNat 64 b + BitVec.ofInt 64 off)

theorem vdefs_got (d : Nat) (nm : String) : vdefs (.loadExtNameGot (.vreg d .int) nm) = [d] := rfl

theorem vuseNums_got (d : Nat) (nm : String) : vuseNums (.loadExtNameGot (.vreg d .int) nm) = [] := rfl

theorem symOk_got {sb : Nat} {syms : String → Option Nat} (hM : MemRefinesR Rd F sb syms isem)
    (st : LState) (nm : String) :
    SymOk F isem syms st ((st.fresh .int).2.emit (.loadExtNameGot (st.fresh .int).1 nm))
      [.loadExtNameGot (st.fresh .int).1 nm] st.nextVreg nm 0 := by
  rw [fresh_fst]
  refine ⟨frag_one st _ (vdefs_got _ _), Nat.le_refl _, ?_, fun b ρ w hb => ?_⟩
  · intro m hm u hu
    simp only [List.mem_singleton] at hm; subst hm
    simp [vuseNums_got] at hu
  · refine (runs_got hM hb ρ w).imp fun ρ' _ _ e => ?_
    subst e
    rw [upd_same, mem_lo64_ofX]; simp

theorem symOk_add {sb : Nat} {syms : String → Option Nat} (hM : MemRefinesR Rd F sb syms isem)
    (st : LState) {st3 : LState} {ms : List MInst} {nm : String} {off : Int} {d : Nat}
    (hadd : AddOk F isem ((st.fresh .int).2.emit (.loadExtNameGot (st.fresh .int).1 nm)) st3 ms
      st.nextVreg off d)
    (hd : st.nextVreg + 1 ≤ d) :
    SymOk F isem syms st st3 (.loadExtNameGot (st.fresh .int).1 nm :: ms) d nm off := by
  have hg := symOk_got hM st nm
  have hn1 : ((st.fresh .int).2.emit (.loadExtNameGot (st.fresh .int).1 nm)).nextVreg =
      st.nextVreg + 1 := nextVreg_fresh_emit ..
  refine ⟨hg.frag.append hadd.frag, by omega, ?_, fun b ρ w hb => ?_⟩
  · intro m hm u hu
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hg.uses _ (List.mem_singleton_self _) u hu
    · rcases hadd.uses m hm u hu with h | rfl
      · omega
      · exact Nat.le_refl _
  · rw [fresh_fst]
    refine (runs_got hM hb ρ w).append fun ρ1 w1 e => ?_
    subst e
    refine (hadd.run _ w1).imp fun ρ' _ _ h => ?_
    rw [h, upd_same, mem_lo64_ofX]

end Sym

variable {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {isem : Sem}

include hp hc in
/-- **`load_ext_name name off dist`** (`is_pic` rules; the non-PIC rules fail). -/
theorem load_ext_name_ok (hR : Refines F isem) {sb : Nat} {syms : String → Option Nat}
    (hM : MemRefinesR Rd F sb syms isem) {n : Nat} (hn : 100 ≤ n) {nm : String} {off : Int} {dist : V}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 570 [.op (.extName nm), .int off, dist] s v s') :
    ∃ ms d, v = .reg (.vreg d .int) ∧ SymOk F isem syms s.1 s'.1 ms d nm off := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 570
  · mem_inv hp [] at hm he
    have h571 := ‹ApplyInternal _ _ _ _ 27 571 _ _ _ _›
    obtain ⟨rfl, hs⟩ := load_ext_name_got_ok hp ctx hc (by omega) h571
    simp only at hs
    subst hs
    exact ⟨_, _, by rw [fresh_fst], symOk_got hM _ nm⟩
  · mem_inv hp [] at hm he
  · mem_inv hp [] at hm he
  · mem_inv hp [] at hm he
    have h571 := ‹ApplyInternal _ _ _ _ 27 571 _ _ _ _›
    have h553 := ‹ApplyInternal _ _ _ _ 27 553 _ _ _ _›
    have h432 := ‹ApplyInternal _ _ _ _ 27 432 _ _ _ _›
    obtain ⟨rfl, hs⟩ := load_ext_name_got_ok hp ctx hc (by omega) h571
    obtain ⟨ms, d, rfl, hsh, hrun⟩ := imm64_inv hp ctx hc hR (by omega) h553
    obtain ⟨rfl, hs3⟩ := add64_inv hp ctx hc (by omega) h432
    simp only [fresh_fst] at h432 hs3 hs ⊢
    rw [hs] at hsh
    subst hs3
    refine ⟨_, _, rfl, symOk_add hM _ (addOk_add hR hsh ?_ fun ρ => ?_) ?_⟩
    · rw [nextVreg_fresh_emit]; omega
    · obtain ⟨ρ', X, h1, h2, h3, -⟩ := hrun ρ; exact ⟨ρ', X, h1, h2, h3⟩
    have := hsh.mono
    rw [nextVreg_fresh_emit] at this
    omega

end Backend.Proof
