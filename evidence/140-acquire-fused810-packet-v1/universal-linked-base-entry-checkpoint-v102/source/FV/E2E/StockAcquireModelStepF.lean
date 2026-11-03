import FV.E2E.StockAcquireLinkedAccessPermissions

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Checked layout and the actual model program derive the fetched word and decoded instruction. -/
theorem layout_decode_at_line {fa : FnAsm} {fb : FnBin} {labels : Std.HashMap Lbl Nat}
    {base : BitVec 64} {state : Arm.ArmState} {j : Nat} {inst : Insn} {trap : Option Clif.TrapCode}
    (layout : fa.layout = .ok fb) (labelMap : labelOffsets fa.lines = .ok labels)
    (fits : 4*fb.words.size ≤ 2^64) (located : fa.lines.toList[j]? = some (.ins inst trap))
    (program : state.program = fb.program base)
    (pc : Arm.r .PC state = base+BitVec.ofNat 64 (lineOffset fa.lines.toList j)) :
    ∃ (word : BitVec 32) (decoded : Arm.ArmInst),Arm.fetch_inst (Arm.r .PC state) state = some word ∧
      inst.toArmInst ⟨lineOffset fa.lines.toList j,(labels[·]?)⟩ = .ok decoded ∧
      Concurrency.ArmFoot.decodeAt state = some decoded := by
  obtain ⟨aligned,word,encoded,present⟩ := FnAsm.layout_word layout labelMap located rfl
  have fetched : Arm.fetch_inst (Arm.r .PC state) state = some word := by
    rw [Arm.fetch_inst_from_program,program,pc]
    have actual := FnBin.program_find (base := base) fits present
    rwa [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero aligned)] at actual
  obtain ⟨decoded,semantic,bits⟩ := Insn.decode_encode encoded
  refine ⟨word,decoded,fetched,semantic,?_⟩
  simp only [Concurrency.ArmFoot.decodeAt,fetched]
  exact bits

/-- Internal image permissions and an unhooked actual line identify the fault-aware model step.
ELF relocation and the final executable's program remain a separate correspondence obligation. -/
theorem goodAtW_stepF_eq_mach (L : LinkSys) {M : Nat} {g : Clif.Function} {initial state : Arm.ArmState}
    {mp : ArmFault.MemMap} {codeImage : BitVec 64 → Prop} (good : L.GoodAtW M g initial state)
    (layout : (L.A g).fa.layout = .ok (L.A g).fb) (fits : 4*(L.A g).fb.words.size ≤ 2^64)
    (kept : ∀ a,(mp a).allows .W = false → L.Img a)
    (readable : ∀ a,codeImage a → (mp a).allows .R = true)
    (tableImage : ∀ j tag bytes,(L.A g).fa.lines.toList[j]? = some (.word tag bytes) →
      ∀ i < 4,codeImage ((L.A g).base+BitVec.ofNat 64 (lineOffset (L.A g).fa.lines.toList j)+BitVec.ofNat 64 i))
    (unhooked : ∀ (j : Nat) (inst : Insn) (trap : Option Clif.TrapCode),(L.A g).fa.lines.toList[j]? = some (.ins inst trap) → inst.hooked = false) :
    ArmFault.stepF mp state = L.mach M g state := by
  have originalGood := good
  obtain ⟨X,K,G,gv,machine,actual,image,imageMem,blr⟩ := good
  obtain ⟨inst,⟨j,trap,located,pc⟩,tail⟩ := actual.1.line
  obtain ⟨labels,labelMap⟩ := FnAsm.layout_labelOffsets layout
  obtain ⟨word,decoded,fetched,semantic,decode⟩ := layout_decode_at_line layout labelMap fits located actual.1.prog pc
  have allowed := L.goodAtW_access_allowed_code_image originalGood kept readable tableImage located pc
    (unhooked j inst trap located) semantic
  obtain ⟨actualDecoded,actualSemantic,executed⟩ := armStepX_ins (X := X) (H := L.hooks M)
    layout labelMap fits located (unhooked j inst trap located) actual.1.prog pc actual.1.err
  have equal := Except.ok.inj (actualSemantic.symm.trans semantic)
  subst actualDecoded
  calc
    ArmFault.stepF mp state = Arm.exec_inst decoded state := by
      rw [ArmFault.stepF_eq_execF actual.1.err decode,ArmFault.execF_of_ok allowed]
    _ = ArmStepX X (L.hooks M) (L.A g).fa state := executed.symm
    _ = L.mach M g state := congrFun machine state

end E2E.StockAcquirePending
