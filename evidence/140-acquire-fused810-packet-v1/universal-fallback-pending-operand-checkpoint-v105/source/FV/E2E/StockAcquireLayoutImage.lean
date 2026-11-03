import FV.E2E.StockAcquireTwoLoadModelStepF

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Layout places every byte of an instruction or data word inside the actual binary word array. -/
theorem layout_line_byte_bound {fa : FnAsm} {fb : FnBin} {line : Line} {j i : Nat}
    (layout : fa.layout = .ok fb) (located : fa.lines.toList[j]? = some line)
    (code : line.isLabel = false) (byte : i < 4) :
    lineOffset fa.lines.toList j + i < 4 * fb.words.size := by
  obtain ⟨labels, labelMap⟩ := FnAsm.layout_labelOffsets layout
  obtain ⟨aligned, word, _, present⟩ := FnAsm.layout_word layout labelMap located code
  have bound := (Array.getElem?_eq_some_iff.1 present).1
  omega

/-- A checked byte image supplies the actual table-image condition through layout alone. -/
theorem layout_table_image {fa : FnAsm} {fb : FnBin} {base : BitVec 64}
    {codeImage : BitVec 64 → Prop} (layout : fa.layout = .ok fb)
    (bytes : ∀ offset < 4 * fb.words.size, codeImage (base + BitVec.ofNat 64 offset)) :
    ∀ j target origin, fa.lines.toList[j]? = some (.word target origin) →
      ∀ i < 4, codeImage (base + BitVec.ofNat 64 (lineOffset fa.lines.toList j) + BitVec.ofNat 64 i) := by
  intro j target origin located i byte
  have inside := layout_line_byte_bound layout located rfl byte
  have included := bytes (lineOffset fa.lines.toList j + i) inside
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using included

/-- Actual layout gives code-address membership without an extra bounds certificate. -/
theorem layout_line_codeAddr {fa : FnAsm} {fb : FnBin} {base : BitVec 64}
    {line : Line} {j i : Nat} (layout : fa.layout = .ok fb)
    (located : fa.lines.toList[j]? = some line) (code : line.isLabel = false) (byte : i < 4) :
    CodeAddr (Arm.set_program Arm.ArmState.default (fb.program base))
      (base + BitVec.ofNat 64 (lineOffset fa.lines.toList j) + BitVec.ofNat 64 i) := by
  obtain ⟨labels, labelMap⟩ := FnAsm.layout_labelOffsets layout
  obtain ⟨aligned, word, _, present⟩ := FnAsm.layout_word layout labelMap located code
  have address := codeAddr_word (base := base) (s := Arm.set_program Arm.ArmState.default (fb.program base))
    rfl present byte
  have offset : 4 * (lineOffset fa.lines.toList j / 4) = lineOffset fa.lines.toList j := by omega
  rwa [offset] at address

/-- The original linker code-address field supplies the table-image condition. -/
theorem layout_table_image_of_codeAddr {fa : FnAsm} {fb : FnBin} {base : BitVec 64}
    {codeImage : BitVec 64 → Prop} (layout : fa.layout = .ok fb)
    (addresses : ∀ a, CodeAddr (Arm.set_program Arm.ArmState.default (fb.program base)) a → codeImage a) :
    ∀ j target origin, fa.lines.toList[j]? = some (.word target origin) →
      ∀ i < 4, codeImage (base + BitVec.ofNat 64 (lineOffset fa.lines.toList j) + BitVec.ofNat 64 i) := by
  intro j target origin located i byte
  exact addresses _ (layout_line_codeAddr layout located rfl byte)

end E2E.StockAcquirePending
