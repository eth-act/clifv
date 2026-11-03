import FV.E2E.ActualBinCheck
import FV.Backend.Proof.EncodeLayout

namespace E2E.StockAcquirePending
open Backend Backend.Proof E2E.LinkCheck E2E.BinCheck Elf
set_option autoImplicit false
set_option Elab.async false

/-- The original binary contract names the artifact from the actual result table. -/
theorem actual_result_art_ok {I : LinkInput} {results : Res} {data : List Clif.DataObject} {file : ByteArray}
    (checked : BinOkWithResults I results data file)
    (names : ((progOf results).funcs.map (·.name)).Nodup)
    {f : Clif.Function} (member : f ∈ (progOf results).funcs) : ArtOk I file (artOf results f) := by
  exact checked.code _ (tab_mem names member)

/-- An actual artifact without relocations reads its exact compiled words from the ELF image. -/
theorem actual_result_ELF_plain_word {I : LinkInput} {results : Res} {data : List Clif.DataObject} {file : ByteArray}
    (checked : BinOkWithResults I results data file)
    (names : ((progOf results).funcs.map (·.name)).Nodup)
    {f : Clif.Function} (member : f ∈ (progOf results).funcs)
    (noRelocs : (artOf results f).fb.relocs = []) {index : Nat} {word : BitVec 32}
    (present : (artOf results f).fb.words[index]? = some word) :
    readN (loadMem file) 4 (wAt (artOf results f) (4 * index)) = some word := by
  apply (actual_result_art_ok checked names member).plain index word present
  intro relocation recorded
  rw [noRelocs] at recorded
  cases recorded

/-- Layout and the original ELF checks derive the exact instruction word and decoder result. -/
theorem actual_result_ELF_line_decode {I : LinkInput} {results : Res} {data : List Clif.DataObject} {file : ByteArray}
    (checked : BinOkWithResults I results data file)
    (names : ((progOf results).funcs.map (·.name)).Nodup)
    {f : Clif.Function} (member : f ∈ (progOf results).funcs)
    (layout : (artOf results f).fa.layout = .ok (artOf results f).fb)
    (noRelocs : (artOf results f).fb.relocs = [])
    {j : Nat} {inst : Insn} {trap : Option Clif.TrapCode}
    (located : (artOf results f).fa.lines.toList[j]? = some (.ins inst trap)) :
    ∃ (labels : Std.HashMap Lbl Nat) (word : BitVec 32) (decoded : Arm.ArmInst),
      labelOffsets (artOf results f).fa.lines = .ok labels ∧
      inst.encode ⟨lineOffset (artOf results f).fa.lines.toList j,(labels[·]?)⟩ = .ok word ∧
      readN (loadMem file) 4 (wAt (artOf results f) (lineOffset (artOf results f).fa.lines.toList j)) = some word ∧
      inst.toArmInst ⟨lineOffset (artOf results f).fa.lines.toList j,(labels[·]?)⟩ = .ok decoded ∧
      Arm.decode_raw_inst word = some decoded := by
  obtain ⟨labels,labelMap⟩ := FnAsm.layout_labelOffsets layout
  obtain ⟨aligned,word,encoded,present⟩ := FnAsm.layout_word layout labelMap located rfl
  obtain ⟨decoded,semantic,bits⟩ := Insn.decode_encode encoded
  have bytes := actual_result_ELF_plain_word checked names member noRelocs present
  rw [show 4 * (lineOffset (artOf results f).fa.lines.toList j / 4) =
    lineOffset (artOf results f).fa.lines.toList j by omega] at bytes
  exact ⟨labels,word,decoded,labelMap,encoded,bytes,semantic,bits⟩

end E2E.StockAcquirePending
