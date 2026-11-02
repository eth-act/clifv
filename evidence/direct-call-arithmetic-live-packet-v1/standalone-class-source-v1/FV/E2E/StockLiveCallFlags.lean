import FV.Backend.StockLiveCallCheck

namespace Backend.Stock.LiveCall
set_option autoImplicit false
set_option Elab.async false

theorem checked_instruction {sig : Clif.Signature} {vc : VCode}
    (checked : codeCheck sig vc = true) {b pc : Nat} {block : VBlock} {inst : MInst}
    (placed : vc.blocks[b]? = some block) (found : block.insts[pc]? = some inst) :
    instruction sig b pc inst = true := by
  have bm : (block,b) ∈ vc.blocks.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using placed)
  have im : (inst,pc) ∈ block.insts.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using found)
  exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked (block,b) bm)).2 (inst,pc) im

theorem noTls_of_codeCheck {sig : Clif.Signature} {vc : VCode}
    (checked : codeCheck sig vc = true) : vc.hasTls = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  simp only [VCode.hasTls,Array.any_eq_true] at present
  obtain ⟨b,hb,pc,hpc,flag⟩ := present
  generalize atInst : vc.blocks[b].insts[pc] = inst at flag
  cases inst <;> try cases flag
  rename_i name rd temp
  have found := checked_instruction checked
    (Array.getElem?_eq_some_iff.mpr ⟨hb,rfl⟩)
    (Array.getElem?_eq_some_iff.mpr ⟨hpc,atInst⟩)
  change false = true at found
  cases found

theorem noTryCall_of_codeCheck {sig : Clif.Signature} {vc : VCode}
    (checked : codeCheck sig vc = true) : vc.hasTryCall = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  simp only [VCode.hasTryCall,Array.any_eq_true] at present
  obtain ⟨b,hb,pc,hpc,flag⟩ := present
  generalize atInst : vc.blocks[b].insts[pc] = inst at flag
  cases inst <;> try cases flag
  rename_i info ti
  have found := checked_instruction checked
    (Array.getElem?_eq_some_iff.mpr ⟨hb,rfl⟩)
    (Array.getElem?_eq_some_iff.mpr ⟨hpc,atInst⟩)
  change false = true at found
  cases found

end Backend.Stock.LiveCall
