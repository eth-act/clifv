import FV.E2E.StockLiveCallLayout
import FV.E2E.StockVoidCallEntry

namespace Backend.Stock.LiveCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false

theorem callB_false {inst : MInst} (noCall : ∀ info,inst ≠ .call info) : callB inst = false := by
  cases inst <;> try rfl
  exact False.elim (noCall _ rfl)

/-- Actual prefix admission derives every original ABI-read obligation before the call. -/
theorem prefixReads_of_append {sig : Clif.Signature} {block start : Nat}
    {prelude suffix : List MInst}
    (checked : prefixReads sig block start (prelude ++ suffix) = true)
    (noCalls : ∀ inst ∈ prelude,∀ info,inst ≠ .call info) :
    ∀ j inst,prelude[j]? = some inst → Backend.ABIReadOnly.instruction sig block (start+j) inst = true := by
  induction prelude generalizing start with
  | nil => intro j inst found; simp at found
  | cons head rest ih =>
    have headNoCall := callB_false (noCalls head (by simp))
    simp only [List.cons_append,prefixReads,headNoCall,Bool.false_eq_true,↓reduceIte,Bool.and_eq_true] at checked
    intro j inst found
    cases j with
    | zero =>
      have same : head = inst := Option.some.inj found
      subst inst
      simpa only [Nat.add_zero] using checked.1
    | succ j =>
      have tail : rest[j]? = some inst := found
      have result := ih checked.2 (fun i member => noCalls i (by simp [member])) j inst tail
      simpa only [Nat.add_assoc,Nat.add_comm 1 j] using result

/-- Whole-code checks imply the exact prelude obligations used by the existing world transport. -/
theorem prelude_read_checks {sig : Clif.Signature} {vc : VCode}
    (checked : codeCheck sig vc = true) {block : VBlock} (placed : vc.blocks[0]? = some block)
    {prelude body : Array MInst} (pieces : block.insts = prelude ++ body)
    (noCalls : ∀ inst ∈ prelude.toList,∀ info,inst ≠ .call info) :
    ∀ j inst,prelude.toList[j]? = some inst → Backend.ABIReadOnly.instruction sig 0 j inst = true := by
  have blockMember : (block,0) ∈ vc.blocks.toList.zipIdx := by
    exact List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using placed)
  have admitted := List.all_eq_true.mp checked (block,0) blockMember
  have prefix : prefixReads sig 0 0 (prelude.toList ++ body.toList) = true := by
    have first := Bool.and_eq_true_iff.mp admitted
    simpa only [pieces,Array.toList_append] using first.1
  simpa only [Nat.zero_add] using prefixReads_of_append prefix noCalls

end Backend.Stock.LiveCall
