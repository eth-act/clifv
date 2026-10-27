import FV.Backend.Proof.StockMemoryReturnBody
import FV.Backend.Proof.StockMemoryReturnRefines
import FV.Backend.Proof.StockMemoryNotrap
import FV.Backend.Proof.StockMemoryContract

namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The original source-only single-load return class satisfies the complete
memory-capable entry/return/trap contract. Actual record retention, selected load,
result aliases, body execution and ABI entry/return are all derived internally.
The original memory/world relation supplies validity; no source certificate or
new initial heap condition is added. -/
theorem domain_of_single_load_return {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    {b : Clif.Block} (blocks : f.blocks = [b]) {x z : Nat} {flags : Clif.MemFlags}
    (singleton : b.body = [⟨[z],.load .load .i32 flags x 0⟩])
    (ret : b.term = .ret [z]) (parameter : x ∈ b.params.map (·.1))
    (notrap : flags.trapCode = none) : Domain f := by
  have family : ∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst := by
    intro stm member
    have same : stm = ⟨[z],.load .load .i32 flags x 0⟩ := by simpa only [singleton,List.mem_singleton] using member
    subst stm
    constructor
    · intro fn args impossible; cases impossible
    · intro sig callee args impossible; cases impossible
  have entryBlock : f.blocks[0]? = some b := by simp [blocks]
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable memoryOk w memory arguments
    apply OrdinaryBody.actual_ordinary_entry_return_refines_frame run scope dominated abi blocks family ret
      entered returned refines driver memorySem stable ?_ memory arguments
    intro event events
    obtain ⟨b',term,body,split⟩ := stock_lower_body_scan_split run scope events
    have bound : event.block < 1 := by have h := lt_of_getElem? split.block; simpa [blocks] using h
    have zero : event.block = 0 := by omega
    have actualBlock : f.blocks[event.block]? = some b := by rw [zero]; exact entryBlock
    exact stock_single_load_return_body run scope dominated events actualBlock singleton ret entryBlock parameter
      stable memorySem memoryOk
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable memoryOk w memory arguments
    obtain ⟨b',regs,entry,argTypes,paramTypes,set,frame⟩ := entered
    have sameBlock : b' = b := by
      have found : some b = some b' := by simpa only [Clif.Function.entry?,blocks,List.head?_cons] using entry
      exact Option.some.inj found.symm
    subst b'
    have sourceFamily : ∀ stm ∈ fr.body,OrdinaryBody.OrdinaryInst stm.inst ∧
        ∀ fr cm c,Clif.evalInst fr cm stm.inst ≠ .trap c := by
      intro stm member
      have present : stm ∈ b.body := by rw [frame] at member; exact member
      refine ⟨family stm present,?_⟩
      have same : stm = ⟨[z],.load .load .i32 flags x 0⟩ := by simpa only [singleton,List.mem_singleton] using present
      subst stm
      intro fr cm c
      exact Clif.evalInst_notrap rfl notrap c
    exact False.elim ((OrdinaryBody.ordinary_source_notrap fuel ⟨fr,[],cm⟩ rfl sourceFamily
      (by rw [frame]; exact ret) code) trapped)

end Backend.Stock.Memory
