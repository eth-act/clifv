import FV.Backend.Proof.StockMemoryStoreNopTwoBlockReturn
import FV.Backend.Proof.StockMemoryCfgNotrap

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original source syntax derives the complete return-and-trap contract across the jump. -/
theorem domain_of_two_block_nop_store_return (kind : Kind) (ty : Clif.Ty) {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    {entry target : Clif.Block} (blocks : f.blocks = [entry,target])
    (nops : ∀ stm ∈ entry.body,stm.inst = .nop) (jump : entry.term = .jump ⟨target.id,[]⟩)
    {storeIndex value pointer : Nat} {flags : Clif.MemFlags} {valueTy : Clif.Ty}
    (statement : target.body[storeIndex]? = some ⟨[],.store kind.sourceOp ty flags value pointer 0⟩)
    (shape : ∀ j stm,target.body[j]? = some stm → j = storeIndex ∨ stm.inst = .nop)
    (ret : target.term = .ret []) (parameter : pointer ∈ entry.params.map (·.1))
    (valueParameter : (value,valueTy) ∈ entry.params)
    (width : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits)
    (notrap : flags.trapCode = none) : Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable memoryOk w memory arguments
    refine ⟨entrySeed result.ctx fr,?_⟩
    exact two_block_nop_store_return_function kind ty run scope dominated abi blocks nops jump
      statement shape ret parameter valueParameter width entered refines driver memorySem stable memoryOk
      returned memory arguments
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable memoryOk w memory arguments
    have family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst ∧
        ∀ fr cm c,Clif.evalInst fr cm stm.inst ≠ .trap c := by
      intro b member stm present
      have which : b = entry ∨ b = target := by simpa [blocks] using member
      rcases which with same | same
      · subst b
        rw [nops stm present]
        refine ⟨by simp [OrdinaryBody.OrdinaryInst],?_⟩
        intro fr cm c impossible
        cases impossible
      · subst b
        obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp present
        rcases shape j stm found with selected | nop
        · subst j
          have equal := Option.some.inj (found.symm.trans statement)
          subst stm
          refine ⟨by simp [OrdinaryBody.OrdinaryInst],?_⟩
          intro fr cm c
          exact Clif.evalInst_notrap rfl notrap c
        · rw [nop]
          refine ⟨by simp [OrdinaryBody.OrdinaryInst],?_⟩
          intro fr cm c impossible
          cases impossible
    have terms : ∀ b ∈ f.blocks,(∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) := by
      intro b member
      have which : b = entry ∨ b = target := by simpa [blocks] using member
      rcases which with rfl | rfl
      · exact .inl ⟨_,jump⟩
      · exact .inr ⟨_,ret⟩
    obtain ⟨original,regs,lookup,argTypes,paramTypes,set,frame⟩ := entered
    have same : original = entry := by
      have found : some entry = some original := by
        simpa only [Clif.Function.entry?,blocks,List.head?_cons] using lookup
      exact Option.some.inj found.symm
    subst original
    have initialBody : ∀ stm ∈ fr.body,OrdinaryBody.OrdinaryInst stm.inst ∧
        ∀ fr cm c,Clif.evalInst fr cm stm.inst ≠ .trap c := by
      intro stm member
      apply family entry (by simp [blocks]) stm
      rw [frame] at member
      exact member
    have initialTerm : (∃ bc,fr.term = .jump bc) ∨ (∃ xs,fr.term = .ret xs) := by
      exact .inl ⟨_,by rw [frame]; exact jump⟩
    exact False.elim ((OrdinaryCfg.ordinary_jump_return_notrap family terms fuel ⟨fr,[],cm⟩
      (by rw [frame]) rfl initialBody initialTerm code) trapped)

end Backend.Stock.Memory.StoreRoots
