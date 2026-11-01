import FV.Backend.Proof.StockMemorySretCopyClass
import FV.Backend.Proof.StockMemoryABIContract
import FV.Backend.Proof.StockMemoryCfgNotrap

namespace Backend.Stock.Memory.SretCopy
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Original source syntax derives both complete return and trap obligations for the sret copy. -/
theorem CfgClass.domainABI {f : Clif.Function} (source : CfgClass f) : DomainABI f := by
  obtain ⟨entry,middle,target,i0,i8,j0,j8,base,destination,low,high,lf0,lf8,sf0,sf8,
    blocks,jump0,jump1,ret,entryMiddle,entryTarget,middleTarget,entryNops,targetNops,
    loadLow,loadHigh,storeLow,storeHigh,lowEarlier,highEarlier,shape,
    baseParameter,destinationParameter,ln0,ln8,sn0,sn8⟩ := source.shape
  refine ⟨source.scope,source.dominated,source.abi,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable memoryOk w memory arguments
    exact sret_copy_return_function run source.scope source.dominated source.abi
      blocks jump0 jump1 ret rfl rfl entryMiddle entryTarget middleTarget entryNops targetNops
      loadLow loadHigh storeLow storeHigh lowEarlier highEarlier shape baseParameter destinationParameter
      ln0 ln8 sn0 sn8 entered returned refines driver memorySem stable memoryOk memory arguments
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable memoryOk w memory arguments
    have nop (stm : Clif.Stmt) (same : stm.inst = .nop) : OrdinaryBody.OrdinaryInst stm.inst ∧
        ∀ fr cm c,Clif.evalInst fr cm stm.inst ≠ .trap c := by
      rw [same]
      refine ⟨by simp [OrdinaryBody.OrdinaryInst],?_⟩
      intro fr cm c impossible
      cases impossible
    have family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst ∧
        ∀ fr cm c,Clif.evalInst fr cm stm.inst ≠ .trap c := by
      intro b member stm present
      have which : b = entry ∨ b = middle ∨ b = target := by simpa [blocks] using member
      rcases which with rfl | rfl | rfl
      · exact nop stm (entryNops stm present)
      · obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp present
        rcases shape j stm found with selected | selected | selected | selected | isNop
        · subst j
          have same := Option.some.inj (found.symm.trans loadLow)
          subst stm
          exact ⟨by simp [OrdinaryBody.OrdinaryInst],fun fr cm c => Clif.evalInst_notrap rfl ln0 c⟩
        · subst j
          have same := Option.some.inj (found.symm.trans loadHigh)
          subst stm
          exact ⟨by simp [OrdinaryBody.OrdinaryInst],fun fr cm c => Clif.evalInst_notrap rfl ln8 c⟩
        · subst j
          have same := Option.some.inj (found.symm.trans storeLow)
          subst stm
          exact ⟨by simp [OrdinaryBody.OrdinaryInst],fun fr cm c => Clif.evalInst_notrap rfl sn0 c⟩
        · subst j
          have same := Option.some.inj (found.symm.trans storeHigh)
          subst stm
          exact ⟨by simp [OrdinaryBody.OrdinaryInst],fun fr cm c => Clif.evalInst_notrap rfl sn8 c⟩
        · exact nop stm isNop
      · exact nop stm (targetNops stm present)
    have terms : ∀ b ∈ f.blocks,(∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) := by
      intro b member
      have which : b = entry ∨ b = middle ∨ b = target := by simpa [blocks] using member
      rcases which with rfl | rfl | rfl
      · exact .inl ⟨_,jump0⟩
      · exact .inl ⟨_,jump1⟩
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
    have initialTerm : (∃ bc,fr.term = .jump bc) ∨ (∃ xs,fr.term = .ret xs) :=
      .inl ⟨_,by rw [frame]; exact jump0⟩
    exact False.elim ((OrdinaryCfg.ordinary_jump_return_notrap family terms fuel ⟨fr,[],cm⟩
      (by rw [frame]) rfl initialBody initialTerm code) trapped)

end Backend.Stock.Memory.SretCopy
