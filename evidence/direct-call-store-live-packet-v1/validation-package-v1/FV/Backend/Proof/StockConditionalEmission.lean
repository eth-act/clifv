import FV.Backend.Proof.StockConditionalValues

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program

/-- Decoded actual conditional code. This is derived from helper execution,
rather than supplied as an accepted-program certificate. -/
inductive BranchCode (yes no : Label) : V → List MInst → Prop where
  | zero (key index : Nat) (size : OperandSize) (decoded : OperandSize.ofIdx? index = some size) :
      BranchCode yes no (.data 123 0 [.reg (.vreg key .int),.data 93 index []])
        [.condBr yes no (.zero (.vreg key .int) size)]
  | nonzero (key index : Nat) (size : OperandSize) (decoded : OperandSize.ofIdx? index = some size) :
      BranchCode yes no (.data 123 1 [.reg (.vreg key .int),.data 93 index []])
        [.condBr yes no (.notZero (.vreg key .int) size)]
  | flags (raw : V) (producer : MInst) (condition : Cond) (decoded : MInst.ofV raw = some producer)
      (notAl : condition ≠ .al) (notNv : condition ≠ .nv) (noDefs : vdefs producer = []) :
      BranchCode yes no (.data 123 2 [.data 47 1 [raw],.data 96 condition.idx []])
        [producer,.condBr yes no (.cond condition)]

/-- Actual descriptor construction and emission derive the entire appended
branch fragment, including its flag producer. No prefix or earlier compiler
state is discarded and no emitted-code equality is assumed. -/
theorem descriptor_emits {ctx : Ctx} {cfg : Config} (overlap : cfg.checkOverlap = false)
    {constructFuel emitFuel : Nat} (enoughConstruct : 100 ≤ constructFuel) (enoughEmit : 30 ≤ emitFuel)
    {raw descriptor out : V} {P : Nat → Prop} (shape : CondShape raw P) {yes no : Label}
    {before middle next : State} {trace constructTrace final : Array RuleId}
    (construct : ApplyInternal program (Stock.sem ctx) cfg constructFuel 46 722
      [raw,.label yes,.label no] (before,trace) descriptor (middle,constructTrace))
    (emit : ApplyInternal program (Stock.sem ctx) cfg emitFuel 13 242
      [descriptor] (middle,constructTrace) out (next,final)) :
    ∃ code,BranchCode yes no raw code ∧ Frag before.base next.base code := by
  obtain ⟨base,descriptorEq⟩ := descriptor_shape overlap enoughConstruct shape construct
  have projected := BranchHelpers.stock_emit_side_effect_projects ctx cfg overlap (emitFuel+1)
    [descriptor] middle constructTrace
  have legacy : ApplyInternal program (Backend.sem ctx) cfg emitFuel 13 242
      [descriptor] (middle.base,constructTrace) out (next.base,final) := by
    unfold ApplyInternal at emit ⊢
    rw [emit] at projected
    exact projected.symm
  rw [base,descriptorEq] at legacy
  rcases shape with ⟨key,index,size,rfl,decoded,_⟩ | ⟨key,index,size,rfl,decoded,_⟩ |
    ⟨raw,producer,condition,rfl,decoded,notAl,notNv,noDefs,_⟩
  · obtain ⟨inst,decodedInst,finish,_⟩ := emit_side_effect_inst_ok data_program overlap enoughEmit legacy
    rw [ofV_condBr_zero decoded] at decodedInst
    cases decodedInst
    refine ⟨_,BranchCode.zero key index size decoded,?_⟩
    dsimp only at finish
    rw [finish]
    exact Frag.emit_nodef _ rfl
  · obtain ⟨inst,decodedInst,finish,_⟩ := emit_side_effect_inst_ok data_program overlap enoughEmit legacy
    rw [ofV_condBr_notZero decoded] at decodedInst
    cases decodedInst
    refine ⟨_,BranchCode.nonzero key index size decoded,?_⟩
    dsimp only at finish
    rw [finish]
    exact Frag.emit_nodef _ rfl
  · obtain ⟨first,last,finish,decodedFirst,decodedLast⟩ := emit_side_effect_inst2_ok data_program overlap enoughEmit legacy
    rw [decoded] at decodedFirst
    cases decodedFirst
    rw [ofV_condBr_cond] at decodedLast
    cases decodedLast
    refine ⟨_,BranchCode.flags raw producer condition decoded notAl notNv noDefs,?_⟩
    dsimp only at finish
    rw [finish]
    exact (Frag.emit_nodef _ noDefs).append (Frag.emit_nodef _ rfl)

end Backend.Stock.Proof.ConditionalValues
