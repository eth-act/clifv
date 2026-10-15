import FV.Backend.Proof.StockSelectBooleanCompanion
import FV.Backend.Proof.StockSelectWitness
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- All scalar widths and every machine condition inhabit the actual660/659
calls used by the decoder-free observations. These remain helper witnesses;
complete retained source witnesses for all select forms are a separate obligation. -/
theorem stock_select_decoded_observation_witness (w : Nat)
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (condition : Cond) :
    ∃ ctx st mi out660 next660 trace660 out659 next659 trace659,
      ApplyInternal program (Stock.sem ctx) {} 999 22 660
        [.ty (.int w),.data 47 1 [mi],.data 96 condition.idx [],.value 7,.value 31]
        (st,#[]) out660 (next660,trace660) ∧
      ApplyInternal program (Stock.sem ctx) {} 999 22 659
        [.ty (.int w),.data 123 2 [.data 47 1 [mi],.data 96 condition.idx []],.value 7,.value 31]
        (st,#[]) out659 (next659,trace659) ∧
      ∃ m,MInst.ofV mi = some m ∧ DemandAllowed ctx st 7 ∧ DemandAllowed ctx (st.mark 7) 31 ∧
        ∃ rx ry,ctx.valueReg? 7 = some rx ∧ ctx.valueReg? 31 = some ry ∧
          out660 = .regs [(st.base.fresh .int).1] ∧ out659 = out660 ∧
          next660 = {(st.mark 7).mark 31 with base := (((st.base.fresh .int).2.emit m).emit
            (.csel (st.base.fresh .int).1 rx ry condition))} ∧ next659 = next660 := by
  obtain ⟨_,⟨out660,next660,trace660,run660⟩,⟨out659,next659,trace659,run659⟩⟩ :=
    Witness.stock_select_flags_helper_witness w width condition
  obtain ⟨m,decoded,safeX,safeY,rx,ry,mapX,mapY,result660,state660⟩ :=
    stock_select_cond_decoded_observed data_program _ rfl (by decide) width condition run660
  obtain ⟨m',decoded',_,_,rx',ry',mapX',mapY',result659,state659⟩ :=
    stock_select_flags_decoded_observed data_program _ rfl (by decide) width condition run659
  have sameM : m' = m := Option.some.inj (decoded'.symm.trans decoded)
  have sameX : rx' = rx := Option.some.inj (mapX'.symm.trans mapX)
  have sameY : ry' = ry := Option.some.inj (mapY'.symm.trans mapY)
  subst m'; subst rx'; subst ry'
  exact ⟨_,_,_,out660,next660,trace660,out659,next659,trace659,run660,run659,m,decoded,
    safeX,safeY,rx,ry,mapX,mapY,result660,result659.trans result660.symm,state660,state659.trans state660.symm⟩
/-- The same real scalar select calls inhabit the boolean-companion theorem,
with its exact fresh result and complete original/companion states. -/
theorem stock_select_boolean_companion_witness (w : Nat)
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (condition : Cond) :
    ∃ ctx st mi out next trace m rx ry booleanTrace,
      ApplyInternal program (Stock.sem ctx) {} 999 22 659
        [.ty (.int w),.data 123 2 [.data 47 1 [mi],.data 96 condition.idx []],.value 7,.value 31]
        (st,#[]) out (next,trace) ∧ MInst.ofV mi = some m ∧
      ctx.valueReg? 7 = some rx ∧ ctx.valueReg? 31 = some ry ∧ out = .regs [(st.base.fresh .int).1] ∧
      next = {(st.mark 7).mark 31 with base := (((st.base.fresh .int).2.emit m).emit
        (.csel (st.base.fresh .int).1 rx ry condition))} ∧
      ApplyInternal program (Stock.sem ctx) {} 119 27 715
        [.data 123 2 [.data 47 1 [mi],.data 96 condition.idx []]] (st,#[]) (.reg (st.base.fresh .int).1)
        ({st with base := (((st.base.fresh .int).2.emit m).emit
          (.cset (st.base.fresh .int).1 condition))},booleanTrace) := by
  obtain ⟨_,_,⟨out,next,trace,run⟩⟩ := Witness.stock_select_flags_helper_witness w width condition
  obtain ⟨m,rx,ry,decoded,_,_,mapX,mapY,output,finish,booleanTrace,booleanRun⟩ :=
    stock_select_flags_boolean_companion data_program _ rfl (by decide) width condition run
  exact ⟨_,_,_,out,next,trace,m,rx,ry,booleanTrace,run,decoded,mapX,mapY,output,finish,booleanRun⟩
end Backend.Stock.Proof.ScalarSelect
