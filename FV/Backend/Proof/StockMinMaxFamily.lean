module

public import FV.Backend.Proof.StockPopcountFamily
public import FV.Backend.Proof.StockMinMaxActualDispatch
public import FV.Backend.Proof.StockAvailableTypes

@[expose] public section

namespace Backend.Stock.Proof.MinMaxBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

abbrev operation := ScalarSelect.MinMaxRegisterFixture.minmaxOperation

def Family (inst : Clif.Inst) : Prop :=
  PopcountBody.Family inst ∨ ∃ unsigned maximum ty x y, inst = .binary (operation unsigned maximum) ty x y

theorem family_pure {inst : Clif.Inst} (family : Family inst) : pureInst inst = true := by
  rcases family with old | ⟨unsigned,maximum,ty,x,y,rfl⟩
  · exact PopcountBody.family_pure old
  · cases unsigned <;> cases maximum <;> rfl

theorem family_quiet {inst : Clif.Inst} (family : Family inst) : colored inst = false := by
  rcases family with old | ⟨unsigned,maximum,ty,x,y,rfl⟩
  · exact PopcountBody.family_quiet old
  · cases unsigned <;> cases maximum <;> rfl

theorem family_single {inst : Clif.Inst} (family : Family inst) (f : Clif.Function) :
    (inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·)).map List.length = some 1 := by
  rcases family with old | ⟨unsigned,maximum,ty,x,y,rfl⟩
  · exact PopcountBody.family_single old f
  · cases unsigned <;> cases maximum <;> rfl

theorem family_formats {inst : Clif.Inst} (family : Family inst) : CastBody.SafeFormat inst := by
  rcases family with old | ⟨unsigned,maximum,ty,x,y,rfl⟩
  · exact PopcountBody.family_formats old
  · cases unsigned <;> cases maximum <;> simp [CastBody.SafeFormat,instNames,operation,ScalarSelect.MinMaxRegisterFixture.minmaxOperation]

theorem minmax_inst_notrap {inst : Clif.Inst} (family : Family inst)
    (fr : Clif.Frame) (cm : Clif.Mem) (c : Clif.TrapCode) : Clif.evalInst fr cm inst ≠ .trap c := by
  rcases family with old | ⟨unsigned,maximum,ty,x,y,rfl⟩
  · exact PopcountBody.popcount_inst_notrap old fr cm c
  · cases unsigned <;> cases maximum
    all_goals
      cases getX : fr.getAs x ty with
      | trap code => exact False.elim (PureBody.frame_getAs_notrap fr x ty code getX)
      | stuck message => simp [Clif.evalInst,operation,ScalarSelect.MinMaxRegisterFixture.minmaxOperation,Clif.BinaryOp.isShift,getX]
      | ok u =>
        cases getY : fr.getAs y ty with
        | trap code => exact False.elim (PureBody.frame_getAs_notrap fr y ty code getY)
        | stuck message => simp [Clif.evalInst,operation,ScalarSelect.MinMaxRegisterFixture.minmaxOperation,Clif.BinaryOp.isShift,getX,getY]
        | ok v => simp [Clif.evalInst,operation,ScalarSelect.MinMaxRegisterFixture.minmaxOperation,Clif.BinaryOp.isShift,getX,getY]

theorem minmax_source_notrap {env : Clif.Env} {cp : Clif.Program} (fuel : Nat)
    (s : Clif.State) (callers : s.callers = []) (family : ∀ stm ∈ s.frame.body,Family stm.inst)
    {xs : List Nat} (ret : s.frame.term = .ret xs) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel s ≠ .trapped code := by
  apply PureBody.pure_source_notrap fuel s callers ?_ ret code
  intro stm member
  exact ⟨family_pure (family stm member),minmax_inst_notrap (family stm member)⟩
end Backend.Stock.Proof.MinMaxBody
