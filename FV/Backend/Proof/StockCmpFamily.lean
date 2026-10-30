import FV.Backend.Proof.StockMinMaxFamily
import FV.Backend.Proof.StockCastDispatch
namespace Backend.Stock.Proof.CmpBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

def Family (inst : Clif.Inst) : Prop :=
  MinMaxBody.Family inst ∨ ∃ cc ty x y,inst = .icmp cc ty x y

theorem family_pure {inst : Clif.Inst} (family : Family inst) : pureInst inst = true := by
  rcases family with old | ⟨cc,ty,x,y,rfl⟩
  · exact MinMaxBody.family_pure old
  · rfl

theorem family_quiet {inst : Clif.Inst} (family : Family inst) : colored inst = false := by
  rcases family with old | ⟨cc,ty,x,y,rfl⟩
  · exact MinMaxBody.family_quiet old
  · rfl

theorem family_single {inst : Clif.Inst} (family : Family inst) (f : Clif.Function) :
    (inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·)).map List.length = some 1 := by
  rcases family with old | ⟨cc,ty,x,y,rfl⟩
  · exact MinMaxBody.family_single old f
  · rfl

theorem family_formats {inst : Clif.Inst} (family : Family inst) : CastComplete.MemoryFormat inst := by
  rcases family with old | ⟨cc,ty,x,y,rfl⟩
  · have safe := MinMaxBody.family_formats old
    exact ⟨safe.1,safe.2.1⟩
  · simp [CastComplete.MemoryFormat,instNames]

theorem cmp_inst_notrap {inst : Clif.Inst} (family : Family inst)
    (fr : Clif.Frame) (cm : Clif.Mem) (c : Clif.TrapCode) : Clif.evalInst fr cm inst ≠ .trap c := by
  rcases family with old | ⟨cc,ty,x,y,rfl⟩
  · exact MinMaxBody.minmax_inst_notrap old fr cm c
  · cases getX : fr.getAs x ty with
    | trap code => exact False.elim (PureBody.frame_getAs_notrap fr x ty code getX)
    | stuck message => simp [Clif.evalInst,getX]
    | ok u =>
      cases getY : fr.getAs y ty with
      | trap code => exact False.elim (PureBody.frame_getAs_notrap fr y ty code getY)
      | stuck message => simp [Clif.evalInst,getX,getY]
      | ok v => simp [Clif.evalInst,getX,getY]

theorem cmp_source_notrap {env : Clif.Env} {cp : Clif.Program} (fuel : Nat)
    (s : Clif.State) (callers : s.callers = []) (family : ∀ stm ∈ s.frame.body,Family stm.inst)
    {xs : List Nat} (ret : s.frame.term = .ret xs) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel s ≠ .trapped code := by
  apply PureBody.pure_source_notrap fuel s callers ?_ ret code
  intro stm member
  exact ⟨family_pure (family stm member),cmp_inst_notrap (family stm member)⟩
end Backend.Stock.Proof.CmpBody
