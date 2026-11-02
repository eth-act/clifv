import FV.Backend.Proof.StockBitFamily
namespace Backend.Stock.Proof.PopcountBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

def Family (inst : Clif.Inst) : Prop :=
  BitBody.Family inst ∨ ∃ ty x, inst = .unary .popcnt ty x

theorem family_pure {inst : Clif.Inst} (family : Family inst) : pureInst inst = true := by
  rcases family with old | ⟨ty,x,rfl⟩
  · exact BitBody.family_pure old
  · rfl

theorem family_quiet {inst : Clif.Inst} (family : Family inst) : colored inst = false := by
  rcases family with old | ⟨ty,x,rfl⟩
  · exact BitBody.family_quiet old
  · rfl

theorem family_single {inst : Clif.Inst} (family : Family inst) (f : Clif.Function) :
    (inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·)).map List.length = some 1 := by
  rcases family with old | ⟨ty,x,rfl⟩
  · exact BitBody.family_single old f
  · rfl

theorem family_formats {inst : Clif.Inst} (family : Family inst) : CastBody.SafeFormat inst := by
  rcases family with old | ⟨ty,x,rfl⟩
  · exact BitBody.family_formats old
  · simp [CastBody.SafeFormat,instNames]

theorem popcount_inst_notrap {inst : Clif.Inst} (family : Family inst)
    (fr : Clif.Frame) (cm : Clif.Mem) (c : Clif.TrapCode) : Clif.evalInst fr cm inst ≠ .trap c := by
  rcases family with old | ⟨ty,x,rfl⟩
  · exact BitBody.bit_inst_notrap old fr cm c
  · cases getX : fr.getAs x ty with
    | trap code => exact False.elim (PureBody.frame_getAs_notrap fr x ty code getX)
    | stuck message => simp [Clif.evalInst,getX]
    | ok u => simp [Clif.evalInst,getX]

theorem popcount_source_notrap {env : Clif.Env} {cp : Clif.Program} (fuel : Nat)
    (s : Clif.State) (callers : s.callers = []) (family : ∀ stm ∈ s.frame.body,Family stm.inst)
    {xs : List Nat} (ret : s.frame.term = .ret xs) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel s ≠ .trapped code := by
  apply PureBody.pure_source_notrap fuel s callers ?_ ret code
  intro stm member
  exact ⟨family_pure (family stm member),popcount_inst_notrap (family stm member)⟩
end Backend.Stock.Proof.PopcountBody
