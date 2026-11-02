import FV.Backend.Proof.StockParameterMetadata
import FV.Backend.Proof.StockForwardSourceOrder

namespace Backend.Stock.Proof.ParameterCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ForwardSource
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A wide original parameter may be inherited from any original source block. -/
def ParameterCondition (f : Clif.Function) (c : Nat) : Prop :=
  ∃ (pbi : Nat) (pb : Clif.Block) (ty : Clif.Ty),f.blocks[pbi]? = some pb ∧
    (c,ty) ∈ pb.params ∧ (ty = .i32 ∨ ty = .i64)

def ParameterBranch (f : Clif.Function) (b : Clif.Block) : Prop :=
  ∃ c yes no,b.term = .brif c yes no ∧ yes.args = [] ∧ no.args = [] ∧ ParameterCondition f c

def NonentryParameterTerms (f : Clif.Function) : Prop :=
  ∀ bi b,f.blocks[bi]? = some b → bi ≠ 0 →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ ParameterBranch f b

theorem parameter_metadata {f : Clif.Function} {c : Nat} (parameter : ParameterCondition f c)
    (ssa : (valueDefs f).Nodup) {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) :
    ctx.defInst? c = none ∧
      (ctx.valueType? c = some (.int 32) ∨ ctx.valueType? c = some (.int 64)) := by
  obtain ⟨pbi,pb,ty,block,member,wide⟩ := parameter
  exact parameter_condition_metadata_ssa ssa block member wide build


def ParameterTerms (f : Clif.Function) : Prop :=
  ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ ParameterBranch f b

theorem parameter_terms_nonentry {f : Clif.Function} (terms : ParameterTerms f) : NonentryParameterTerms f :=
  fun bi b block _ => terms bi b block


end Backend.Stock.Proof.ParameterCfg
