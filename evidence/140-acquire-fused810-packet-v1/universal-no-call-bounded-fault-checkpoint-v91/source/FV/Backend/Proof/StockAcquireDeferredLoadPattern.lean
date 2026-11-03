import FV.Backend.Proof.StockAcquireMatchedSinkSources
import FV.Backend.Proof.StockEligibilitySinkTarget
import FV.Backend.Proof.IselCtlUnmatch

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program

def deferredLoadPattern : Pattern :=
  .term 18 209 [.bind 14 0 (.wildcard 14),.term 152 2463
    [.term 151 2313 [],.bind 15 1 (.wildcard 15),
     .term 137 103 [.bind 142 2 (.wildcard 142)],.bind 138 3 (.wildcard 138)]]

/-- The actual nested definition pattern binds the original ordinary-load target and value. -/
theorem deferred_load_bound_source {ctx : Ctx} {state : State} {value : V}
    {env bound : Isle.Interp.Env V}
    (matched : matchPat program (Stock.sem ctx) state
      (.bind 15 4 (.term 15 1 [deferredLoadPattern])) value env = .ok (some bound)) :
    ∃ (original producer : Nat) (info : IInfo) (fields : List V),
      value = .value original ∧ bound[4]? = some (some (.value original)) ∧
      ctx.defInst? original = some producer ∧ ctx.insts[producer]? = some info ∧
      info.data = .data 152 16 fields := by
  obtain ⟨inside,inner⟩ := matchPat_bind_inv matched
  have kept := stock_pattern_keeps (k := 4) (by decide +kernel) inner
  have stored : bound[4]? = some (some value) := by
    rw [kept]
    simp [inside]
  rw [stock_matchPat] at inner
  obtain ⟨values,extracted,args⟩ := matchPat_extract_inv data_program.t1 term_1_kind rfl inner
  rw [Backend.Proof.sem_extract] at extracted
  cases value with
  | value original =>
    obtain ⟨producer,defined,rfl⟩ := (ext_def_inst_iff ctx state.base original values).mp extracted
    obtain ⟨middle,child,ending⟩ := matchArgs_cons_inv args
    obtain ⟨info,fields,found,data⟩ := fmtD_match_k data_program
      (q := deferredLoadPattern) rfl data_program.t2463 term_2463_kind child
    exact ⟨original,producer,info,fields,rfl,stored,defined,found,data⟩
  | _ => cases extracted

end Backend.Stock.Proof.Acquire810
