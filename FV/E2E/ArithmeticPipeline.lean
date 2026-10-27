import FV.E2E.ProductionPipelineWith
import FV.E2E.CompiledSemantic

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Preserve every existing static check and its position. Only the lowering
verdict gains the proved actual-Stock alternative. Link/layout checks remain
in the existing linker check list. -/
def staticChksSemantic (cleanup : Bool) (I : LinkInput) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let old := staticChksWith (Stock.Arithmetic.stageF cleanup) I g r
  old.take 1 ++ [("compiled: lowerCheck",Stock.Arithmetic.check g (getOk r).vc)] ++ old.drop 2

/-- A complete arithmetic attempt is accepted only after the original static
checks with semantic lowering validation. A failure retries the shipped scalar
pipeline, preserving original source, allocator and cleanup settings. -/
def LinkInput.pipeArithmetic (I : LinkInput) (cleanup : Bool) (fi : FnInput) : Except String Art :=
  match I.pipeOfWithLowering Stock.Arithmetic.lowerCandidate (Stock.Arithmetic.stageF cleanup) fi with
  | .ok a =>
    if (staticChksSemantic cleanup I fi.func (.ok a)).all (·.2) then .ok a
    else I.pipeProductionWith Stock.ScalarAdd.lower cleanup fi
  | .error _ => I.pipeProductionWith Stock.ScalarAdd.lower cleanup fi

set_option maxHeartbeats 1000000 in
/-- All stages of the artifact returned by either complete attempt are actual
pipeline results. The arithmetic candidate never supplies allocation evidence. -/
theorem LinkInput.pipeArithmetic_prepared {I : LinkInput} {cleanup : Bool} {fi : FnInput} {a : Art}
    (h : I.pipeArithmetic cleanup fi = .ok a) :
    prepare (Stock.Arithmetic.stageF cleanup fi.func a.vc) = .ok a.vcp ∧
    lowerRFunc a.vcp a.rf = .ok a.af ∧ emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧
    a.k = fi.k ∧ a.base = BitVec.ofNat 64 (I.baseOf fi.func.name) := by
  have fallback (h : I.pipeProductionWith Stock.ScalarAdd.lower cleanup fi = .ok a) :
      prepare (Stock.Arithmetic.stageF cleanup fi.func a.vc) = .ok a.vcp ∧
      lowerRFunc a.vcp a.rf = .ok a.af ∧ emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧
      a.k = fi.k ∧ a.base = BitVec.ofNat 64 (I.baseOf fi.func.name) := by
    have facts := LinkInput.pipeProductionWith_spec h
    cases cleanup <;> exact facts.2
  unfold LinkInput.pipeArithmetic at h
  split at h
  · split at h
    · cases h
      exact (LinkInput.pipeOfWithLowering_provenance (by assumption)).2
    · exact fallback h
  · exact fallback h

/-- Runtime verdicts and pipeline observations construct the semantic artifact
used by the source/world consumers; raw Stock never needs a legacy verdict. -/
theorem LinkInput.pipeArithmetic_compiled {I : LinkInput} {cleanup : Bool} {fi : FnInput} {a : Art}
    (h : I.pipeArithmetic cleanup fi = .ok a)
    (checked : (staticChksSemantic cleanup I fi.func (.ok a)).all (·.2) = true) :
    CompiledSemantic fi.func a.k a.vc a.vcp a.rf a.af a.fa a.fb := by
  have hall := List.all_eq_true.mp checked
  have lower := hall ("compiled: lowerCheck",Stock.Arithmetic.check fi.func a.vc)
    (by simp [staticChksSemantic,staticChksWith,getOk])
  have prep := hall ("compiled: prepCheck",prepCheck (Stock.Arithmetic.stageF cleanup fi.func a.vc) a.vcp)
    (by simp [staticChksSemantic,staticChksWith,getOk])
  have check := hall ("compiled: checkAlloc",(Backend.checkAlloc a.vcp a.rf).toBool)
    (by simp [staticChksSemantic,staticChksWith,getOk])
  obtain ⟨prepared,alloc,emit,layout,_⟩ := LinkInput.pipeArithmetic_prepared h
  exact CompiledSemantic.of_checks lower prepared prep (toBool_unit check) alloc emit layout

/-- Previously accepted static artifacts remain accepted, with identical
remaining checks and stage labels. -/
theorem staticChksSemantic_of_legacy {cleanup : Bool} {I : LinkInput} {g : Clif.Function}
    {r : Except String Art}
    (h : (staticChksWith (Stock.Arithmetic.stageF cleanup) I g r).all (·.2) = true) :
    (staticChksSemantic cleanup I g r).all (·.2) = true := by
  simp only [staticChksWith,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true] at h
  simp only [staticChksSemantic,staticChksWith,List.take_succ_cons,List.take_zero,List.drop_succ_cons,
    List.drop_zero,List.singleton_append,List.cons_append,List.nil_append,
    List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true]
  exact ⟨h.1,by simp only [Stock.Arithmetic.check,Bool.or_eq_true]; exact .inl h.2.1,h.2.2⟩

end E2E.LinkCheck
