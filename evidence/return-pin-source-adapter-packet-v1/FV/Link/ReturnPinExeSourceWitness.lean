import FV.Link.ReturnPinExeSourceWith
import FV.E2E.ReturnPinBinaryWitness

namespace Link.ReturnPinSourceWitness
open Backend E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
  E2E.LegalProgram Opt.Legal Opt.Legalize128
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private abbrev fn := ProductionBoundaryWitness.f
private abbrev arg := ProductionBoundaryWitness.argument
private abbrev input (cleanup : Bool) : SemanticStackBound.CompilerInput :=
  ReturnPinCompilerWith.input Stock.Production.lower (ProductionBoundaryWitness.spec cleanup) cleanup

private theorem input_original (cleanup : Bool) : input cleanup = ProductionBoundaryWitness.input cleanup := rfl

private def checks (cleanup : Bool) : Bool :=
  decide (ReturnPinCompilerWith.attempt Stock.Production.lower
    (ProductionBoundaryWitness.spec cleanup) (ProductionBoundaryWitness.file0 cleanup) cleanup =
      .ok (ProductionBoundaryWitness.file cleanup)) &&
  SrcScopeB (input cleanup) &&
  decide ((input cleanup).toLinkInput.srcProg = ({funcs := [fn]} : Clif.Program)) &&
  decide (legalize fn = fn)

attribute [local irreducible] checks
-- witness: native_decide (the original fixed linked identity image and source records only)
private theorem checks_true (cleanup : Bool) : checks cleanup = true := by
  cases cleanup <;> native_decide

private theorem facts (cleanup : Bool) :
    ReturnPinCompilerWith.attempt Stock.Production.lower
      (ProductionBoundaryWitness.spec cleanup) (ProductionBoundaryWitness.file0 cleanup) cleanup =
        .ok (ProductionBoundaryWitness.file cleanup) ∧
    SrcScopeB (input cleanup) = true ∧
    (input cleanup).toLinkInput.srcProg = ({funcs := [fn]} : Clif.Program) ∧ legalize fn = fn := by
  simpa only [checks,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using checks_true cleanup

private theorem source_find (cleanup : Bool) :
    (input cleanup).toLinkInput.srcProg.func? ProductionBoundaryWitness.name = some fn := by
  rw [(facts cleanup).2.2.1]
  rfl

private theorem no_wide (cleanup : Bool) :
    ¬ ∃ f ∈ (input cleanup).toLinkInput.srcProg.funcs,mentions128 f = true := by
  rw [(facts cleanup).2.2.1]
  rintro ⟨f,member,wide⟩
  simp only [List.mem_singleton] at member
  subst f
  change false = true at wide
  cases wide

private theorem no_indirect (cleanup : Bool) :
    (∃ g ∈ (prog (input cleanup)).funcs,¬ Clif.IndFree g) → ∀ n,closedBase.env.sigOf n = none := by
  rintro ⟨g,member,indirect⟩
  rw [input_original,(ProductionBoundaryWitness.concrete_facts cleanup).1] at member
  simp only [List.mem_singleton] at member
  subst g
  exact False.elim (indirect (indFreeB_sound (by rfl)))

/-- Every continuing source state passes the predicate before the run ends. -/
private def allB (env : Clif.Env) (p : Clif.Program) (Q : Clif.State → Bool) : Nat → Clif.State → Bool
  | 0, _ => false
  | fuel+1, state => Q state && match Clif.step env p state with
    | .next next => allB env p Q fuel next
    | _ => true

private theorem allB_sound {env : Clif.Env} {p : Clif.Program} {Q : Clif.State → Bool} :
    ∀ (fuel : Nat) (state : Clif.State),allB env p Q fuel state = true →
      ∀ next,Opt.Legal.SReach env p state next → Q next = true
  | 0, _, checked => by simp [allB] at checked
  | fuel+1, state, checked => by
    simp only [allB,Bool.and_eq_true] at checked
    obtain ⟨here,remaining⟩ := checked
    intro next reached
    cases reached with
    | refl => exact here
    | step step path =>
      rw [step] at remaining
      exact allB_sound fuel _ remaining next path

private theorem source_bounded (cleanup : Bool) (word : BitVec 64) :
    ∀ next,Opt.Legal.SReach closedBase.env (input cleanup).toLinkInput.srcProg
      (ProductionBoundaryWitness.cs cleanup word) next → Opt.Legal.MemBounded next.mem := by
  have checked : allB closedBase.env (input cleanup).toLinkInput.srcProg
      (fun state => state.mem.allocs.isEmpty) 4 (ProductionBoundaryWitness.cs cleanup word) = true := by rfl
  intro next reached a n valid
  have empty := allB_sound 4 _ checked next reached
  simp only [List.isEmpty_iff] at empty
  simp [Clif.Mem.valid,empty] at valid

private theorem source_returns (cleanup : Bool) (word : BitVec 64) :
    Clif.runLoop closedBase.env (input cleanup).toLinkInput.srcProg 4
      (ProductionBoundaryWitness.cs cleanup word) =
        .returned [arg word] (ProductionBoundaryWitness.cm cleanup) := by
  have returned := Clif.StockPrologueSource.source_body ProductionBoundaryWitness.name [] word
    (ProductionBoundaryWitness.entered cleanup) closedBase.env (input cleanup).toLinkInput.srcProg
  have memory := Clif.StockPrologueSource.source_memory_roundtrip ProductionBoundaryWitness.name []
    (ProductionBoundaryWitness.cm cleanup)
  change Clif.runLoop closedBase.env (input cleanup).toLinkInput.srcProg 4
    (ProductionBoundaryWitness.cs cleanup word) =
      .returned [arg word] (((Clif.enterSlots fn (ProductionBoundaryWitness.cm cleanup)).2).free []).leave at returned
  change (((Clif.enterSlots fn (ProductionBoundaryWitness.cm cleanup)).2).free []).leave =
    ProductionBoundaryWitness.cm cleanup at memory
  rw [memory] at returned
  exact returned

private theorem no_cycle (cleanup : Bool) :
    ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls (input cleanup) (input cleanup).results) fn := by
  have checked : SemanticStackBound.okB (input cleanup) = true := by
    rw [input_original]
    exact ReturnPinBinaryWitness.old_checked cleanup
  have good : SemanticStackBound.goodN (input cleanup) ProductionBoundaryWitness.name = true := by
    rw [input_original]
    exact (ProductionBoundaryWitness.concrete_facts cleanup).2.2.1
  obtain ⟨g,found,acyclic⟩ := (SemanticStackBound.goodN_iff checked).mp good
  have found' : (prog (input cleanup)).func? ProductionBoundaryWitness.name = some fn := by
    rw [input_original]
    exact ProductionBoundaryWitness.program_find cleanup
  have same : g = fn := Option.some.inj (found.symm.trans found')
  subst g
  exact acyclic

/-- The original source outcome refines to the unchanged linked image. -/
def OriginalResult (cleanup : Bool) (word : BitVec 64) : Prop :=
  ∃ values,Opt.Legal.ExpRel ((Opt.Legal.groups fn.sig.returns).getD []) [arg word] values ∧
    ExecRefines (art (input cleanup) fn).fb (art (input cleanup) fn).base
      (xreg 30 (ProductionBoundaryWitness.machine cleanup word))
      (step (input cleanup) closedBase (ProductionBoundaryWitness.file cleanup))
      (ProductionBoundaryWitness.machine cleanup word)
      (RelocAtWithResults (input cleanup) (input cleanup).results)
      (.returned values (ProductionBoundaryWitness.cm cleanup))

/-- The ordinary original-source variant has a complete existing fixture in both cleanup modes. -/
-- witness: native_decide (only fixed source/image and existing compiler facts; the argument remains arbitrary)
theorem original_source_witness (cleanup : Bool) (word : BitVec 64) : OriginalResult cleanup word := by
  have base : BaseOk (sys (input cleanup) closedBase) := by
    rw [input_original]
    exact ProductionBoundaryWitness.base_ok cleanup
  have proof := ReturnPinCompilerWith.attempt_correct_source (facts cleanup).1 (facts cleanup).2.1
    closedBase base (hooksSim_closed _) (fun h => False.elim (no_wide cleanup h)) (no_indirect cleanup)
    (source_find cleanup) (by simpa only [(facts cleanup).2.2.2] using no_cycle cleanup)
    (r := ProductionBoundaryWitness.machine cleanup word) (args := [arg word]) (args' := [arg word])
    (cs := ProductionBoundaryWitness.cs cleanup word) (cs' := ProductionBoundaryWitness.cs cleanup word)
    (ReturnPinBinaryWitness.intact cleanup word)
    (by simpa only [input_original,(facts cleanup).2.2.2,fn,arg,ReturnPinBinaryWitness.original,
        ProductionBoundaryWitness.cs,ProductionBoundaryWitness.input,ProductionCompiler.input,
        LinkSpec.inputProductionWith_original] using ReturnPinBinaryWitness.outside cleanup word)
    (by simpa only [input_original,(facts cleanup).2.2.2,fn,arg,ReturnPinBinaryWitness.original,
        ProductionBoundaryWitness.cs,ProductionBoundaryWitness.input,ProductionCompiler.input,
        LinkSpec.inputProductionWith_original] using ReturnPinBinaryWitness.source_run cleanup word)
    (ProductionBoundaryWitness.source_entry cleanup word) (by exact ⟨rfl,trivial⟩) rfl rfl
    (source_bounded cleanup word) 4
  exact proof.1 _ _ (source_returns cleanup word)

/-- The peak-depth original-source variant retains the same fixture with source depth zero. -/
-- witness: native_decide (only fixed source/image and existing compiler facts; the argument remains arbitrary)
theorem original_source_peak_witness (cleanup : Bool) (word : BitVec 64) : OriginalResult cleanup word := by
  have base : BaseOk (sys (input cleanup) closedBase) := by
    rw [input_original]
    exact ProductionBoundaryWitness.base_ok cleanup
  have bounded : frameDrop (art (input cleanup) fn).af + (input cleanup).D*0 ≤ 4096 := by
    rw [input_original]
    have bound := ReturnPinBinaryWitness.depth_budget cleanup
    change frameDrop (art (ProductionBoundaryWitness.input cleanup) ProductionBoundaryWitness.f).af +
      (ProductionBoundaryWitness.input cleanup).D*3 ≤ 4096 at bound
    change frameDrop (art (ProductionBoundaryWitness.input cleanup) ProductionBoundaryWitness.f).af ≤ 4096
    omega
  have proof := ReturnPinCompilerWith.attempt_correct_source_peak (facts cleanup).1 (facts cleanup).2.1
    closedBase base (hooksSim_closed _) (fun h => False.elim (no_wide cleanup h)) (no_indirect cleanup)
    (source_find cleanup) 0
    (r := ProductionBoundaryWitness.machine cleanup word) (args := [arg word]) (args' := [arg word])
    (cs := ProductionBoundaryWitness.cs cleanup word) (cs' := ProductionBoundaryWitness.cs cleanup word)
    (ReturnPinBinaryWitness.intact cleanup word)
    (by simpa only [input_original,(facts cleanup).2.2.2,fn,arg,ReturnPinBinaryWitness.original,
        ProductionBoundaryWitness.cs,ProductionBoundaryWitness.input,ProductionCompiler.input,
        LinkSpec.inputProductionWith_original] using
      ReturnPinBinaryWitness.outside_budget cleanup word _ bounded)
    (by simpa only [input_original,(facts cleanup).2.2.2,fn,arg,ReturnPinBinaryWitness.original,
        ProductionBoundaryWitness.cs,ProductionBoundaryWitness.input,ProductionCompiler.input,
        LinkSpec.inputProductionWith_original] using ReturnPinBinaryWitness.source_run cleanup word)
    (ProductionBoundaryWitness.source_entry cleanup word) (by exact ⟨rfl,trivial⟩) rfl rfl
    (source_bounded cleanup word) (Clif.depthLe_of_depthB 4 _ (by rfl)) 4
  exact proof.1 _ _ (source_returns cleanup word)

end Link.ReturnPinSourceWitness
