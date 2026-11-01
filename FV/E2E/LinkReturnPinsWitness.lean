import FV.E2E.LinkReturnPins
import FV.E2E.CompiledSemanticReturnPinsWitness
import FV.E2E.LinkSemanticNI
import FV.E2E.NonVacuityLink

namespace E2E.LinkReturnPinsWitness
open Backend Backend.Proof Backend.Proof.Driver LinkWitness
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def system : LinkSys := (L fun _ => True).std
private theorem original_ok : (L fun _ => True).Ok := L_ok _ (fun _ _ => trivial)
private theorem system_ok : system.Ok := original_ok.withCrun _
private instance : system.CrunOk := (L fun _ => True).crunOk_std original_ok
private def world : Arm.ArmState := Arm.w (.GPR 31#5) 0x100000 Arm.ArmState.default
private def memory : Clif.Mem := {
  symbols := system.syms,place := some ⟨[0x100000],system.frames,none⟩ }
private def sourceCheck : Bool :=
  match Clif.initState system.P fH.name [⟨.i64,41⟩] memory with
  | .trap _ | .stuck _ => false
  | .ok cs => match system.crun 3 cs with
    | .returned vals _ => decide (vals = [⟨.i64,42⟩])
    | _ => false

-- witness: native_decide (fixed linked fixture only)
private theorem sourceCheck_true : sourceCheck = true := by native_decide
-- witness: native_decide (fixed linked fixture only)
private theorem fixedFacts :
    fH.sig = {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV} ∧ fH.sig.params.length = 1 ∧
    (sigRets fH.sig).length = 1 ∧
    (RAFrame.compute (system.A fG).vcp (system.A fG).rf).intBase = 0 ∧
    ({name := "h",sig := fH.sig,colocated := true} : Clif.ExtFunc) ∈ fG.externs.map (·.2) ∧
    system.P.func? "h" = some fH := by native_decide

-- witness: native_decide (fixed linked fixture only)
private theorem old_check : SemanticNI.check fH (system.A fH).vc = true := by native_decide

private theorem locations : locsOf fH.sig = [.reg (.x 0)] := by
  rw [fixedFacts.1]
  rfl

private theorem memory_rel : MemRel (fun _ => True) system.syms memory world := by
  refine ⟨?_,?_,rfl⟩
  · intro a b valid _
    simp [memory,Clif.Mem.valid] at valid
  · intro a n valid
    simp [memory,Clif.Mem.valid] at valid

private theorem arguments : ArgsAt fH.sig [⟨.i64,41⟩] [41] world := by
  refine ⟨fixedFacts.2.1.symm,?_,?_⟩
  · simp only [regArgVals,locations,List.zip_cons_cons,List.zip_nil_right,
      List.filterMap_cons,List.filterMap_nil]
    refine ⟨rfl,?_⟩
    intro j v x found held
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found held
      subst v; subst x; rfl
    | succ j => simp at found
  · intro off v member
    simp [locations] at member

private theorem avoids : StackArgsAvoid (fun _ => True) fH.sig [⟨.i64,41⟩] world := by
  intro off v member
  simp [locations] at member

/-- The retained linked fixture makes a real successful call with a nonzero result.
The original guard, all original system conditions, and the source run are inhabited. -/
theorem successful_program_call_witness :
    system.Ok ∧ ∃ (cs : Clif.State) (cm : Clif.Mem) (values : List CV) (next : Arm.ArmState),
      Clif.initState system.P fH.name [⟨.i64,41⟩] memory = .ok cs ∧
      system.crun 3 cs = .returned [⟨.i64,42⟩] cm ∧
      system.progXWithPins (fun f => (List.range (sigRets f.sig).length).map Reg.x)
        (fun M _ => system.K M) 3 (fun _ => True) fH [41] world = some (values,next) ∧
      system.progXABI (fun M _ => system.K M) 3 (fun _ => True) fH [41] world = some (values,next) ∧
      values.length = 1 ∧ PrefixHold [⟨.i64,42⟩] values := by
  have source := sourceCheck_true
  unfold sourceCheck at source
  cases entered : Clif.initState system.P fH.name [⟨.i64,41⟩] memory with
  | trap code => rw [entered] at source; cases source
  | stuck message => rw [entered] at source; cases source
  | ok cs =>
    rw [entered] at source
    dsimp only at source
    cases returned : system.crun 3 cs with
    | returned vals cm =>
      rw [returned] at source
      have equal : vals = [⟨.i64,42⟩] := of_decide_eq_true source
      subst vals
      have hg : fG ∈ system.P.funcs := by change fG ∈ P.funcs; simp [P]
      have hh : fH ∈ system.P.funcs := by change fH ∈ P.funcs; simp [P]
      have callee : system.Callee fG fH :=
        .inr (.inl ⟨_,fixedFacts.2.2.2.2.1,fixedFacts.2.2.2.2.2⟩)
      have hL := system_ok.toSemanticNI
      have budget := system.budget_K_semantic hL
      have sp : spv world = 0x100000 := Arm.r_of_w_same
      have relation : RelW ⟨fun _ => True,system.syms,(system.A fG).af.slotBase,
          (RAFrame.compute (system.A fG).vcp (system.A fG).rf).intBase⟩
          fG 0x100000 [] memory world := by
        refine ⟨⟨memory_rel,?_,?_⟩,sp,?_⟩
        · intro id b member; cases member
        · rw [fixedFacts.2.2.2.1]
          exact outRel_zero _ _ _
        · decide +kernel
      have dead : ∀ a,StackBelow (system.K 3) (0x100000 : BitVec 64) a → True ∧ ¬ system.Img a := by
        intro a below
        refine ⟨trivial,fun image => ?_⟩
        have upper := img_lt image
        change a.toNat < 1048576 ∧ 1048576 ≤ a.toNat + 192 at below
        omega
      obtain ⟨values,next,called,arity,held,_⟩ := system.progResult_semantic hL budget
        (fun _ => system.thm_semantic hL budget 2) hg hh callee (fun _ _ => trivial)
        (by decide +kernel) dead (by decide +kernel) arguments avoids relation (fun _ => ⟨[],rfl⟩)
        entered returned
      refine ⟨system_ok,cs,cm,values,next,rfl,returned,?_,?_,?_,held⟩
      · rw [system.progXWithPins_ordinary]
        exact called
      · rw [system.progXABI_previous old_check]
        exact called
      · exact arity.trans fixedFacts.2.2.1
    | trapped code => rw [returned] at source; cases source
    | stuck message => rw [returned] at source; cases source
    | outOfFuel => rw [returned] at source; cases source

/-- The unchanged sret source inhabits the physical prefix proof at x8. -/
theorem sret_prefix_witness :
    let f := Backend.Stock.Memory.StoreRoots.ComputedFixture.function
    ReturnPinMode.stockABI.pins f (sigRets f.sig).length = [.x 8] ∧
      ReturnPinMode.stockABI.Valid f [(.vreg 9 .int,.x 8)] := by
  let f := Backend.Stock.Memory.StoreRoots.ComputedFixture.function
  change ReturnPinMode.stockABI.pins f (sigRets f.sig).length = [.x 8] ∧
    ReturnPinMode.stockABI.Valid f [(.vreg 9 .int,.x 8)]
  have valid : ReturnPinMode.stockABI.Valid f [(.vreg 9 .int,.x 8)] :=
    CompiledSemanticReturnPinsWitness.physical_pin_witness.1
  have bound : (sigRets f.sig).length ≤ ([((.vreg 9 .int : Reg),(.x 8 : Reg))]).length := by
    rw [show f = _ from Backend.Stock.Memory.SretCopy.Fixture.captured_sret_source_shape_witness]
    decide +kernel
  have selected := ReturnPinMode.pins_prefix_of_valid valid bound
  have count : (sigRets f.sig).length = 1 := by
    rw [show f = _ from Backend.Stock.Memory.SretCopy.Fixture.captured_sret_source_shape_witness]
    rfl
  refine ⟨?_,valid⟩
  simpa only [count,List.map_cons,List.map_nil,List.take_succ_cons,List.take_zero] using selected

end E2E.LinkReturnPinsWitness
