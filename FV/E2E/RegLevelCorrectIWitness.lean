import FV.E2E.RegLevelCorrectI
import FV.E2E.RegLevelCorrectU

/-!
# Witnesses for the counted register-level theorem (`FV/E2E/RegLevelCorrectI.lean`)

* `csemVI` steps: a `rets []` at counter `3` keeps the counter, and is a `csemI` step
  (`csemVI_sub`); a move of the allocated code at counter `5` projects to one without the counter
  and lifts back (`MStep.counted_proj`, `MStep.counted_lift`);
* `Realizes.counted`/`mono_T`/`congr_Q` on the realisation by the identity machine that every
  semantics has (`realizes_any`), at every index;
* `RL.Q_withX`, `StRel.withX`: on any activation;
* `worldI_const`: `regLevelCorrect_worldI` applies to `RegLevelCorrectUWitness`'s compiled
  function with a call (`args`, `call f`, `rets`; its allocation, lowering and emission decided
  there) with one external semantics for every call index, from `regLevelCorrect_backend`'s
  premises.
-/

namespace Backend.Proof.RegLevelCorrectIWitness

open Backend Backend.Proof E2E Backend.Proof.Driver

/-- A `rets []` of the counted semantics at counter `3`. -/
theorem rets_step (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI)
    (w : Arm.ArmState) : csemVI gv F ctx X (.rets []) [] (w, 3) = some ([], (w, 3), .ret) := rfl

theorem rets_csemI (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI)
    (w : Arm.ArmState) : csemI F ctx X (.rets []) [] (w, 3) = some ([], (w, 3), .ret) :=
  csemVI_sub (rets_step gv F ctx X w)

theorem csemI_counted (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) :
    csemI F ctx X = ISem.counted fun n => csem F ctx (X.at n) := csemI_eq_counted F ctx X

theorem counted_some_rets (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSemI) (w : Arm.ArmState) :
    csemV gv F ctx (X.at 3) (.rets []) [] w = some ([], w, .ret) ∧ (w, 3).2 = 3 :=
  ISem.counted_some (sem := fun n => csemV gv F ctx (X.at n)) (rets_step gv F ctx X w)

/-- A move at counter `5`, without the counter. -/
theorem move_proj (vc : VCode) (rf : RFunc) (sem : Nat → ISem CV Arm.ArmState) (src dst : Loc)
    (its : List RItem) (m : Loc → CV) (w : Arm.ArmState) :
    MStep vc (sem 5) ckeep rf (.run ⟨0, .move src dst :: its, m, w⟩)
      (.run ⟨0, its, upd m dst (m src), w⟩) :=
  MStep.counted_proj (sem := sem) (c' := .run ⟨0, its, upd m dst (m src), (w, 5)⟩) .move

theorem move_lift (vc : VCode) (rf : RFunc) (sem : Nat → ISem CV Arm.ArmState) (src dst : Loc)
    (its : List RItem) (m : Loc → CV) (w : Arm.ArmState) :
    ∃ c', c'.mapW Prod.fst = .run ⟨0, its, upd m dst (m src), w⟩ ∧
      MStep vc (ISem.counted sem) ckeep rf (.run ⟨0, .move src dst :: its, m, (w, 5)⟩) c' :=
  MStep.counted_lift .move

/-- The identity machine realises every semantics under the trivial relation. -/
theorem realizes_any {V W : Type} (vc : VCode) (rf : RFunc) (sem : ISem V W) (keep : Reg → V → V) :
    Realizes vc rf sem keep (id : Unit → Unit) (fun _ _ => True) (fun _ => True) :=
  fun _ _ c' _ hs => ⟨0, c', hs, trivial, fun _ _ => trivial⟩

theorem realizes_counted_any (vc : VCode) (rf : RFunc) (sem : Nat → ISem CV Arm.ArmState) :
    Realizes vc rf (ISem.counted sem) ckeep (id : Unit → Unit) (fun _ _ => True) (fun _ => True) :=
  Realizes.counted (Q := fun _ _ => True) fun n => realizes_any vc rf (sem n) ckeep

theorem realizes_mono_congr (vc : VCode) (rf : RFunc) (sem : ISem CV Arm.ArmState) :
    Realizes vc rf sem ckeep (id : Unit → Unit) (fun _ _ => True ∧ True) (fun _ => True ∨ False) :=
  ((realizes_any vc rf sem ckeep).mono_T fun _ _ => .inl trivial).congr_Q
    fun _ _ => ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩

theorem q_withX (R : RL) (X : ExtSem) (hP : ({ R with X := X } : RL).sP = R.sP)
    (s : Arm.ArmState) (c : MConf CV Arm.ArmState) :
    Q { R with X := X } s c ↔ Q R s c := RL.Q_withX R X hP s c

theorem stRel_withX {R : RL} {X : ExtSem} (hP : ({ R with X := X } : RL).sP = R.sP)
    {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState}
    (h : StRel R s m w) : StRel R s m w := (h.withX hP).ofWithX hP

open RegLevelCorrectUWitness in
/-- **`regLevelCorrect_worldI` applies to a compiled function with a call** with one external
semantics for every call index (`ExtSemI.const X`), from `regLevelCorrect_backend`'s premises. -/
theorem worldI_const {X : ExtSem} {H : ArmHooks} {K : Nat} {fb : FnBin}
    (hlayout : fa.layout = .ok fb) (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vc)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s) K X H vc.CallSite)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) {w₀ : Arm.ArmState}
    (hbe : BodyEntryW (frameW K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s)
      vc.EntryArg af s w₀) (ρ₀ : Nat → CV) (us : List (Reg × Reg)) (vals : List CV)
    (w : Arm.ArmState) (nc : Nat)
    (hret : VRetFrom vc (csemVI (fun _ _ => False) (frameWG K (RAFrame.compute vc rf).intBase
        (RAFrame.compute vc rf).size af (fun _ => False) s) ⟨fa.k, af.slotBase⟩ (ExtSemI.const X))
        ⟨0, 0, ρ₀, (w₀, 0)⟩ us vals (w, nc)) :
    ∃ n, ArmRet ra s (E2E.runX (ArmStepX X H fa) n s) := by
  obtain ⟨hca, halloc, hemit, -⟩ := premises K X
  have hnt : vc.hasTryCall = false := by decide +kernel
  have hnl : vc.hasTls = false := by decide +kernel
  have e := frameWG_false K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s
  obtain ⟨n, h, -⟩ := (regLevelCorrect_worldI (XI := ExtSemI.const X) (G := fun _ => False)
    (gv := fun _ _ => False) hca halloc hemit hlayout hcov hent hres (fun _ h => h.elim)
    (fun _ => by rw [e]; exact (hC s).g _ s _ _) (fun h => absurd h (by rw [hnt]; decide))
    (fun h => absurd h (by rw [hnl]; decide)) (by rw [e]; exact hbe) ρ₀).1 us vals w nc hret
  exact ⟨n, h⟩

end Backend.Proof.RegLevelCorrectIWitness
