import FV.Backend.Proof.IselPrgSound

/-!
# Progress of the ISLE lowering (V7): a root run returns

`root_run`: a driver call `runTerm ctx term args s` of a root term returns a value its table
entry's output describes, when a table entry above the arguments' abstract values surely returns
a value within the interpreter's fuel (`progress`, at fuel `1000000`).
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx} {tab : PTab}
  {aext : TermId → PA → Option (List (List PA) × Bool)} {actor : TermId → List PA → Option (PA × Bool)}
  {aidata : Nat → Option (List PA)} {hand : RuleId → Option (Nat × PA)}

/-- **A root run returns.** -/
theorem root_run (M : Model f ctx aext actor aidata) (H : HandOk f ctx program {} tab hand)
    (htab : chkTab program tab aext actor aidata hand = true) {term : String} {T : Term}
    (hT : program.termByName? term = some T) {as : List PA} {e : PEnt}
    (he : tabFind tab T.id as = some e) (hos : e.osome = true) (hfu : e.fu ≤ 1000000)
    {args : List V} (hargs : γL f ctx as args) (s : LState) :
    ∃ w s' tr, runTerm ctx term args s = .ok (some w, s', tr) ∧ γ f ctx e.out w := by
  obtain ⟨hmem, -, hle⟩ := tabFind_sound he
  have hP := progress M H rfl htab 1000000 e hmem hfu T.ret args s #[] (leL_sound _ _ hle _ hargs)
  obtain ⟨v, st', tr', hrun, hsome, hout⟩ := hP
  obtain ⟨w, rfl⟩ := Option.isSome_iff_exists.mp (hsome hos)
  refine ⟨w, st', tr'.toList, ?_, hout w rfl⟩
  have het : e.t = T.id := (tabFind_sound he).2.1
  rw [het] at hrun
  unfold runTerm Interp.run
  simp only [hT, bind, Except.bind, hrun, pure, Except.pure]

end Backend.Proof.Prg
