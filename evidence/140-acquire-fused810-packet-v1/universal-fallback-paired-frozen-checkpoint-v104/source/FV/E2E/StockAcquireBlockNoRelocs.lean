import FV.E2E.StockAcquireEmitNoRelocs
import FV.E2E.StockAcquireBlockNoHooks

namespace Backend.Proof
open Backend E2E Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

theorem pushLines_no_relocs (int : Bool) (rs : List Reg) :
    ∀ l ∈ pushLines int rs, l.noRelocB = true := by
  intro l hl
  unfold pushLines at hl
  generalize pairsOf rs = po at hl
  obtain ⟨ps, o⟩ := po
  simp only [List.mem_append, List.mem_map] at hl
  rcases hl with hl | ⟨p, _, rfl⟩
  · cases o with
    | none => simp at hl
    | some r => simp only [List.mem_singleton] at hl; subst hl; cases int <;> rfl
  · cases int <;> rfl

theorem popLines_no_relocs (int : Bool) (rs : List Reg) :
    ∀ l ∈ popLines int rs, l.noRelocB = true := by
  intro l hl
  unfold popLines at hl
  generalize pairsOf rs = po at hl
  obtain ⟨ps, o⟩ := po
  simp only [List.mem_append, List.mem_map] at hl
  rcases hl with ⟨p, _, rfl⟩ | hl
  · cases int <;> rfl
  · cases o with
    | none => simp at hl
    | some r => simp only [List.mem_singleton] at hl; subst hl; cases int <;> rfl

theorem spAdjLines_no_relocs (sub : Bool) (size : Nat) :
    ∀ l ∈ spAdjLines sub size, l.noRelocB = true := by
  unfold spAdjLines
  split
  · simp
  · split
    · intro l hl; simp only [List.mem_singleton] at hl; subst hl; cases sub <;> rfl
    · intro l hl
      simp only [List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · exact loadConst64_no_relocs _ _ l hl
      · cases sub <;> rfl

theorem prologueLines_no_relocs (saves : List Reg) (size : Nat) :
    ∀ l ∈ prologueLines saves size, l.noRelocB = true := by
  intro l hl
  simp only [prologueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with (((rfl | rfl) | hl) | hl) | hl
  · rfl
  · rfl
  · exact pushLines_no_relocs _ _ l hl
  · exact pushLines_no_relocs _ _ l hl
  · exact spAdjLines_no_relocs _ _ l hl

theorem epilogueLines_no_relocs (saves : List Reg) (size : Nat) :
    ∀ l ∈ epilogueLines saves size, l.noRelocB = true := by
  intro l hl
  simp only [epilogueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with ((hl | hl) | hl) | (rfl | rfl)
  · exact spAdjLines_no_relocs _ _ l hl
  · exact popLines_no_relocs _ _ l hl
  · exact popLines_no_relocs _ _ l hl
  · rfl
  · rfl

theorem ainstLines_no_relocs {c : FnCtx} {af : AFunc} {a : AInst}
    {ps ps' : PState} {ls : List Line}
    (run : ainstLines c af a ps = .ok (ls, ps')) (noHook : NoHookAInst a) :
    ∀ l ∈ ls, l.noRelocB = true := by
  cases a with
  | inst m => exact lines_no_reloc run noHook
  | prologue =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, _⟩ := run
    split
    · exact prologueLines_no_relocs _ _
    · simp
  | epilogueRet =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, _⟩ := run
    split
    · exact epilogueLines_no_relocs _ _
    · intro l hl; simp only [List.mem_singleton] at hl; subst hl; rfl

theorem codeLinesE_no_relocs {c : FnCtx} {af : AFunc} :
    ∀ {code : List AInst} {ps ps' : PState} {ls : List Line},
      codeLinesE c af code ps = .ok (ls, ps') →
      (∀ a ∈ code, NoHookAInst a) → ∀ l ∈ ls, l.noRelocB = true
  | [], ps, ps', ls, run, _ => by
    simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at run
    rw [← run.1]; simp
  | a :: rest, ps, ps', ls, run, noHook => by
    simp only [codeLinesE, bind, Except.bind] at run
    split at run
    · cases run
    · rename_i first firstRun
      split at run
      · cases run
      · rename_i second secondRun
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at run
        rw [← run.1]
        intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact ainstLines_no_relocs firstRun (noHook a (by simp)) l hl
        · exact codeLinesE_no_relocs secondRun (fun m hm => noHook m (by simp [hm])) l hl

end Backend.Proof
