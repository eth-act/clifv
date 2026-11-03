import FV.E2E.StockAcquireAllocatedNoHooks
import FV.E2E.StockAcquireBlockNoRelocs

namespace Backend.Proof
open Backend E2E Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

theorem blocksLinesE_no_relocs {c : FnCtx} {af : AFunc} :
    ∀ {blocks : List (Label × Array AInst)} {ps ps' : PState} {lines : List Line},
      blocksLinesE c af blocks ps = .ok (lines, ps') →
      (∀ block ∈ blocks, ∀ inst ∈ block.2.toList, NoHookAInst inst) →
      ∀ line ∈ lines, line.noRelocB = true
  | [], ps, ps', lines, run, _ => by
    simp only [blocksLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at run
    rw [← run.1]; simp
  | (label, code) :: blocks, ps, ps', lines, run, noHook => by
    simp only [blocksLinesE, bind, Except.bind] at run
    split at run
    · cases run
    · rename_i first firstRun
      split at run
      · cases run
      · rename_i second secondRun
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at run
        rw [← run.1]
        intro line member
        simp only [List.cons_append, List.mem_cons, List.mem_append] at member
        rcases member with rfl | member | member
        · rfl
        · exact codeLinesE_no_relocs firstRun (noHook (label, code) (by simp)) line member
        · exact blocksLinesE_no_relocs secondRun (fun b hb => noHook b (by simp [hb])) line member

theorem noRelocB_invertTo (inst : Insn) (label : Lbl) (trap : Option Clif.TrapCode) :
    (Line.ins (inst.invertTo label) trap).noRelocB = (Line.ins inst trap).noRelocB := by
  cases inst <;> rfl

theorem ftStep_no_relocs {line : Line} (noHook : line.noRelocB = true) (first second : Option Line) :
    ∀ out ∈ (ftStep line first second).1, out.noRelocB = true := by
  unfold ftStep
  repeat' split
  all_goals simp_all [noRelocB_invertTo]
  all_goals rfl

theorem ftList_no_relocs_aux : ∀ (bound : Nat) (lines : List Line), lines.length ≤ bound →
    (∀ line ∈ lines, line.noRelocB = true) → ∀ line ∈ ftList lines, line.noRelocB = true
  | _, [], _, _ => by simp [ftList]
  | 0, _ :: _, bound, _ => by simp at bound
  | bound + 1, head :: tail, length, noHook => by
    have positive := (ftStep_pos head tail[0]? tail[1]?).1
    rw [ftList_cons]
    intro line member
    rcases List.mem_append.mp member with member | member
    · exact ftStep_no_relocs (noHook head (by simp)) _ _ line member
    · exact ftList_no_relocs_aux bound _ (by simp at length ⊢; omega)
        (fun l hl => noHook l (List.mem_of_mem_drop hl)) line member

theorem ftList_no_relocs {lines : List Line} (noHook : ∀ line ∈ lines, line.noRelocB = true) :
    ∀ line ∈ ftList lines, line.noRelocB = true :=
  ftList_no_relocs_aux lines.length lines (Nat.le_refl _) noHook

theorem relaxLine_no_relocs {line : Line} (noHook : line.noRelocB = true) (far : Lbl → Bool) :
    ∀ out ∈ relaxLine far line, out.noRelocB = true := by
  cases line with
  | label label => simp [relaxLine, Line.relaxable?, Line.noRelocB]
  | word target base => simp [relaxLine, Line.relaxable?, Line.noRelocB]
  | ins inst trap =>
    cases trap with
    | some trap => simpa [relaxLine, Line.relaxable?] using noHook
    | none =>
      cases target : inst.relaxTarget? with
      | none => simpa [relaxLine, Line.relaxable?, target] using noHook
      | some label =>
        by_cases isFar : far label = true
        · simp only [relaxLine, Line.relaxable?, target, Option.map_some, isFar, ite_true,
            List.mem_cons, List.not_mem_nil, or_false]
          intro out member
          rcases member with rfl | rfl
          · simpa only [noRelocB_invertTo] using noHook
          · rfl
        · simpa [relaxLine, Line.relaxable?, target, isFar] using noHook

theorem relaxLines_no_relocs {lines : List Line} (noHook : ∀ line ∈ lines, line.noRelocB = true)
    (far : Lbl → Bool) : ∀ line ∈ relaxLines far lines, line.noRelocB = true := by
  intro line member
  obtain ⟨original, located, emitted⟩ := List.mem_flatMap.mp member
  exact relaxLine_no_relocs (noHook original located) far line emitted

theorem trapLines_no_relocs (traps : List (Lbl × Clif.TrapCode)) :
    ∀ line ∈ trapLines traps, line.noRelocB = true := by
  intro line member
  obtain ⟨trap, _, member⟩ := List.mem_flatMap.mp member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

/-- Successful actual emission preserves the no-relocation property through branch rewriting and trap stubs. -/
theorem emitFunc_no_relocs {k : Nat} {af : AFunc} {fa : FnAsm}
    (run : emitFunc k af = .ok fa)
    (noHook : ∀ block ∈ af.blocks.toList, ∀ inst ∈ block.2.toList, NoHookAInst inst) :
    ∀ line ∈ fa.lines.toList, line.noRelocB = true := by
  obtain ⟨body, ps, bodyRun, lines, _⟩ := emitFunc_ok run
  rw [lines]
  apply relaxLines_no_relocs
  intro line member
  rcases List.mem_append.mp member with member | member
  · exact ftList_no_relocs (blocksLinesE_no_relocs bodyRun noHook) line member
  · exact trapLines_no_relocs _ line member

/-- Successful layout records no relocations when actual emitted instructions have none. -/
theorem layout_no_relocations {fa : FnAsm} {fb : FnBin}
    (layout : fa.layout = .ok fb) (noReloc : ∀ line ∈ fa.lines.toList, line.noRelocB = true) :
    fb.relocs = [] := by
  cases records : fb.relocs with
  | nil => rfl
  | cons relocation rest =>
    have member : relocation ∈ fb.relocs := by rw [records]; simp
    obtain ⟨j,inst,trap,located,relocated,_⟩ := (FnAsm.layout_relocs layout relocation).mp member
    have clean := noReloc _ (List.mem_of_getElem? located)
    change inst.reloc?.isNone = true at clean
    rw [relocated] at clean
    cases clean

end Backend.Proof
