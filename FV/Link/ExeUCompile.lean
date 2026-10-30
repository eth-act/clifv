import FV.Link.EhCheck
import FV.Link.UnwFns
import FV.Link.DeadCleanupCompile

/-!
# The executable compiler with the unwind tables checked (S10f)

`compileExeU S file0`: `Link.DeadCleanup.compileExe`, then `unwOkB` on the written executable —
the unwind tables rust-lld wrote for the region are the compiled functions'
(`Link.EhCheck.ehOkR`) and the compiled functions pass the unwinding checks
(`Link.EhCheck.unwFnsB`). `lake exe lean-link` evaluates `unwOkB` after `compileExe` (and
reports the exceptional edges as covered only when it holds). `FV/Link/ExeUnwind.lean` proves
what it guarantees (`compileExe_correct_unwind`).
-/

namespace Link.DeadCleanup

set_option autoImplicit false

open E2E E2E.LinkCheck Backend Unw EhCheck E2E.Elf

/-! ## Diagnostics: the first reason `ehOkR` fails (messages only; the decision is `unwOkB`) -/

/-- The first conjunct of `fnEhOkB` the function `a` fails. -/
def fnEhFail (rd : Nat → Nat → List UInt8) (phs : List Phdr) (h cnt : Nat) (a : Art) :
    Option String :=
  match tabsOf a with
  | none => some "callSites/unwindRows fail"
  | some T =>
    let s := a.base.toNat
    let n := a.fb.size
    let loc := fun i => (hdrEntry rd h i).map (·.1)
    let segOk := match segIn phs s with
      | some p => decide (s + n ≤ p.vaddr + p.memsz)
      | none => false
    if !segOk then some "code not inside one PT_LOAD segment"
    else match search loc s 0 cnt with
    | none => some ".eh_frame_hdr search: unreadable entry"
    | some j =>
      if !decide (j < cnt) then some ".eh_frame_hdr search: index out of range"
      else match hdrEntry rd h j with
      | none => some ".eh_frame_hdr: unreadable entry"
      | some (l, fx) =>
        if l != s then some s!".eh_frame_hdr: no entry for {s} (found {l})"
        else if !(decide (j + 1 = cnt) || match loc (j + 1) with
            | some y => decide (s + n ≤ y)
            | none => false) then some ".eh_frame_hdr: next entry inside the code"
        else match fdeAt rd fx with
        | none => some s!"FDE at {fx}: not decodable (outside the model)"
        | some f =>
          if f.pcBegin != s then some "FDE: pc_begin differs"
          else if !decide (n ≤ f.pcRange) then some s!"FDE: pc_range {f.pcRange} < {n}"
          else if !decide (f.pcBegin + f.pcRange < 2 ^ 64) then some "FDE: range wraps"
          else match (fdeTablesW rd lsdaWin f).orElse fun _ => fdeTables rd f with
          | none => some "FDE: LSDA not decodable (outside the model)"
          | some T' =>
            if T'.cie != T.cie then some s!"FDE: CIE instructions differ: {repr T'.cie} vs {repr T.cie}"
            else if T'.fde != T.fde then
              some s!"FDE: instructions differ: {repr T'.fde} vs {repr T.fde}"
            else if T'.lsda != T.lsda then
              some s!"FDE: LSDA differs: {repr T'.lsda} vs {repr T.lsda}"
            else none

/-- The first reason `ehOkR R file` fails (`none`: it holds, or a reason not listed). -/
def ehFail (R : Res) (file : ByteArray) : Option String :=
  match phdrs (fileRd file) with
  | none => some "no program headers"
  | some phs => match ehHdrOf phs with
    | none => some "not exactly one PT_GNU_EH_FRAME"
    | some h =>
      match parseHdr h (memRd file h 12) with
      | some hd =>
        let loc := fun i => (hdrEntry (memRd file) h i).map (·.1)
        if hd.count = 0 then some ".eh_frame_hdr: no table"
        else if !sortedB loc hd.count then some ".eh_frame_hdr: table not sorted"
        else
          (progOf R).funcs.findSome? fun g =>
            (fnEhFail (memRd file) phs h hd.count (artOf R g)).map fun e => s!"{g.name}: {e}"
      | none => some ".eh_frame_hdr: header outside the model"

/-- The first per-function unwinding check `unwFnsB R` fails. -/
def unwFnsFail (R : Res) : Option String :=
  (progOf R).funcs.findSome? fun g =>
    let a := artOf R g
    if !Backend.Proof.Driver.unwCheck g a.vc then some s!"{g.name}: unwCheck"
    else if !(Backend.callSites a.af a.fa).toBool then some s!"{g.name}: callSites"
    else if !(Backend.unwindRows a.af a.fa).toBool then some s!"{g.name}: unwindRows"
    else if !Backend.Proof.padsNonzeroB a.af a.fa then some s!"{g.name}: padsNonzeroB"
    else if !Backend.Proof.lastCallsOk a.af a.fa then some s!"{g.name}: lastCallsOk"
    else if !Backend.savedCheck a.vcp a.rf then some s!"{g.name}: savedCheck"
    else none

/-- The first reason `unwOkB S file` fails. -/
def unwFail (S : LinkSpec) (file : ByteArray) : String :=
  let R := parResultsCleanupT S.input0
  ((ehFail R file).orElse fun _ => unwFnsFail R).getD "unknown"

/-- **The unwinding checks of the written executable `file`**: its unwind tables
(`ehOkR`) and the compiled functions' unwinding checks (`unwFnsB`). -/
def unwOkB (S : LinkSpec) (file : ByteArray) : Bool :=
  let R := parResultsCleanupT S.input0
  EhCheck.ehOkR R file && EhCheck.unwFnsB R

/-- **The executable compiler with the unwind tables checked.** -/
def compileExeU (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  match compileExe S file0 with
  | .ok file =>
    if unwOkB S file then .ok file
    else .error "the executable's unwind tables are not the compiled functions' (unwOkB)"
  | .error e => .error e

theorem compileExeU_spec {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) : compileExe S file0 = .ok file ∧ unwOkB S file = true := by
  unfold compileExeU at h
  split at h
  · rename_i f hf
    by_cases hu : unwOkB S f = true
    · rw [if_pos hu] at h
      cases h
      exact ⟨hf, hu⟩
    · rw [if_neg hu] at h
      cases h
  · cases h

/-- The compiled functions `unwOkB` checks are the input's (`S.inputCleanup.resultsCleanup`). -/
theorem parResultsCleanupT_input (S : LinkSpec) :
    parResultsCleanupT S.input0 = S.inputCleanup.resultsCleanup := by
  rw [parResultsCleanupT_eq, S.inputCleanup_results]
  rfl

end Link.DeadCleanup
