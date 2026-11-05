import FV.Link.ExeUCompile
import FV.Link.UnwCheckIn

/-!
# Measuring the unwinding conditions (S10g, #404; report only)

`lake exe lean-link` prints, per executable, how many compiled functions fail each per-function
unwinding check `unwFnsB` decides (`unwCheck`, `callSites`, `unwindRows`, `padsNonzeroB`,
`savedCheck`), the input conditions of `tryInfoOk_of_input` (`tryTablesB`) and
`unwCheck_complete` (`tryRetsB`), `aliasEntryOkB` (the premise of the generic
`padsNonzero_complete`; a theorem on the pipeline's output, `alias_ne_entry`/
`fwd_ne_entry_input`, so this row is a cross-check expected to be 0), and the
functions whose `.eh_frame` entry `ehOkR` rejects (`fnEhFail`). Nothing here is a premise or a
decision of the compiler; it measures how often the conditions of the totality argument fail on
real code.
-/

namespace Link.DeadCleanup

set_option autoImplicit false

open E2E E2E.LinkCheck Backend Unw EhCheck E2E.Elf

/-- The per-function conditions measured, in report order. -/
def unwConds : List (String × (Clif.Function → Art → Bool)) :=
  [("unwCheck", fun g a => Backend.Proof.Driver.unwCheck g a.vc),
   ("callSites", fun _ a => (Backend.callSites a.af a.fa).toBool),
   ("unwindRows", fun _ a => (Backend.unwindRows a.af a.fa).toBool),
   ("padsNonzeroB", fun _ a => Backend.Proof.padsNonzeroB a.af a.fa),
   ("savedCheck", fun _ a => Backend.savedCheck a.vcp a.rf),
   ("tryTablesB", fun g _ => Link.EhCheck.Complete.tryTablesB g),
   ("tryRetsB", fun g _ => Link.EhCheck.Complete.tryRetsB g),
   ("aliasEntryOkB", fun _ a => Link.EhCheck.Complete.aliasEntryOkB a.af a.fa)]

/-- The functions whose `.eh_frame` entry `ehOkR` rejects (`none`: the program-level part of
`ehOkR` fails, with its reason). -/
def ehFails (R : Res) (file : ByteArray) : Except String (List String) :=
  match phdrs (fileRd file) with
  | none => .error "no program headers"
  | some phs => match ehHdrOf phs with
    | none => .error "not exactly one PT_GNU_EH_FRAME"
    | some h =>
      match parseHdr h (memRd file h 12) with
      | some hd =>
        let loc := fun i => (hdrEntry (memRd file) h i).map (·.1)
        if hd.count = 0 then .error ".eh_frame_hdr: no table"
        else if !sortedB loc hd.count then .error ".eh_frame_hdr: table not sorted"
        else .ok <| (progOf R).funcs.filterMap fun g =>
          (fnEhFail (memRd file) phs h hd.count (artOf R g)).map fun e => s!"{g.name}: {e}"
      | none => .error ".eh_frame_hdr: header outside the model"

/-- **The report**: the number of functions (and with a `try_call`), per condition the number
failing it and the first failing names, and `ehOkR`'s failures. -/
def unwReport (S : LinkSpec) (file : ByteArray) : String :=
  let R := parResultsCleanupT S.input0
  let fs := (progOf R).funcs
  let rows := parMap (fun g => let a := artOf R g; unwConds.map fun (_, c) => c g a) fs
  let nTry := (fs.filter fun g => g.blocks.any (·.term.isTry)).length
  let per := unwConds.zipIdx.map fun ((n, _), i) =>
    let bad := (fs.zip rows).filter fun (_, r) => !(r[i]?.getD true)
    if bad.isEmpty then s!"{n} 0" else s!"{n} {bad.length} {(bad.take 3).map (·.1.name)}"
  let eh := match ehFails R file with
    | .error e => s!"ehOkR: {e}"
    | .ok [] => "ehOkR 0"
    | .ok l => s!"ehOkR {l.length} {l.take 2}"
  s!"{fs.length} function(s), {nTry} with try_call; failing: {", ".intercalate per}, {eh}"

end Link.DeadCleanup
