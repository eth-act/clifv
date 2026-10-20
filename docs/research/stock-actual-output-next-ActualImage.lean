import FV.Link.DeadCleanupImage

/-! The existing byte writer parameterized by the actual compiler result table.
Every placement, relocation, code-map, ELF-region and outside-image check is
retained. The old linker functions and their theorem variants are untouched. -/
set_option autoImplicit false
namespace Link
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend

def leanLinkWithResults (S : LinkSpec) (file0 : ByteArray)
    (results : LinkInput → Res) : Except String ByteArray :=
  match phdrs (fileRd file0) with
  | none => .error "no program headers"
  | some phs =>
    -- Compile once and use that same result table for depth, relocations and bytes.
    let I0 := S.input0
    let Rs := results I0
    let I := I0.withDepth Rs
    let T := tabOf Rs
    let tp := tpOff phs
    if !S.placeOkB then .error "the placement's conditions fail (placeOkB)"
    else if !(Rs.all (·.2.toBool)) then .error "the compiler's pipeline rejects a function"
    else if !(S.namesOkB T) then .error "the compiled functions' names are not the placement's (namesOkB)"
    else if !(S.sizesOkB T) then .error "the compiled code's sizes are not the placement's (sizesOkB)"
    else if !(T.all fun e => relocsOkB I tp e.2) then .error "a relocation fails the checks (relocsOkB)"
    else if !(codeMapB I T) then .error "the code map check fails (codeMapB)"
    else
      let B := ByteArray.mk (regionBytes I tp ((T.take S.funcs.length).map (·.2))).toArray
      let off := offsetOf phs S.R
      if !regionOkB file0 S.R B.size off then
        .error "the region is not a read-only part of one PT_LOAD segment (regionOkB)"
      else
        let file := patch file0 off B
        if !outsideOkB I S.data file then
          .error "rust-lld's output fails the checks: static headers, data objects, symbols (outsideOkB)"
        else .ok file

/-- The legacy instance preserves every result and error for arbitrary inputs. -/
theorem leanLinkWithResults_plain (S : LinkSpec) (file0 : ByteArray) :
    leanLinkWithResults S file0 parResultsT = leanLink S file0 := by
  rfl

/-- The cleanup instance preserves every result and error for arbitrary inputs. -/
theorem leanLinkWithResults_cleanup (S : LinkSpec) (file0 : ByteArray) :
    leanLinkWithResults S file0 DeadCleanup.parResultsCleanupT =
      DeadCleanup.leanLink S file0 := by
  rfl
end Link
