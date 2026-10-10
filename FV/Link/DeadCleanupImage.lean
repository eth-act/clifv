import FV.Link.Image
import FV.Link.LayoutFacts
import FV.E2E.DeadCleanupLinkScope

/-! Cleanup executable pipeline. The legacy linker and input scope remain available. -/
namespace Link.LinkSpec
open E2E E2E.LinkCheck Backend
variable (S : LinkSpec)

def inputCleanup : LinkInput := S.input0.withDepth S.input0.resultsCleanupT

theorem inputCleanup_results : S.inputCleanup.resultsCleanup = S.inputCleanup.resultsCleanupT :=
  LinkInput.resultsCleanup_fallback rfl

@[simp] theorem inputCleanup_funcs : S.inputCleanup.funcs = S.funcs := rfl
@[simp] theorem inputCleanup_addrs : S.inputCleanup.addrs = S.addrs := rfl
@[simp] theorem inputCleanup_aliases : S.inputCleanup.aliases = [] := rfl
@[simp] theorem inputCleanup_raStar : S.inputCleanup.raStar = S.R + S.size := rfl
@[simp] theorem inputCleanup_syms : S.inputCleanup.syms =
    S.symNames.filterMap (fun n => (S.addrs.lookup n).map (n, ·)) := rfl

theorem inputCleanup_baseOf_name {S : LinkSpec} (hP : PlaceOk S) {i : Nat} (hi : i < S.funcs.length) :
    S.inputCleanup.baseOf S.names[i]! = S.R + (offs S.sizes 0)[i]! :=
  baseOf_name hP hi
end Link.LinkSpec

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend

def parResultsCleanupT (I : LinkInput) : Res :=
  parMap (fun fi => let f := fi.func
    (f, pipeCleanupT f fi.k (BitVec.ofNat 64 (I.baseOf f.name)) (raJ fi.ra fi.j))) I.funcs

theorem parResultsCleanupT_eq (I : LinkInput) : parResultsCleanupT I = I.resultsCleanupT := by
  simp only [parResultsCleanupT, parMap_eq]; rfl

/-- **The Lean linker**: the executable `file0` (the outside part, linked around a placeholder
of the region) with the program part written into the region. -/
def leanLink (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  match phdrs (fileRd file0) with
  | none => .error "no program headers"
  | some phs =>
    -- the pipeline once, in parallel: `S.inputCleanup` is `S.input0.withDepth S.input0.resultsCleanupT`, and
    -- `resultsT` does not read the depth
    let I0 := S.input0
    let Rs := parResultsCleanupT I0
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


end Link.DeadCleanup
