import FV.Link.DeadCleanupExeLd
import FV.Link.Ld.SpecTotal

/-! # The shipped executable compiler is total on `lean-ld`'s inputs (A1, #409)

`Link.DeadCleanup.compileExe_total_ld` assumes a successful link (`link o ins = .ok r`) and a
plan agreeing with the link spec (`r.plan.specOkB`). **`compileExe_total_ldIn`** assumes neither:
its premises are decided on the original inputs — the link's options `o` and input files `ins`,
and the link spec `S` of the program part — without linking:

* resolution and `--gc-sections` succeed (`resolve`, `St.gc`: the first two steps of `link`);
* the layout's references resolve (`layRefsB`) and its relocations apply (`relsInB`), both
  decided without addresses (`FV/Link/Ld/{LayoutTotal,RelsTotal}.lean`);
* the headers and tables fit (`fitsB`) and the link spec's conditions (`specPreB`: the region in
  the `R E` segment, the program part's symbols, the TLS offsets, the CLIF data objects), decided
  on `lean-ld`'s placement of the inputs (`layPre`; no relocation applied, no byte written);
* the compiler's input conditions (`InScopeIn`, `layoutOkB`, `reachOkB`) on the link spec at
  the placement's symbols (`ldSpec`: `R` and the outside part's addresses are values of the
  plan's symbols, `LinkSpec.atSyms`, so the outside part of `symsPlanB` holds by construction).

Then `lean-ld` links (`link o ins = .ok r`) and the compiler succeeds on its output. The link
spec's addresses from the executable's symbol table (`Front.buildSpec`) stay the rust-lld
route's (`compileExe_total_reach_input`, with `file0OkB` checked on the file).
-/

namespace Link.DeadCleanup

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec Ld

/-- **The link spec at `lean-ld`'s placement**: `S` with the addresses of the placement's
symbols (`LinkSpec.atSyms`), at the Lean compiler's layout (`placed`). -/
def ldSpec (S : LinkSpec) (o : Opts) (st : St) (g : GcOut) : LinkSpec :=
  placed (S.atSyms ((layPre o st g).syms o st g).1)

/-- **The shipped executable compiler succeeds on `lean-ld`'s output, from conditions on the
inputs**: `lean-ld` links the inputs and `compileExe` succeeds on the executable. -/
theorem compileExe_total_ldIn {S : LinkSpec} {o : Opts} {ins : List Input} {st : St} {g : GcOut}
    (hres : resolve (o.entry :: o.undefs) ins = .ok st) (hgc : st.gc (o.entry :: o.undefs) o.gc = .ok g)
    (hrefs : layRefsB o st g = true) (hrels : relsInB o st g = true) (hfit : fitsB o st g = true)
    (hsp : specPreB (ldSpec S o st g) o st g = true)
    (hin : InScopeIn (ldSpec S o st g).input0 = true) (hl : (ldSpec S o st g).layoutOkB = true)
    (hreach : (ldSpec S o st g).reachOkB = true) :
    ∃ r, link o ins = .ok r ∧
      compileExe (ldSpec S o st g) r.img.write =
        .ok (patch r.img.write (offsetOf r.img.phs (ldSpec S o st g).R)
          (regionOf (ldSpec S o st g) (tpOff r.img.phs))) := by
  obtain ⟨r, hlk, hlay⟩ := link_okIn hres hgc hrefs hrels hfit
  have hsyms : r.plan.syms = ((layPre o st g).syms o st g).1 := by
    obtain ⟨e, ps, -, -, h⟩ := layout_parts hlay
    rw [h]; rfl
  have hP : r.plan.specOkB (ldSpec S o st g) = true :=
    specOkB_of_pre hlay hsp fun p hp => outside_inSyms (pl := r.plan) S.outside p (by
      rw [hsyms]
      exact hp)
  exact ⟨r, hlk, compileExe_total_ld hin hl hlk hP hreach⟩

end Link.DeadCleanup
