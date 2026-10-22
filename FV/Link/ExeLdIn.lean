import FV.Link.DeadCleanupExeLd
import FV.Link.Ld.SpecTotal
import FV.Link.Ld.RelsFast

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

/-- When the placement's symbols give `S`'s own addresses, the link spec at the placement is
`S`'s (`lake exe lean-link --ld` decides the premises on the spec it compiled). -/
theorem ldSpec_self {S : LinkSpec} {o : Opts} {st : St} {g : GcOut}
    (hR : (S.atSyms ((layPre o st g).syms o st g).1).R = S.R)
    (ho : (S.atSyms ((layPre o st g).syms o st g).1).outside = S.outside) : ldSpec S o st g = placed S := by
  unfold ldSpec
  congr 1
  revert hR ho
  cases S
  simp only [LinkSpec.atSyms]
  intro hR ho
  rw [hR, ho]

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

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck Backend.Proof.RelocProv

/-- **`reachOkB` with the link map as a hash map and the region's size computed once**
(`reachOkPar_eq`; `reachOkB` looks every name up in the list and sums the sizes per check). -/
def LinkSpec.reachOkPar (P : LinkSpec) : Bool :=
  let am := addrMap P.addrs
  let sz := P.size
  let R := P.R
  let addr := fun n => (am[n]?).getD 0
  P.funcs.all fun fi =>
    let f := fi.func
    (externNames f).all (fun n => let t := addr n
      t % 4 == 0 && decide (R + sz ≤ t + 2 ^ 27) && decide (t < R + 2 ^ 27)) &&
    (refNames f).all fun n => (refOffs f).all fun o =>
      let T := (BitVec.ofNat 64 (addr n) + BitVec.ofInt 64 o).toNat
      decide (pageOf (R + sz) ≤ pageOf T + 2 ^ 20) && decide (pageOf T < pageOf R + 2 ^ 20)

theorem LinkSpec.reachOkPar_eq (P : LinkSpec) : P.reachOkPar = P.reachOkB := by
  have h : ∀ n, P.input0.addrOf n = ((addrMap P.addrs)[n]?).getD 0 := fun n => by
    rw [addrMap_get]; rfl
  simp only [reachOkPar, reachOkB, refsReachB, callReachB, pageReachB, LinkInput.symAddr, h]

end Link
