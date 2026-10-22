import FV.Link.Image
import FV.Backend.Proof.RelocProvDefs

/-! Executable relocation reach checks without linker totality proofs.
The existing predicates and theorem variants remain unchanged. Equality to
`reachOkB` is proved separately in `ReachCheckEq`, outside the CLI import graph. -/
namespace Link
open E2E E2E.LinkCheck E2E.BinCheck Backend.Proof.RelocProv

/-- The region's reach predicate using one address map and one size computation. -/
def LinkSpec.reachOkMap (P : LinkSpec) : Bool :=
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

end Link
