import FV.Opt.Proof.Dom

/-!
# The facts of `Cfg.dominators` (M1)

`Opt.DomFacts c` states what the completeness proofs of the mid-end need of the dominator tree
`c.idom` of a CFG `c` (`Cfg.build`): its entries are blocks, the entry block is the root, RPO
numbers decrease towards the root, every edge `u → x` out of a reachable block has `idom x` as a
tree ancestor of `u` (the edge certificate of `Opt.wfCert`), and every dominator of a reachable
block — every block on all paths from the entry to it (`Opt.ReachAvoid`) — is a tree ancestor
of it (completeness: the fixed number of rounds of `Cfg.dominators` suffices).
-/

namespace Opt

/-- `x` is reachable from the entry block along `succs` without passing through block `a`. -/
inductive ReachAvoid (succs : Array (List Nat)) (a : Nat) : Nat → Prop
  | entry : a ≠ 0 → ReachAvoid succs a 0
  | step {u x : Nat} : ReachAvoid succs a u → x ∈ succs[u]! → x ≠ a → ReachAvoid succs a x

/-- The facts of the dominator tree of a CFG (module doc). -/
structure DomFacts (c : Cfg) : Prop where
  lt : ∀ b x : Nat, c.idom[b]?.join = some x → x < c.size
  root : c.idom[0]?.join = none
  rank : ∀ b x : Nat, c.idom[b]?.join = some x →
    (c.rpoNum[x]?.join).getD 0 < (c.rpoNum[b]?.join).getD 0
  edge : ∀ u x : Nat, c.reachable u = true → x ∈ c.succs[u]! → ∀ y : Nat, c.idom[x]?.join = some y →
    Anc c.idom y u
  complete : ∀ a b : Nat, c.reachable b = true → a < c.size → ¬ ReachAvoid c.succs a b →
    Anc c.idom a b

end Opt
