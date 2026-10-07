import FV.E2E.EmitSize
import FV.Backend.Proof.IselSzDefs

/-!
# The size bound from the input (V6c): measures

`spillSizeOkB vcp` (`EmitSize`) bounds the words of the spill allocation's code of the prepared
VCode. This file defines the measures the input-side bound goes through:

* on a VCode (`vcW M vc`): per block its prologue (7), callee-saved saves (`restW`), the entry
  stores of a predecessor's terminator defs (`10 · M`, `M` bounding every instruction's register
  operands, `maxRC`), the parallel copy of its branch arguments (`40` per argument), and the
  weight `wtA` of its instructions (`IselSzDefs`); `vcTg vc`: its branch targets (each may become
  an edge block of `prepare`, of weight `jumpBW M`);
* on the CLIF function (`sizeBoundIn f`): the same per block, with the ISLE runs' bounds
  (`stmtSzB`, `termSzB`, `termTgB`: the driver's contract `IselSz`), the entry block's `Args`
  and parameter loads, the result `mov`s, the `tryCall` replacing a `try_call`'s call, and the
  edge blocks `lowerFunction` creates; `sizeOkB f` requires it below `2 ^ 24`.
-/

namespace E2E

open Backend Backend.Proof.Cov Backend.Proof.Driver

/-! ## On a VCode -/

/-- The largest `regCount` of an instruction of `vc` (at least 5). -/
def maxRC (vc : VCode) : Nat :=
  vc.blocks.foldl (fun m vb => vb.insts.foldl (fun m i => max m (regCount i)) m) 5

/-- The words of block `vb`'s spill-allocated code, `M` bounding every instruction's register
operands: prologue, callee-saved saves, entry stores, the branch arguments' parallel copy, and
its instructions' weight. -/
def vbW (M : Nat) (vb : VBlock) : Nat :=
  7 + restW + 10 * M + 40 * vb.branchArgs.size + wtA vb.insts

/-- The words of a VCode's spill-allocated code. -/
def vcW (M : Nat) (vc : VCode) : Nat := (vc.blocks.toList.map (vbW M)).sum

/-- The branch targets of a VCode's instructions. -/
def vcTg (vc : VCode) : Nat := (vc.blocks.toList.map fun vb => tgA vb.insts).sum

/-- The words of an edge block `prepare` creates (one `jump`). -/
def jumpBW (M : Nat) : Nat := 7 + restW + 10 * M + szInstW (.jump 0)

/-! ## On the CLIF function -/

/-- The words of a result `mov` (`lowerFunction`'s `extra`). -/
def movW : Nat := 101

/-- The words of the entry block's `Args` (one pair per register-passed parameter) and
stack-passed parameter loads. -/
def entryIn (B : Clif.Block) : Nat := 1 + 125 * B.params.length

/-- A statement's bound: its run and a result `mov` per result. -/
def stmtIn (s : Clif.Stmt) : Nat := stmtSzB s.inst + movW * s.results.length

/-- The successors of a `try_call` (`ExnTable.dests`; none for another terminator). -/
def tryDestsIn : Clif.Terminator → Nat
  | .tryCall _ _ et | .tryCallIndirect _ _ et => et.dests.length
  | _ => 0

/-- A terminator's bound: its run, and for a `try_call` the `tryCall` replacing its call (one
word more, a target per successor). -/
def termIn (t : Clif.Terminator) : Nat :=
  termSzB t + (match t with
    | .tryCall .. | .tryCallIndirect .. => 1 + tryDestsIn t
    | _ => 0)

/-- The arguments of a `jump` (its block's branch arguments). -/
def jumpArgsIn : Clif.Terminator → Nat
  | .jump bc => bc.args.length
  | _ => 0

/-- The argument counts of the edge blocks `lowerFunction` creates for a terminator: one per
`brif`/`br_table` successor with arguments, one per `try_call` successor. -/
def edgeArgsIn : Clif.Terminator → List Nat
  | .brif _ a b => [a, b].filterMap fun bc => if bc.args.isEmpty then none else some bc.args.length
  | .brTable _ d tbl =>
    (d :: tbl).filterMap fun bc => if bc.args.isEmpty then none else some bc.args.length
  | .tryCall _ _ et | .tryCallIndirect _ _ et => et.dests.map (·.args.length)
  | _ => []

/-- A bound on every instruction's register operands: the entry `Args`' parameters, and the
weight over 20 of every ISLE run (`szInstW` counts 20 per register operand). -/
def mIn (f : Clif.Function) : Nat :=
  f.blocks.foldl (fun m B => max m (max B.params.length
    (max ((B.body.map fun s => stmtSzB s.inst / 20).foldl max 0) (termSzB B.term / 20)))) 5

/-- The bound of block `bi` (`B`) of `f`, `M` bounding the register operands. -/
def blockIn (M : Nat) (bi : Nat) (B : Clif.Block) : Nat :=
  7 + restW + 10 * M + 40 * jumpArgsIn B.term + (if bi = 0 then entryIn B else 0) +
    (B.body.map stmtIn).sum + termIn B.term

/-- The bound of an edge block of `lowerFunction` with `n` arguments (one `jump`). -/
def edgeIn (M n : Nat) : Nat := 7 + restW + 10 * M + 40 * n + szInstW (.jump 0)

/-- The words of `lowerFunction`'s blocks and edge blocks, `M` bounding the register operands. -/
def vcIn (M : Nat) (f : Clif.Function) : Nat :=
  (f.blocks.zipIdx.map fun (B, bi) => blockIn M bi B).sum +
    (f.blocks.map fun B => ((edgeArgsIn B.term).map (edgeIn M)).sum).sum

/-- The branch targets of `lowerFunction`'s output: each terminator run's, a `tryCall`'s
successors, an edge block's `jump`. -/
def tgIn (f : Clif.Function) : Nat :=
  (f.blocks.map fun B => termTgB B.term + tryDestsIn B.term + (edgeArgsIn B.term).length).sum

/-- **The input-side word bound**: `lowerFunction`'s blocks and edge blocks, and an edge block of
`prepare` per branch target. -/
def sizeBoundIn (f : Clif.Function) : Nat :=
  vcIn (mIn f) f + jumpBW (mIn f) * tgIn f

/-- **The input-side size condition**: the word bound below `2 ^ 24`. -/
def sizeOkB (f : Clif.Function) : Bool := decide (sizeBoundIn f < 2 ^ 24)

end E2E
