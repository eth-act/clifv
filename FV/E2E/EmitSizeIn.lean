import FV.Clif.Syntax

/-!
# The input-side size condition (`E2E.sizeOkB`)

`spillSizeOkB vcp` (`FV/E2E/EmitSize.lean`) bounds the spill allocation's code of the prepared
VCode. `sizeOkB f` is a condition on the CLIF function itself: a word bound `sizeBoundIn f`
summed over the blocks, statements and terminators of `f`, below `2 ^ 24`.

The per-item constants are upper bounds on what the pipeline makes of each item, in the word
measure of `EmitSize` (`instWords`, plus `20` words per operand for the spill loads and stores,
plus the callee-saved restores before a `Rets`):

* every block: its prologue (7), the callee-saved saves (18 moves of at most 20 words), the
  entry stores of a predecessor's terminator defs (at most 20 operands): `blkW = 767`;
* the entry block: the `Args` pseudo-instruction and a load per stack-passed parameter;
* a `jump`'s block arguments: the parallel copy through temporaries (4 moves per argument);
* a statement: its ISLE lowering (`stmtRunW`: 1000, a call `1500 + 25` per argument for the
  stack-argument stores) and a result `mov` per result;
* a terminator: its ISLE lowering (`termW`), the `tryCall` replacing a `try_call`'s call;
* the edge blocks `lowerFunction` creates for successors with arguments (`termEdgesW`) and the
  edge blocks `prepare` may create when it splits critical edges (`termTargets`).

`E2E.spillSizeOk_of_input` (`FV/E2E/EmitSizeProof.lean`) proves `spillSizeOkB vcp` from
`sizeOkB f`, given that the ISLE runs of the driver stay within `stmtRunW`/`termW`
(`E2E.RunWeights`).
-/

namespace E2E

/-- The fixed words of every block (prologue, callee-saved saves, entry stores). -/
def blkW : Nat := 767

/-- The weight bound of a statement's `lower` run. -/
def stmtRunW : Clif.Inst → Nat
  | .call _ args | .callIndirect _ _ args => 1500 + 25 * args.length
  | _ => 1000

/-- The weight bound of a statement: its `lower` run and a result `mov` per result. -/
def stmtW (s : Clif.Stmt) : Nat := stmtRunW s.inst + 41 * s.results.length

/-- The weight bound of a terminator's ISLE run. -/
def termW : Clif.Terminator → Nat
  | .ret _ => 600
  | .trap _ => 10
  | .jump _ => 10
  | .brif .. => 1000
  | .brTable _ _ tbl => 500 + 3 * (tbl.length + 1)
  | .tryCall _ args _ | .tryCallIndirect _ args _ => 1500 + 25 * args.length
  | .returnCall .. => 0

/-- The successor count of a terminator (`lowerFunction`'s successor labels). -/
def termTargets : Clif.Terminator → Nat
  | .brif .. => 2
  | .brTable _ _ tbl => tbl.length + 1
  | .tryCall _ _ et | .tryCallIndirect _ _ et => et.dests.length
  | _ => 0

/-- The words of an edge block with `n` arguments. -/
def edgeW (n : Nat) : Nat := blkW + 1 + 80 * n

/-- The edge block of a branch successor (only one with arguments gets one). -/
def bcEdgeW (bc : Clif.BlockCall) : Nat := if bc.args.isEmpty then 0 else edgeW bc.args.length

/-- The words of the edge blocks `lowerFunction` creates for a terminator. -/
def termEdgesW : Clif.Terminator → Nat
  | .brif _ a b => bcEdgeW a + bcEdgeW b
  | .brTable _ d tbl => bcEdgeW d + (tbl.map bcEdgeW).sum
  | .tryCall _ _ et | .tryCallIndirect _ _ et => (et.dests.map fun td => edgeW td.args.length).sum
  | _ => 0

/-- The block arguments of a `jump`. -/
def jumpArgsN : Clif.Terminator → Nat
  | .jump bc => bc.args.length
  | _ => 0

/-- The word bound of block `bi` (`B`). -/
def blockIn (bi : Nat) (B : Clif.Block) : Nat :=
  blkW + (if bi = 0 then 1 + 45 * B.params.length else 0) + 80 * jumpArgsN B.term +
    (B.body.map stmtW).sum + (termW B.term + 1) + termEdgesW B.term + (blkW + 1) * termTargets B.term

/-- The word bound of the whole function. -/
def sizeBoundIn (f : Clif.Function) : Nat :=
  (f.blocks.zipIdx.map fun (B, bi) => blockIn bi B).sum

/-- **The input-side size condition**: the word bound below `2 ^ 24`. -/
def sizeOkB (f : Clif.Function) : Bool := decide (sizeBoundIn f < 2 ^ 24)

end E2E
