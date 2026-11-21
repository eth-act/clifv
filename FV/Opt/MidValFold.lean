import FV.Opt.MidValCert
import FV.Opt.ConstPhi

/-!
# Branch folding before the mid-end validator's comparison (#1119, `rewrite:blocks`)

Cranelift's mid-end turns a `brif` (or `br_table`) whose condition is a constant into a `jump`
and then drops the blocks that became unreachable; the validator, which compares `f` and `g`
block by block, rejected every such pair (`rewrite:blocks`). This file folds the same branches
of the unoptimised function `f` before the comparison, so that the existing check runs on the
folded `f` (the theorem stays about the original `f`: the fold is proved to be simulated by its
input, `Opt.MidVal.foldBr_simU`, `FV/Opt/Proof/MidValFold.lean`).

* `constEval K i`: the constant value of a pure, non-partial instruction whose operands all have
  constants in `K` (`Clif.evalInst` in a frame holding `K`), or of an `iconst`.
* `kMap f` (untrusted): constants of `f`'s values, by passes over the statements in layout order;
  only values below `f.freshValue`.
* `kOk f K` (the checker the proof relies on): no block parameter has a constant; every statement
  that defines a value with a constant `v` defines only that value and `constEval K` gives `v`
  for it. Then, in every run of `f`, a value with a constant holds it or nothing (each register
  is written only by its definitions), so a branch on it can only take the branch the constant
  selects.
* `foldBr f bs`: when `kOk f (kMap f)`, each block of `bs` whose `brif`/`br_table` condition
  has a constant ends in the `jump` it selects; otherwise `f`.
* `foldPre f bs = ConstPhi.run (foldBr f bs)`: the folded function without the blocks that became
  unreachable (`Opt.removeUnreachable`, and constant-phi removal, inside `ConstPhi.run`).
* `foldBlocks hints`: the fold requests among the hints of `checkCertC` (`FV/Opt/MidValCond.lean`):
  a hinted block with an empty wrapper chain, which `condPrep` leaves unchanged.
* `foldCands f g` (untrusted): the blocks whose `brif`/`br_table` is a `jump` in `g`.
-/

namespace Opt.MidVal

open Clif

/-- The frame in which `constEval` evaluates an instruction: registers `K`, no function, no
slots (a pure instruction with operands reads neither). -/
def kFrame (K : ValueId → Option Val) : Frame :=
  { func := default, regs := K, slots := [], body := [], term := .ret [] }

/-- The constant value of `i` when its operands have the constants `K`: an `iconst`, or a pure,
non-partial instruction with operands, evaluated by `Clif.evalInst` (module doc). -/
def constEval (K : ValueId → Option Val) (i : Inst) : Option Val :=
  match i with
  | .iconst ty imm => some ⟨ty, imm⟩
  | _ =>
    if isPure i && !partialK i && !(operands i).isEmpty && (operands i).all (fun x => (K x).isSome) then
      match evalInst (kFrame K) Mem.empty i with
      | .ok ([v], _) => some v
      | _ => none
    else none

/-- One pass of `kMap` over `f`'s statements in layout order. -/
def kPass (f : Function) (hm : Std.HashMap ValueId Val) : Std.HashMap ValueId Val :=
  f.blocks.foldl (fun hm b => b.body.foldl (fun hm st =>
    match st.results with
    | [r] =>
      if hm.contains r then hm
      else match constEval (fun x => hm[x]?) st.inst with
        | some v => hm.insert r v
        | none => hm
    | _ => hm) hm) hm

/-- **The constants of `f`'s values** (untrusted; `kOk` checks them): passes of `kPass` until
nothing changes (at most four), restricted to the values below `f.freshValue`. -/
def kMap (f : Function) : ValueId → Option Val :=
  let rec go : Nat → Std.HashMap ValueId Val → Std.HashMap ValueId Val
    | 0, hm => hm
    | n + 1, hm =>
      let hm' := kPass f hm
      if hm'.size == hm.size then hm' else go n hm'
  let hm := go 4 {}
  let fv := f.freshValue
  fun x => if x < fv then hm[x]? else none

/-- **The constants' checker** (module doc). -/
def kOk (f : Function) (K : ValueId → Option Val) : Bool :=
  f.blocks.all fun b =>
    b.params.all (fun p => (K p.1).isNone) &&
    b.body.all fun st => st.results.all fun r =>
      match K r with
      | none => true
      | some v => st.results == [r] && decide (constEval K st.inst = some v)

/-- A terminator with a constant condition as the `jump` it takes. -/
def foldT (K : ValueId → Option Val) : Terminator → Terminator
  | .brif c t e => match K c with
    | some v => .jump (if Sem.truthy v.bits then t else e)
    | none => .brif c t e
  | .brTable x d tbl => match K x with
    | some v => .jump (tbl[v.toNat]?.getD d)
    | none => .brTable x d tbl
  | t => t

/-- A block of `bs` with its terminator folded. -/
def foldBlock (K : ValueId → Option Val) (bs : List BlockId) (b : Block) : Block :=
  { b with term := if bs.contains b.id then foldT K b.term else b.term }

/-- Every block through `foldBlock`. -/
def foldFn (f : Function) (K : ValueId → Option Val) (bs : List BlockId) : Function :=
  { f with blocks := f.blocks.map (foldBlock K bs) }

/-- **Branch folding** (module doc): the blocks of `bs` with their constant-condition branches
folded, when `kOk` accepts `f`'s constants; `f` otherwise. -/
def foldBr (f : Function) (bs : List BlockId) : Function :=
  if bs.isEmpty then f
  else
    let K := kMap f
    if kOk f K then foldFn f K bs else f

/-- **The folded function without its unreachable blocks** (module doc). -/
def foldPre (f : Function) (bs : List BlockId) : Function :=
  ConstPhi.run (foldBr f bs)

/-- The fold requests among `checkCertC`'s hints: the blocks hinted with an empty wrapper
chain. -/
def foldBlocks (hints : List (BlockId × List Wrap)) : List BlockId :=
  hints.filterMap fun (b, ws) => if ws.isEmpty then some b else none

/-- The blocks of `f` ending in a `brif`/`br_table` that ends in a `jump` in `g` (untrusted). -/
def foldCands (f g : Function) : List BlockId :=
  let gt : Std.HashMap BlockId Bool := g.blocks.foldl (fun m b =>
    if m.contains b.id then m
    else m.insert b.id (match b.term with | .jump _ => true | _ => false)) {}
  f.blocks.filterMap fun b => match b.term with
    | .brif .. | .brTable .. => if gt[b.id]?.getD false then some b.id else none
    | _ => none

end Opt.MidVal
