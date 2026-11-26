import FV.Opt.MidValCert
import FV.Opt.ConstPhi
import FV.Isle.Opt.Helpers

/-!
# Branch folding before the mid-end validator's comparison (#1119, `rewrite:blocks`)

Cranelift's mid-end turns a `brif` (or `br_table`) whose condition is a constant into a `jump`
and then drops the blocks that became unreachable; the validator, which compares `f` and `g`
block by block, rejected every such pair (`rewrite:blocks`). This file folds the same branches
of the unoptimised function `f` before the comparison, so that the existing check runs on the
folded `f` (the theorem stays about the original `f`: the fold is proved to be simulated by its
input, `Opt.MidVal.foldBr_simU`, `FV/Opt/Proof/MidValFold.lean`).

* `constEval K i`: the constant value of a pure, non-partial instruction whose operands all have
  constants in `K` (`Clif.evalInst` in a frame holding `K`), of an `iconst`, or of an unsigned
  comparison with 0 whatever the other operand (`zeroCmp`: `icmp ult x, 0` and `icmp ugt 0, x`
  are 0, `icmp uge x, 0` and `icmp ule 0, x` are 1; Cranelift's mid-end folds the branches on
  them, `rewrite:domtree`/`rewrite:blocks`).
* `kTable f` (untrusted): constants of `f`'s values, by passes over the statements in layout
  order; `kLook f.freshValue (kTable f)` keeps only values below `f.freshValue`.
* `kOk f K` (the checker the proof relies on): no block parameter has a constant; every statement
  that defines a value with a constant `v` defines only that value and `constEval K` gives `v`
  for it. Then, in every run of `f`, a value with a constant holds it or nothing (each register
  is written only by its definitions), so a branch on it can only take the branch the constant
  selects.
* `foldBr f bs`: when `kOk f K` for `K = kLook f.freshValue (kTable f)`, each block of `bs` whose
  `brif`/`br_table` condition has a constant ends in the `jump` it selects; otherwise `f`.
* `divPre f bs` (division by a constant, `skeleton-removed div`): when `kOk f K`, in the blocks
  `bs`, a `udiv`/`sdiv` whose divisor has the constant 1 becomes `imul x, y`, a `urem` by 1
  `iconst 0`, a `udiv` by `2^k` (`k ≥ 1`) `ushr x, s` with a new `s = iconst k`, and a `urem` by
  `2^k` `band x, s` with a new `s = iconst (2^k - 1)`, each `s` placed just before, as
  Cranelift's mid-end does; the new values are gap values (`gapVals f`, untrusted) below
  `f.freshValue` that `f` never uses (`supplyOk`), so `f.freshValue`, and with it the `try_call`
  windows, is unchanged; otherwise `f`. Divisor 0, `srem`, `sdiv` by other constants (rounding
  toward zero, the `-1` trap) and the magic-number divisions are left alone
  (`Opt.MidVal.divPre_simU`, `FV/Opt/Proof/MidValDiv.lean`).
* `magicPre f bs` (division by other constants, `skeleton-removed div`): when `kOk f K` and `f`
  reads only values below its fresh value (`refsOk`), in the blocks `bs`, a `udiv`/`urem` at width
  32 or 64 whose divisor has a constant `d ≥ 2` that is not a power of two becomes Cranelift's
  multiply-high sequence (`apply_div_const_magic_u32`/`_u64`, `prelude_opt.isle`): `q0 = umulhi
  x, M`, then `q0 >> s`, or with the add step `((x - q0) >> 1 + q0) >> (s - 1)` (a shift by 0
  left out, as Cranelift's rules remove it), for `urem` then `x - q * d`; `M`, `add`, `s` from
  `Isle.Opt.Rust.magicU` (the port of `magic_u32`/`magic_u64` the ISLE interpreter runs, proved
  correct for every such `d`: `Opt.Proof.DivConst.magicU_spec`). The new values are numbered from
  `f.freshValue` on, so the fresh value grows; the `try_call` windows move with it, on both
  sides alike (`Opt.MidVal.magicPre_simU`, `FV/Opt/Proof/MidValMagic.lean`). `sdiv`/`srem` (the
  signed sequence) are left alone.
* `phiPre f` (removed block parameters, `shape:params`/`jump arity`): `ConstPhi`'s solution
  applied when `phiOk` or `phiOkM` accepts it; `phiOk` is `ConstPhi.cpOk` without two conditions
  the backend needs for the function it compiles (`ConstPhi.run f`: in a function with a
  `try_call`, an unchanged fresh value; the result's well-formedness), `phiOkM` the same with the
  validator's `wfCheck` (a `call_indirect` typed by its signature declaration); Cranelift removes
  those parameters (`Opt.MidVal.phiPre_simU`, `FV/Opt/Proof/MidValPhi.lean`).
* `foldPre f bs = ConstPhi.run (foldBr (magicPre (divPre (phiPre f) bs) bs) bs)`: the parameters
  removed (before the folds, as Cranelift's `remove_constant_phis` runs before its mid-end), the
  divisions rewritten and the branches folded, without the blocks that became unreachable
  (`Opt.removeUnreachable`, and constant-phi removal, inside `ConstPhi.run`).
* `foldPreK f bs`: the same without the constant-phi removal after the folds (only
  `Opt.removeUnreachable`): a parameter that receives one value once a folded edge is gone stays,
  as in Cranelift, which removes constant phis only before its mid-end. `checkCertC` accepts the
  copy against either (`Opt.MidVal.foldPreK_simU`).
* `foldBlocks hints`: the prep requests (fold, division, and the entry block alone for
  `phiPre`) among the hints of `checkCertC` (`FV/Opt/MidValCond.lean`): a hinted block with an
  empty wrapper chain, which `condPrep` leaves unchanged.
* `foldCands f g` (untrusted): the blocks whose `brif`/`br_table` is a `jump` in `g`, and the
  blocks with a division.
-/

namespace Opt.MidVal

open Clif

/-- The frame in which `constEval` evaluates an instruction: registers `K`, no function, no
slots (a pure instruction with operands reads neither). -/
def kFrame (K : ValueId → Option Val) : Frame :=
  { func := default, regs := K, slots := [], body := [], term := .ret [] }

/-- An unsigned comparison with 0 whose value does not depend on the other operand: `x <u 0`
and `0 >u x` are false, `x ≥u 0` and `0 ≤u x` true, when the operand compared with has the
constant 0 of the compared type in `K` (module doc). -/
def zeroCmp (K : ValueId → Option Val) : Inst → Option Val
  | .icmp cc ty x y =>
    match cc with
    | .ult => if K y == some ⟨ty, 0⟩ then some ⟨.i8, 0⟩ else none
    | .uge => if K y == some ⟨ty, 0⟩ then some ⟨.i8, 1⟩ else none
    | .ule => if K x == some ⟨ty, 0⟩ then some ⟨.i8, 1⟩ else none
    | .ugt => if K x == some ⟨ty, 0⟩ then some ⟨.i8, 0⟩ else none
    | _ => none
  | _ => none

/-- The constant value of `i` when its operands have the constants `K`: an `iconst`, a pure,
non-partial instruction with operands, evaluated by `Clif.evalInst`, or an unsigned comparison
with 0 (`zeroCmp`; module doc). -/
def constEval (K : ValueId → Option Val) (i : Inst) : Option Val :=
  match i with
  | .iconst ty imm => some ⟨ty, imm⟩
  | _ =>
    if isPure i && !partialK i && !(operands i).isEmpty && (operands i).all (fun x => (K x).isSome) then
      match evalInst (kFrame K) Mem.empty i with
      | .ok ([v], _) => some v
      | _ => none
    else zeroCmp K i

/-- One pass of `kTable` over `f`'s statements in layout order. -/
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
nothing changes (at most four). -/
def kTable (f : Function) : Std.HashMap ValueId Val :=
  let rec go : Nat → Std.HashMap ValueId Val → Std.HashMap ValueId Val
    | 0, hm => hm
    | n + 1, hm =>
      let hm' := kPass f hm
      if hm'.size == hm.size then hm' else go n hm'
  go 4 {}

/-- The constants of a table, restricted to the values below `fv` (`f.freshValue`, computed once
by the caller: a lookup must not recompute the table or the fresh value). -/
def kLook (fv : Nat) (hm : Std.HashMap ValueId Val) (x : ValueId) : Option Val :=
  if x < fv then hm[x]? else none

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
folded, when `kOk` accepts `f`'s constants (`kTable`, below `f.freshValue`); `f` otherwise. -/
def foldBr (f : Function) (bs : List BlockId) : Function :=
  if bs.isEmpty then f
  else
    let fv := f.freshValue
    let hm := kTable f
    let K := kLook fv hm
    if kOk f K then foldFn f K bs else f

/-! ## Division by a constant -/

/-- `k` with `2 ^ k = n`, if `n` is a power of two. -/
def log2Exact (n : Nat) : Option Nat :=
  if 2 ^ n.log2 == n then some n.log2 else none

/-- The statements that replace `v = op ty x y` when `y` has the constant `c` in `K`
(`udiv`/`sdiv` by 1: `imul x, y`; `urem` by 1: `iconst 0`; `udiv` by `2^k`: `ushr x, k`;
`urem` by `2^k`: `band x, 2^k - 1`), with `s` the value of an inserted constant; whether `s`
is used. `none`: the statement is left alone. -/
def divRw (K : ValueId → Option Val) (s : ValueId) (st : Stmt) : Option (List Stmt × Bool) :=
  match st.results, st.inst with
  | [v], .div op ty x y =>
    match K y with
    | some c =>
      match log2Exact c.bits.toNat with
      | some k =>
        if c.ty ≠ ty then none
        else if k = 0 then
          if op = .urem then some ([⟨[v], .iconst ty 0⟩], false)
          else if op = .udiv ∨ op = .sdiv then some ([⟨[v], .binary .imul ty x y⟩], false)
          else none
        else if op = .udiv then
          some ([⟨[s], .iconst ty (BitVec.ofNat _ k)⟩, ⟨[v], .binary .ushr ty x s⟩], true)
        else if op = .urem then
          some ([⟨[s], .iconst ty (BitVec.ofNat _ (2 ^ k - 1))⟩, ⟨[v], .binary .band ty x s⟩], true)
        else none
      | none => none
    | none => none
  | _, _ => none

/-- A body with its divisions by constants rewritten (`divRw`), the inserted constants taking
values from the supply `sup` (a statement needing one is left alone when it is empty); the rest
of the supply. -/
def divBody (K : ValueId → Option Val) : List Stmt → List ValueId → List Stmt × List ValueId
  | [], sup => ([], sup)
  | st :: ss, sup =>
    match sup with
    | s :: sup' =>
      match divRw K s st with
      | some (xs, true) => let r := divBody K ss sup'; (xs ++ r.1, r.2)
      | some (xs, false) => let r := divBody K ss sup; (xs ++ r.1, r.2)
      | none => let r := divBody K ss sup; (st :: r.1, r.2)
    | [] =>
      match divRw K 0 st with
      | some (xs, false) => let r := divBody K ss []; (xs ++ r.1, r.2)
      | _ => let r := divBody K ss []; (st :: r.1, r.2)

/-- The blocks of `bs` with their divisions rewritten, the supply threaded through them. -/
def divBlocks (K : ValueId → Option Val) (bs : List BlockId) :
    List Block → List ValueId → List Block
  | [], _ => []
  | b :: rest, sup =>
    if bs.contains b.id then
      let r := divBody K b.body sup
      { b with body := r.1 } :: divBlocks K bs rest r.2
    else b :: divBlocks K bs rest sup

/-- Every value `f` defines or reads. -/
def usedVals (f : Function) : List ValueId :=
  f.blocks.flatMap fun b => b.params.map (·.1) ++
    b.body.flatMap (fun st => st.results ++ operands st.inst) ++ termOperands b.term

/-- Values below `f.freshValue` that `f` neither defines nor reads, at most `n` (untrusted: the
supply of `divPre`; `divPre` checks it). -/
def gapVals (f : Function) (n : Nat) : List ValueId := Id.run do
  let used : Std.HashSet ValueId := (usedVals f).foldl (fun s v => s.insert v) {}
  let mut out : Array ValueId := #[]
  for v in [0:f.freshValue] do
    if out.size ≥ n then break
    if !used.contains v then out := out.push v
  return out.toList

/-- Every block through `divBlocks`, with the supply `S`. -/
def divFn (f : Function) (K : ValueId → Option Val) (bs : List BlockId) (S : List ValueId) :
    Function :=
  { f with blocks := divBlocks K bs f.blocks S }

/-- The supply's check: values below `f.freshValue` that `f` neither defines nor reads. -/
def supplyOk (f : Function) (S : List ValueId) : Bool :=
  let used := usedVals f
  S.all fun s => s < f.freshValue && !used.contains s

/-- **Division by a constant** (module doc): in the blocks of `bs`, the divisions whose divisor
has a constant (`kOk`, as `foldBr`) become the pure statements `divRw` gives, inserted constants
taking values that `f` neither defines nor reads (`supplyOk`) and that keep its fresh value;
`f` otherwise. -/
def divPre (f : Function) (bs : List BlockId) : Function :=
  if bs.isEmpty then f
  else
    let fv := f.freshValue
    let hm := kTable f
    let K := kLook fv hm
    if kOk f K then
      let n := f.blocks.foldl (fun n b => n + (b.body.filter fun st => match st.inst with
        | .div .. => true | _ => false).length) 0
      let S := gapVals f n
      let f' := divFn f K bs S
      if supplyOk f S && f'.freshValue == fv then f' else f
    else f

/-! ## Division by a constant: the magic numbers -/

/-- Every value `g` reads (statement operands, terminator operands) is below its fresh value
(`Opt.closedB`'s test; the validator does not import the optimiser). -/
def refsOk (g : Function) : Bool :=
  g.blocks.all fun b =>
    (b.body.all fun st => (operands st.inst).all (· < g.freshValue)) &&
      (termOperands b.term).all (· < g.freshValue)

/-- The unsigned quotient by the magic numbers `M`, `add`, `s` (`Isle.Opt.Rust.magicU`, the port
of Cranelift's `magic_u32`/`magic_u64` the ISLE interpreter runs) of `x` (type `ty`) into `dst`,
the temporaries numbered from `n` on (Cranelift's `apply_div_const_magic_u*`; its shift by 0, which
Cranelift's own rules remove, left out); the number of temporaries. -/
def uQuot (ty : Ty) (x : ValueId) (M : Nat) (add : Bool) (s : Nat) (n dst : ValueId) :
    List Stmt × Nat :=
  if add then
    let pre : List Stmt :=
      [⟨[n], .iconst ty (BitVec.ofNat _ M)⟩, ⟨[n + 1], .binary .umulhi ty x n⟩,
        ⟨[n + 2], .binary .isub ty x (n + 1)⟩, ⟨[n + 3], .iconst ty (BitVec.ofNat _ 1)⟩,
        ⟨[n + 4], .binary .ushr ty (n + 2) (n + 3)⟩]
    if s ≤ 1 then (pre ++ [⟨[dst], .binary .iadd ty (n + 1) (n + 4)⟩], 5)
    else
      (pre ++ [⟨[n + 5], .binary .iadd ty (n + 1) (n + 4)⟩,
        ⟨[n + 6], .iconst ty (BitVec.ofNat _ (s - 1))⟩, ⟨[dst], .binary .ushr ty (n + 5) (n + 6)⟩], 7)
  else if s = 0 then ([⟨[n], .iconst ty (BitVec.ofNat _ M)⟩, ⟨[dst], .binary .umulhi ty x n⟩], 1)
  else
    ([⟨[n], .iconst ty (BitVec.ofNat _ M)⟩, ⟨[n + 1], .binary .umulhi ty x n⟩,
      ⟨[n + 2], .iconst ty (BitVec.ofNat _ s)⟩, ⟨[dst], .binary .ushr ty (n + 1) (n + 2)⟩], 3)

/-- The statements of `v = op ty x y` by the magic numbers `M`, `add`, `s`, the new values from
`n` on, and how many: for `udiv` the quotient (`uQuot`), otherwise (`urem`) the quotient into
`n`, then `t = imul n, y; v = isub x, t` (Cranelift's `apply_div_const_magic_u*_finish`). -/
def magicStmts (op : DivOp) (ty : Ty) (v x y : ValueId) (M : Nat) (add : Bool) (s n : Nat) :
    List Stmt × Nat :=
  if op = .udiv then uQuot ty x M add s n v
  else
    let q := uQuot ty x M add s (n + 1) n
    (q.1 ++ [⟨[n + 1 + q.2], .binary .imul ty n y⟩, ⟨[v], .binary .isub ty x (n + 1 + q.2)⟩],
      q.2 + 2)

/-- The signed sequence's fix-up of `q1 = smulhi x, m` (value `n + 1`): `q1 + x` when `d > 0` and
`m < 0`, `q1 - x` when `d < 0` and `m > 0` (into `n + 2`), else `q1`; the value holding `q2`. -/
def sFix (ty : Ty) (x : ValueId) (d m : Int) (n : ValueId) : List Stmt × ValueId :=
  if 0 < d ∧ m < 0 then ([⟨[n + 2], .binary .iadd ty (n + 1) x⟩], n + 2)
  else if d < 0 ∧ 0 < m then ([⟨[n + 2], .binary .isub ty (n + 1) x⟩], n + 2)
  else ([], n + 1)

/-- The signed sequence's `q3 = q2 >>ₛ s` (into `n + 4`; for `s = 0` `q2` itself, as Cranelift's
rules remove a shift by 0); the value holding `q3`. -/
def sShift (ty : Ty) (s : Nat) (q2 n : ValueId) : List Stmt × ValueId :=
  if s = 0 then ([], q2)
  else ([⟨[n + 3], .iconst ty (BitVec.ofNat _ s)⟩, ⟨[n + 4], .binary .sshr ty q2 (n + 3)⟩], n + 4)

/-- The signed quotient by the magic numbers `m`, `s` (`Isle.Opt.Rust.magicS`) of `x` by `d` into
`dst`, the temporaries numbered from `n` on (Cranelift's `apply_div_const_magic_s32`/`_s64`:
`q1 = smulhi x, m`, the fix-up `sFix`, `q3 = q2 >>ₛ s` `sShift`, then `q3 + (q3 >> (w - 1))`);
the number of temporaries. -/
def sQuot (ty : Ty) (x : ValueId) (d m : Int) (s : Nat) (n dst : ValueId) : List Stmt × Nat :=
  let f := sFix ty x d m n
  let h := sShift ty s f.2 n
  ([⟨[n], .iconst ty (BitVec.ofInt _ m)⟩, ⟨[n + 1], .binary .smulhi ty x n⟩] ++ f.1 ++ h.1 ++
    [⟨[n + 5], .iconst ty (BitVec.ofNat _ (ty.width - 1))⟩, ⟨[n + 6], .binary .ushr ty h.2 (n + 5)⟩,
      ⟨[dst], .binary .iadd ty h.2 (n + 6)⟩], 7)

/-- `magicStmts` for `sdiv` (`sQuot`) and otherwise `srem` (the quotient into `n`, then
`t = imul n, y; v = isub x, t`, `apply_div_const_magic_s*_finish`). -/
def magicStmtsS (op : DivOp) (ty : Ty) (v x y : ValueId) (d m : Int) (s n : Nat) :
    List Stmt × Nat :=
  if op = .sdiv then sQuot ty x d m s n v
  else
    let q := sQuot ty x d m s (n + 1) n
    (q.1 ++ [⟨[n + 1 + q.2], .binary .imul ty n y⟩, ⟨[v], .binary .isub ty x (n + 1 + q.2)⟩],
      q.2 + 2)

/-- The statements that replace `v = op ty x y` when `y` has a constant `d` in `K` that Cranelift
divides by with magic numbers: `udiv`/`urem` at width 32 or 64, `d` neither 0, 1 nor a power of
two, `magicStmts` with `Isle.Opt.Rust.magicU`'s numbers; `sdiv`/`srem` at width 32 or 64, `|d|`
(signed) neither 0, 1 nor a power of two, `magicStmtsS` with `Isle.Opt.Rust.magicS`'s numbers;
values from `n` on, and how many. `none`: the statement is left alone. -/
def magicRw (K : ValueId → Option Val) (n : ValueId) (st : Stmt) : Option (List Stmt × Nat) :=
  match st.results, st.inst with
  | [v], .div op ty x y =>
    match K y with
    | some c =>
      let w := ty.width
      let d := c.bits.toNat
      let ds := c.bits.toInt
      if c.ty = ty ∧ (op = .udiv ∨ op = .urem) ∧ (w = 32 ∨ w = 64) ∧ 2 ≤ d ∧
          log2Exact d = none then
        let mg := Isle.Opt.Rust.magicU w d
        some (magicStmts op ty v x y mg.1 mg.2.1 mg.2.2.toNat n)
      else if c.ty = ty ∧ (op = .sdiv ∨ op = .srem) ∧ (w = 32 ∨ w = 64) ∧ 2 ≤ ds.natAbs ∧
          log2Exact ds.natAbs = none then
        let mg := Isle.Opt.Rust.magicS w ds
        some (magicStmtsS op ty v x y ds mg.1 mg.2.toNat n)
      else none
    | none => none
  | _, _ => none

/-- A body with its divisions by magic numbers rewritten (`magicRw`), the new values numbered
from `n` on; the next new value. -/
def magicBody (K : ValueId → Option Val) : List Stmt → ValueId → List Stmt × ValueId
  | [], n => ([], n)
  | st :: ss, n =>
    match magicRw K n st with
    | some (xs, k) => let r := magicBody K ss (n + k); (xs ++ r.1, r.2)
    | none => let r := magicBody K ss n; (st :: r.1, r.2)

/-- The blocks of `bs` with their divisions by magic numbers rewritten, the new values threaded
through them. -/
def magicBlocks (K : ValueId → Option Val) (bs : List BlockId) :
    List Block → ValueId → List Block
  | [], _ => []
  | b :: rest, n =>
    if bs.contains b.id then
      let r := magicBody K b.body n
      { b with body := r.1 } :: magicBlocks K bs rest r.2
    else b :: magicBlocks K bs rest n

/-- Every block through `magicBlocks`, new values from `n` on. -/
def magicFn (f : Function) (K : ValueId → Option Val) (bs : List BlockId) (n : ValueId) :
    Function :=
  { f with blocks := magicBlocks K bs f.blocks n }

/-- **Division by a constant with magic numbers** (module doc): when `kOk` accepts `f`'s
constants (as `foldBr`) and `f` reads only values below its fresh value (`refsOk`), in the blocks
of `bs` the divisions `magicRw` rewrites, the new values numbered from `f.freshValue` on; `f`
otherwise. -/
def magicPre (f : Function) (bs : List BlockId) : Function :=
  if bs.isEmpty then f
  else
    let fv := f.freshValue
    let hm := kTable f
    let K := kLook fv hm
    if kOk f K && refsOk f then magicFn f K bs fv else f

/-! ## Constant-phi removal without the backend's fresh-value condition -/

/-- **The validator's constant-phi checker**: `ConstPhi.cpOk` without its last two conjuncts,
the well-formedness of the result and, in a function with a `try_call`, the unchanged fresh
value. Both are for the backend, which compiles `ConstPhi.run f`; the copy `phiPre f` only
exists inside the check, and the soundness proof (`ConstPhi.cpOk_facts`) uses neither. -/
def phiOk (f : Function) (sol : List (ValueId × ValueId)) : Bool :=
  match Opt.check f with
  | .error _ => false
  | .ok fi =>
    let m := ConstPhi.solMap sol
    ConstPhi.keysOk (defMap f) fi.cfg.idom m sol && ConstPhi.edgesOk fi.cfg.index m f

/-- **`phiOk` with the validator's well-formedness check** `wfCheck` in place of `Opt.check`:
`wfCheck` also accepts a `call_indirect` (its result types from the function's signature
declarations, `sigDeclOf`), which `Opt.check` rejects; so the parameters Cranelift removes in a
function with a `call_indirect` are removed here too (`Opt.MidVal.phiOkM_simU`). -/
def phiOkM (f : Function) (sol : List (ValueId × ValueId)) : Bool :=
  match wfCheck f with
  | .error _ => false
  | .ok fi =>
    let m := ConstPhi.solMap sol
    ConstPhi.keysOk (defMap f) fi.cfg.idom m sol && ConstPhi.edgesOk fi.cfg.index m f

/-- **Constant-phi removal for the comparison** (module doc): `ConstPhi`'s solution of `f`
applied when `phiOk` or `phiOkM` accepts it, `f` otherwise. -/
def phiPre (f : Function) : Function :=
  let sol := ConstPhi.solve f
  if !sol.isEmpty && (phiOk f sol || phiOkM f sol) then ConstPhi.apply f sol else f

/-- **The folded function without its unreachable blocks** (module doc): the parameters
`ConstPhi.run` kept removed (`phiPre`, before the folds, where Cranelift removes them),
divisions by constants rewritten (`divPre`, then `magicPre`), constant-condition branches folded
(`foldBr`), then constant-phi removal. -/
def foldPre (f : Function) (bs : List BlockId) : Function :=
  ConstPhi.run (foldBr (magicPre (divPre (phiPre f) bs) bs) bs)

/-- **The folded function without its unreachable blocks, parameters kept** (module doc): as
`foldPre`, with `Opt.removeUnreachable` (when `freshOkB` allows it, as in `ConstPhi.runCore`) in
place of the final `ConstPhi.run`. -/
def foldPreK (f : Function) (bs : List BlockId) : Function :=
  let f1 := foldBr (magicPre (divPre (phiPre f) bs) bs) bs
  if freshOkB f1 then removeUnreachable f1 else f1

/-- The fold requests among `checkCertC`'s hints: the blocks hinted with an empty wrapper
chain. -/
def foldBlocks (hints : List (BlockId × List Wrap)) : List BlockId :=
  hints.filterMap fun (b, ws) => if ws.isEmpty then some b else none

/-- The blocks of `f` ending in a `brif`/`br_table` that ends in a `jump` in `g`, and the blocks
with a division (untrusted). -/
def foldCands (f g : Function) : List BlockId :=
  let gt : Std.HashMap BlockId Bool := g.blocks.foldl (fun m b =>
    if m.contains b.id then m
    else m.insert b.id (match b.term with | .jump _ => true | _ => false)) {}
  f.blocks.filterMap fun b =>
    let fold := match b.term with
      | .brif .. | .brTable .. => gt[b.id]?.getD false
      | _ => false
    let div := b.body.any fun st => match st.inst with | .div .. => true | _ => false
    if fold || div then some b.id else none

end Opt.MidVal
