import FV.Clif.Run
import Std.Data.HashMap

/-!
# `Opt.Legalize128`: rewrite `i128` away before the backend (rust-route step 5)

The Lean backend's value model is one vreg per value and its ABI layer (`sigArgs`,
`sigArgLocs`, `lowerFunction`) rejects `i128`, so the 41 remaining corpus functions cannot be
compiled. Like Cranelift's legalizer, this pass rewrites `i128` away *before* the backend:
every `i128` value becomes a pair of `i64` values (`lo`, `hi`), every `i128` instruction
becomes the equivalent `i64` code, and `i128` signatures become two `i64` parameters/returns
each — with an unused `i64` parameter/return reproducing the AAPCS64 even/odd register-pair
alignment whenever a pair would start at an odd register. Division/remainder become calls to
the `__udivti3`/`__divti3`/`__umodti3`/`__modti3` runtime helpers (implemented in
`scripts/rust-clif/rust-runtime.c` and given a byte-exact semantics in `Clif.Rust.env`).

The output is plain `i8..i64` CLIF, so the existing backend compiles it unchanged. The pass
is untrusted: `Opt.Legal.checkW` (`FV/Opt/Legal.lean`) validates each legalised function
against the original with the certificate `function128Cert` returns, and the refinement
theorem (`FV/Opt/Proof/Legal*.lean`, `E2E.backend_correct_legal_wide`) covers the functions it
accepts (reported verified when the legalised form is inside the backend theorem); the others
are flagged unverified (`i128 legalized (outside backend_correct: Opt.Legal.checkW rejects)`).

Semantics (all against `Clif.Sem`, which is what `Clif.run` executes — the differential
`clif-filetest --legalize128` mode runs every run line through both):

* `iadd`/`isub` via the carry/borrow chain (`icmp ult` of the wrapped low sum/difference);
  `imul` via the cross products (`imul` + `umulhi`); `umulhi`/`smulhi` at `i128` are not
  legalised (the function stays unsupported);
* `band`/`bor`/`bxor`/`bnot` pairwise; `ineg` = `(~x + 1) mod 2^128`; `iabs` by `select`;
  `clz`/`ctz`/`popcnt`/`cls`/`bitrev`/`bswap` from the halves;
* shifts/rotates by the amount mod 128 (`(lo + hi·2^64) mod w = lo mod w` for the
  `i128`-typed amount of a narrower shift, since `w` divides 64), with a `select` for the
  half-crossing amount and a zeroing `select` for the amount-0 edge of the cross-half
  contribution;
* `icmp` lexicographically (the high halves with the same condition code, the low halves
  unsigned when the high halves are equal);
* `uextend`/`sextend` (`hi = 0` or `sshr lo, 63`), `ireduce` takes `lo`, `iconcat`/`isplit`
  copy the halves (`bor x, x`), `bitcast.i128` copies the pair, `select`/`bmask`/`bitselect`
  decompose pairwise, and an `i128` `brif`/`trapz`/`trapnz` condition is
  `(lo != 0) | (hi != 0)`;
* loads/stores of `i128` become two `i64` accesses at `+0`/`+8` (little-endian);
* `udiv`/`sdiv`/`urem`/`srem` at `i128` call the helper; `Clif.Rust.env` gives it the
  trapping semantics of the opcodes it replaces (`int_divz`, and `int_ovf` for
  `sdiv(i128::MIN, -1)`), so `Clif.run` original and legalised agree.

This module has the shared definitions (the type map, the ABI groups, the helpers' signature,
the certificate); the canonical `i64` patterns are `Opt.Legal.Pat` (`FV/Opt/Legal.lean`) and the
pass, which emits for every statement the pattern of its `Opt.Legal.planOf` plan, is
`FV/Opt/Legalize128Pass.lean`.

An instruction this pass does not implement (atomics at `i128`, float conversions, …) makes
the legalisation fail: the function is left alone and reported unsupported by the backend,
exactly as before.
-/

namespace Opt.Legalize128

open Clif

/-! ## Types of values, and "does the function mention i128" -/

/-- Types of the values defined in `f` (block parameters and instruction results). -/
def typeMapOf (f : Function) : Std.HashMap ValueId Ty := Id.run do
  let sigOf := fun r => (f.externs.lookup r).map (·.sig)
  let declOf := fun s => f.sigDecls.lookup s
  let mut m : Std.HashMap ValueId Ty := {}
  for b in f.blocks do
    for (v, t) in b.params do m := m.insert v t
    for st in b.body do
      if let some ts := st.inst.resultTypes sigOf declOf then
        for (r, t) in st.results.zip ts do m := m.insert r t
  return m

/-- Does a signature mention `i128`? -/
def sig128 (s : Signature) : Bool := (s.params ++ s.returns).any (·.ty == .i128)

/-- Does the instruction (its controlling type or any operand) mention `i128`? -/
def inst128 (ty : ValueId → Option Ty) : Inst → Bool
  | .iconst t _ => t == .i128
  | .unary _ t x => t == .i128 || ty x == some .i128
  | .binary op t x y => t == .i128 || ty x == some .i128 || ty y == some .i128
  | .div _ t x y => t == .i128 || ty x == some .i128 || ty y == some .i128
  | .overflow _ t x y => t == .i128 || ty x == some .i128 || ty y == some .i128
  | .carry _ t x y _ => t == .i128 || ty x == some .i128 || ty y == some .i128
  | .uaddOverflowTrap t x y _ => t == .i128 || ty x == some .i128 || ty y == some .i128
  | .icmp _ t x y => t == .i128 || ty x == some .i128 || ty y == some .i128
  | .select t c x y | .selectSpectreGuard t c x y =>
    t == .i128 || ty c == some .i128 || ty x == some .i128 || ty y == some .i128
  | .bitselect t c x y =>
    t == .i128 || ty c == some .i128 || ty x == some .i128 || ty y == some .i128
  | .bmask t x => t == .i128 || ty x == some .i128
  | .extend _ t x => t == .i128 || ty x == some .i128
  | .ireduce t x => t == .i128 || ty x == some .i128
  | .iconcat t lo hi =>
    t.double? == some .i128 || ty lo == some .i128 || ty hi == some .i128
  | .isplit t x => t == .i128 || ty x == some .i128
  | .load _ t _ p _ => t == .i128 || ty p == some .i128
  | .store _ t _ x p _ => t == .i128 || ty x == some .i128 || ty p == some .i128
  | .stackAddr t _ _ => t == .i128
  | .call .. | .callIndirect .. => false  -- the signatures are checked separately
  | .funcAddr t _ => t == .i128
  | .atomicRmw _ t _ p x => t == .i128 || ty p == some .i128 || ty x == some .i128
  | .atomicCas t _ p e x =>
    t == .i128 || ty p == some .i128 || ty e == some .i128 || ty x == some .i128
  | .atomicLoad t _ p => t == .i128 || ty p == some .i128
  | .atomicStore t _ x p => t == .i128 || ty x == some .i128 || ty p == some .i128
  | .fence => false
  | .bitcast t _ x => t == .i128 || ty x == some .i128
  | .trapz c _ | .trapnz c _ => ty c == some .i128
  | .nop => false
  | .symbolValue t _ | .tlsValue t _ => t == .i128
  | .float _ t args => t == .i128 || args.any (ty · == some .i128)

/-- Does `f` mention `i128` anywhere (its signature, an extern's, a `sigN` declaration, a
block parameter, or an instruction operand/result)? -/
def mentions128 (f : Function) : Bool :=
  sig128 f.sig || f.externs.any (fun e => sig128 e.2.sig) ||
    f.sigDecls.any (fun d => sig128 d.2) ||
  let m := typeMapOf f
  f.blocks.any fun b =>
    b.params.any (·.2 == .i128) ||
    b.body.any fun st => inst128 (fun v => m[v]?) st.inst

/-! ## The ABI expansion of a signature

AAPCS64 passes/returns an `i128` in an even/odd register pair; when the next free register
is odd one is skipped (Cranelift's aarch64 `compute_arg_locs`: `next_xreg % 2 != 0`). The
legalised signature reproduces this with an unused `i64` parameter/return occupying exactly
the skipped register, which the callee ignores. An `sret` parameter does not consume the
`x0..x7` sequence (`sigArgLocs`); a float takes the next of `v0..v7` (Cranelift's
`next_vreg`), not an `x` register.

A pair that does not fit in `x0..x7` goes on the stack (Cranelift: a 16-byte slot at the
next 16-aligned offset, low half first; `next_xreg` unchanged), as do the integer and float
parameters after the registers of their class are used up (8-byte slots). The legalised
signature passes the halves as two `i64` parameters, which the backend places in the next
8-byte stack slots (`argLocs`) once `x0..x7` are used up, so:
* registers used up (`k = 8`): the pair, after an `i64` pad when the stack offset is not
  16-aligned;
* only `x7` left (`k = 7`): the halves go on the stack, which needs a 16-aligned stack
  offset, and Cranelift leaves `x7` to the next integer parameter. When the next parameter is
  one (`x7` placement), the legalised signature passes it first, in `x7`, then the halves: the
  pair's group is `[.val q, .lo, .hi]` (`q` that parameter) and `q`'s own group is empty.
  Otherwise a pad takes `x7`, and a later integer parameter makes the legalisation fail
  (`hole`: Cranelift passes it in `x7`).

Returns use the same expansion; more than eight legalised returns are rejected by the
backend (`retRegs`), as Cranelift rejects stack returns. -/

/-- The legalised slots of one parameter/return: itself, or a pair with an optional pad. -/
inductive SlotEl where
  | val (p : AbiParam)
  | pad
  | lo
  | hi
  deriving Repr, Inhabited

/-- The slots of every parameter, in order; `k` counts the `x` registers consumed so far
(`x0..x7`), `v` the float registers (`v0..v7`), `st` the stack bytes (a multiple of 8),
`hole`: a pair went on the stack while Cranelift still had `x7` free. An `i128` group
`[.val q, .lo, .hi]` is followed by the empty group of the parameter `q` it carries in `x7`. -/
def expandGroups (ps : List AbiParam) : Except String (List (List SlotEl)) :=
  go ps 0 0 0 false
where
  go : List AbiParam → Nat → Nat → Nat → Bool → Except String (List (List SlotEl))
    | [], _, _, _, _ => return []
    | p :: ps, k, v, st, hole =>
      if p.ty == .i128 then
        if p.ext != .none then throw "legalize128: i128 argument with an extension"
        else if p.purpose != .normal then throw "legalize128: special-purpose i128 argument"
        else if k + 2 ≤ 8 then do
          let rest ← go ps (if k % 2 == 1 then k + 3 else k + 2) v st hole
          return (if k % 2 == 1 then [.pad, .lo, .hi] else [.lo, .hi]) :: rest
        else if k == 7 then
          if st % 16 == 0 then
            match ps with
            | q :: qs =>
              if q.ty != .i128 && q.purpose != .sret && !q.ty.isFloat then do
                -- `x7` placement: `q` in `x7`, then the halves on the stack
                let rest ← go qs 8 v (st + 16) false
                return [.val q, .lo, .hi] :: [] :: rest
              else do
                let rest ← go (q :: qs) 8 v (st + 16) true
                return [.pad, .lo, .hi] :: rest
            | [] => do
              let rest ← go [] 8 v (st + 16) true
              return [.pad, .lo, .hi] :: rest
          else throw "legalize128: i128 argument on an unaligned stack offset while x7 is free"
        else if st % 16 == 0 then do
          let rest ← go ps k v (st + 16) hole
          return [.lo, .hi] :: rest
        else do
          let rest ← go ps k v (st + 24) hole
          return [.pad, .lo, .hi] :: rest
      else if p.purpose == .sret then do
        let rest ← go ps k v st hole
        return [.val p] :: rest
      else if p.ty.isFloat then do
        let rest ← go ps k (if v < 8 then v + 1 else v) (if v < 8 then st else st + 8) hole
        return [.val p] :: rest
      else if k < 8 then do
        let rest ← go ps (k + 1) v st hole
        return [.val p] :: rest
      else if hole then
        throw "legalize128: an integer argument Cranelift passes in x7 after a stack-passed i128"
      else do
        let rest ← go ps k v (st + 8) hole
        return [.val p] :: rest

/-- The `AbiParam` of a slot. -/
def elTy : SlotEl → AbiParam
  | .val p => p
  | _ => { ty := .i64 }

def expandSig (s : Signature) : Except String Signature := do
  let pg ← expandGroups s.params
  let rg ← expandGroups s.returns
  return { s with params := pg.flatMap (·.map elTy), returns := rg.flatMap (·.map elTy) }


/-! ## Division and remainder via the runtime helpers -/

/-- The helper of a `div` at `i128`. -/
def divHelper : DivOp → String
  | .udiv => "__udivti3" | .sdiv => "__divti3" | .urem => "__umodti3" | .srem => "__modti3"

/-- The declared signature of a `__*ti3` helper: two 128-bit arguments as `i64` pairs,
returning one 128-bit value as an `i64` pair. -/
def helperSig : Signature where
  params := [{ ty := .i64 }, { ty := .i64 }, { ty := .i64 }, { ty := .i64 }]
  returns := [{ ty := .i64 }, { ty := .i64 }]
  callConv := none


/-- The biggest value id in `f` (fresh ids continue after it). -/
def maxValueId (f : Function) : ValueId :=
  f.blocks.foldl (fun acc b =>
    let acc := b.params.foldl (fun a p => max a p.1) acc
    b.body.foldl (fun a s => s.results.foldl (fun a2 r => max a2 r) a) acc) 0 + 1

/-- The biggest function-reference id in `f` (helper declarations continue after it). -/
def maxFnRef (f : Function) : FnRef :=
  f.externs.foldl (fun a e => max a e.1) 0 + 1

/-- What the validator `Opt.Legal.checkW` needs besides the two functions: the pair of every
`i128` value and the shared zero of the pad values. -/
structure Cert where
  pairs : List (ValueId × ValueId × ValueId) := []
  zero : ValueId := 0
  deriving Repr, Inhabited

/-! ## Run commands: the original's arguments and the legalised outcome -/

/-- The arguments of a run command of the original function, expanded for the legalised
signature (an `i128` argument becomes its pair, a pad gets zero; with `x7` placement the next
argument comes first). -/
def expandRunArgs (orig : Signature) (vs : List Val) : Except String (List Val) := do
  let gs ← expandGroups orig.params
  go gs vs
where
  go : List (List SlotEl) → List Val → Except String (List Val)
    | [], [] => return []
    | [.val _, .lo, .hi] :: [] :: gs, v :: u :: vs => do
      let pair ← groupVal [.lo, .hi] v
      let rest ← go gs vs
      return u :: pair ++ rest
    | g :: gs, v :: vs => do
      let mine ← groupVal g v
      let rest ← go gs vs
      return mine ++ rest
    | _, _ => throw "legalize128: run arguments do not match the signature"
  groupVal : List SlotEl → Val → Except String (List Val)
    | [.val _], v => return [v]
    | [.pad], _ => return [Val.ofNat .i64 0]
    | [.lo, .hi], v =>
      match v.ty with
      | .i128 => return [⟨.i64, v.bits.extractLsb' 0 64⟩, ⟨.i64, v.bits.extractLsb' 64 64⟩]
      | _ => throw "legalize128: run argument is not i128"
    | [.pad, .lo, .hi], v =>
      match v.ty with
      | .i128 =>
        return [Val.ofNat .i64 0, ⟨.i64, v.bits.extractLsb' 0 64⟩,
                ⟨.i64, v.bits.extractLsb' 64 64⟩]
      | _ => throw "legalize128: run argument is not i128"
    | _, _ => throw "legalize128: bad slot group"

/-- A legalised run outcome mapped back to the original signature's shape. -/
def joinRunOutcome (orig : Signature) (o : Outcome) : Outcome :=
  match o with
  | .returned vs mem =>
    match (expandGroups orig.returns).toOption.bind (fun gs => joinVals gs vs) with
    | some vs' => .returned vs' mem
    | none => .stuck "legalize128: returned values do not match the signature"
  | _ => o
where
  joinVals : List (List SlotEl) → List Val → Option (List Val)
    | [], [] => some []
    | g :: gs, v :: vs =>
      match g with
      | [.val _] => (joinVals gs vs).map (v :: ·)
      | [.pad] => joinVals gs vs
      | [.lo, .hi] =>
        match v :: vs with
        | l :: h :: rest =>
          match l.as? .i64, h.as? .i64 with
          | some l', some h' => (joinVals gs rest).map (⟨.i128, h' ++ l'⟩ :: ·)
          | _, _ => none
        | _ => none
      | [.pad, .lo, .hi] =>
        match v :: vs with
        | _ :: l :: h :: rest =>
          match l.as? .i64, h.as? .i64 with
          | some l', some h' => (joinVals gs rest).map (⟨.i128, h' ++ l'⟩ :: ·)
          | _, _ => none
        | _ => none
      | _ => none
    | _, _ => none

end Opt.Legalize128
