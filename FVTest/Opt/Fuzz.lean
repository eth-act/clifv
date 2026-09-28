import FVTest.Opt.Common
import FV.Clif.Run
import FV.Clif.Print

/-!
`opt-fuzz [--seed N] [--count N] [--ext] [--out FILE.clif] [-v] [--opt-* options]`: random
differential testing of the mid-end.

Generates `count` random functions (integer types i8..i64): a straight-line entry block of
pure arithmetic over the parameters and constants chosen to trigger rewrites (0, ±1, powers of
two, min/max, …), a `brif` diamond joining in a block parameter, a counted loop (3
iterations) whose body mixes loop-carried values with invariant expressions (LICM), and an
exit block; occasionally trapping divisions. Opcodes are from the backend subset E; `--ext`
adds non-E pure ones (saturating arithmetic, `iabs`, `cls`, `bmask`, `bitselect`).

Each function is run with `Clif.run` on 8 argument vectors before and after `Opt.optimize`
(same refinement check as `opt-difftest`); failures print both functions. With `--out`, the
original functions are written with `; run:` lines holding the `Clif.run` results of the
returning runs, as a regular runtest file for `clif-native`, `clif-oracle` and
`scripts/lean-backend-filetests.sh --opt`.
-/

open Clif Opt

namespace OptFuzz

structure G where
  gen : StdGen
  next : ValueId := 0
  pool : Array (ValueId × Ty) := #[]
  body : Array Stmt := #[]
  ext : Bool := false

abbrev GM := StateM G

def rand (n : Nat) : GM Nat := do
  if n ≤ 1 then return 0
  let g ← get
  let (k, gen) := randNat g.gen 0 (n - 1)
  set { g with gen }
  return k

def pick {α} [Inhabited α] (xs : Array α) : GM α := do
  return xs[← rand xs.size]!

def tys : Array Ty := #[.i8, .i16, .i32, .i64]

def interesting (t : Ty) : GM Int := do
  let w := t.width
  let k ← rand 20
  if k < 17 then
    return (#[0, 1, -1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 255, 256,
              2 ^ (w - 1) - 1, -(2 ^ (w - 1))] : Array Int)[k]!
  else
    return (← rand (2 ^ 16)) - 2 ^ 15

def fresh : GM ValueId := modifyGet fun g => (g.next, { g with next := g.next + 1 })

def emit (inst : Inst) (t : Ty) : GM ValueId := do
  let v ← fresh
  modify fun g => { g with body := g.body.push { results := [v], inst }, pool := g.pool.push (v, t) }
  return v

def const (t : Ty) : GM ValueId := do
  let k ← interesting t
  emit (.iconst t (BitVec.ofInt t.width k)) t

/-- A value of type `t` from the pool (or a new constant). -/
def valOf (t : Ty) : GM ValueId := do
  let xs := (← get).pool.filter (·.2 == t)
  if xs.isEmpty || (← rand 5) == 0 then const t else return (← pick xs).1

def anyVal : GM (ValueId × Ty) := do
  let g ← get
  if g.pool.isEmpty then let t ← pick tys; return (← const t, t)
  pick g.pool

def binOps : Array BinaryOp :=
  #[.iadd, .isub, .imul, .umulhi, .smulhi, .band, .bor, .bxor, .ishl, .ushr, .sshr, .rotl, .rotr,
    .smin, .smax, .umin, .umax]
def extBinOps : Array BinaryOp := #[.uaddSat, .saddSat, .usubSat, .ssubSat]
def unOps : Array UnaryOp := #[.ineg, .bnot, .clz, .ctz, .popcnt, .bitrev, .bswap]
def extUnOps : Array UnaryOp := #[.iabs, .cls]

/-- One random pure (or rarely trapping) statement. -/
def genInst : GM Unit := do
  let ext := (← get).ext
  let t ← pick tys
  match ← rand 14 with
  | 0 => discard <| const t
  | 1 | 2 | 3 | 4 | 5 =>
    let op ← pick (if ext then binOps ++ extBinOps else binOps)
    let x ← valOf t
    let y ← if op.isShift && (← rand 2) == 0 then (·.1) <$> anyVal
      else if (← rand 3) == 0 then const t else valOf t
    discard <| emit (.binary op t x y) t
  | 6 =>
    let op ← pick (if ext then unOps ++ extUnOps else unOps)
    let op := if op == .bswap && t == .i8 then .bnot else op
    discard <| emit (.unary op t (← valOf t)) t
  | 7 | 8 =>
    let cc ← pick IntCC.all.toArray
    let x ← valOf t
    let y ← if (← rand 2) == 0 then const t else valOf t
    discard <| emit (.icmp cc t x y) .i8
  | 9 =>
    let (c, _) ← anyVal
    discard <| emit (.select t c (← valOf t) (← valOf t)) t
  | 10 =>
    let (x, s) ← anyVal
    let wider := tys.filter (·.width > s.width)
    let narrower := tys.filter (·.width < s.width)
    if !wider.isEmpty && (narrower.isEmpty || (← rand 2) == 0) then
      let op ← pick #[ExtendOp.uextend, .sextend]
      let u ← pick wider
      discard <| emit (.extend op u x) u
    else if !narrower.isEmpty then
      let u ← pick narrower
      discard <| emit (.ireduce u x) u
  | 11 =>
    if ext then
      match ← rand 2 with
      | 0 => let (x, _) ← anyVal; discard <| emit (.bmask t x) t
      | _ => discard <| emit (.bitselect t (← valOf t) (← valOf t) (← valOf t)) t
    else discard <| const t
  | 12 =>
    if (← rand 4) == 0 then
      let op ← pick #[DivOp.udiv, .sdiv, .urem, .srem]
      let x ← valOf t
      let y ← valOf t
      -- mostly non-zero divisors: y | 1
      let one ← emit (.iconst t 1) t
      let y ← if (← rand 3) == 0 then pure y else emit (.binary .bor t y one) t
      discard <| emit (.div op t x y) t
    else discard <| const t
  | _ =>
    -- a repeated computation (GVN fodder)
    let g ← get
    let cands := g.body.filter fun s => isPure s.inst && s.results.length == 1
    if cands.isEmpty then discard <| const t else
    let s ← pick cands
    let rt := (g.pool.find? (·.1 == s.results.head!)).map (·.2) |>.getD t
    discard <| emit s.inst rt

def genStmts (n : Nat) : GM (List Stmt) := do
  modify fun g => { g with body := #[] }
  for _ in [0:n] do genInst
  let g ← get
  return g.body.toList

/-- Combine the pool values defined since index `from` (converted to `rt`) with `x` by
`bxor`, so that the random code is live. -/
def fold (rt : Ty) (x : ValueId) (start : Nat) : GM ValueId := do
  let vals := (← get).pool.extract start (← get).pool.size
  let mut acc := x
  for (v, t) in vals do
    let v' ← if t == rt then pure v
      else if t.width < rt.width then emit (.extend .uextend rt v) rt
      else emit (.ireduce rt v) rt
    acc ← emit (.binary .bxor rt acc v') rt
  return acc

def jumpTo (b : BlockId) (args : List ValueId) : Terminator := .jump { block := b, args }

/-- A random function `%name`. -/
def genFunc (name : String) : GM Function := do
  modify fun g => { g with next := 0, pool := #[], body := #[] }
  let nparams := 1 + (← rand 3)
  let mut params : Array (ValueId × Ty) := #[]
  for _ in [0:nparams] do
    let t ← pick tys
    params := params.push (← fresh, t)
  modify fun g => { g with pool := params }
  let rt ← pick tys
  -- block0: straight line, then brif
  let s0 ← genStmts (4 + (← rand 10))
  let (c, _) ← anyVal
  let s0 := s0 ++ (← get).body.toList.drop s0.length
  let pool0 := (← get).pool
  -- block1 / block2: arms of the diamond
  let s1 ← genStmts (1 + (← rand 4))
  let a ← fold rt (← valOf rt) pool0.size
  let s1 := s1 ++ (← get).body.toList.drop s1.length
  modify fun g => { g with pool := pool0 }
  let s2 ← genStmts (1 + (← rand 4))
  let b ← fold rt (← valOf rt) pool0.size
  let s2 := s2 ++ (← get).body.toList.drop s2.length
  modify fun g => { g with pool := pool0 }
  -- block3(m): join, enter the loop
  let m ← fresh
  modify fun g => { g with pool := g.pool.push (m, rt), body := #[] }
  let z0 ← emit (.iconst .i32 0) .i32
  let s3 := (← get).body.toList
  -- block4(i, acc): loop body
  let i ← fresh
  let acc ← fresh
  modify fun g => { g with pool := g.pool.push (i, .i32) |>.push (acc, rt), body := #[] }
  let start4 := (← get).pool.size
  let _ ← genStmts (2 + (← rand 6))
  let acc' ← fold rt acc start4
  let one ← emit (.iconst .i32 1) .i32
  let i' ← emit (.binary .iadd .i32 i one) .i32
  let three ← emit (.iconst .i32 3) .i32
  let lc ← emit (.icmp .ult .i32 i' three) .i8
  let s4 := (← get).body.toList
  -- block5(r): exit
  let r ← fresh
  modify fun g => { g with pool := g.pool.push (r, rt), body := #[] }
  let _ ← genStmts (1 + (← rand 5))
  let res ← fold rt r 0
  let s5 := (← get).body.toList
  let blocks : List Block := [
    { id := 0, params := params.toList, body := s0,
      term := .brif c { block := 1 } { block := 2 } },
    { id := 1, body := s1, term := jumpTo 3 [a] },
    { id := 2, body := s2, term := jumpTo 3 [b] },
    { id := 3, params := [(m, rt)], body := s3, term := jumpTo 4 [z0, m] },
    { id := 4, params := [(i, .i32), (acc, rt)], body := s4,
      term := .brif lc { block := 4, args := [i', acc'] } { block := 5, args := [acc'] } },
    { id := 5, params := [(r, rt)], body := s5, term := .ret [res] }]
  return { name, sig := { params := params.toList.map fun (_, t) => { ty := t },
                          returns := [{ ty := rt }] }, blocks }

def showO : Outcome → String
  | .returned vs _ => s!"returned {vs.map (·.toInt)}"
  | .trapped c => s!"trapped {c.name}"
  | .stuck m => s!"stuck {m}"
  | .outOfFuel => "out of fuel"

def genArgs (f : Function) : GM (List Val) :=
  f.sig.params.mapM fun p => do
    let k ← interesting p.ty
    return Val.ofInt p.ty k

end OptFuzz

open OptFuzz in
def main (args : List String) : IO UInt32 := do
  let ((cfg : Option Config), rest) ← match parseOptArgs args with
    | .ok r => pure r
    | .error e => do IO.eprintln s!"opt-fuzz: {e}"; return 2
  let cfg := cfg.getD {}
  let mut seed := 1
  let mut count := 100
  let mut ext := false
  let mut out : Option String := none
  let mut verbose := false
  let mut xs := rest
  for _ in [0:rest.length + 1] do
    match xs with
    | "--seed" :: n :: r => seed := n.toNat!; xs := r
    | "--count" :: n :: r => count := n.toNat!; xs := r
    | "--ext" :: r => ext := true; xs := r
    | "--out" :: o :: r => out := some o; xs := r
    | "-v" :: r => verbose := true; xs := r
    | [] => break
    | a :: _ => IO.eprintln s!"opt-fuzz: unknown argument {a}"; return 2
  let mut st : G := { gen := mkStdGen seed, ext }
  let mut funcs : Array Function := #[]
  let mut runs := 0
  let mut agree := 0
  let mut fails := 0
  let mut noclaim := 0
  let mut before := 0
  let mut after := 0
  let mut rewritten := 0
  let mut notOpt := 0
  for k in [0:count] do
    let (f, st1) := (genFunc s!"fz{seed}_{k}").run st
    st := st1
    let (g, rep) := optimizeReport cfg f
    if rep.illFormed.isSome || rep.passError.isSome then
      notOpt := notOpt + 1
      IO.println s!"%{f.name}: {repr rep.illFormed} {repr rep.passError}"
      if rep.passError.isSome then fails := fails + 1
    before := before + rep.sizeBefore
    after := after + rep.sizeAfter
    rewritten := rewritten + rep.rewritten
    let p : Program := { funcs := [f] }
    let p' : Program := { funcs := [g] }
    let mut rcs : Array RunCommand := #[]
    let mut bad := false
    for _ in [0:8] do
      let (as, st2) := (genArgs f).run st
      st := st2
      let o := Clif.run {} p f.name as 100000
      let o' := Clif.run {} p' f.name as 200000
      runs := runs + 1
      let ok? : Option Bool := match o, o' with
        | .returned vs _, .returned ws _ => some (vs == ws)
        | .trapped c, .trapped d => some (c == d)
        | .returned .., _ | .trapped _, _ => some false
        | _, _ => none
      match ok? with
      | some true => agree := agree + 1
      | some false =>
        fails := fails + 1; bad := true
        IO.println s!"FAIL %{f.name}{as.map (·.toInt)}: before {showO o}, after {showO o'}"
      | none => noclaim := noclaim + 1
      if let .returned vs _ := o then
        rcs := rcs.push { func := f.name, args := as, expect := .eq vs }
    if bad || verbose then
      IO.println (Function.print f)
      IO.println (Function.print g)
    funcs := funcs.push { f with runs := rcs.toList }
  if let some o := out then
    let prog : Program :=
      { header := ["test interpret", "test run", "target aarch64"], funcs := funcs.toList }
    IO.FS.writeFile o (Clif.print prog)
  IO.println s!"opt-fuzz seed {seed}: functions {count} (not optimised {notOpt}), runs {runs} agree {agree} fail {fails} noclaim {noclaim}, insts {before} -> {after}, rewritten {rewritten}"
  return if fails == 0 then 0 else 1
