import FV.Clif.Run

/-!
# Trusted Rust externs: `mem*` and panics (rust-route step 2)

`rustc_codegen_cranelift` output calls out to `memcpy`/`memmove`/`memset`/`memcmp` (the
Cranelift `Memcpy`/… libcalls, named `memcpy`/… by `normalize.py`) and to the diverging
`core` panic entry points. `Clif.Rust.env` gives both a `Clif.Env` semantics so `Clif.run`
can execute such calls; they are trusted contracts in the sense of `XCallsOk`/`CalleeOk`
(`docs/contracts/e2e.md`), implemented natively by `scripts/rust-clif/rust-runtime.{c,s}`.

Contracts (byte-level, on `Clif.Mem`):

* `memcpy(dst, src, n)` / `memmove(dst, src, n)`: copies `n` bytes, byte by byte,
  preserving each byte's initialisation state (`memmove` semantics — exact for every
  overlap). Both ranges must be inside one allocation and the destination must not be
  read-only (the `notrap`/`readonly` preconditions of `Mem.load`/`Mem.store`); `stuck`
  otherwise. Returns `dst` (`i64`), like the C function.
* `memset(dst, c, n)`: stores the low byte of `c` `n` times (same checks).
* `memcmp(a, b, n) -> i32`: bytewise unsigned, `0` when equal, `-1`/`1` at the first
  difference; reading an uninitialised byte is `stuck`.
* Every diverging entry point (`Clif.Rust.isPanic`: the corpus's mangled `panic*`,
  `*_fail`, `handle_*`, `fmt` names) ends the run with `trapped (.user 1)` — the `trap
  user1` of the unreachable continuation is what the program would execute next, and no
  value is returned. Natively these entries are `udf #251` (SIGILL), which the harness
  reports as a fault; the two representations of "aborted" are agreed at the call site.
-/

namespace Clif.Rust

/-! ## Name classification -/

/-- Is `sub` a substring of `s`? (Nonempty `sub`: `s.splitOn sub` splits it off, so the
single-part result means absence.) -/
def hasSub (sub s : String) : Bool :=
  if sub.isEmpty then true else !(s.splitOn sub == [s])

/-- Does the extern name (without `%`) denote a diverging Rust entry point? Matches the
mangled `core`/`alloc` panic and failure entry points of the corpus (`*_undef` lists):
anything with a `panic`/`fail`/`handle_`-shaped mangled name, plus `core::fmt::Formatter`
methods and integer `Display` impls (`…3fmt`). -/
def isPanic (name : String) : Bool :=
  hasSub "panic" name || hasSub "unwrap_failed" name || hasSub "slice_index_fail" name ||
    hasSub "len_mismatch_fail" name || hasSub "handle_alloc_error" name ||
    hasSub "handle_error" name || hasSub "Formatter" name || name.endsWith "3fmt"

/-! ## The `mem*` semantics -/

/-- The mem* arguments `(dst, src, n)`, as byte addresses/counts; `none` on an arity or
type mismatch (`stuck`). -/
def memArgs (vals : List Val) : Option (Nat × Nat × Nat) :=
  match vals[0]?, vals[1]?, vals[2]? with
  | some d, some s, some n =>
    match d.as? .i64, s.as? .i64, n.as? .i64 with
    | some dv, some sv, some nv => some (dv.toNat, sv.toNat, nv.toNat)
    | _, _, _ => none
  | _, _, _ => none

/-- `memcpy`/`memmove` of `n` bytes from `src` to `dst`: a byte-by-byte copy that
preserves each byte's initialisation state (`none` stays `none`; the `memmove` semantics
are exact for every overlap). Both ranges must be inside one allocation and the
destination must not be read-only. -/
def memcopy (m : Mem) (dst src n : Nat) : Res Mem :=
  if n == 0 then pure m else do
    Res.check (m.valid src n) s!"memcpy: source not in one allocation at {src}"
    Res.check (m.valid dst n) s!"memcpy: destination not in one allocation at {dst}"
    Res.check (!m.readonlyAt dst n) s!"memcpy: destination is read-only at {dst}"
    let bytes : List (Nat × Option (BitVec 8)) :=
      (List.range n).map (fun i => (dst + i, m.bytes (src + i)))
    pure { m with bytes := fun a =>
      match bytes.find? (fun (addr, _) => a == addr) with
      | some (_, v) => v
      | none => m.bytes a }

/-- `memset` of `n` bytes with the low byte of `c` (the `Mem.store` checks). -/
def memstore (m : Mem) (dst c n : Nat) : Res Mem := do
  Res.check (m.valid dst n) s!"memset: destination not in one allocation at {dst}"
  Res.check (!m.readonlyAt dst n) s!"memset: destination is read-only at {dst}"
  let c8 : BitVec 8 := BitVec.ofInt 8 c
  pure { m with bytes := fun a => if dst ≤ a ∧ a < dst + n then some c8 else m.bytes a }

/-- `memcmp` of `n` bytes: bytewise unsigned; `0` when equal, `-1`/`1` at the first
difference. `stuck` on uninitialised bytes. -/
def memcmp (m : Mem) (a b : Nat) : Nat → Res Int
    | 0 => pure 0
    | n + 1 => do
      let x ← Res.ofOption "memcmp: read of uninitialised memory" (m.bytes a)
      let y ← Res.ofOption "memcmp: read of uninitialised memory" (m.bytes b)
      if x != y then pure (if x < y then -1 else 1) else memcmp m (a + 1) (b + 1) n

/-- The outcome of a mem* call on `(args, mem)`. -/
def memOutcome (name : String) (args : List Val) (m : Mem) : Outcome :=
  match memArgs args with
  | none => .stuck "mem*: arity or argument types"
  | some (dst, src, n) =>
    let res : Res (List Val × Mem) :=
      match name with
      | "memcpy" | "memmove" => do
        let m' ← memcopy m dst src n
        pure ([Val.ofInt .i64 dst], m')
      | "memset" => do
        let c := match args[1]? with | some v => v.toNat % 256 | none => 0
        let m' ← memstore m dst c n
        pure ([Val.ofInt .i64 dst], m')
      | "memcmp" => do
        let r ← memcmp m dst src n
        pure ([Val.ofInt .i32 (if r == 0 then 0 else if r == -1 then -1 else 1)], m)
      | _ => .stuck s!"unknown mem* extern %{name}"
    match res with
    | .ok (vs, m') => .returned vs m'
    | .trap c => .trapped c
    | .stuck m => .stuck m

/-- The `__*ti3` helpers of 128-bit division/remainder (rust-route step 5). The corpus calls
`__udivti3`/`__modti3` from `div`/`rem` at `u128`/`i128` (cg_clif's libcall lowering), and
`Opt.Legalize128` lowers the `div`/`rem` opcodes to the same helpers, so `Clif.run` runs
both the original and the legalised form through this semantics. The arguments arrive
either as one `i128` value per 128-bit operand (the original's `fnN` declaration) or as two
`i64` pairs (the legalised declaration); the returned values always match the declared
signature's return types.

Byte-exact semantics of the helpers (libgcc/`scripts/rust-clif/rust-runtime.c`): exact
unsigned/signed (truncating) division and remainder. A zero divisor is `trapped int_divz` —
what the `udiv`/`sdiv`/`urem`/`srem` opcode it replaces would trap — and `sdiv(i128::MIN,
-1)` is `trapped int_ovf`, so `Clif.run` on the original opcode and on the legalised helper
call agree. (Natively the runtime helper aborts on a zero divisor, like libgcc, and wraps
on the overflow case; no run line exercises either.) -/
def div128 (signed : Bool) (isRem : Bool) (vals : List Val) : Option (List Val × Option TrapCode) :=
  -- the two 128-bit operands, as (bits, unsigned interpretation, signed interpretation)
  let ops : Option ((Nat × Int) × (Nat × Int)) :=
    match vals with
    | [a, b] =>
      match a.as? .i128, b.as? .i128 with
      | some x, some y =>
        let u (v : BitVec 128) : Nat := v.toNat
        let s (v : BitVec 128) : Int := v.toInt
        some ((u x, s x), (u y, s y))
      | _, _ => none
    | [alo, ahi, blo, bhi] =>
      match alo.as? .i64, ahi.as? .i64, blo.as? .i64, bhi.as? .i64 with
      | some x0, some x1, some y0, some y1 =>
        let pair (lo hi : BitVec 64) : Nat × Int :=
          let n := lo.toNat + hi.toNat * (2 ^ 64 : Nat)
          (n, if hi.toNat ≥ 2 ^ 63 then n - 2 ^ 128 else n)
        some (pair x0 x1, pair y0 y1)
      | _, _, _, _ => none
    | _ => none
  match ops with
  | none => none
  | some ((nu, ns), (du, ds)) =>
    let q (v : Nat) : List Val :=
      let lo := v % (2 ^ 64 : Nat)
      let hi := v / (2 ^ 64 : Nat)
      if vals.length == 2 then [⟨.i128, BitVec.ofNat 128 v⟩]
      else [⟨.i64, BitVec.ofNat 64 lo⟩, ⟨.i64, BitVec.ofNat 64 hi⟩]
    if du = 0 then some ([], some .intDivz)
    else if signed ∧ !isRem ∧ ns = -(2 ^ 127 : Int) ∧ du = 2 ^ 128 - 1 then
      some ([], some .intOvf)
    else if signed then
      -- truncated division/remainder (C semantics: the quotient rounds toward zero, the
      -- remainder has the sign of the dividend), on the magnitudes
      let (m, d) := (ns.natAbs, ds.natAbs)
      let qv := m / d
      let rv := m % d
      let qv : Int := if (ns < 0) != (ds < 0) then -(qv : Int) else qv
      let rv : Int := if ns < 0 then -(rv : Int) else rv
      let mm := qv % (2 ^ 128 : Int)
      let mm := if mm < 0 then mm + 2 ^ 128 else mm
      if isRem then
        let rm := rv % (2 ^ 128 : Int)
        let rm := if rm < 0 then rm + 2 ^ 128 else rm
        some (q rm.toNat, none)
      else
        some (q mm.toNat, none)
    else
      let r := if isRem then nu % du else nu / du
      some (q r, none)

/-- Is `name` one of the `__*ti3` helpers? -/
def isDivHelper (name : String) : Bool :=
  name == "__udivti3" || name == "__divti3" || name == "__umodti3" || name == "__modti3"

/-- The outcome of a `__*ti3` call on `(args, mem)`: the helpers do not touch memory, so a
return keeps `mem`. -/
def divOutcome (name : String) (vals : List Val) (m : Mem) : Outcome :=
  let signed := name == "__divti3" || name == "__modti3"
  let isRem := name == "__umodti3" || name == "__modti3"
  match div128 signed isRem vals with
  | none => .stuck s!"%{name}: argument types"
  | some (_, some c) => .trapped c
  | some (vs, none) => .returned vs m

/-- The trusted Rust contracts as a `Clif.Env`: the mem* byte-level semantics, the `__*ti3`
division helpers, and every diverging entry point ends the run. -/
def env : Env where
  extern name :=
    if isPanic name then
      some fun _ _ => .trapped (.user 1)
    else if name == "memcpy" || name == "memmove" || name == "memset" || name == "memcmp" then
      some (memOutcome name)
    else if isDivHelper name then
      some fun vals m => divOutcome name vals m
    else none

end Clif.Rust
