# DSL contract (`FV/DSL`, producer M1-frontend)

## Status (kept current for resumption)

Complete. `lake build FV.DSL Corpus FVTest.DSL.Negative` is clean (the only message is the
`flat_def.timing` info line for the ChaCha20 corpus function). No `sorry`, no `axiom`.

| File | Contents |
| --- | --- |
| `FV/DSL/Map.lean` | `DSL.Map` (collection) and its laws |
| `FV/DSL/Ty.lean` | `IntW`, `Ty`, `Ty.denote`, `Err`, `Err.tag`/`ofTag`, `M` |
| `FV/DSL/Ops.lean` | shallow primitives `DSL.Ops.*`, notation, lemmas for user proofs |
| `FV/DSL/Syntax.lean` | `Var`, `Env`, `Args`, `IBin`/`ICmp`/`Cast`/`IOp`, `Expr`, `Exprs`, `Op`, `Stmt`, `FlatFn` |
| `FV/DSL/Denote.lean` | `Expr.denote`, `Op.denote`, `Stmt.denote`, `DSL.denote` |
| `FV/DSL/Check.lean` | `FlatFn.check`/`checkB`/`checked`, affine and fragment rules |
| `FV/DSL/TestCase.lean` | `DSL.TestCase` (differential-testing vectors) |
| `FV/DSL/Frontend.lean` | the `flat def` command |
| `FV/DSL.lean` | root, imports all of the above |
| `corpus/dsl/Corpus/*.lean` | 31 programs, `Corpus.all`, user proofs (lake lib `Corpus`) |
| `FVTest/DSL/Negative.lean` | rejected programs |

A consumer that must not see the `flat def` tokens (`requires`, `ensures` are reserved
keywords once `FV.DSL.Frontend` is imported) should import `FV.DSL.Check` (the whole AST and
semantics) instead of `FV.DSL`.

## 1. Types, errors, effect (`FV/DSL/Ty.lean`)

```lean
inductive DSL.IntW | w8 | w16 | w32 | w64            -- IntW.bits : IntW → Nat  (8/16/32/64)
inductive DSL.Ty
  | int (w : IntW) | bool | unit | vec (n : Nat) (t : Ty) | prod (a b : Ty) | map (k v : Ty)
@[match_pattern] abbrev Ty.u8 := Ty.int .w8     -- also u16 u32 u64
def Ty.denote : Ty → Type   -- int w ↦ BitVec w.bits, bool ↦ Bool, unit ↦ Unit,
                            -- vec n t ↦ Vector t.denote n, prod ↦ ×, map k v ↦ DSL.Map k.denote v.denote
instance Ty.decEq : (t : Ty) → DecidableEq t.denote        -- also Repr, Inhabited
def Ty.default : (t : Ty) → t.denote                        -- zeros / false / empty map
def Ty.isScalar, Ty.linear, Ty.hasMap, Ty.isKey, Ty.wf : Ty → Bool

inductive DSL.Err | overflow | divByZero | indexOutOfBounds | notFound | user (code : Fin 200)
abbrev DSL.M := Except DSL.Err
instance DSL.instDecidableEqExcept [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
abbrev DSL.U8 := BitVec 8   -- U16 U32 U64 (in Frontend.lean)
```

Machine integers are width-indexed so every integer operation is stated once, generically in
`w`; `Ty.u8 … Ty.u64` are the pattern-matchable names.

### Error-tag ABI (`Err.tag`)

| `Err` | tag |
| --- | --- |
| (ok) | 0 |
| `overflow` | 1 |
| `divByZero` | 2 |
| `indexOutOfBounds` | 3 |
| `notFound` | 4 |
| reserved for future built-ins | 5 … 55 |
| `user k` (`k < 200`) | `56 + k` (56 … 255) |

`Err.tag : Err → Nat`, `Err.tag8 : Err → BitVec 8`, `Err.ofTag : Nat → Option Err`,
`Err.userBase = 56`. Theorems: `tag_pos : 0 < e.tag`, `tag_lt : e.tag < 256`,
`ofTag_tag : ofTag e.tag = some e`, `tag_ofTag : ofTag k = some e → e.tag = k`,
`tag_injective`, `tag8_toNat : e.tag8.toNat = e.tag`.

## 2. Deep AST (`FV/DSL/Syntax.lean`)

Contexts are `List Ty`, most recent binder first. Parameters: `x₁` of `f (x₁ … xₙ)` is `#0`.

```lean
inductive Var : List Ty → Ty → Type | zero : Var (t :: Γ) t | succ : Var Γ t → Var (s :: Γ) t
def Var.idx : Var Γ t → Nat
@[reducible] def Env : List Ty → Type   -- Env [] = Unit, Env (t :: Γ) = t.denote × Env Γ
abbrev Args (σ : List Ty) := Env σ       -- f x y ↦ args (x, y, ())
def Var.get : Var Γ t → Env Γ → t.denote
def Var.set : Var Γ t → Env Γ → t.denote → Env Γ

inductive IBin | add | sub | mul | and | or | xor | shl | lshr | ashr   -- wrapping
inductive ICmp | eq | ne | ult | ule | slt | sle
inductive Cast | zext | sext | trunc
inductive IOp  | addC | subC | mulC | udiv | urem                        -- fallible, unsigned

inductive Expr : List Ty → Ty → Type          -- pure, total
  | var (v : Var Γ t)          -- moves if t.linear
  | clone (v : Var Γ t)        -- copy, never moves
  | ilit (w : IntW) (v : BitVec w.bits) | blit (b : Bool) | unit
  | ibin (op : IBin) : Expr Γ (.int w) → Expr Γ (.int w) → Expr Γ (.int w)
  | inot : Expr Γ (.int w) → Expr Γ (.int w)
  | icmp (op : ICmp) : Expr Γ (.int w) → Expr Γ (.int w) → Expr Γ .bool
  | cast (op : Cast) (w' : IntW) : Expr Γ (.int w) → Expr Γ (.int w')
  | band | bor : Expr Γ .bool → Expr Γ .bool → Expr Γ .bool   | bnot : Expr Γ .bool → Expr Γ .bool
  | cond : Expr Γ .bool → Expr Γ t → Expr Γ t → Expr Γ t       -- pure select
  | pair : Expr Γ a → Expr Γ b → Expr Γ (.prod a b) | fst | snd
  | vrepl (n : Nat) : Expr Γ t → Expr Γ (.vec n t)             -- Vector.replicate
  | mapEmpty : Expr Γ (.map k v)
  | mapContains : Var Γ (.map k v) → Expr Γ k → Expr Γ .bool   -- reads, no move

inductive Exprs : List Ty → List Ty → Type | nil : Exprs Γ [] | cons : Expr Γ t → Exprs Γ σ → Exprs Γ (t :: σ)

inductive Op : List Ty → Ty → Type            -- fallible primitives
  | iop (op : IOp) : Expr Γ (.int w) → Expr Γ (.int w) → Op Γ (.int w)
  | vget : Var Γ (.vec n t) → Expr Γ (.int w) → Op Γ t          -- indexOutOfBounds
  | mapGet : Var Γ (.map k v) → Expr Γ k → Op Γ v               -- notFound

inductive Stmt : List Ty → Ty → Type
  | ret : Expr Γ τ → Stmt Γ τ
  | throw : Err → Stmt Γ τ
  | op : Op Γ τ → Stmt Γ τ
  | call (name : String) (body : Stmt σ τ) (args : Exprs Γ σ) : Stmt Γ τ
  | let_ : Expr Γ α → Stmt (α :: Γ) τ → Stmt Γ τ
  | letPair : Expr Γ (.prod a b) → Stmt (b :: a :: Γ) τ → Stmt Γ τ     -- x = #1, y = #0
  | bind : Stmt Γ α → Stmt (α :: Γ) τ → Stmt Γ τ
  | set (v : Var Γ α) : Expr Γ α → Stmt Γ τ → Stmt Γ τ
  | vset (v : Var Γ (.vec n α)) : Expr Γ (.int w) → Expr Γ α → Stmt Γ τ → Stmt Γ τ
  | mapInsert (v : Var Γ (.map k val)) : Expr Γ k → Expr Γ val → Stmt Γ τ → Stmt Γ τ
  | ite : Expr Γ .bool → Stmt Γ τ → Stmt Γ τ → Stmt Γ τ
  | forRange (n : Nat) : Expr Γ α → Stmt (α :: .u64 :: Γ) α → Stmt Γ α   -- body: acc = #0, i = #1

structure FlatFn (σ : List Ty) (τ : Ty) where
  name : String       -- fully qualified Lean name of the flat def, e.g. "Corpus.sumChecked"
  body : Stmt σ τ
```

Design choices: effects are in A-normal form (`Expr` is pure, fallible primitives only occur as
`Stmt.op`, sequenced by `Stmt.bind`); calls embed the callee's name *and body*, so `denote` is
structural and recursion is impossible by construction; loops are folds over an explicit
accumulator (static bound `n`, index `u64`).

## 3. Semantics (`FV/DSL/Denote.lean`)

```lean
def Expr.denote  : Expr Γ t → Env Γ → t.denote
def Exprs.denote : Exprs Γ σ → Env Γ → Env σ
def Op.denote    : Op Γ t → Env Γ → M t.denote
def Stmt.denote  : Stmt Γ τ → Env Γ → M τ.denote
def DSL.denote (f : FlatFn σ τ) (args : Args σ) : M τ.denote := f.body.denote args
```

All structurally recursive, no well-founded recursion. Primitive meanings, by constructor:

| Construct | Meaning |
| --- | --- |
| `ibin add/sub/mul/and/or/xor` | `BitVec` `+ - * &&& ||| ^^^` (wrapping) |
| `ibin shl/lshr/ashr` | `Ops.shl/lshr/ashr a b` = shift by `b.toNat % n` (CLIF masking) |
| `icmp eq/ne/ult/ule/slt/sle` | `==`, `!=`, `BitVec.ult/ule/slt/sle` |
| `cast zext/sext/trunc w'` | `Ops.zext/sext/trunc w'.bits` = `setWidth`/`signExtend`/`setWidth` |
| `iop addC/subC/mulC` | `Ops.addC/subC/mulC`: `overflow` iff `BitVec.uaddOverflow/usubOverflow/umulOverflow` |
| `iop udiv/urem` | `Ops.udiv/urem`: `divByZero` iff divisor is 0, else `/`, `%` |
| `vget v i` | `Ops.vget`: `indexOutOfBounds` iff `i.toNat ≥ n` |
| `vset v i e k` | `Ops.vset` (same check) `>>= fun xs => k (v := xs)` |
| `mapGet m k` | `Ops.mapGet`: `notFound` iff `m.get? k = none` |
| `mapInsert m k x c` | `c` with `m := m.insert k x` |
| `bind s k` | `s.denote env >>= fun x => k.denote (x, env)` |
| `forRange n init body` | `Ops.forRange n init (fun i acc => body.denote (acc, i, env))` |
| `call _ body args` | `body.denote (args.denote env)` |
| `throw e` | `throw e` (the whole function returns the error) |

`Ops.forRange n init f` runs `f 0, f 1, …, f (n-1)` (index `BitVec.ofNat 64 i`) threading the
accumulator, stopping at the first error.

## 4. Checker (`FV/DSL/Check.lean`)

```lean
def FlatFn.check  (f : FlatFn σ τ) : Except String Unit     -- explains rejections
def FlatFn.checkB (f : FlatFn σ τ) : Bool
def FlatFn.checked (f : FlatFn σ τ) : Prop := f.checkB = true   -- Decidable
def Stmt.chk : Stmt Γ τ → Option Nat → CheckSt → Except String CheckSt   -- (and Expr/Op/Exprs.chk)
```

Fragment rules: every type in parameters, result, and binders is `Ty.wf` (map keys and values
are `int`/`bool`; no maps inside vectors; vector length `> 0`); `zext`/`sext` do not narrow and
`trunc` does not widen; `forRange n` has `n < 2^64`; every callee body is checked too.

Affine rule, over *linear* types (`Ty.linear`: containing a vector or map):

* `Expr.var v` in any position is a **move**: `v` is dead afterwards. `clone`, `vget`,
  `mapGet`, `mapContains` read without moving.
* Any occurrence of a dead variable (read, move, clone, in-place update target) is rejected.
  `set v e` may target a dead `v` and revives it.
* `bind s k`: a linear variable of the enclosing context updated in `s` (`set`, `vset`,
  `mapInsert`) is dead in `k`.
* `ite`: after the join, a variable is dead if dead after either branch.
* `forRange` body: may not move or update any linear variable bound outside the body.

**Invariant the emitter may assume for `f.checked`:** at every read or in-place update of a
linear variable `v`, `v` is alive and no other live variable, loop accumulator, or value in
flight shares `v`'s storage. Hence: a move may transfer the pointer (no copy); `vset` and
`mapInsert` may write in place; `set v e` on a linear `v` may rebind `v` to `e`'s storage;
`clone` must copy. Scalars (and products of scalars) are freely copyable SSA values.

## 5. Emitter guide (how to traverse `Stmt`)

Representation (a suggestion consistent with the invariant): scalars are SSA values (`bool` as
`i8` 0/1, `unit` as nothing); `vec n t` is a pointer (`i64`) to `n · size t` bytes, little-endian,
bool elements one byte; `prod a b` is the flattened pair of representations; `map` is an `i64`
runtime handle. A compiled `f : FlatFn σ τ` is a CLIF function named after `f.name` returning
`(i8 tag, payload…)` (docs/ARCHITECTURE.md error-tag ABI).

* `throw e` anywhere (also inside `bind`/loops/callees): return `(e.tag8, zero payload)` from the
  current function. Every `throw` is a function exit because `M` short-circuits.
* `op o`: compute; failure → return its tag. Suggested checks (clif-subset-v1, no
  `*_overflow` ops): `addC` carry = `icmp ult sum, a`; `subC` borrow = `icmp ult a, b`;
  `mulC` overflow = `umulhi a b ≠ 0`; `udiv/urem` guard `b = 0` before the op;
  `vget/vset` guard `uextend(i) <u n` before address computation (then `notrap aligned` loads
  and stores are justified).
* `call name body args`: collect callees transitively from the AST, emit one CLIF function per
  distinct `name` (the frontend guarantees `name` is the unique Lean declaration name), call it,
  propagate a non-zero tag.
* `ret e` in tail position: return `(0, e)`. `ret e` inside the first part of `bind s k`:
  jump to the join block of `k` with `e` as block arguments.
* `bind s k`: compile `s` with continuation "jump join(α-values)"; the join block binds `#0`.
* `let_`/`set`/`letPair`: environment bookkeeping (no code for scalars).
* `ite c t e`: `brif` (use `brif` with block params instead of `select`, which is not in E).
  Also `Expr.cond`.
* `forRange n init body`: header block `(i : i64, acc…)`, exit when `i = n` (unsigned; `n` is
  a static constant `< 2^64`), body continuation jumps back with `i + 1` and the new accumulator.
* `Expr.icmp` gives an `i8` 0/1; `band/bor` are `band/bor` on `i8`, `bnot b` is `bxor b, 1`.
* `cast`: `uextend`/`sextend`/`ireduce`, or nothing if the width is unchanged.

### Collections: runtime externs (C ABI, `aarch64-unknown-linux-gnu`)

Keys and values (`int`/`bool` only) are passed zero-extended in an `i64`; `bool` is 0/1.

| DSL | Extern | C signature |
| --- | --- | --- |
| `Expr.mapEmpty` | `flat_map_new` | `int64_t flat_map_new(void)` |
| `Stmt.mapInsert m k v` | `flat_map_insert` | `void flat_map_insert(int64_t h, uint64_t k, uint64_t v)` (in place) |
| `Expr.mapContains m k` | `flat_map_contains` | `uint8_t flat_map_contains(int64_t h, uint64_t k)` (0/1) |
| `Op.mapGet m k` | `flat_map_get` | `uint8_t flat_map_get(int64_t h, uint64_t k, uint64_t *out)` (1 = found, writes `*out`; 0 → `notFound`) |
| `Expr.clone m` | `flat_map_clone` | `int64_t flat_map_clone(int64_t h)` |
| (map variable dies unmoved) | `flat_map_free` | `void flat_map_free(int64_t h)` (optional in M1: leaks are not observable) |
| test harness only | `flat_map_len`, `flat_map_entry` | `uint64_t flat_map_len(int64_t h)`, `void flat_map_entry(int64_t h, uint64_t i, uint64_t *k, uint64_t *v)` (insertion order) |

Semantics (`FV/DSL/Map.lean`): `DSL.Map K V` is an insertion-ordered association list
(`entries : List (K × V)`); `insert` replaces in place if the key exists, else appends, so
iteration order is first-insertion order (deterministic). Laws (theorems): `get?_empty`,
`contains_empty`, `get?_insert_self`, `get?_insert_ne`, `get?_insert`, `contains_insert_self`,
`contains_insert_ne`, `contains_insert`, `contains_iff_get?`, `size_insert_of_not_contains`,
`size_insert_of_contains`, `get?_insert_insert`. The runtime may use any representation that
satisfies them and reproduces `entries` order through `flat_map_entry`.

## 6. Surface language: `flat def` (`FV/DSL/Frontend.lean`)

```
flat def f (x₁ : T₁) … (xₙ : Tₙ) : T
  requires P            -- optional (term over x₁ … xₙ)
  ensures r, Q          -- optional (term over x₁ … xₙ and r)
  := do
  <statements>
proof by <tactics>      -- required iff requires/ensures; must start LEFT of the statements' column
```

Types: `BitVec 8|16|32|64` (or `DSL.U8 … DSL.U64`), `Bool`, `Unit`, `Vector T n` (numeral `n`),
`A × B`, `DSL.Map K V` / `Map K V`. `UInt8…UInt64` are rejected with a hint.

Statements: `let x := e`, `let mut x (: T)? := e`, `let x ← e` (same as `:=`), `x := e`
(mutable `x`), `xs := xs.set! i e` (checked in-place update), `m := m.insert k v`,
`if c then … (else if c then …)* (else …)?`, `for i in [0:n] do …` / `for _ in [:n] do …`
(numeral `n`), `return e`, `throw err` (`.overflow`, `.divByZero`, `.indexOutOfBounds`,
`.notFound`, `.user k` with `k < 200`), a final expression (returned), an effectful
expression statement (a call whose result is discarded). Rejected: `while`/`repeat`, `return`
inside loops (and inside a non-tail `if` whose other paths fall through), unknown statements.

Expressions: variables, `x.clone`, numerals (width from context or `(n : BitVec w)`),
`true/false`, `()`, `+% -% *%` (wrapping), `+? -? *?` (unsigned checked, `overflow`), `/? %?`
(unsigned, `divByZero`), `&&& ||| ^^^ ~~~ <<< >>>`, `ashr a b`, `== != < ≤ > ≥` (unsigned),
`BitVec.slt/sle/ult/ule a b`, `&& || !` (bool), `if c then a else b` (pure arms only),
`(a, b)`, `p.1`, `p.2`, `p.fst`, `p.snd`, `xs[i]!` (checked, `indexOutOfBounds`),
`Vector.replicate n x`, `DSL.Map.empty`, `m.contains k`, `m.get! k` (`notFound`),
`zext w a`, `sext w a`, `trunc w a`, calls `g a b` of earlier flat defs. Bare `+ - * / %` on
machine integers and `xs[i]` are rejected with a message.

Evaluation order: effectful sub-expressions (checked ops, `xs[i]!`, `m.get!`, calls) are
lifted left to right, innermost first, before the enclosing statement (A-normal form).
`&&`/`||` evaluate both operands (write an `if` to guard a fallible operand). Unlike Lean's
`Vector.set!`, `xs.set! i e` throws `indexOutOfBounds`. Parameters are immutable
(`let mut y := x` makes a mutable copy). Mutable variables assigned in a loop body or in a
non-tail `if` are carried through the loop accumulator / join point as a right-nested tuple.

Generated declarations (in the current namespace):

| Name | Statement |
| --- | --- |
| `f.ast` | `def f.ast : DSL.FlatFn [T₁, …, Tₙ] T := { name := "<full name>", body := … }` |
| `f` | `def f (x₁ : T₁) … : DSL.M T` — direct style, explicit `>>=`/`let`/`if`/`DSL.Ops.forRange` |
| `f.denote_eq` | `@[simp] theorem f.denote_eq : ∀ x₁ … xₙ, DSL.denote f.ast (x₁, …, xₙ, ()) = f x₁ … xₙ` |
| `f.checked` | `theorem f.checked : DSL.FlatFn.checked f.ast` (by `decide`) |
| `f.contract` | `theorem f.contract : ∀ x₁ … xₙ, P → ∃ r, f x₁ … xₙ = Except.ok r ∧ Q` (by the user's `proof by`); `True` for an omitted `requires`/`ensures` |

With zero parameters the `∀` is omitted and the argument tuple is `()`.

Before generating `f.checked` the frontend runs `FlatFn.check` (compiled evaluation) and
fails with its message: `flat def rejected by the fragment checker: <name>: <reason>`. Common
affine violations are reported earlier with variable names (`` `xs` is used after it was
moved; write `xs.clone` … ``, `the loop body moves/updates `xs` …`).

`denote_eq` proof: `Eq.refl` checked by the kernel only (`addKernelRfl`, synchronous
`Environment.addDeclCore`, then `addDecl`). Fallback if the kernel check fails:
`first | exact rfl | with_unfolding_all exact rfl | simp only [DSL.denote, …]`. Rationale:
`exact rfl` (elaborator `isDefEq`) blows up exponentially on straight-line code with
reassignments (9.2 s for a 12-statement ChaCha prefix; the full function did not finish in
300 s), while the kernel's shared defeq check is fast. `set_option flat_def.timing true`
reports the time.

**Measured** (largest corpus function `Corpus.chacha20Block`: 16 loads, a 10-iteration loop
with 16 carried `u32` variables and 96 wrapping/rotate statements, 16 checked `set!`):
`denote_eq` 1.08–1.54 s (kernel, synchronous check; `addDecl` re-checks asynchronously), the
whole module `Corpus.Big` 4.6–5.8 s including `checked` by `decide` and the RFC 7539 §2.3.2
test vector via `#guard`.

`#print axioms Corpus.chacha20Block.denote_eq` → `[propext, Quot.sound]` (same for
`sumChecked.denote_eq`, `incrTwice.denote_eq`); `Corpus.chacha20Block.checked` → `[propext]`.

Contracts and irreducibility: with `requires`/`ensures`, `f` is made `@[irreducible]` right
after `f.denote_eq`, `f.checked`, `f.contract` (Lean has no end-of-module hook, so this holds
in the defining module too; proofs there use `unfold f`, `simp [f]` or `f.eq_def`, which ignore
reducibility). Callers' `denote_eq` is unaffected (the kernel ignores reducibility; see
`Corpus.incrTwice`). Equation lemmas: `f.denote_eq` is `@[simp]` (rewrites deep to shallow);
unfolding the shallow `f` uses Lean's generated `f.eq_def`/`f.eq_1` (not `@[simp]`, deliberately:
bodies such as ChaCha20 are large).

User-proof support (`FV/DSL/Ops.lean`): `ok_bind`, `error_bind`, `pure_eq_ok`,
`throw_eq_error` (simp), `addC_eq_ok`, `addC_ok`, `addC_overflow`, `subC_ok`,
`subC_overflow`, `mulC_ok`, `vget_ok`, `vget_oob`, `vset_ok`, `forRange_zero`,
`forRange_succ` (peel the last iteration), `forRange_inv` (partial correctness invariant),
`forRange_ok` (total correctness invariant).

## 7. Corpus and test vectors

```lean
structure DSL.TestVector (σ : List Ty) (τ : Ty) where args : Args σ; expected : M τ.denote
structure DSL.TestCase where σ : List Ty; τ : Ty; fn : FlatFn σ τ; vectors : List (TestVector σ τ)
def DSL.TestCase.mk' (fn : FlatFn σ τ) (vs : List (Args σ × M τ.denote)) : TestCase
def DSL.TestCase.passes : TestCase → Bool            -- all vectors agree with denote
def DSL.Env.values : (σ : List Ty) → Env σ → List ((t : Ty) × t.denote)   -- generic arg traversal
def Corpus.all : List DSL.TestCase                     -- in Corpus.All
```

`Corpus.all`: 31 functions, 79 vectors, 30 of which end in `throw`. Every function has
`checkB = true`. Programs: Arith (`addU8` u8, `macU16` u16, `absDiff` u32, `divMod`, `casts`,
`bits16`, `sub3` u64, `max3`, `answer`), Vectors (`sumChecked`, `prefixSum`, `minMax`,
`reverse8`, `dot`, `swapAt`, `tableSum` nested loops, `bumpCopy` clone), Errors (`safeDiv`,
`validate` user tags 1/2/3, `findIdx` notFound, `classify` user 199), Calls (`square`,
`sumSquares`, `meanSquare` 3-deep + cross-module, `incr` with contract, `incrTwice` calling an
irreducible function, `squares`), Maps (`histogram`, `lookup`, `markSeen` map parameter and
result), Big (`chacha20Block`). User proofs (Proofs.lean): `absDiff_spec`,
`safeDiv_error_iff`, `sumChecked_ok_of_small` (loop invariant), `lookup_one`, `lookup_other`
(map laws), plus `incr.contract`.

`#guard` counts: 81 in `corpus/dsl/Corpus/*.lean` (shallow and `denote` sides, including
error paths), 6 `#guard` + 18 `#guard_msgs` in `FVTest/DSL/Negative.lean`.

Negative tests: bare `+`, `*`, `/`; affine violations (use after move, update after alias,
loop moving an outer vector); `while`; ill-typed (`Bool` for `BitVec 64`, mixed widths,
`UInt64`, literal out of range); `return` in a loop; unchecked index; non-numeral loop bound;
assignment to an immutable parameter; calling a non-flat function; and hand-written ASTs
failing `checkB` (loop updating an outer vector, update in `bind` then read, move in one
branch then use, narrowing `zext`, vector map keys, an unchecked callee).

## 8. Known gaps

* No signed checked arithmetic or signed division (the task listed them as optional).
* Loop bounds are numerals; the index is `u64`; no `break`/`continue`; `return` only outside
  loops.
* Frontend name-based affine errors cover straight-line code and loops; a move inside one
  branch of a join-point `if` followed by a later use is reported by the checker in de Bruijn
  terms (`variable #i`).
* `@[irreducible]` is applied only to functions with a contract, immediately (not "outside the
  module").
* Map keys/values are restricted to `int`/`bool`; map equality is structural (insertion order
  matters) but is not observable from DSL programs.
* `denote_eq` is kernel-checked twice (synchronous pre-check, then `addDecl`).
