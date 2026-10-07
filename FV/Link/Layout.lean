import FV.E2E.LinkScopeDefs

/-! # The program part's layout (L2b, docs/research/lean-linker.md)

The Lean linker places the program's compiled functions (the program part) in one region of the
executable starting at `R`: consecutive, in the order given, each function's words followed by
one gap word (so that the return address of a call in the last word of a function is not the
next function's entry, `raCallB`). The outside part (cg_clif's fallback code and data, std,
musl, compiler-rt) is linked by rust-lld around the region; its addresses enter as `outside`.

* `offs`, `span`: the byte offsets of the functions in the region and the region's size.
* `LinkSpec`: the program's functions in placement order with their sizes in words (the
  driver's, checked against the compiled code: `sizesOkB`), `cargo fv`'s self-call aliases, the
  outside part's symbol addresses and data objects, the names of the CLIF image's symbols, the
  region's base.
* `LinkSpec.input`: the crate-level input (`E2E.LinkCheck.LinkInput`) of the placed program:
  its link map is the placement, by construction (no link map is read back).
* `placeOkB`: the conditions on the placement (distinct names, one positive size per function,
  the region in the address space, no outside symbol in the region), which the linker checks
  before writing anything.
-/

namespace Link

open E2E E2E.LinkCheck Backend

/-- The byte offsets of consecutive functions of `ns` words each from `o`, each followed by one
gap word. -/
def offs : List Nat → Nat → List Nat
  | [], _ => []
  | n :: ns, o => o :: offs ns (o + 4 * n + 4)

/-- The bytes the functions of `ns` words take, gap words included. -/
def span (ns : List Nat) : Nat := (ns.map fun n => 4 * n + 4).sum

/-- **What the Lean linker links**: the program's functions in placement order (`funcs`), their
names and sizes in words (`names`, `sizes`: the driver's, checked against the compiled code,
`namesOkB`/`sizesOkB`), the self-call aliases (`aliases`: `(f__fvself, f)`, `aliasFns`: their
functions, as `link-check` builds them; an alias's address is the gap word after its function,
which no symbol has), the outside part's symbol addresses (`outside`) and the CLIF data objects
the program reaches (`data`, laid out by rust-lld), the names the CLIF image needs a symbol for
(`symNames`), and the region's base address `R`. -/
structure LinkSpec where
  funcs : List FnInput
  names : List String
  sizes : List Nat
  aliases : List (String × String) := []
  aliasFns : List FnInput := []
  outside : List (String × Nat)
  data : List Clif.DataObject := []
  symNames : List String
  R : Nat
  deriving Inhabited

/-- `l` has no duplicates (decided with a hash set: linear; `decide l.Nodup` is quadratic). -/
def nodupGo : List String → Std.HashSet String → Bool
  | [], _ => true
  | x :: xs, s => !s.contains x && nodupGo xs (s.insert x)

/-- `l` has no duplicates. -/
def nodupB (l : List String) : Bool := nodupGo l {}

/-- No address of `l` (modulo `2 ^ 64`) is in `[R, R + n)`. -/
def clearOfB (R n : Nat) (l : List (String × Nat)) : Bool :=
  l.all fun e => decide (e.2 % 2 ^ 64 < R) || decide (R + n ≤ e.2 % 2 ^ 64)

namespace LinkSpec

variable (S : LinkSpec)

/-- The region's size in bytes. -/
def size : Nat := span S.sizes

/-- **The placement**: every function at its offset from `R`. -/
def progAddrs : List (String × Nat) := S.names.zip ((offs S.sizes 0).map (S.R + ·))

/-- The functions' offsets and sizes by name. -/
def gapTab : List (String × Nat × Nat) := S.names.zip ((offs S.sizes 0).zip S.sizes)

/-- The address of the gap word after the function `f` in the region at `R` with the offsets
and sizes `t` (`R` when `f` is not there). -/
def gapIn (R : Nat) (t : List (String × Nat × Nat)) (f : String) : Nat :=
  match t.lookup f with
  | some (o, n) => R + o + 4 * n
  | none => R

/-- The address of the gap word after the function `f` (`R` when `f` is not placed). -/
def gapOf (f : String) : Nat := gapIn S.R S.gapTab f

/-- A self-call alias's fresh address: the gap word after its function (no symbol is there). -/
def aliasAddrs : List (String × Nat) := let t := S.gapTab; S.aliases.map fun p => (p.1, gapIn S.R t p.2)

/-- **The link map**: the placement, the aliases, then the outside part's symbols. -/
def addrs : List (String × Nat) := S.progAddrs ++ S.aliasAddrs ++ S.outside

/-- The input before the call-level stack is known: the compiler's pipeline (`fallback`), so
its results are the compiler's (`input_results`). -/
def input0 : LinkInput where
  funcs := S.funcs ++ S.aliasFns
  addrs := S.addrs
  syms := let a := S.addrs; S.symNames.filterMap fun n => (a.lookup n).map (n, ·)
  raStar := S.R + S.size
  D := 0
  aliases := S.aliases
  fallback := true

/-- **The crate-level input of the placed program**: its link map is the placement, the CLIF
image's symbols are read from it, the return address `raStar` is the end of the region, the
stack of one call level is the largest frame (`depthOf`). -/
def input : LinkInput := S.input0.withDepth S.input0.resultsT

/-- **The placed program's results are the compiler's** (`fallback`): every theorem about
`S.input.results` (`okB`, `BinOk`, the binary theorems) is about the code the compiler emits and
`leanLink` writes. -/
theorem input_results : S.input.results = S.input.resultsT :=
  LinkInput.results_fallback rfl

/-- **The placement's conditions**: distinct function and alias names (an alias is no placed
function), one alias per function, every alias of a placed function; one size per function,
each positive (so the gap word after a function, an alias's address, is no function's entry);
the region is nonzero, word-aligned and in the address space; no outside symbol has an address
in the region. -/
def placeOkB : Bool :=
  nodupB (S.names ++ S.aliases.map (·.1)) && nodupB (S.aliases.map (·.2)) &&
  S.aliases.all (fun p => S.names.contains p.2) &&
  decide (S.aliasFns.map (·.func.name) = S.aliases.map (·.1)) &&
  decide (S.names.length = S.funcs.length) &&
  decide (S.sizes.length = S.funcs.length) && S.sizes.all (0 < ·) &&
  decide (0 < S.R) && S.R % 4 == 0 && decide (S.R + S.size < 2 ^ 64) &&
  clearOfB S.R S.size S.outside

/-- **The compiled code has the placement's names and sizes**: the first `S.funcs.length`
entries of the compiled table `T` (the placed functions) are named `S.names` and have
`S.sizes` words. -/
def namesOkB (T : List (Clif.Function × Art)) : Bool :=
  decide ((T.take S.funcs.length).map (·.1.name) = S.names)

/-- See `namesOkB`. -/
def sizesOkB (T : List (Clif.Function × Art)) : Bool :=
  decide ((T.take S.funcs.length).map (·.2.fb.words.size) = S.sizes)

end LinkSpec

end Link
