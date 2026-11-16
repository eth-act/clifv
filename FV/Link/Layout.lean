import FV.E2E.LinkScopeDefs

/-! # The program part's layout (L2b, docs/research/lean-linker.md)

The Lean linker places the program's compiled functions (the program part) in one region of the
executable starting at `R`: consecutive, in the order given, each function started at its
alignment and its words followed by one gap word (so that the return address of a call in the
last word of a function is not the next function's entry, `raCallB`). The bytes between a gap
word and the next aligned start are zeros (`udf #0`, the filler rust-lld writes). The outside
part (cg_clif's fallback code and data, std, musl, compiler-rt) is linked by rust-lld around
the region; its addresses enter as `outside`.

* `offs`, `span`: the byte offsets of consecutive functions without alignment and their size;
  `alignW`, `offsA`, `endA`: the offsets of the functions each started at its alignment (#1061:
  a function with a literal pool is 8-aligned, as Cranelift's `MachBuffer` and rust-lld place
  it) and their end.
* `LinkSpec`: the program's functions in placement order with their sizes in words (the
  driver's, checked against the compiled code: `sizesOkB`) and alignments (the driver's: where
  `ld -r` starts each function), the outside part's symbol addresses and data objects, the
  names of the CLIF image's symbols, the region's base.
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

/-- `o` rounded up by whole words to a multiple of the alignment `a` (in bytes): of `a / 4`
words; an alignment below a word adds nothing. -/
def alignW (o a : Nat) : Nat := o + 4 * ((a / 4 - o / 4 % (a / 4)) % (a / 4))

/-- The byte offsets of consecutive functions of `ns` words each from `o`, each started at its
alignment `as` (in bytes; a missing one is a word) and followed by one gap word. -/
def offsA : List Nat → List Nat → Nat → List Nat
  | [], _, _ => []
  | n :: ns, as, o => alignW o (as.headD 4) :: offsA ns as.tail (alignW o (as.headD 4) + 4 * n + 4)

/-- The end of the functions of `offsA ns as o`, gap words included. -/
def endA : List Nat → List Nat → Nat → Nat
  | [], _, o => o
  | n :: ns, as, o => endA ns as.tail (alignW o (as.headD 4) + 4 * n + 4)

/-- **What the Lean linker links**: the program's functions in placement order (`funcs`), their
names and sizes in words (`names`, `sizes`: the driver's, checked against the compiled code,
`namesOkB`/`sizesOkB`) and alignments in bytes (`aligns`: the driver's, where `ld -r` starts
each function in the region object; a missing one is a word), the outside part's symbol
addresses (`outside`) and the CLIF data objects the program reaches (`data`, laid out by
rust-lld), the names the CLIF image needs a symbol for (`symNames`), and the region's base
address `R`. -/
structure LinkSpec where
  funcs : List FnInput
  names : List String
  sizes : List Nat
  outside : List (String × Nat)
  data : List Clif.DataObject := []
  symNames : List String
  R : Nat
  aligns : List Nat := []
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
def size : Nat := endA S.sizes S.aligns 0

/-- **The placement**: every function at its aligned offset from `R`. -/
def progAddrs : List (String × Nat) := S.names.zip ((offsA S.sizes S.aligns 0).map (S.R + ·))

/-- **The link map**: the placement, then the outside part's symbols. -/
def addrs : List (String × Nat) := S.progAddrs ++ S.outside

/-- The input before the call-level stack is known: the compiler's pipeline (`fallback`), so
its results are the compiler's (`input_results`). -/
def input0 : LinkInput where
  funcs := S.funcs
  addrs := S.addrs
  syms := let a := S.addrs; S.symNames.filterMap fun n => (a.lookup n).map (n, ·)
  raStar := S.R + S.size
  D := 0
  aliases := []
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

/-- **The placement's conditions**: distinct function names, one positive size per function;
the region is nonzero, word-aligned and in the address space; no outside symbol has an address
in the region. -/
def placeOkB : Bool :=
  nodupB S.names &&
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
