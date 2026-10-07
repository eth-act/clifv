import FV.E2E.LinkScopeDefs

/-! # The program part's layout (L2b, docs/research/lean-linker.md)

The Lean linker places the program's compiled functions (the program part) in one region of the
executable starting at `R`: consecutive, in the order given, each function's words followed by
one gap word (so that the return address of a call in the last word of a function is not the
next function's entry, `raCallB`). The outside part (cg_clif's fallback code and data, std,
musl, compiler-rt) is linked by rust-lld around the region; its addresses enter as `outside`.

* `offs`, `span`: the byte offsets of the functions in the region and the region's size.
* `LinkSpec`: the program's functions in placement order, `cargo fv`'s self-call aliases, the
  outside part's symbol addresses, the names of the CLIF image's symbols, the region's base.
* `LinkSpec.input`: the crate-level input (`E2E.LinkCheck.LinkInput`) of the placed program:
  its link map is the placement, by construction (no link map is read back).
* `placeOkB`: the conditions on the placement (distinct names, the region in the address space,
  no outside symbol in the region), which the linker checks before writing anything.
-/

namespace Link

open E2E E2E.LinkCheck Backend

/-- The compiler's pipeline (`pipeT`) on a function input, loaded at `0`. The load address is
only recorded (`Art.base`), so the code does not depend on it (`pipeT_base`). -/
def compile0 (fi : FnInput) : Except String Art := pipeT fi.func fi.k 0 (raJ fi.ra fi.j)

/-- The number of words of a function's compiled code (`0` when the pipeline rejects it). -/
def wordsOf (fi : FnInput) : Nat := (getOk (compile0 fi)).fb.words.size

/-- The byte offsets of consecutive functions of `ns` words each from `o`, each followed by one
gap word. -/
def offs : List Nat → Nat → List Nat
  | [], _ => []
  | n :: ns, o => o :: offs ns (o + 4 * n + 4)

/-- The bytes the functions of `ns` words take, gap words included. -/
def span (ns : List Nat) : Nat := (ns.map fun n => 4 * n + 4).sum

/-- **What the Lean linker links**: the program's functions in placement order (`funcs`), the
self-call aliases (`aliases`: `(f__fvself, f)`, `aliasFns`: their functions, as `link-check`
builds them), the outside part's symbol addresses (`outside`), the names the CLIF image needs a
symbol for (`symNames`), and the region's base address `R`. -/
structure LinkSpec where
  funcs : List FnInput
  aliases : List (String × String) := []
  aliasFns : List FnInput := []
  outside : List (String × Nat)
  symNames : List String
  R : Nat
  deriving Inhabited

namespace LinkSpec

variable (S : LinkSpec)

/-- The functions' sizes in words. -/
def sizes : List Nat := S.funcs.map wordsOf

/-- The functions' names. -/
def names : List String := S.funcs.map (·.func.name)

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

/-- A self-call alias's fresh address: the gap word after its function (no symbol is there).
(The table is computed once: every evaluation of `S.sizes` compiles the program.) -/
def aliasAddrs : List (String × Nat) := let t := S.gapTab; S.aliases.map fun p => (p.1, gapIn S.R t p.2)

/-- **The link map**: the placement, the aliases, then the outside part's symbols. -/
def addrs : List (String × Nat) := S.progAddrs ++ S.aliasAddrs ++ S.outside

/-- The input before the call-level stack is known. -/
def input0 : LinkInput where
  funcs := S.funcs ++ S.aliasFns
  addrs := S.addrs
  syms := let a := S.addrs; S.symNames.filterMap fun n => (a.lookup n).map (n, ·)
  raStar := S.R + S.size
  D := 0
  aliases := S.aliases

/-- **The crate-level input of the placed program**: its link map is the placement, the CLIF
image's symbols are read from it, the return address `raStar` is the end of the region, the
stack of one call level is the largest frame (`depthOf`). -/
def input : LinkInput := S.input0.withDepth S.input0.resultsT

/-- **The placement's conditions**: distinct function and alias names (an alias is no placed
function), one alias per function, every alias of a placed function; the region is nonzero,
word-aligned and in the address space; no outside symbol has an address in the region. -/
def placeOkB : Bool :=
  decide (S.names ++ S.aliases.map (·.1)).Nodup && decide (S.aliases.map (·.2)).Nodup &&
  S.aliases.all (fun p => S.names.contains p.2) &&
  decide (S.aliasFns.map (·.func.name) = S.aliases.map (·.1)) &&
  decide (0 < S.R) && S.R % 4 == 0 && decide (S.R + S.size < 2 ^ 64) &&
  -- the size once (every evaluation of `S.size` compiles the program)
  (let n := S.size
   S.outside.all fun e => decide (e.2 % 2 ^ 64 < S.R) || decide (S.R + n ≤ e.2 % 2 ^ 64))

end LinkSpec

end Link
