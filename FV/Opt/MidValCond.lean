import FV.Opt.MidValFold

/-!
# Family 3 of the mid-end validator: branch conditions (#1119, route D)

Cranelift's mid-end often rewrites a `brif`'s condition: `f` branches on `icmp ne x, 0` (or an
extension of a comparison) where `g` branches on `x` itself. Both take the same successor
whenever `f`'s condition evaluates. The validator does not relax its terminator comparison;
instead `checkCertC` re-checks `f` against `condPrep g hints`, a copy of `g` in which each hinted
block ends with fresh statements rebuilding `f`'s condition shape on top of `g`'s condition
value (`z = iconst ty 0; t = icmp ne y, z`, `t = uextend y`, …) and branches on the last one.
The compiled function stays `g`: the copy only exists inside the check.

* `condPrep g hints`: the copy; a hint is a block id and its wrapper chain (innermost first,
  `Wrap`). A block is changed only if its terminator is a `brif` whose condition is below
  `g.freshValue` and every wrapper keeps the truth of the condition (`Wrap.ok`); the inserted
  values are numbered from `g.freshValue` on.
* `refsOk g`: every value `g` reads is below `g.freshValue` (so no inserted value is read by a
  statement of `g`).
* `checkCertC f g cert hints`: `checkCert f g cert` without hints; otherwise `refsOk g` and
  `checkCert f (condPrep g hints) cert`, or, when some hint has an empty wrapper chain (a fold
  request, `foldBlocks`, `FV/Opt/MidValFold.lean`), `checkCert (foldPre f bs) (condPrep g hints)
  cert` with the default normaliser of `foldPre f bs`: the block parameters `ConstPhi.run` kept
  removed (`phiPre`), divisions by constants rewritten, `f`'s constant-condition branches in the
  requested blocks folded and the blocks that became unreachable removed (`rewrite:blocks`), or
  the same with `foldPreK f bs` (no constant-phi removal after the folds, as in Cranelift).
  `checkCertSymsC`: the hoisting mode without folding (`FV/Opt/MidValSyms.lean`: with folding,
  at a symbol table).
* `checkC`/`emitC` (untrusted): the check without hints, else with the hints the relaxed check
  (`checkRun … (cond := true)`) records, else the same on `foldPre f bs`, then on `foldPreK f
  bs`, for the blocks `bs` whose branch is a `jump` in `g` or that divide (`foldCands`; the entry
  block alone when there is none), with `bs` as fold requests appended to the hints; in the
  hoisting mode (`hoist := true`) every step in that mode.
-/

namespace Opt.MidVal

open Clif

/-- The statements of one wrapper around `y`, its fresh values from `n` on: the result's value
and the next fresh value. -/
def Wrap.stmts (y n : ValueId) : Wrap → List Stmt × ValueId × ValueId
  | .icmp cc ty zl =>
    ([{ results := [n], inst := .iconst ty 0 },
      { results := [n + 1], inst := if zl then .icmp cc ty n y else .icmp cc ty y n }], n + 1, n + 2)
  | .ext op ty => ([{ results := [n], inst := .extend op ty y }], n, n + 1)

/-- The statements of a wrapper chain (innermost first) around `y`, fresh values from `n` on:
the statements, the value of the outermost wrapper, the next fresh value. -/
def prepChain (y n : ValueId) : List Wrap → List Stmt × ValueId × ValueId
  | [] => ([], y, n)
  | w :: ws =>
    let (s, t, n') := w.stmts y n
    let (ss, r, n'') := prepChain t n' ws
    (s ++ ss, r, n'')

/-- One block of `condPrep` (fresh values from `n` on, `base` = `g.freshValue`): the block and
the next fresh value. -/
def prepBlock (hints : List (BlockId × List Wrap)) (base : ValueId) (n : ValueId) (b : Block) :
    Block × ValueId :=
  match b.term, hints.lookup b.id with
  | .brif c th el, some ws =>
    if c < base && !ws.isEmpty && ws.all Wrap.ok then
      let (ss, r, n') := prepChain c n ws
      ({ b with body := b.body ++ ss, term := .brif r th el }, n')
    else (b, n)
  | _, _ => (b, n)

def prepBlocks (hints : List (BlockId × List Wrap)) (base : ValueId) :
    List Block → ValueId → List Block
  | [], _ => []
  | b :: bs, n =>
    let (b', n') := prepBlock hints base n b
    b' :: prepBlocks hints base bs n'

/-- **`g` with `f`'s branch-condition shapes rebuilt** (module doc). -/
def condPrep (g : Function) (hints : List (BlockId × List Wrap)) : Function :=
  { g with blocks := prepBlocks hints g.freshValue g.blocks g.freshValue }

/-- **The re-check with branch-condition hints and fold requests** (module doc). -/
def checkCertC (f g : Function) (cert : Cert) (hints : List (BlockId × List Wrap))
    (norm : Norm := Norm.stdD f) : Bool :=
  if hints.isEmpty then checkCert f g cert norm
  else if (foldBlocks hints).isEmpty then refsOk g && checkCert f (condPrep g hints) cert norm
  else refsOk g && (checkCert (foldPre f (foldBlocks hints)) (condPrep g hints) cert ||
    checkCert (foldPreK f (foldBlocks hints)) (condPrep g hints) cert)

/-- The hoisting mode of `checkCertC`. -/
def checkCertSymsC (f g : Function) (cert : Cert) (hints : List (BlockId × List Wrap))
    (norm : Norm := Norm.stdD f) : Bool :=
  if hints.isEmpty then checkCertSyms f g cert norm
  else refsOk g && checkCertSyms f (condPrep g hints) cert norm

/-! ## The executable check (untrusted) -/

/-- The hints of the relaxed check without folding: `.ok []` if `check` accepts; otherwise the
wrapper chains the relaxed check records, if `check` accepts `f` against `condPrep g` of them
(else `check`'s own rejection). -/
def checkC0 (f g : Function) (norm : Norm := Norm.stdD f) (hoist : Bool := false) :
    Except Reject (List (BlockId × List Wrap)) :=
  match check f g norm hoist with
  | .ok () => .ok []
  | .error e =>
    match checkRun f g norm hoist (cond := true) with
    | .ok (st, _) =>
      let h := st.conds.toList
      if h.isEmpty || !refsOk g then .error e
      else match check f (condPrep g h) norm hoist with
        | .ok () => .ok h
        | .error _ => .error e
    | .error _ => .error e

/-- The hints of the relaxed check (`checkC0`); when it rejects, the same on `foldPre f bs`, then
on `foldPreK f bs`, for the blocks `bs` whose branch is a `jump` in `g` or that divide
(`foldCands`), or, when there is none, the entry block alone (a request for `foldPre`'s
constant-phi removal `phiPre`), with the fold requests `(b, [])` of `bs` appended; each step in
the hoisting mode when `hoist`. A copy is skipped when it has `f`'s blocks or its blocks are not
`g`'s. A pair rejected for `rewrite:blocks`, a division or a block parameter that the prep does
not rescue reports the rejection of the `foldPreK` copy, marked `[prep]`. -/
def checkC (f g : Function) (norm : Norm := Norm.stdD f) (hoist : Bool := false) :
    Except Reject (List (BlockId × List Wrap)) :=
  match checkC0 f g norm hoist with
  | .ok h => .ok h
  | .error e =>
    let bs := match foldCands f g with
      | [] => (f.blocks.head?.map (·.id)).toList
      | bs => bs
    let fail (e' : Reject) : Except Reject (List (BlockId × List Wrap)) :=
      .error (if e == "rewrite:blocks" || e.startsWith "rewrite:skeleton-removed div" ||
          e.startsWith "shape:params" || (e.splitOn " arity").length > 1 then
        s!"{e'} [prep]" else e)
    let prep (f' : Function) : Except Reject (List (BlockId × List Wrap)) :=
      if f'.blocks == f.blocks then fail e
      else if f'.blocks.map (·.id) != g.blocks.map (·.id) then fail "rewrite:blocks"
      else match checkC0 f' g (hoist := hoist) with
        | .ok h => .ok (h ++ bs.map fun b => (b, []))
        | .error e' => fail e'
    if bs.isEmpty then .error e
    else match prep (foldPre f bs) with
      | .ok h => .ok h
      | .error _ => prep (foldPreK f bs)

/-- The certificate and hints of an accepted pair (`checkC`, then `emit` against the copy, from
`foldPre f bs`, or else `foldPreK f bs`, for fold requests `bs`; in the hoisting mode when
`hoist`). -/
def emitC (f g : Function) (norm : Norm := Norm.stdD f) (hoist : Bool := false) :
    Except Reject (Cert × List (BlockId × List Wrap)) := do
  let h ← checkC f g norm hoist
  let bs := foldBlocks h
  let cert ← if bs.isEmpty then emit f (if h.isEmpty then g else condPrep g h) norm hoist
    else match emit (foldPre f bs) (condPrep g h) (hoist := hoist) with
      | .ok c => pure c
      | .error _ => emit (foldPreK f bs) (condPrep g h) (hoist := hoist)
  pure (cert, h)

end Opt.MidVal
