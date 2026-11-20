import FV.Opt.MidVal

/-!
# `Opt.MidVal.checkCert`: the re-check of the mid-end validator's certificate (#1119)

`Opt.MidVal.check` (`FV/Opt/MidVal.lean`) is the executable, untrusted checker: hash-consed
terms, hash maps, memory versions. On acceptance it emits a certificate (`emit`), and the
soundness theorem is about `checkCert f g cert`, a Bool over plain lists and arrays, structurally
recursive, that re-checks it. The certificate:

* `tms`: the term table (`Tm`); a `node`'s operands are earlier term ids;
* `site`: per term, a program point of `f` (layout index of a block, position `t`: `0` = the
  block's parameters, `k + 1` = after statement `k`) such that every atom of the term is defined
  at or before it in the dominance order (`le`): an atom's site is its definition, a node's site
  is at least each operand's;
* `envF`/`envG`: the term of every value of `f`/`g` (indexed by value id);
* `facts`: per block, the facts holding at its entry (`Fact`): a memory location with its value,
  an idempotent trapping instruction that has evaluated (`eqn`), a term that has evaluated
  (`defd`, for `symbol_value`/`func_addr`/`tls_value`). Memory versions do not appear: a writer
  removes every memory fact (one alias region), and each edge's target facts must be among the
  facts at the end of the source block (`blockOk`), so no dataflow fixpoint is re-checked.

`checkCert` checks, per block, the walk of `f`'s statements against `g`'s (`walk`): pure nodes
of either side are terms of their operands' terms (typed: `floatTyped`; at a site no later than
their definition, for `g` no later than `f`'s next skeleton statement); skeleton statements
match in order with equal term operands, their results being the atoms `res b k j`; a skeleton
statement of `f` without counterpart is a load whose location is a fact (its value is the
fact's), a `notrap` load (its result the atom `poison b k`), a store of a known value, or an
idempotent trapping instruction equal to an evaluated one (`removeOk`); the terminators are
equal on terms. Term equality is id equality, so the table need not be hash-consed.
-/

namespace Opt.MidVal

open Clif

/-- A fact holding at a program point of `f` (module doc). Terms are ids into `Cert.tms`. -/
inductive Fact where
  /-- the value `val` is at address `addr + off`, accessed as `ty` with `kind` and byte order -/
  | mem (addr : Nat) (off : Int) (ty : Ty) (kind : Kind) (endian : Option Endianness) (val : Nat)
  /-- the trapping instruction `i` (term operands) evaluated, with result `res` -/
  | eqn (i : Inst) (res : Option Nat)
  /-- the term `t` evaluated -/
  | defd (t : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The terms a fact mentions. -/
def Fact.terms : Fact → List Nat
  | .mem addr _ _ _ _ val => [addr, val]
  | .eqn i res => operands i ++ res.toList
  | .defd t => [t]

def Fact.isMem : Fact → Bool
  | .mem .. => true
  | _ => false

/-- The certificate (module doc). -/
structure Cert where
  tms : Array Tm
  site : Array (Nat × Nat)
  envF : Array Nat
  envG : Array Nat
  facts : Array (List Fact)
  deriving Repr, Inhabited

/-- What `checkCert` reads besides the certificate: `f`'s dominator tree and block index,
the value types of both functions (`wfCheck`), the normaliser (by default `Norm.stdT f`). -/
structure CC where
  idom : Array (Option Nat)
  index : BlockId → Option Nat
  fty : ValueId → Option Ty
  gty : ValueId → Option Ty
  cert : Cert
  norm : Norm

namespace CC

variable (c : CC)

def anc (a b : Nat) : Bool := ancB c.idom c.idom.size a b

/-- Dominance order on program points (module doc). -/
def le : Nat × Nat → Nat × Nat → Bool
  | (d, t), (b, k) => if d == b then t ≤ k else c.anc d b

def tm (t : Nat) : Option Tm := c.cert.tms[t]?
def siteOf (t : Nat) : Nat × Nat := c.cert.site.getD t (0, 0)
def ef (v : ValueId) : Nat := c.cert.envF.getD v 0
def eg (v : ValueId) : Nat := c.cert.envG.getD v 0
def factsAt (b : Nat) : List Fact := c.cert.facts.getD b []

/-- Term `t` is a well-formed entry of the table. -/
def tmOk (t : Nat) : Tm → Bool
  | .node i => (operands i).all fun o => o < t && c.le (c.siteOf o) (c.siteOf t)
  | .param b _ => c.siteOf t == (b, 0)
  | .res b k _ => c.siteOf t == (b, k + 1)
  | .poison b k => c.siteOf t == (b, k + 1)

def tmsOk : Bool :=
  c.cert.site.size == c.cert.tms.size && (c.cert.tms.toList.zipIdx.all fun (x, t) => c.tmOk t x)

/-- A node without operands: its value does not depend on the frame's registers. -/
def closed (t : Nat) : Bool :=
  match c.tm t with
  | some (.node i) => (operands i).isEmpty
  | _ => false

/-- The facts at the entry of block `b` mention only terms of strict dominators of `b` (so
entering `b`, which rebinds `b`'s parameters, keeps their values), or, at the entry block,
nodes without operands sited at its start (the hoisting mode's facts, `hoistFact`). -/
def entryOk (b : Nat) : Bool :=
  (c.factsAt b).all fun F => F.terms.all fun t =>
    ((c.siteOf t).1 != b && c.anc (c.siteOf t).1 b) ||
      (b == 0 && c.siteOf t == (0, 0) && c.closed t)

/-- A fact the hoisting mode allows at the entry of the function: a `symbol_value`, `tls_value`
or `func_addr` that `f` contains has evaluated (it holds under `globalsResolve f`). -/
def hoistFact (f : Function) : Fact → Bool
  | .defd t => c.siteOf t == (0, 0) && match c.tm t with
    | some (.node i) => partialK i && hasInst f i
    | _ => false
  | _ => false

/-- A pure statement of one side (`env`, `ty`) is the node of its operands' terms (or what the
normaliser makes of it), typed, at a site no later than `bound`. Its result's term. -/
def pureOk (env : ValueId → Nat) (ty : ValueId → Option Ty) (st : Stmt) (bound : Nat × Nat) :
    Option Nat :=
  match st.results with
  | [r] =>
    let t := env r
    let i := mapOperands env st.inst
    if floatTyped ty st.inst &&
        (c.tm t == some (.node i) || (c.norm c.cert.tms i).isSome && c.norm c.cert.tms i == c.tm t) &&
        c.le (c.siteOf t) bound then some t else none
  | _ => none

/-- The results of the skeleton statement `k` of block `bi` are the atoms `res bi k j`. -/
def resOk (env : ValueId → Nat) (rs : List ValueId) (bi k : Nat) : Bool :=
  rs.zipIdx.all fun (r, j) => c.tm (env r) == some (.res bi k j)

/-- `g`'s pure statements before its next skeleton statement, checked against the bound
`(bi, k)` (`f`'s next skeleton statement) and the facts `S` (partial terms must have evaluated
in `f`): the rest, from that skeleton statement on, and its index. -/
def gPre (bound : Nat × Nat) (S : List Fact) : List Stmt → Nat → Option (List Stmt × Nat)
  | [], k' => some ([], k')
  | t :: ts, k' =>
    if t.inst == .nop then gPre bound S ts (k' + 1)
    else if pureK t.inst then
      match c.pureOk c.eg c.gty t bound with
      | some tt => if !partialK t.inst || S.contains (.defd tt) then gPre bound S ts (k' + 1) else none
      | none => none
    else some (t :: ts, k')

end CC

/-- The first skeleton statement of a body. -/
def nextSkel : List Stmt → Option Stmt
  | [] => none
  | t :: ts => if t.inst == .nop || pureK t.inst then nextSkel ts else some t

/-- Remove the memory facts (a writer). -/
def kill (S : List Fact) : List Fact := S.filter fun F => !F.isMem

/-- The memory fact of an access (term operands; `r` the term of a load's result). -/
def memFact? (r : Option Nat) : Inst → Option Fact
  | .load op ty fl p off => r.map fun v => .mem p off ty (loadKind op) fl.endianness v
  | .store op ty fl x p off => some (.mem p off ty (storeKind op) fl.endianness x)
  | _ => none

/-- The facts after a matched skeleton statement `i` (term operands; `r` the term of its first
result): a writer removes the memory facts, an access adds its location, an idempotent trapping
instruction adds its evaluation. -/
def afterKeep (i : Inst) (r : Option Nat) (S : List Fact) : List Fact :=
  let S := if writerK i then kill S else S
  let S := match memFact? r i with
    | some F => F :: S
    | none => S
  if mergeK i then .eqn i r :: S else S

namespace CC

variable (c : CC)

/-- `f`'s skeleton statement `s` (statement `k` of block `bi`, term operands `i`) may be removed
under the facts `S` (module doc). -/
def removeOk (bi k : Nat) (s : Stmt) (S : List Fact) : Inst → Bool
  | .load op ty fl p off =>
    match s.results with
    | [r] => S.contains (.mem p off ty (loadKind op) fl.endianness (c.ef r)) ||
        (fl.trapCode.isNone && c.tm (c.ef r) == some (.poison bi k))
    | _ => false
  | .store op ty fl x p off => S.contains (.mem p off ty (storeKind op) fl.endianness x)
  | i => mergeK i && match s.results with
    | [r] => S.contains (.eqn i (some (c.ef r)))
    | [] => S.contains (.eqn i none)
    | _ => false

/-- The walk of block `bi`: `f`'s remaining statements (from index `k`) against `g`'s (from
`k'`), under the facts `S`; the facts at the end of `f`'s body. -/
def walk (bi : Nat) : List Stmt → List Stmt → Nat → Nat → List Fact → Option (List Fact)
  | [], gs, k, k', S =>
    match c.gPre (bi, k) S gs k' with
    | some ([], _) => some S
    | _ => none
  | s :: fs, gs, k, k', S =>
    if s.inst == .nop then walk bi fs gs (k + 1) k' S
    else if pureK s.inst then
      match c.pureOk c.ef c.fty s (bi, k + 1) with
      | some t => walk bi fs gs (k + 1) k' (if partialK s.inst then .defd t :: S else S)
      | none => none
    else
      let i := mapOperands c.ef s.inst
      let matched := match nextSkel gs with
        | some t => i == mapOperands c.eg t.inst && s.results.length == t.results.length
        | none => false
      if matched then
        match c.gPre (bi, k) S gs k' with
        | some (t :: ts, k'') =>
          if c.resOk c.ef s.results bi k && c.resOk c.eg t.results bi k then
            walk bi fs ts (k + 1) (k'' + 1) (afterKeep i (s.results.head?.map c.ef) S)
          else none
        | _ => none
      else if c.removeOk bi k s S i then walk bi fs gs (k + 1) k' S
      else none

/-- Block `bi` of `f` (`fb`) against `g`'s (`gb`). -/
def blockOk (bi : Nat) (fb gb : Block) : Bool :=
  fb.params.map (·.2) == gb.params.map (·.2) &&
  (fb.params.zipIdx.all fun (p, i) => c.tm (c.ef p.1) == some (.param bi i)) &&
  (gb.params.zipIdx.all fun (p, i) => c.tm (c.eg p.1) == some (.param bi i)) &&
  match c.walk bi fb.body gb.body 0 0 (c.factsAt bi) with
  | some S =>
    mapTerm c.ef fb.term == mapTerm c.eg gb.term &&
    let S := if fb.term.isTry then kill S else S
    (termSuccs fb.term).all fun s => match c.index s with
      | some si => (c.factsAt si).all (S.contains ·)
      | none => false
  | none => false

def blocksOk : Nat → List Block → List Block → Bool
  | bi, fb :: fbs, gb :: gbs => c.entryOk bi && c.blockOk bi fb gb && blocksOk (bi + 1) fbs gbs
  | _, [], [] => true
  | _, _, _ => false

/-- Static sites: the term of every value of `f` is no later than its definition site; the term
of every value of `g` defined in block `d` has its site in `d` or a dominator of `d`. -/
def sitesOk (f g : Function) : Bool :=
  ((defSites f).all fun (v, s) => c.le (c.siteOf (c.ef v)) s) &&
  ((defSites g).all fun (v, d, _) => c.anc (c.siteOf (c.eg v)).1 d)

end CC

/-- The re-check of the certificate, with or without the hoisting mode (`hoist`: the entry
block's facts may be `hoistFact`s; otherwise it has none). -/
def checkCertWith (hoist : Bool) (f g : Function) (cert : Cert) (norm : Norm) : Bool :=
  sameHeader f g && g.sigDecls == f.sigDecls &&
  match wfCheck f, wfCheck g with
  | .ok fi, .ok gi =>
    g.blocks.map (·.id) == f.blocks.map (·.id) &&
    g.blocks.head?.map (·.params) == f.blocks.head?.map (·.params) && gi.cfg.idom == fi.cfg.idom &&
    let c : CC := { idom := fi.cfg.idom, index := fi.cfg.index.get?, fty := fi.types.get?,
                    gty := gi.types.get?, cert, norm }
    c.tmsOk && (c.factsAt 0).all (fun F => hoist && c.hoistFact f F) && c.sitesOk f g &&
      c.blocksOk 0 f.blocks g.blocks
  | _, _ => false

/-- **The re-check of the certificate** (module doc): what the soundness theorem is about. -/
def checkCert (f g : Function) (cert : Cert) (norm : Norm := Norm.stdT f) : Bool :=
  checkCertWith false f g cert norm

/-- **The re-check in the hoisting mode**: `g` may evaluate a `symbol_value`, `tls_value` or
`func_addr` that `f` contains earlier than `f` does. Its soundness theorem assumes the function's
global values resolve (`globalsResolve`). -/
def checkCertSyms (f g : Function) (cert : Cert) (norm : Norm := Norm.stdT f) : Bool :=
  checkCertWith true f g cert norm

/-! ## Emission (untrusted) -/

/-- The certificate of an accepted pair, from the final state of `check` (`checkRun`; `hoist`:
the hoisting mode, whose partial terms evaluated by `g` first are facts of every block). -/
def emit (f g : Function) (norm : Norm := Norm.stdT f) (hoist : Bool := false) : Except Reject Cert := do
  let (st, c, fi) ← checkRun f g norm hoist
  let idom := fi.cfg.idom
  let anc := fun a b => ancB idom idom.size a b
  let le : Nat × Nat → Nat × Nat → Bool := fun (d, t) (b, k) => if d == b then t ≤ k else anc d b
  let site := st.tms.foldl (init := (#[] : Array (Nat × Nat))) fun acc tm =>
    acc.push <| match tm with
      | .param b _ => (b, 0)
      | .res b k _ => (b, k + 1)
      | .poison b k => (b, k + 1)
      | .node i => (operands i).foldl (init := (0, 0)) fun s o =>
          let so := acc.getD o (0, 0)
          if le s so then so else s
  let arr (m : Std.HashMap ValueId Nat) : Array Nat :=
    let n := m.fold (fun a k _ => max a (k + 1)) 0
    m.fold (fun a k v => a.set! k v) (Array.replicate n 0)
  let nb := f.blocks.length
  -- facts recorded in a strict dominator `d` of `b`, at `b`'s entry version (memory), used
  let sdom := fun d b => d != b && c.dom d b
  let hoisted : List Fact := st.usedHoist.toList.map .defd
  let mut facts : Array (List Fact) := Array.replicate nb hoisted
  for b in [1:nb] do
    let vb := c.ver[b]!
    let mut S : List Fact := hoisted
    for (key, xs) in st.facts.toList do
      if key.ver == vb then
        for (v, d) in xs do
          if sdom d b && st.usedMem.contains (key, v) then
            S := .mem key.addr key.off key.ty key.kind key.endian v :: S
    for (nt, xs) in st.merges.toList do
      if st.usedMerge.contains nt then
        for (r, d) in xs do
          if sdom d b then
            S := .eqn (st.tms[nt]!.inst) r :: S
    for (t, xs) in st.partials.toList do
      if st.usedPart.contains t && xs.any (fun (d, _) => sdom d b) then
        S := .defd t :: S
    facts := facts.set! b S.eraseDups
  pure { tms := st.tms, site, envF := arr st.envF, envG := arr st.envG, facts }

end Opt.MidVal
