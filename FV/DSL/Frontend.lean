import Lean
import FV.DSL.Check

/-!
# The `flat def` command

```
flat def name (x₁ : T₁) … (xₙ : Tₙ) : T
  requires P            -- optional
  ensures r, Q          -- optional
  := do
  <restricted do-block>
  proof by <tactics>    -- required iff requires/ensures is present
```

generates, in the current namespace:

* `name.ast : DSL.FlatFn [T₁, …, Tₙ] T` (deep AST, `name := "<full name>"`),
* `name : T₁ → … → Tₙ → DSL.M T` (shallow, direct style, built from `DSL.Ops`),
* `@[simp] theorem name.denote_eq : ∀ x₁ … xₙ, DSL.denote name.ast (x₁, …, xₙ, ()) = name x₁ … xₙ`,
* `theorem name.checked : name.ast.checked` (by `decide`, after a readable pre-check),
* with a contract: `theorem name.contract : ∀ x₁ … xₙ, P → ∃ r, name x₁ … xₙ = .ok r ∧ Q`,
  and `name` is then made `@[irreducible]`.

The accepted fragment is documented in `docs/contracts/dsl.md` ("Surface language").
Translation is a single pass over the `do` syntax producing both terms side by side; every
effectful sub-expression is lifted (A-normal form) in left-to-right evaluation order.
-/

namespace DSL

abbrev U8 := BitVec 8
abbrev U16 := BitVec 16
abbrev U32 := BitVec 32
abbrev U64 := BitVec 64

infixl:70 " /? " => DSL.Ops.udiv
infixl:70 " %? " => DSL.Ops.urem

def Ty.surface : Ty → String
  | .int w => s!"BitVec {w.bits}"
  | .bool => "Bool"
  | .unit => "Unit"
  | .vec n t => s!"Vector ({t.surface}) {n}"
  | .prod a b => s!"({a.surface} × {b.surface})"
  | .map k v => s!"DSL.Map ({k.surface}) ({v.surface})"

namespace Frontend

open Lean Elab Term Command Meta

/-! ## Meta-level IR (variables are de Bruijn *levels*) -/

/-- Pure expressions. -/
inductive PE where
  | var (lvl : Nat)
  | clone (lvl : Nat)
  | ilit (w : IntW) (v : Nat)
  | blit (b : Bool)
  | unit
  | ibin (op : IBin) (a b : PE)
  | inot (a : PE)
  | icmp (op : ICmp) (a b : PE)
  | cast (op : Cast) (w : IntW) (a : PE)
  | band (a b : PE)
  | bor (a b : PE)
  | bnot (a : PE)
  | cond (c a b : PE)
  | pair (a b : PE)
  | fst (p : PE)
  | snd (p : PE)
  | vrepl (n : Nat) (x : PE)
  | mapEmpty (k v : Ty)
  | mapContains (lvl : Nat) (k : PE)
  deriving Inhabited

/-- Fallible operations, lifted into `Stmt.bind`. -/
inductive FO where
  | iop (op : IOp) (a b : PE)
  | vget (lvl : Nat) (i : PE)
  | mapGet (lvl : Nat) (k : PE)
  | call (fn : Name) (args : List PE)
  deriving Inhabited

structure LVar where
  name : Name
  ty : Ty
  isMut : Bool := false
  /-- Moved out (affine rule), tracked for readable errors; `FlatFn.check` is authoritative. -/
  moved : Bool := false
  deriving Inhabited

structure Scope where
  vars : Array LVar := #[]
  /-- Levels below `loopBase` are bound outside the innermost loop body. -/
  loopBase : Nat := 0
  deriving Inhabited

def Scope.depth (sc : Scope) : Nat := sc.vars.size
def Scope.push (sc : Scope) (v : LVar) : Scope := { sc with vars := sc.vars.push v }
def Scope.setMoved (sc : Scope) (lvl : Nat) (b : Bool) : Scope :=
  { sc with vars := sc.vars.modify lvl fun v => { v with moved := b } }

def Scope.lookup? (sc : Scope) (n : Name) : Option (Nat × LVar) := Id.run do
  let mut i := sc.vars.size
  while i > 0 do
    i := i - 1
    if sc.vars[i]!.name == n then return some (i, sc.vars[i]!)
  return none

def Scope.rename (sc : Scope) (lvl : Nat) (n : Name) (isMut : Bool) : Scope :=
  { sc with vars := sc.vars.modify lvl fun v => { v with name := n, isMut } }

def tmpName (lvl : Nat) : Name := Name.mkSimple s!"_t{lvl}"

/-! ## Types -/

def widthOf? : Nat → Option IntW
  | 8 => some .w8
  | 16 => some .w16
  | 32 => some .w32
  | 64 => some .w64
  | _ => none

def numLit? (stx : Syntax) : Option Nat := stx.isNatLit?

partial def parseTy (t : Term) : TermElabM Ty := do
  match t with
  | `(($t)) => parseTy t
  | `($a × $b) => return .prod (← parseTy a) (← parseTy b)
  | `($f:ident $args*) =>
    let n := f.getId.eraseMacroScopes
    match n.toString, args.toList with
    | "BitVec", [w] =>
      match (numLit? w).bind widthOf? with
      | some iw => return .int iw
      | none => throwErrorAt w "flat def: `BitVec n` needs n ∈ \{8, 16, 32, 64}"
    | "Vector", [e, len] =>
      match numLit? len with
      | some k => return .vec k (← parseTy ⟨e⟩)
      | none => throwErrorAt len "flat def: vector length must be a numeral"
    | "DSL.Map", [k, v] | "Map", [k, v] => return .map (← parseTy ⟨k⟩) (← parseTy ⟨v⟩)
    | _, _ => throwErrorAt t "flat def: unsupported type `{t}`"
  | `($f:ident) =>
    match f.getId.eraseMacroScopes.toString with
    | "Bool" => return .bool
    | "Unit" => return .unit
    | "U8" | "DSL.U8" => return .u8
    | "U16" | "DSL.U16" => return .u16
    | "U32" | "DSL.U32" => return .u32
    | "U64" | "DSL.U64" => return .u64
    | "UInt8" | "UInt16" | "UInt32" | "UInt64" =>
      throwErrorAt t "flat def: machine integers are `BitVec n` (or `DSL.U8 … DSL.U64`), not `{f}`"
    | _ => throwErrorAt t "flat def: unsupported type `{t}`"
  | _ => throwErrorAt t "flat def: unsupported type `{t}`"

def num (n : Nat) : Term := Syntax.mkNumLit (toString n)

def wStx : IntW → TermElabM Term
  | .w8 => `(DSL.IntW.w8)
  | .w16 => `(DSL.IntW.w16)
  | .w32 => `(DSL.IntW.w32)
  | .w64 => `(DSL.IntW.w64)

partial def tyDeep : Ty → TermElabM Term
  | .int w => do `(DSL.Ty.int $(← wStx w))
  | .bool => `(DSL.Ty.bool)
  | .unit => `(DSL.Ty.unit)
  | .vec n t => do `(DSL.Ty.vec $(num n) $(← tyDeep t))
  | .prod a b => do `(DSL.Ty.prod $(← tyDeep a) $(← tyDeep b))
  | .map k v => do `(DSL.Ty.map $(← tyDeep k) $(← tyDeep v))

partial def tyShallow : Ty → TermElabM Term
  | .int w => `(BitVec $(num w.bits))
  | .bool => `(Bool)
  | .unit => `(Unit)
  | .vec n t => do `(Vector $(← tyShallow t) $(num n))
  | .prod a b => do `(($(← tyShallow a) × $(← tyShallow b)))
  | .map k v => do `(DSL.Map $(← tyShallow k) $(← tyShallow v))

/-- Read a `DSL.Ty` value back from a Lean expression (callee signatures). -/
partial def exprToTy (e : Lean.Expr) : MetaM Ty := do
  let e ← whnf e
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``DSL.Ty.int, #[w] =>
    match (← whnf w).constName? with
    | some ``DSL.IntW.w8 => return .u8
    | some ``DSL.IntW.w16 => return .u16
    | some ``DSL.IntW.w32 => return .u32
    | some ``DSL.IntW.w64 => return .u64
    | _ => throwError "flat def: cannot read width {w}"
  | some ``DSL.Ty.bool, _ => return .bool
  | some ``DSL.Ty.unit, _ => return .unit
  | some ``DSL.Ty.vec, #[n, t] =>
    let n ← whnf n
    match n.rawNatLit? <|> n.nat? with
    | some k => return .vec k (← exprToTy t)
    | none => throwError "flat def: cannot read vector length {n}"
  | some ``DSL.Ty.prod, #[a, b] => return .prod (← exprToTy a) (← exprToTy b)
  | some ``DSL.Ty.map, #[k, v] => return .map (← exprToTy k) (← exprToTy v)
  | _, _ => throwError "flat def: cannot read type {e}"

partial def exprToTys (e : Lean.Expr) : MetaM (List Ty) := do
  let e ← whnf e
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``List.nil, _ => return []
  | some ``List.cons, #[_, h, t] => return (← exprToTy h) :: (← exprToTys t)
  | _, _ => throwError "flat def: cannot read type list {e}"

/-! ## Emission of deep and shallow terms -/

partial def varStx : Nat → TermElabM Term
  | 0 => `(DSL.Var.zero)
  | n + 1 => do `(DSL.Var.succ $(← varStx n))

/-- Deep variable for level `lvl` at context depth `d`. -/
def varAt (d lvl : Nat) : TermElabM Term := varStx (d - 1 - lvl)

def ibinStx : IBin → TermElabM Term
  | .add => `(DSL.IBin.add) | .sub => `(DSL.IBin.sub) | .mul => `(DSL.IBin.mul)
  | .and => `(DSL.IBin.and) | .or => `(DSL.IBin.or) | .xor => `(DSL.IBin.xor)
  | .shl => `(DSL.IBin.shl) | .lshr => `(DSL.IBin.lshr) | .ashr => `(DSL.IBin.ashr)

def icmpStx : ICmp → TermElabM Term
  | .eq => `(DSL.ICmp.eq) | .ne => `(DSL.ICmp.ne) | .ult => `(DSL.ICmp.ult)
  | .ule => `(DSL.ICmp.ule) | .slt => `(DSL.ICmp.slt) | .sle => `(DSL.ICmp.sle)

def castStx : Cast → TermElabM Term
  | .zext => `(DSL.Cast.zext) | .sext => `(DSL.Cast.sext) | .trunc => `(DSL.Cast.trunc)

def iopStx : IOp → TermElabM Term
  | .addC => `(DSL.IOp.addC) | .subC => `(DSL.IOp.subC) | .mulC => `(DSL.IOp.mulC)
  | .udiv => `(DSL.IOp.udiv) | .urem => `(DSL.IOp.urem)

partial def PE.deep (d : Nat) : PE → TermElabM Term
  | .var l => do `(DSL.Expr.var $(← varAt d l))
  | .clone l => do `(DSL.Expr.clone $(← varAt d l))
  | .ilit w v => do `(DSL.Expr.ilit $(← wStx w) $(num v))
  | .blit true => `(DSL.Expr.blit true)
  | .blit false => `(DSL.Expr.blit false)
  | .unit => `(DSL.Expr.unit)
  | .ibin op a b => do `(DSL.Expr.ibin $(← ibinStx op) $(← a.deep d) $(← b.deep d))
  | .inot a => do `(DSL.Expr.inot $(← a.deep d))
  | .icmp op a b => do `(DSL.Expr.icmp $(← icmpStx op) $(← a.deep d) $(← b.deep d))
  | .cast op w a => do `(DSL.Expr.cast $(← castStx op) $(← wStx w) $(← a.deep d))
  | .band a b => do `(DSL.Expr.band $(← a.deep d) $(← b.deep d))
  | .bor a b => do `(DSL.Expr.bor $(← a.deep d) $(← b.deep d))
  | .bnot a => do `(DSL.Expr.bnot $(← a.deep d))
  | .cond c a b => do `(DSL.Expr.cond $(← c.deep d) $(← a.deep d) $(← b.deep d))
  | .pair a b => do `(DSL.Expr.pair $(← a.deep d) $(← b.deep d))
  | .fst p => do `(DSL.Expr.fst $(← p.deep d))
  | .snd p => do `(DSL.Expr.snd $(← p.deep d))
  | .vrepl n x => do `(DSL.Expr.vrepl $(num n) $(← x.deep d))
  | .mapEmpty k v => do `(DSL.Expr.mapEmpty (k := $(← tyDeep k)) (v := $(← tyDeep v)))
  | .mapContains l k => do `(DSL.Expr.mapContains $(← varAt d l) $(← k.deep d))

def nameAt (sc : Scope) (l : Nat) : Ident := mkIdent sc.vars[l]!.name

partial def PE.shallow (sc : Scope) : PE → TermElabM Term
  | .var l | .clone l => pure (nameAt sc l)
  | .ilit w v => `(($(num v) : BitVec $(num w.bits)))
  | .blit true => `(true)
  | .blit false => `(false)
  | .unit => `(())
  | .ibin op a b => do
    let a ← a.shallow sc; let b ← b.shallow sc
    match op with
    | .add => `(($a + $b)) | .sub => `(($a - $b)) | .mul => `(($a * $b))
    | .and => `(($a &&& $b)) | .or => `(($a ||| $b)) | .xor => `(($a ^^^ $b))
    | .shl => `(DSL.Ops.shl $a $b) | .lshr => `(DSL.Ops.lshr $a $b)
    | .ashr => `(DSL.Ops.ashr $a $b)
  | .inot a => do `((~~~$(← a.shallow sc)))
  | .icmp op a b => do
    let a ← a.shallow sc; let b ← b.shallow sc
    match op with
    | .eq => `(($a == $b)) | .ne => `(($a != $b))
    | .ult => `(BitVec.ult $a $b) | .ule => `(BitVec.ule $a $b)
    | .slt => `(BitVec.slt $a $b) | .sle => `(BitVec.sle $a $b)
  | .cast op w a => do
    let a ← a.shallow sc
    match op with
    | .zext => `(DSL.Ops.zext $(num w.bits) $a)
    | .sext => `(DSL.Ops.sext $(num w.bits) $a)
    | .trunc => `(DSL.Ops.trunc $(num w.bits) $a)
  | .band a b => do `(($(← a.shallow sc) && $(← b.shallow sc)))
  | .bor a b => do `(($(← a.shallow sc) || $(← b.shallow sc)))
  | .bnot a => do `((!$(← a.shallow sc)))
  | .cond c a b => do
    let c ← c.shallow sc; let a ← a.shallow sc; let b ← b.shallow sc
    `((if $c then $a else $b))
  | .pair a b => do `(($(← a.shallow sc), $(← b.shallow sc)))
  | .fst p => do `(($(← p.shallow sc)).1)
  | .snd p => do `(($(← p.shallow sc)).2)
  | .vrepl n x => do `((Vector.replicate $(num n) $(← x.shallow sc)))
  | .mapEmpty k v => do `((DSL.Map.empty : DSL.Map $(← tyShallow k) $(← tyShallow v)))
  | .mapContains l k => do `((DSL.Map.contains $(nameAt sc l) $(← k.shallow sc)))

def astIdent (fn : Name) : Ident := mkIdent (fn ++ `ast)

partial def exprsDeep (d : Nat) : List PE → TermElabM Term
  | [] => `(DSL.Exprs.nil)
  | e :: es => do `(DSL.Exprs.cons $(← e.deep d) $(← exprsDeep d es))

def FO.deep (d : Nat) : FO → TermElabM Term
  | .iop op a b => do `(DSL.Stmt.op (DSL.Op.iop $(← iopStx op) $(← a.deep d) $(← b.deep d)))
  | .vget l i => do `(DSL.Stmt.op (DSL.Op.vget $(← varAt d l) $(← i.deep d)))
  | .mapGet l k => do `(DSL.Stmt.op (DSL.Op.mapGet $(← varAt d l) $(← k.deep d)))
  | .call f args => do
    let a := astIdent f
    `(DSL.Stmt.call ($a).name ($a).body $(← exprsDeep d args))

def FO.shallow (sc : Scope) : FO → TermElabM Term
  | .iop op a b => do
    let a ← a.shallow sc; let b ← b.shallow sc
    match op with
    | .addC => `(DSL.Ops.addC $a $b) | .subC => `(DSL.Ops.subC $a $b)
    | .mulC => `(DSL.Ops.mulC $a $b) | .udiv => `(DSL.Ops.udiv $a $b)
    | .urem => `(DSL.Ops.urem $a $b)
  | .vget l i => do `(DSL.Ops.vget $(nameAt sc l) $(← i.shallow sc))
  | .mapGet l k => do `(DSL.Ops.mapGet $(nameAt sc l) $(← k.shallow sc))
  | .call f args => do
    let args ← args.toArray.mapM (·.shallow sc)
    if args.isEmpty then pure (mkIdent f) else `($(mkIdent f) $args*)

/-- A pair of generated terms: deep `Stmt` and shallow `M` term. -/
abbrev Out := Term × Term

/-- A lifted fallible operation, bound at level `lvl` (as `Stmt.bind (op) k`). -/
structure Pre where
  op : FO
  lvl : Nat
  deriving Inhabited

/-- Wrap `k` in the binds of `pre` (in order). `sc` is the scope *after* all binds. -/
def emitPre (sc : Scope) (pre : Array Pre) (k : TermElabM Out) : TermElabM Out := do
  let mut out ← k
  for p in pre.reverse do
    let d := p.lvl -- depth before the bind = level of the bound variable
    let x := nameAt sc p.lvl
    let deep ← `(DSL.Stmt.bind $(← p.op.deep d) $(out.1))
    let sh ← `($(← p.op.shallow sc) >>= fun $x => $(out.2))
    out := (deep, sh)
  return out

/-! ## Expressions -/

structure ESt where
  sc : Scope
  pre : Array Pre := #[]

abbrev ExprM := StateRefT ESt TermElabM

def lift (op : FO) (ty : Ty) : ExprM PE := do
  let st ← get
  let lvl := st.sc.depth
  set { st with sc := st.sc.push { name := tmpName lvl, ty }, pre := st.pre.push ⟨op, lvl⟩ }
  return .var lvl

def expectTy (stx : Syntax) (got : Ty) (exp : Option Ty) : ExprM Unit := do
  if let some t := exp then
    unless t == got do
      throwErrorAt stx "flat def: type mismatch: expected `{t.surface}`, got `{got.surface}`"

def needInt (stx : Syntax) (t : Ty) : ExprM IntW := do
  match t with
  | .int w => return w
  | _ => throwErrorAt stx "flat def: expected a machine integer (`BitVec n`), got `{t.surface}`"

/-- An occurrence of level `l`; `move` for value positions (moves linear values). -/
def touch (stx : Syntax) (l : Nat) (move : Bool) : ExprM Unit := do
  let sc := (← get).sc
  let v := sc.vars[l]!
  if v.moved then
    throwErrorAt stx "flat def: affine rule: `{v.name}` is used after it was moved; write `{v.name}.clone` at the earlier use to keep it"
  if move && v.ty.linear then
    if l < sc.loopBase then
      throwErrorAt stx "flat def: affine rule: the loop body moves `{v.name}`, which is bound outside the loop; use `{v.name}.clone`"
    modify fun st => { st with sc := st.sc.setMoved l true }

def isNum (stx : Syntax) : Bool := (numLit? stx).isSome

def lookupVar (x : Syntax) (n : Name) : ExprM (Nat × LVar) := do
  match (← get).sc.lookup? n with
  | some r => return r
  | none => throwErrorAt x "flat def: unknown variable `{n}`"

def rejectBare (stx : Syntax) (op wrap chk : String) : ExprM α :=
  throwErrorAt stx "flat def: bare `{op}` on machine integers is rejected: write `{wrap}` (wrapping) or `{chk}` (checked, throws)"

/-- Split `x.f` where `x` is a local variable. -/
def splitField? (sc : Scope) (n : Name) : Option (Nat × LVar × String) :=
  match n with
  | .str p f => (sc.lookup? p).map fun (l, v) => (l, v, f)
  | _ => none

mutual

partial def elabE (stx : Term) (exp : Option Ty) : ExprM (PE × Ty) := do
  match stx with
  | `(($e)) => elabE e exp
  | `(($e : $t)) =>
    let ty ← parseTy t
    let (p, _) ← elabE e (some ty)
    expectTy stx ty exp
    return (p, ty)
  | `(()) => expectTy stx .unit exp; return (.unit, .unit)
  | `($a +% $b) => ibinE .add a b exp
  | `($a -% $b) => ibinE .sub a b exp
  | `($a *% $b) => ibinE .mul a b exp
  | `($a &&& $b) => ibinE .and a b exp
  | `($a ||| $b) => ibinE .or a b exp
  | `($a ^^^ $b) => ibinE .xor a b exp
  | `($a <<< $b) => ibinE .shl a b exp
  | `($a >>> $b) => ibinE .lshr a b exp
  | `(~~~$a) => do
    let (pa, ta) ← elabE a exp
    let _ ← needInt a ta
    return (.inot pa, ta)
  | `($a +? $b) => iopE .addC a b exp
  | `($a -? $b) => iopE .subC a b exp
  | `($a *? $b) => iopE .mulC a b exp
  | `($a /? $b) => iopE .udiv a b exp
  | `($a %? $b) => iopE .urem a b exp
  | `($_ + $_) => rejectBare stx "+" "+%" "+?"
  | `($_ - $_) => rejectBare stx "-" "-%" "-?"
  | `($_ * $_) => rejectBare stx "*" "*%" "*?"
  | `($_ / $_) => throwErrorAt stx "flat def: bare `/` is rejected: write `/?` (unsigned, throws .divByZero)"
  | `($_ % $_) => throwErrorAt stx "flat def: bare `%` is rejected: write `%?` (unsigned, throws .divByZero)"
  | `($a == $b) => icmpE .eq a b false stx exp
  | `($a != $b) => icmpE .ne a b false stx exp
  | `($a < $b) => icmpE .ult a b false stx exp
  | `($a > $b) => icmpE .ult a b true stx exp
  | `($a ≤ $b) => icmpE .ule a b false stx exp
  | `($a ≥ $b) => icmpE .ule a b true stx exp
  | `($a && $b) => do
    expectTy stx .bool exp
    let (pa, _) ← elabE a (some .bool)
    let (pb, _) ← elabE b (some .bool)
    return (.band pa pb, .bool)
  | `($a || $b) => do
    expectTy stx .bool exp
    let (pa, _) ← elabE a (some .bool)
    let (pb, _) ← elabE b (some .bool)
    return (.bor pa pb, .bool)
  | `(!$a) => do
    expectTy stx .bool exp
    let (pa, _) ← elabE a (some .bool)
    return (.bnot pa, .bool)
  | `(if $c then $a else $b) => do
    let (pc, _) ← elabE c (some .bool)
    let n0 := (← get).pre.size
    let (pa, ta) ← elabE a exp
    let (pb, _) ← elabE b (some ta)
    if (← get).pre.size != n0 then
      throwErrorAt stx "flat def: fallible operation inside an `if` expression; use an `if` statement"
    return (.cond pc pa pb, ta)
  | `(($a, $b)) => do
    let (ea, eb) := match exp with
      | some (.prod x y) => (some x, some y)
      | _ => (none, none)
    let (pa, ta) ← elabE a ea
    let (pb, tb) ← elabE b eb
    return (.pair pa pb, .prod ta tb)
  | `($xs[$i]!) => do
    let (l, v) ← varOf xs
    match v.ty with
    | .vec _ t =>
      let (pi, ti) ← elabE i (if isNum i then some .u64 else none)
      let _ ← needInt i ti
      expectTy stx t exp
      return (← lift (.vget l pi) t, t)
    | t => throwErrorAt xs "flat def: `{xs}` is not a vector (it has type `{t.surface}`)"
  | `($_[$_]) =>
    throwErrorAt stx "flat def: unchecked indexing is not supported: write `xs[i]!` (throws .indexOutOfBounds)"
  | _ =>
    if stx.raw.getKind == ``Lean.Parser.Term.proj then
      let p : Term := ⟨stx.raw[0]⟩
      let fld := stx.raw[2]
      let (pp, tp) ← elabE p none
      match tp, fld.isFieldIdx? with
      | .prod a _, some 1 => expectTy stx a exp; return (.fst pp, a)
      | .prod _ b, some 2 => expectTy stx b exp; return (.snd pp, b)
      | _, _ => throwErrorAt stx "flat def: unsupported projection `{stx}`"
    else if let some n := numLit? stx then
      match exp with
      | some (.int w) =>
        unless n < 2 ^ w.bits do
          throwErrorAt stx "flat def: literal {n} does not fit in `BitVec {w.bits}`"
        return (.ilit w n, .int w)
      | some t => throwErrorAt stx "flat def: numeric literal where `{t.surface}` is expected"
      | none => throwErrorAt stx "flat def: cannot infer the width of literal {n}; write `({n} : BitVec 64)`"
    else match stx with
      | `($f:ident $args*) => appE stx f args exp
      | `($f:ident) => identE stx f exp
      | _ => throwErrorAt stx "flat def: unsupported expression `{stx}`"

partial def varOf (x : Term) : ExprM (Nat × LVar) := do
  match x with
  | `($n:ident) =>
    let r ← lookupVar x n.getId.eraseMacroScopes
    touch x r.1 false
    return r
  | _ => throwErrorAt x "flat def: expected a variable"

partial def ibinE (op : IBin) (a b : Term) (exp : Option Ty) : ExprM (PE × Ty) := do
  let (pa, pb, t) ← binOperands a b exp
  let _ ← needInt a t
  return (.ibin op pa pb, t)

partial def iopE (op : IOp) (a b : Term) (exp : Option Ty) : ExprM (PE × Ty) := do
  let (pa, pb, t) ← binOperands a b exp
  let _ ← needInt a t
  return (← lift (.iop op pa pb) t, t)

partial def icmpE (op : ICmp) (a b : Term) (swap : Bool) (stx : Term) (exp : Option Ty) :
    ExprM (PE × Ty) := do
  expectTy stx .bool exp
  let (pa, pb, t) ← binOperands a b none
  let _ ← needInt a t
  return (if swap then .icmp op pb pa else .icmp op pa pb, .bool)

/-- Elaborate two same-typed operands left to right; a literal operand takes the other's type. -/
partial def binOperands (a b : Term) (exp : Option Ty) : ExprM (PE × PE × Ty) := do
  if exp.isNone && isNum a && !isNum b then
    let (pb, tb) ← elabE b none
    let (pa, _) ← elabE a (some tb)
    return (pa, pb, tb)
  else
    let (pa, ta) ← elabE a exp
    let (pb, _) ← elabE b (some ta)
    return (pa, pb, ta)

partial def identE (stx : Term) (f : Ident) (exp : Option Ty) : ExprM (PE × Ty) := do
  let n := f.getId.eraseMacroScopes
  let sc := (← get).sc
  if let some (l, v) := sc.lookup? n then
    expectTy stx v.ty exp
    touch stx l true
    return (.var l, v.ty)
  if let some (l, v, fld) := splitField? sc n then
    match fld with
    | "clone" => expectTy stx v.ty exp; touch stx l false; return (.clone l, v.ty)
    | "fst" => return ← elabE (← `(($(mkIdent n.getPrefix)).1)) exp
    | "snd" => return ← elabE (← `(($(mkIdent n.getPrefix)).2)) exp
    | _ => throwErrorAt stx "flat def: unsupported field `{fld}`"
  match n.toString with
  | "true" => expectTy stx .bool exp; return (.blit true, .bool)
  | "false" => expectTy stx .bool exp; return (.blit false, .bool)
  | "DSL.Map.empty" | "Map.empty" =>
    match exp with
    | some (.map k v) => return (.mapEmpty k v, .map k v)
    | _ => throwErrorAt stx "flat def: cannot infer the type of `{f}`; add a type annotation"
  | _ => appE stx f #[] exp

partial def appE (stx : Term) (f : Ident) (args : Array Term) (exp : Option Ty) :
    ExprM (PE × Ty) := do
  let n := f.getId.eraseMacroScopes
  let sc := (← get).sc
  if let some (l, v, fld) := splitField? sc n then
    match fld, v.ty, args.toList with
    | "contains", .map k _, [key] =>
      touch stx l false
      let (pk, _) ← elabE key (some k)
      expectTy stx .bool exp
      return (.mapContains l pk, .bool)
    | "get!", .map k val, [key] =>
      touch stx l false
      let (pk, _) ← elabE key (some k)
      expectTy stx val exp
      return (← lift (.mapGet l pk) val, val)
    | "set!", _, _ | "insert", _, _ =>
      throwErrorAt stx "flat def: `{f}` is only allowed as an update statement `{n.getPrefix} := {f} …`"
    | _, _, _ => throwErrorAt stx "flat def: unsupported method call `{stx}`"
  let intArg (a : Term) : ExprM (PE × IntW) := do
    let (p, t) ← elabE a none
    return (p, ← needInt a t)
  let castE (op : Cast) (w a : Term) : ExprM (PE × Ty) := do
    let some w' := (numLit? w).bind widthOf? |
      throwErrorAt w "flat def: target width must be 8, 16, 32 or 64"
    let (pa, wa) ← intArg a
    let ok : Bool := match op with
      | .zext | .sext => decide (wa.bits ≤ w'.bits)
      | .trunc => decide (w'.bits ≤ wa.bits)
    unless ok do throwErrorAt stx "flat def: `{f}` from {wa.bits} to {w'.bits} bits goes the wrong way"
    expectTy stx (.int w') exp
    return (.cast op w' pa, .int w')
  match n.toString, args.toList with
  | "Vector.replicate", [len, x] =>
    let some k := numLit? len | throwErrorAt len "flat def: vector length must be a numeral"
    let et := match exp with | some (.vec _ t) => some t | _ => none
    let (px, tx) ← elabE x et
    expectTy stx (.vec k tx) exp
    return (.vrepl k px, .vec k tx)
  | "zext", [w, a] | "DSL.Ops.zext", [w, a] => castE .zext w a
  | "sext", [w, a] | "DSL.Ops.sext", [w, a] => castE .sext w a
  | "trunc", [w, a] | "DSL.Ops.trunc", [w, a] => castE .trunc w a
  | "BitVec.slt", [a, b] => icmpE .slt a b false stx exp
  | "BitVec.sle", [a, b] => icmpE .sle a b false stx exp
  | "BitVec.ult", [a, b] => icmpE .ult a b false stx exp
  | "BitVec.ule", [a, b] => icmpE .ule a b false stx exp
  | "ashr", [a, b] | "DSL.Ops.ashr", [a, b] => ibinE .ashr a b exp
  | "shl", [a, b] | "DSL.Ops.shl", [a, b] => ibinE .shl a b exp
  | "lshr", [a, b] | "DSL.Ops.lshr", [a, b] => ibinE .lshr a b exp
  | "throw", _ => throwErrorAt stx "flat def: `throw` is only allowed as a statement"
  | "pure", _ => throwErrorAt stx "flat def: `pure` is only allowed as the final statement"
  | _, _ => callE stx f args exp

/-- Call of another `flat def` (which must have a `.ast`). -/
partial def callE (stx : Term) (f : Ident) (args : Array Term) (exp : Option Ty) :
    ExprM (PE × Ty) := do
  let c ← try realizeGlobalConstNoOverloadWithInfo f
    catch _ => throwErrorAt f "flat def: unknown function or variable `{f}`"
  let env ← getEnv
  let some info := env.find? (c ++ `ast) |
    throwErrorAt f "flat def: `{c}` is not a `flat def` (no `{c}.ast`); only flat defs may be called"
  let ty ← whnf info.type
  let (σ, τ) ← match ty.getAppFn.constName?, ty.getAppArgs with
    | some ``DSL.FlatFn, #[s, t] => pure (← exprToTys s, ← exprToTy t)
    | _, _ => throwErrorAt f "flat def: `{c}.ast` is not a `DSL.FlatFn`"
  unless σ.length == args.size do
    throwErrorAt stx "flat def: `{c}` expects {σ.length} arguments, got {args.size}"
  let mut ps := #[]
  for (a, t) in args.toList.zip σ do
    let (p, _) ← elabE a (some t)
    ps := ps.push p
  expectTy stx τ exp
  return (← lift (.call c ps.toList) τ, τ)

end

def runExpr (sc : Scope) (x : ExprM α) : TermElabM (α × ESt) := x.run { sc }

/-! ## Statements -/

inductive Mode where
  /-- Function body: must end in a result. -/
  | tail (τ : Ty)
  /-- Loop body or branch of a join-point `if`: falls through, yielding the carried variables. -/
  | fall (carried : List Name)

private def getDoSeqElems (doSeq : Syntax) : List Syntax :=
  if doSeq.getKind == ``Parser.Term.doSeqBracketed then
    doSeq[1].getArgs.toList.map fun arg => arg[0]
  else if doSeq.getKind == ``Parser.Term.doSeqIndent then
    doSeq[0].getArgs.toList.map fun arg => arg[0]
  else
    []

/-- Syntactic scan: variables reassigned and variables declared in a block. -/
partial def scanAssigned (stx : Syntax) : StateM (Array Name × Array Name) Unit := do
  let s : TSyntax `doElem := ⟨stx⟩
  match s with
  | `(doElem| $x:ident := $_) | `(doElem| $x:ident ← $_) =>
    modify fun (a, d) => (a.push x.getId.eraseMacroScopes, d)
  | `(doElem| let mut $x:ident $[: $_]? := $_) | `(doElem| let $x:ident $[: $_]? := $_)
  | `(doElem| let mut $x:ident $[: $_]? ← $_) | `(doElem| let $x:ident $[: $_]? ← $_) =>
    modify fun (a, d) => (a, d.push x.getId.eraseMacroScopes)
  | `(doElem| for $x:ident in $_ do $_) =>
    modify fun (a, d) => (a, d.push x.getId.eraseMacroScopes)
  | _ => pure ()
  for c in stx.getArgs do scanAssigned c

/-- Outer mutable variables assigned in `blocks`, in level order. -/
def carriedVars (sc : Scope) (blocks : List Syntax) : List Name := Id.run do
  let ((), (as, ds)) := (blocks.forM scanAssigned).run (#[], #[])
  let mut out : Array (Nat × Name) := #[]
  for n in as do
    if ds.contains n then continue
    if out.any (·.2 == n) then continue
    if let some (l, v) := sc.lookup? n then
      if v.isMut then out := out.push (l, n)
  return (out.qsort (·.1 < ·.1)).toList.map (·.2)

/-- Does control never fall off the end of this block (`return`/`throw` on every path)? -/
partial def isTerminal (elems : List Syntax) : Bool :=
  match elems.getLast? with
  | none => false
  | some s =>
    let e : TSyntax `doElem := ⟨s⟩
    match e with
    | `(doElem| return $_:term) | `(doElem| return) | `(doElem| throw $_) => true
    | `(doElem| $v:term) =>
      match v with
      | `(throw $_) => true
      | _ => false
    | `(doElem| if $_:term then $t $[else if $_:term then $ts]* else $els) =>
      isTerminal (getDoSeqElems t) && ts.all (fun t => isTerminal (getDoSeqElems t)) &&
        isTerminal (getDoSeqElems els)
    | _ => false

partial def containsReturn (stx : Syntax) : Bool :=
  stx.getKind == ``Parser.Term.doReturn || stx.getArgs.any containsReturn

def packTy (sc : Scope) (ns : List Name) : Ty :=
  let rec go : List Name → Ty
    | [] => .unit
    | [n] => ((sc.lookup? n).map (·.2.ty)).getD .unit
    | n :: rest => .prod (((sc.lookup? n).map (·.2.ty)).getD .unit) (go rest)
  go ns

def packPE (sc : Scope) (ns : List Name) : PE :=
  let rec go : List Name → PE
    | [] => .unit
    | [n] => .var (((sc.lookup? n).map (·.1)).getD 0)
    | n :: rest => .pair (.var (((sc.lookup? n).map (·.1)).getD 0)) (go rest)
  go ns

/-- The binder name for a packed value of `ns`. -/
def packBinder (lvl : Nat) : List Name → Name
  | [n] => n
  | _ => tmpName lvl

/-- `sc` has the packed value bound at its last level; unpack it into the names `ns`. -/
partial def unpack (sc : Scope) (ns : List Name) (ty : Ty) (k : Scope → TermElabM Out) :
    TermElabM Out := do
  match ns, ty with
  | [], _ | [_], _ => k sc
  | n :: rest, .prod a b =>
    let d := sc.depth
    let p := nameAt sc (d - 1)
    let sc1 := sc.push { name := n, ty := a, isMut := true }
    let bName := packBinder (d + 1) rest
    let sc2 := sc1.push { name := bName, ty := b, isMut := true }
    let inner ← unpack sc2 rest b k
    let deep ← `(DSL.Stmt.letPair (DSL.Expr.var DSL.Var.zero) $(inner.1))
    let sh ← `(let $(mkIdent n) := ($p).1; let $(mkIdent bName) := ($p).2; $(inner.2))
    return (deep, sh)
  | _, _ => throwError "flat def: internal error in unpack"

def parseErr (e : Term) : TermElabM Term := do
  let e' ← match e with
    | `(($e)) => pure e
    | _ => pure e
  let bad {α} : TermElabM α := throwErrorAt e "flat def: `throw` needs a `DSL.Err`: `.overflow`, `.divByZero`, `.indexOutOfBounds`, `.notFound` or `.user k` (k < 200)"
  match e' with
  | `(.$c:ident) | `(DSL.Err.$c:ident) | `(Err.$c:ident) =>
    match c.getId.toString with
    | "overflow" => `(DSL.Err.overflow)
    | "divByZero" => `(DSL.Err.divByZero)
    | "indexOutOfBounds" => `(DSL.Err.indexOutOfBounds)
    | "notFound" => `(DSL.Err.notFound)
    | _ => bad
  | `(.user $k) | `(DSL.Err.user $k) | `(Err.user $k) =>
    match numLit? k with
    | some n => if n < 200 then `(DSL.Err.user $(num n)) else bad
    | none => bad
  | _ => bad

def doTerm (v : TSyntax `doElem) : TermElabM Term := do
  match v with
  | `(doElem| $t:term) => pure t
  | _ => throwErrorAt v "flat def: expected an expression after `←`"

mutual

partial def transSeq (sc : Scope) (mode : Mode) : List Syntax → TermElabM Out
  | [] => do
    match mode with
    | .tail .unit => return (← `(DSL.Stmt.ret DSL.Expr.unit), ← `(pure ()))
    | .tail _ => throwError "flat def: missing `return` at the end of the function"
    | .fall ns =>
      let p := packPE sc ns
      return (← `(DSL.Stmt.ret $(← p.deep sc.depth)), ← `(pure $(← p.shallow sc)))
  | s :: rest => transElem sc mode s rest

/-- Final value of the function (`return e`, or a trailing expression). -/
partial def transReturn (sc : Scope) (mode : Mode) (e : Term) (rest : List Syntax) : TermElabM Out := do
  let .tail τ := mode |
    throwErrorAt e "flat def: `return` is not allowed inside a loop body or inside an `if` whose other paths fall through"
  unless rest.isEmpty do
    throwErrorAt rest.head! "flat def: unreachable code after `return`"
  let ((p, _), st) ← runExpr sc (elabE e (some τ))
  -- A trailing single fallible operation becomes the tail statement itself.
  if let (.var l, some last) := (p, st.pre.back?) then
    if last.lvl == l then
      let pre := st.pre.pop
      return ← emitPre st.sc pre do
        let d := l
        return (← last.op.deep d, ← last.op.shallow st.sc)
  emitPre st.sc st.pre do
    return (← `(DSL.Stmt.ret $(← p.deep st.sc.depth)), ← `(pure $(← p.shallow st.sc)))

/-- Bind `x` to the value of `e` (new variable, or reassignment when `reassign`). -/
partial def transBind (sc : Scope) (mode : Mode) (x : Ident) (tyAnn : Option Term) (isMut : Bool)
    (reassign : Bool) (e : Term) (rest : List Syntax) : TermElabM Out := do
  let n := x.getId.eraseMacroScopes
  let target ← if reassign then
      match sc.lookup? n with
      | some (l, v) =>
        unless v.isMut do throwErrorAt x "flat def: `{n}` is not mutable (declare it with `let mut`)"
        pure (some (l, v))
      | none => throwErrorAt x "flat def: unknown variable `{n}`"
    else pure none
  let expTy ← match tyAnn, target with
    | some t, _ => some <$> parseTy t
    | none, some (_, v) => pure (some v.ty)
    | none, none => pure none
  -- in-place updates
  if let some (l, v) := target then
    match e with
    | `($f:ident $args*) =>
      if let some (l', _, fld) := splitField? sc f.getId.eraseMacroScopes then
        if fld == "set!" || fld == "insert" then
          unless l' == l do
            throwErrorAt e "flat def: `{f}` must update the variable it is assigned to (`{n} := {n}.{fld} …`)"
          let [a₁, a₂] := args.toList |
            throwErrorAt e "flat def: `{f}` takes two arguments"
          return ← transUpdate sc mode l v fld a₁ a₂ rest
    | _ => pure ()
  let ((p, ty), st) ← runExpr sc (elabE e expTy)
  -- A single trailing fallible operation binds `x` directly.
  if let (.var l, some last) := (p, st.pre.back?) then
    if last.lvl == l then
      let sc' := st.sc.rename l n (isMut || (target.map (·.2.isMut)).getD false)
      return ← emitPre sc' st.pre (transSeq sc' mode rest)
  match target with
  | some (l, _) =>
    emitPre st.sc st.pre do
      let d := st.sc.depth
      let k ← transSeq (st.sc.setMoved l false) mode rest
      let deep ← `(DSL.Stmt.set $(← varAt d l) $(← p.deep d) $(k.1))
      let sh ← `(let $(mkIdent n) : $(← tyShallow ty) := $(← p.shallow st.sc); $(k.2))
      return (deep, sh)
  | none =>
    emitPre st.sc st.pre do
      let d := st.sc.depth
      let sc' := st.sc.push { name := n, ty, isMut }
      let k ← transSeq sc' mode rest
      let deep ← `(DSL.Stmt.let_ $(← p.deep d) $(k.1))
      let sh ← `(let $(mkIdent n) : $(← tyShallow ty) := $(← p.shallow st.sc); $(k.2))
      return (deep, sh)

/-- `xs := xs.set! i v` and `m := m.insert k v`. -/
partial def transUpdate (sc : Scope) (mode : Mode) (l : Nat) (v : LVar) (fld : String)
    (a₁ a₂ : Term) (rest : List Syntax) : TermElabM Out := do
  let x := mkIdent v.name
  if v.moved then
    throwErrorAt a₁ "flat def: affine rule: `{v.name}` is updated after it was moved; write `{v.name}.clone` at the earlier use to keep it"
  if l < sc.loopBase then
    throwErrorAt a₁ "flat def: affine rule: the loop body updates `{v.name}`, which is bound outside the loop"
  match fld, v.ty with
  | "set!", .vec _ t =>
    let ((pi, pe), st) ← runExpr sc do
      let (pi, ti) ← elabE a₁ (if isNum a₁ then some .u64 else none)
      let _ ← needInt a₁ ti
      let (pe, _) ← elabE a₂ (some t)
      return (pi, pe)
    emitPre st.sc st.pre do
      let d := st.sc.depth
      let k ← transSeq st.sc mode rest
      let deep ← `(DSL.Stmt.vset $(← varAt d l) $(← pi.deep d) $(← pe.deep d) $(k.1))
      let sh ← `(DSL.Ops.vset $x $(← pi.shallow st.sc) $(← pe.shallow st.sc) >>= fun $x => $(k.2))
      return (deep, sh)
  | "insert", .map kt vt =>
    let ((pk, pv), st) ← runExpr sc do
      let (pk, _) ← elabE a₁ (some kt)
      let (pv, _) ← elabE a₂ (some vt)
      return (pk, pv)
    emitPre st.sc st.pre do
      let d := st.sc.depth
      let k ← transSeq st.sc mode rest
      let deep ← `(DSL.Stmt.mapInsert $(← varAt d l) $(← pk.deep d) $(← pv.deep d) $(k.1))
      let sh ← `(let $x := DSL.Map.insert $x $(← pk.shallow st.sc) $(← pv.shallow st.sc); $(k.2))
      return (deep, sh)
  | _, t => throwErrorAt a₁ "flat def: `.{fld}` is not available on `{t.surface}`"

/-- Bind the value of statement `s` (deep/shallow) packing `ns`, then unpack and continue. -/
partial def joinThen (sc : Scope) (mode : Mode) (ns : List Name) (s : Out)
    (rest : List Syntax) : TermElabM Out := do
  let ty := packTy sc ns
  let lvl := sc.depth
  let bn := packBinder lvl ns
  let sc1 := sc.push { name := bn, ty, isMut := true }
  let k ← unpack sc1 ns ty fun sc2 => transSeq sc2 mode rest
  return (← `(DSL.Stmt.bind $(s.1) $(k.1)), ← `($(s.2) >>= fun $(mkIdent bn) => $(k.2)))

/-- An `if … then … (else if …)* (else …)?` chain; `branches` are (condition, block). -/
partial def transIfChain (sc : Scope) (mode : Mode) (branches : List (Term × Syntax))
    (els : Option Syntax) (rest : List Syntax) : TermElabM Out := do
  match branches with
  | [] =>
    let elems := (els.map getDoSeqElems).getD []
    transSeq sc mode (elems ++ if isTerminal elems then [] else rest)
  | (c, t) :: more =>
    let ((pc, _), st) ← runExpr sc (elabE c (some .bool))
    emitPre st.sc st.pre do
      let te := getDoSeqElems t
      let kt ← transSeq st.sc mode (te ++ if isTerminal te then [] else rest)
      let ke ← transIfChain st.sc mode more els rest
      let d := st.sc.depth
      return (← `(DSL.Stmt.ite $(← pc.deep d) $(kt.1) $(ke.1)),
              ← `(if $(← pc.shallow st.sc) then $(kt.2) else $(ke.2)))

partial def transIf (sc : Scope) (mode : Mode) (s : Syntax) (branches : List (Term × Syntax))
    (els : Option Syntax) (rest : List Syntax) : TermElabM Out := do
  let isTail := match mode with | .tail _ => true | _ => false
  let hasRet := containsReturn s
  if isTail && (rest.isEmpty || hasRet) then
    -- continuation-passing: `rest` is copied into every branch
    transIfChain sc mode branches els rest
  else
    if hasRet then
      throwErrorAt s "flat def: `return` inside this `if` is not supported here (only in the function body, not in loops or in `if`s whose other paths fall through)"
    let blocks := branches.map (·.2) ++ els.toList
    let ns := carriedVars sc blocks
    let s ← transIfChain sc (.fall ns) branches els []
    joinThen sc mode ns s rest

partial def transFor (sc : Scope) (mode : Mode) (s : Syntax) (i : Name) (n : Nat) (body : Syntax)
    (rest : List Syntax) : TermElabM Out := do
  if containsReturn body then
    throwErrorAt s "flat def: `return` inside a `for` loop is not supported"
  let ns := carriedVars sc [body]
  let accTy := packTy sc ns
  let init := packPE sc ns
  let d := sc.depth
  let sc1 := { sc with loopBase := d }.push { name := i, ty := .u64 }
  let accName := packBinder (d + 1) ns
  let sc2 := sc1.push { name := accName, ty := accTy, isMut := true }
  let b ← unpack sc2 ns accTy fun sc3 => transSeq sc3 (.fall ns) (getDoSeqElems body)
  let deep ← `(DSL.Stmt.forRange $(num n) $(← init.deep d) $(b.1))
  let sh ← `(DSL.Ops.forRange $(num n) $(← init.shallow sc)
    (fun ($(mkIdent i) : BitVec 64) $(mkIdent accName) => $(b.2)))
  joinThen sc mode ns (deep, sh) rest

partial def transElem (sc : Scope) (mode : Mode) (s : Syntax) (rest : List Syntax) : TermElabM Out := do
  let e : TSyntax `doElem := ⟨s⟩
  match e with
  | `(doElem| let mut $x:ident $[: $t]? := $v) => transBind sc mode x t true false v rest
  | `(doElem| let $x:ident $[: $t]? := $v) => transBind sc mode x t false false v rest
  | `(doElem| let mut $x:ident $[: $t]? ← $v) => transBind sc mode x t true false (← doTerm v) rest
  | `(doElem| let $x:ident $[: $t]? ← $v) => transBind sc mode x t false false (← doTerm v) rest
  | `(doElem| $x:ident := $v) => transBind sc mode x none false true v rest
  | `(doElem| $x:ident ← $v) => transBind sc mode x none false true (← doTerm v) rest
  | `(doElem| return $v:term) => transReturn sc mode v rest
  | `(doElem| return) => transReturn sc mode (← `(())) rest
  | `(doElem| for $x:ident in [0 : $n] do $body) | `(doElem| for $x:ident in [: $n] do $body) =>
    let some k := numLit? n | throwErrorAt n "flat def: loop bound must be a numeral"
    transFor sc mode s x.getId.eraseMacroScopes k body rest
  | `(doElem| for _ in [0 : $n] do $body) | `(doElem| for _ in [: $n] do $body) =>
    let some k := numLit? n | throwErrorAt n "flat def: loop bound must be a numeral"
    transFor sc mode s (tmpName sc.depth) k body rest
  | `(doElem| for $_ in $_ do $_) =>
    throwErrorAt s "flat def: only `for i in [0:n]` loops with a numeral bound are supported"
  | `(doElem| if $c:term then $t $[else if $cs:term then $ts]* $[else $els]?) =>
    let branches := (c, t.raw) :: (cs.toList.zip (ts.toList.map (·.raw)))
    transIf sc mode s branches (els.map (·.raw)) rest
  | `(doElem| throw $err) => do
    unless rest.isEmpty do throwErrorAt rest.head! "flat def: unreachable code after `throw`"
    let er ← parseErr err
    return (← `(DSL.Stmt.throw $er), ← `(throw $er))
  | `(doElem| pure $v) =>
    if rest.isEmpty then transReturn sc mode v rest
    else throwErrorAt s "flat def: `pure` is only allowed as the final statement"
  | `(doElem| $v:term) =>
    match v with
    | `(throw $err) => transElem sc mode (← `(doElem| throw $err)) rest
    | `(pure $v) => transElem sc mode (← `(doElem| pure $v)) rest
    | _ =>
      match mode, rest with
      | .tail _, [] => transReturn sc mode v rest
      | _, _ =>
        let (_, st) ← runExpr sc (elabE v none)
        if st.pre.isEmpty then
          throwErrorAt v "flat def: this expression statement has no effect"
        emitPre st.sc st.pre (transSeq st.sc mode rest)
  | _ =>
    let k := s.getKind.toString
    if (k.splitOn "While").length > 1 || (k.splitOn "Repeat").length > 1 then
      throwErrorAt s "flat def: `while`/`repeat` loops are not supported: only bounded `for i in [0:n]` loops (PLAN §3.1)"
    throwErrorAt s "flat def: unsupported statement"

end

/-! ## Readable checker errors -/

unsafe def evalCheckUnsafe (e : Lean.Expr) : TermElabM (Except String Unit) := do
  let ty := mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String) (mkConst ``Unit)
  evalExpr (Except String Unit) ty e

@[implemented_by evalCheckUnsafe]
opaque evalCheck (e : Lean.Expr) : TermElabM (Except String Unit)

/-! ## The command -/

register_option flat_def.timing : Bool := {
  defValue := false
  descr := "flat def: report the time spent proving `denote_eq`"
}

syntax flatBinder := "(" ident " : " term ")"

syntax (name := flatDef) (docComment)? "flat " "def " ident (ppSpace flatBinder)* " : " term
  (ppDedent(ppLine) "requires " term)? (ppDedent(ppLine) "ensures " ident ", " term)?
  " := " term (ppDedent(ppLine) &"proof " "by " Lean.Parser.Tactic.tacticSeq)? : command

/-- Proof script for `denote_eq`: `rfl` first, then unfolding irreducible callees, then `simp`. -/
def denoteEqTactic : CommandElabM (TSyntax `tactic) :=
  `(tactic| first
    | exact rfl
    | (with_unfolding_all exact rfl)
    | (simp only [DSL.denote, DSL.Stmt.denote, DSL.Expr.denote, DSL.Exprs.denote, DSL.Op.denote,
        DSL.Var.get, DSL.Var.set, DSL.IBin.denote, DSL.ICmp.denote, DSL.Cast.denote,
        DSL.IOp.denote]; done))

/-- Add `name : type` (an equation `∀ xs, lhs = rhs`) proven by `Eq.refl lhs`, checked by the
kernel only. The kernel's definitional-equality check shares work across the let-heavy terms
`denote` unfolds to, where `Meta.isDefEq` (`exact rfl`) can blow up exponentially. -/
def addKernelRfl (name : Name) (type : Term) : CommandElabM Unit := liftTermElabM do
  let ty ← elabTerm type (some (mkSort Level.zero))
  synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let val ← forallTelescope ty fun xs body => do
    let some (_, lhs, _) := body.eq? | throwError "flat def: internal error: not an equation"
    mkLambdaFVars xs (← mkEqRefl lhs)
  let decl := Declaration.thmDecl { name, levelParams := [], type := ty, value := val }
  -- Synchronous kernel check first (`addDecl` checks asynchronously and, on failure, would
  -- register the name as an axiom, which blocks the tactic fallback).
  let opts ← getOptions
  match (← getEnv).addDeclCore (maxHeartbeats.get opts * 1000).toUSize
      (maxRecDepth.get opts).toUSize decl none with
  | .ok _ => addDecl decl
  | .error e => throwError "flat def: kernel rfl failed: {e.toMessageData opts}"

/-- Generated terms nest one level per statement; raise the recursion limit for them. -/
def withDeepRecursion (x : CommandElabM α) : CommandElabM α :=
  withScope (fun sc => { sc with opts := maxRecDepth.set sc.opts (max 100000 (maxRecDepth.get sc.opts)) }) x

@[command_elab flatDef]
def elabFlatDef : CommandElab := fun stx => withDeepRecursion do
  match stx with
  | `($[$doc?:docComment]? flat def $name:ident $bs:flatBinder* : $rt:term
        $[requires $pre?:term]? $[ensures $r?:ident, $post?:term]? := $body:term
        $[proof by $tac?:tacticSeq]?) => do
    let params ← bs.mapM fun b => match b with
      | `(flatBinder| ($x:ident : $t:term)) => pure (x, t)
      | _ => throwErrorAt b "flat def: bad binder"
    let nm := name.getId
    let fullName := (← getCurrNamespace) ++ nm
    let astId := mkIdent (nm ++ `ast)
    -- translate
    let (σ, τ, deep, shallow) ← liftTermElabM do
      let σ ← params.mapM fun (_, t) => parseTy t
      let τ ← parseTy rt
      let seq ← match body with
        | `(do $seq:doSeq) => pure seq.raw
        | _ => throwErrorAt body "flat def: the body must be a `do` block"
      -- parameters: x₁ is #0, i.e. the last level
      let mut sc : Scope := {}
      for (x, t) in (params.zip σ).reverse do
        sc := sc.push { name := x.1.getId.eraseMacroScopes, ty := t, isMut := false }
      -- parameters are immutable; `let mut x := x` makes a mutable copy
      let (d, s) ← transSeq sc (.tail τ) (getDoSeqElems seq)
      return (σ, τ, d, s)
    let σDeep ← liftTermElabM <| σ.toList.mapM tyDeep
    let τDeep ← liftTermElabM <| tyDeep τ
    let σSh ← liftTermElabM <| σ.mapM tyShallow
    let τSh ← liftTermElabM <| tyShallow τ
    let fullStr := Syntax.mkStrLit fullName.toString
    elabCommand (← `(
      /-- Deep AST generated by `flat def`. -/
      def $astId : DSL.FlatFn [$(σDeep.toArray),*] $τDeep := { name := $fullStr, body := $deep }))
    -- readable pre-check
    let r ← liftTermElabM do
      let c ← realizeGlobalConstNoOverloadWithInfo astId
      evalCheck (mkApp3 (mkConst ``DSL.FlatFn.check) (← exprToTysE σ) (← exprToTyE τ) (mkConst c))
    if let .error msg := r then
      throwErrorAt name "flat def rejected by the fragment checker: {msg}"
    let binders ← (params.zip σSh).mapM fun ((x, _), t) => `(bracketedBinder| ($x : $t))
    let xs := params.map (·.1)
    elabCommand (← `($[$doc?:docComment]? def $name $binders* : DSL.M $τSh := $shallow))
    -- denote_eq
    let argsTuple ← xs.foldrM (fun x acc => `(($x, $acc))) (← `(()))
    let app ← if xs.isEmpty then pure (name : Term) else `($name $xs*)
    let eqId := mkIdent (nm ++ `denote_eq)
    let eqName := (← getCurrNamespace) ++ nm ++ `denote_eq
    let eqTy ← if xs.isEmpty then `(DSL.denote $astId $argsTuple = $app)
      else `(∀ $binders*, DSL.denote $astId $argsTuple = $app)
    let t0 ← IO.monoMsNow
    let kernelOk ← try addKernelRfl eqName eqTy; pure true catch _ => pure false
    unless kernelOk do
      let tac ← denoteEqTactic
      if xs.isEmpty then
        elabCommand (← `(theorem $eqId : $eqTy := by $tac:tactic))
      else
        elabCommand (← `(theorem $eqId : $eqTy := by intros; $tac:tactic))
    if flat_def.timing.get (← getOptions) then
      logInfo m!"{nm}.denote_eq: {(← IO.monoMsNow) - t0} ms ({if kernelOk then "kernel rfl" else "tactic"})"
    elabCommand (← `(attribute [simp] $eqId))
    -- checked
    let ckId := mkIdent (nm ++ `checked)
    elabCommand (← `(theorem $ckId : DSL.FlatFn.checked $astId := by decide))
    -- contract
    if pre?.isSome || post?.isSome then
      let some tac := tac? | throwErrorAt name "flat def: a `requires`/`ensures` contract needs a trailing `proof by …`"
      let preT ← match pre? with
        | some p => pure p
        | none => `(True)
      let r ← match r? with
        | some r => pure r
        | none => pure (mkIdent `r)
      let postT ← match post? with
        | some q => pure q
        | none => `(True)
      let stmt ← `(∃ $r:ident, $app = Except.ok $r ∧ $postT)
      let ctId := mkIdent (nm ++ `contract)
      if xs.isEmpty then
        elabCommand (← `(theorem $ctId : $preT → $stmt := by $tac))
      else
        elabCommand (← `(theorem $ctId : ∀ $binders*, $preT → $stmt := by $tac))
      elabCommand (← `(attribute [irreducible] $name))
    else if tac?.isSome then
      throwErrorAt name "flat def: `proof by` without `requires`/`ensures`"
  | _ => throwUnsupportedSyntax
where
  exprToTyE (t : Ty) : TermElabM Lean.Expr := do
    elabTerm (← tyDeep t) (some (mkConst ``DSL.Ty))
  exprToTysE (σ : Array Ty) : TermElabM Lean.Expr := do
    let ts ← σ.toList.mapM tyDeep
    elabTerm (← `([$(ts.toArray),*])) (some (mkApp (mkConst ``List [0]) (mkConst ``DSL.Ty)))

end Frontend
end DSL
