/-!
# ISLE programs as Lean data

Datatypes for Cranelift ISLE compilation units after `cranelift-isle`'s semantic analysis
(`sema::TypeEnv` / `sema::TermEnv`, with internal extractors expanded and implicit converters
inserted, exactly the form Cranelift's code generator consumes). The data itself is generated
by `rust/crates/isle2lean` into `FV/Isle/Generated/`; see `docs/contracts/isle.md`.

Everything is plain inductive data with decidable equality, so a rule can be referenced by
name and its structure checked by `rfl` / `decide`.

Identifiers (`TypeId`, `TermId`, `VarId`, rule ids) are the `cranelift-isle` arena indices,
which are deterministic for a given input file list.
-/

namespace Isle

/-- Index into `Program.types` (`sema::TypeId`). -/
abbrev TypeId := Nat
/-- Index into `Program.terms` (`sema::TermId`). -/
abbrev TermId := Nat
/-- Index into a rule's `vars` (`sema::VarId`). -/
abbrev VarId := Nat
/-- Index into `Program.rules` (`sema::RuleId`). -/
abbrev RuleId := Nat

/-- Source position: file name as in Cranelift's generated code (`src/isa/aarch64/lower.isle`,
`<OUT_DIR>/clif_lower.isle`) and **1-based** line. (Cranelift's generated-code comments and
`trace-log` output print 0-based lines.) -/
structure Pos where
  file : String
  line : Nat
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- S-expressions (`cranelift_isle::printer::SExpr`), used for specs and for the source form of
internal extractors. -/
inductive SExpr where
  | atom (s : String)
  | binding (name : String) (e : SExpr)
  | list (es : List SExpr)
  deriving Repr, Inhabited

-- `deriving DecidableEq` does not support nested inductives; these instances are the
-- structural equivalent.
mutual
def SExpr.decEq : (a b : SExpr) → Decidable (a = b)
  | .atom x0, .atom y0 =>
    if h0 : x0 = y0 then
      isTrue (by subst h0; rfl)
    else isFalse (by intro e; injection e; contradiction)
  | .atom _, .binding _ _
  | .atom _, .list _ => isFalse (nomatch ·)
  | .binding x0 x1, .binding y0 y1 =>
    if h0 : x0 = y0 then
      match SExpr.decEq x1 y1 with
      | isFalse h1 => isFalse (by intro e; injection e; contradiction)
      | isTrue h1 =>
        isTrue (by subst h0 h1; rfl)
    else isFalse (by intro e; injection e; contradiction)
  | .binding _ _, .atom _
  | .binding _ _, .list _ => isFalse (nomatch ·)
  | .list x0, .list y0 =>
    match SExpr.decEqList x0 y0 with
    | isFalse h0 => isFalse (by intro e; injection e; contradiction)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .list _, .atom _
  | .list _, .binding _ _ => isFalse (nomatch ·)
def SExpr.decEqList : (a b : List SExpr) → Decidable (a = b)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match SExpr.decEq x y with
    | isFalse h => isFalse (by intro e; injection e; contradiction)
    | isTrue h =>
      match SExpr.decEqList xs ys with
      | isFalse h' => isFalse (by intro e; injection e; contradiction)
      | isTrue h' => isTrue (by subst h h'; rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (nomatch ·)
end

instance : DecidableEq SExpr := SExpr.decEq

/-- ISLE built-in integer types. -/
inductive IntTy where
  | u8 | u16 | u32 | u64 | u128 | usize | i8 | i16 | i32 | i64 | i128 | isize
  deriving Repr, DecidableEq, Inhabited

/-- How the fields of a variant/struct were declared. -/
inductive FieldsKind where
  | unit | named | tuple
  deriving Repr, DecidableEq, Inhabited

/-- A field: name (`"0"`, `"1"`, ... for tuple fields) and type. -/
structure Field where
  name : String
  ty : TypeId
  deriving Repr, DecidableEq, Inhabited

/-- An enum variant; `fullName` is the variant's term name `Enum.Variant`. -/
structure Variant where
  name : String
  fullName : String
  fieldsKind : FieldsKind
  fields : List Field
  deriving Repr, DecidableEq, Inhabited

inductive TypeKind where
  | bool
  | int (t : IntTy)
  /-- An extern primitive (a Rust `Copy` type such as `Type`, `Value`, `Reg`). -/
  | primitive
  | enum (isExtern : Bool) (variants : List Variant)
  | struct (isExtern : Bool) (fieldsKind : FieldsKind) (fields : List Field)
  deriving Repr, DecidableEq, Inhabited

structure TypeDef where
  id : TypeId
  name : String
  kind : TypeKind
  pos : Option Pos
  deriving Repr, DecidableEq, Inhabited

/-- `(decl pure multi partial rec ...)` flags. -/
structure TermFlags where
  isPure : Bool
  isMulti : Bool
  isPartial : Bool
  isRec : Bool
  deriving Repr, DecidableEq, Inhabited

/-- A term's constructor: internal (defined by rules) or an extern Rust function. -/
inductive Ctor where
  | internal
  | external (fn : String)
  deriving Repr, DecidableEq, Inhabited

/-- A term's extractor. Internal extractors are macros that `cranelift-isle` expands into rule
patterns; `form` is the source `(extractor ...)` definition, kept for reference only. -/
inductive Extractor where
  | internal (form : SExpr)
  | external (fn : String) (infallible : Bool)
  deriving Repr, DecidableEq, Inhabited

inductive TermKind where
  /-- Variant number `variant` of the term's result type (an enum). -/
  | enumVariant (variant : Nat)
  /-- The constructor/extractor of the term's result type (a struct). -/
  | struct
  | decl (flags : TermFlags) (ctor : Option Ctor) (extractor : Option Extractor)
  deriving Repr, DecidableEq, Inhabited

structure Term where
  id : TermId
  name : String
  args : List TypeId
  ret : TypeId
  kind : TermKind
  pos : Pos
  deriving Repr, DecidableEq, Inhabited

/-- Left-hand-side patterns (`sema::Pattern`). Each node carries the type of the value it
matches. -/
inductive Pattern where
  /-- Bind the value to `var`, then match `sub`. -/
  | bind (ty : TypeId) (var : VarId) (sub : Pattern)
  /-- Equal to the already-bound `var`. -/
  | var (ty : TypeId) (var : VarId)
  | constBool (ty : TypeId) (b : Bool)
  | constInt (ty : TypeId) (i : Int)
  /-- An extern constant `$name` (stored without the `$`). -/
  | constPrim (ty : TypeId) (name : String)
  /-- Extractor application: enum variant, struct, or extern extractor term. -/
  | term (ty : TypeId) (term : TermId) (args : List Pattern)
  | wildcard (ty : TypeId)
  | and (ty : TypeId) (ps : List Pattern)
  deriving Repr, Inhabited

mutual
def Pattern.decEq : (a b : Pattern) → Decidable (a = b)
  | .bind x0 x1 x2, .bind y0 y1 y2 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then
        match Pattern.decEq x2 y2 with
        | isFalse h2 => isFalse (by intro e; injection e; contradiction)
        | isTrue h2 =>
          isTrue (by subst h0 h1 h2; rfl)
      else isFalse (by intro e; injection e; contradiction)
    else isFalse (by intro e; injection e; contradiction)
  | .bind _ _ _, .var _ _
  | .bind _ _ _, .constBool _ _
  | .bind _ _ _, .constInt _ _
  | .bind _ _ _, .constPrim _ _
  | .bind _ _ _, .term _ _ _
  | .bind _ _ _, .wildcard _
  | .bind _ _ _, .and _ _ => isFalse (nomatch ·)
  | .var x0 x1, .var y0 y1 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then
        isTrue (by subst h0 h1; rfl)
      else isFalse (by intro e; injection e; contradiction)
    else isFalse (by intro e; injection e; contradiction)
  | .var _ _, .bind _ _ _
  | .var _ _, .constBool _ _
  | .var _ _, .constInt _ _
  | .var _ _, .constPrim _ _
  | .var _ _, .term _ _ _
  | .var _ _, .wildcard _
  | .var _ _, .and _ _ => isFalse (nomatch ·)
  | .constBool x0 x1, .constBool y0 y1 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then
        isTrue (by subst h0 h1; rfl)
      else isFalse (by intro e; injection e; contradiction)
    else isFalse (by intro e; injection e; contradiction)
  | .constBool _ _, .bind _ _ _
  | .constBool _ _, .var _ _
  | .constBool _ _, .constInt _ _
  | .constBool _ _, .constPrim _ _
  | .constBool _ _, .term _ _ _
  | .constBool _ _, .wildcard _
  | .constBool _ _, .and _ _ => isFalse (nomatch ·)
  | .constInt x0 x1, .constInt y0 y1 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then
        isTrue (by subst h0 h1; rfl)
      else isFalse (by intro e; injection e; contradiction)
    else isFalse (by intro e; injection e; contradiction)
  | .constInt _ _, .bind _ _ _
  | .constInt _ _, .var _ _
  | .constInt _ _, .constBool _ _
  | .constInt _ _, .constPrim _ _
  | .constInt _ _, .term _ _ _
  | .constInt _ _, .wildcard _
  | .constInt _ _, .and _ _ => isFalse (nomatch ·)
  | .constPrim x0 x1, .constPrim y0 y1 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then
        isTrue (by subst h0 h1; rfl)
      else isFalse (by intro e; injection e; contradiction)
    else isFalse (by intro e; injection e; contradiction)
  | .constPrim _ _, .bind _ _ _
  | .constPrim _ _, .var _ _
  | .constPrim _ _, .constBool _ _
  | .constPrim _ _, .constInt _ _
  | .constPrim _ _, .term _ _ _
  | .constPrim _ _, .wildcard _
  | .constPrim _ _, .and _ _ => isFalse (nomatch ·)
  | .term x0 x1 x2, .term y0 y1 y2 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then
        match Pattern.decEqList x2 y2 with
        | isFalse h2 => isFalse (by intro e; injection e; contradiction)
        | isTrue h2 =>
          isTrue (by subst h0 h1 h2; rfl)
      else isFalse (by intro e; injection e; contradiction)
    else isFalse (by intro e; injection e; contradiction)
  | .term _ _ _, .bind _ _ _
  | .term _ _ _, .var _ _
  | .term _ _ _, .constBool _ _
  | .term _ _ _, .constInt _ _
  | .term _ _ _, .constPrim _ _
  | .term _ _ _, .wildcard _
  | .term _ _ _, .and _ _ => isFalse (nomatch ·)
  | .wildcard x0, .wildcard y0 =>
    if h0 : x0 = y0 then
      isTrue (by subst h0; rfl)
    else isFalse (by intro e; injection e; contradiction)
  | .wildcard _, .bind _ _ _
  | .wildcard _, .var _ _
  | .wildcard _, .constBool _ _
  | .wildcard _, .constInt _ _
  | .wildcard _, .constPrim _ _
  | .wildcard _, .term _ _ _
  | .wildcard _, .and _ _ => isFalse (nomatch ·)
  | .and x0 x1, .and y0 y1 =>
    if h0 : x0 = y0 then
      match Pattern.decEqList x1 y1 with
      | isFalse h1 => isFalse (by intro e; injection e; contradiction)
      | isTrue h1 =>
        isTrue (by subst h0 h1; rfl)
    else isFalse (by intro e; injection e; contradiction)
  | .and _ _, .bind _ _ _
  | .and _ _, .var _ _
  | .and _ _, .constBool _ _
  | .and _ _, .constInt _ _
  | .and _ _, .constPrim _ _
  | .and _ _, .term _ _ _
  | .and _ _, .wildcard _ => isFalse (nomatch ·)
def Pattern.decEqList : (a b : List Pattern) → Decidable (a = b)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match Pattern.decEq x y with
    | isFalse h => isFalse (by intro e; injection e; contradiction)
    | isTrue h =>
      match Pattern.decEqList xs ys with
      | isFalse h' => isFalse (by intro e; injection e; contradiction)
      | isTrue h' => isTrue (by subst h h'; rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (nomatch ·)
end

instance : DecidableEq Pattern := Pattern.decEq

/-- Right-hand-side expressions (`sema::Expr`). -/
inductive Expr where
  | term (ty : TypeId) (term : TermId) (args : List Expr)
  | var (ty : TypeId) (var : VarId)
  | constBool (ty : TypeId) (b : Bool)
  | constInt (ty : TypeId) (i : Int)
  | constPrim (ty : TypeId) (name : String)
  /-- Sequential (`let*`) bindings `(var, type, expr)`. -/
  | «let» (ty : TypeId) (binds : List (VarId × TypeId × Expr)) (body : Expr)
  deriving Repr, Inhabited

mutual
def Expr.decEq : (a b : Expr) → Decidable (a = b)
  | .term x0 x1 x2, .term y0 y1 y2 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then
        match Expr.decEqList x2 y2 with
        | isFalse h2 => isFalse (by intro e; injection e; contradiction)
        | isTrue h2 =>
          isTrue (by subst h0 h1 h2; rfl)
      else isFalse (by intro e; injection e; contradiction)
    else isFalse (by intro e; injection e; contradiction)
  | .term _ _ _, .var _ _
  | .term _ _ _, .constBool _ _
  | .term _ _ _, .constInt _ _
  | .term _ _ _, .constPrim _ _
  | .term _ _ _, .«let» _ _ _ => isFalse (nomatch ·)
  | .var x0 x1, .var y0 y1 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then
        isTrue (by subst h0 h1; rfl)
      else isFalse (by intro e; injection e; contradiction)
    else isFalse (by intro e; injection e; contradiction)
  | .var _ _, .term _ _ _
  | .var _ _, .constBool _ _
  | .var _ _, .constInt _ _
  | .var _ _, .constPrim _ _
  | .var _ _, .«let» _ _ _ => isFalse (nomatch ·)
  | .constBool x0 x1, .constBool y0 y1 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then
        isTrue (by subst h0 h1; rfl)
      else isFalse (by intro e; injection e; contradiction)
    else isFalse (by intro e; injection e; contradiction)
  | .constBool _ _, .term _ _ _
  | .constBool _ _, .var _ _
  | .constBool _ _, .constInt _ _
  | .constBool _ _, .constPrim _ _
  | .constBool _ _, .«let» _ _ _ => isFalse (nomatch ·)
  | .constInt x0 x1, .constInt y0 y1 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then
        isTrue (by subst h0 h1; rfl)
      else isFalse (by intro e; injection e; contradiction)
    else isFalse (by intro e; injection e; contradiction)
  | .constInt _ _, .term _ _ _
  | .constInt _ _, .var _ _
  | .constInt _ _, .constBool _ _
  | .constInt _ _, .constPrim _ _
  | .constInt _ _, .«let» _ _ _ => isFalse (nomatch ·)
  | .constPrim x0 x1, .constPrim y0 y1 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then
        isTrue (by subst h0 h1; rfl)
      else isFalse (by intro e; injection e; contradiction)
    else isFalse (by intro e; injection e; contradiction)
  | .constPrim _ _, .term _ _ _
  | .constPrim _ _, .var _ _
  | .constPrim _ _, .constBool _ _
  | .constPrim _ _, .constInt _ _
  | .constPrim _ _, .«let» _ _ _ => isFalse (nomatch ·)
  | .«let» x0 x1 x2, .«let» y0 y1 y2 =>
    if h0 : x0 = y0 then
      match Expr.decEqBinds x1 y1 with
      | isFalse h1 => isFalse (by intro e; injection e; contradiction)
      | isTrue h1 =>
        match Expr.decEq x2 y2 with
        | isFalse h2 => isFalse (by intro e; injection e; contradiction)
        | isTrue h2 =>
          isTrue (by subst h0 h1 h2; rfl)
    else isFalse (by intro e; injection e; contradiction)
  | .«let» _ _ _, .term _ _ _
  | .«let» _ _ _, .var _ _
  | .«let» _ _ _, .constBool _ _
  | .«let» _ _ _, .constInt _ _
  | .«let» _ _ _, .constPrim _ _ => isFalse (nomatch ·)
def Expr.decEqList : (a b : List Expr) → Decidable (a = b)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match Expr.decEq x y with
    | isFalse h => isFalse (by intro e; injection e; contradiction)
    | isTrue h =>
      match Expr.decEqList xs ys with
      | isFalse h' => isFalse (by intro e; injection e; contradiction)
      | isTrue h' => isTrue (by subst h h'; rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (nomatch ·)
def Expr.decEqBinds : (a b : List (VarId × TypeId × Expr)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | (v, t, x) :: xs, (w, u, y) :: ys =>
    if h1 : v = w then
      if h2 : t = u then
        match Expr.decEq x y with
        | isFalse h => isFalse (by intro e; cases e; contradiction)
        | isTrue h =>
          match Expr.decEqBinds xs ys with
          | isFalse h' => isFalse (by intro e; injection e; contradiction)
          | isTrue h' => isTrue (by subst h1 h2 h h'; rfl)
      else isFalse (by intro e; cases e; contradiction)
    else isFalse (by intro e; cases e; contradiction)
  | [], _ :: _ | _ :: _, [] => isFalse (nomatch ·)
end

instance : DecidableEq Expr := Expr.decEq

/-- `(if-let lhs rhs)`; `(if e)` is `(if-let _ e)`. -/
structure IfLet where
  lhs : Pattern
  rhs : Expr
  deriving Repr, DecidableEq, Inhabited

structure Rule where
  id : RuleId
  /-- Stable Lean name `rule_<file stem>_<line>` (also the name of the generated `def`). -/
  name : String
  /-- The rule's name in `cranelift-isle` (the target of `(attr rule <name> ...)`): the explicit
  name of `(rule name ...)`, or, for a term with a single rule, the term's name. -/
  isleName : Option String
  /-- Whether `isleName` is written in the source. -/
  explicitName : Bool
  /-- The root term being rewritten. -/
  term : TermId
  /-- Patterns on the root term's arguments. -/
  args : List Pattern
  iflets : List IfLet
  rhs : Expr
  /-- Variable names and types, indexed by `VarId`. -/
  vars : List (String × TypeId)
  prio : Int
  pos : Pos
  deriving Repr, DecidableEq, Inhabited

/-- Kinds of VeriISLE spec-language definitions. -/
inductive SpecKind where
  | spec | specMacro | model | state | form | instantiate | attr
  deriving Repr, DecidableEq, Inhabited

/-- A spec-language definition, as its full S-expression. `name` is the term (`spec`,
`instantiate`, `attr` on a term), rule (`attr` on a rule), macro, type (`model`), state or form
name. `term`/`rule` link to the program when the name resolves. -/
structure SpecDef where
  kind : SpecKind
  name : String
  term : Option TermId
  rule : Option RuleId
  pos : Pos
  body : SExpr
  deriving Repr, DecidableEq, Inhabited

/-- `(extern const $name ty)`. -/
structure Const where
  name : String
  ty : TypeId
  deriving Repr, DecidableEq, Inhabited

/-- `(convert inner outer term)`. -/
structure Converter where
  inner : TypeId
  outer : TypeId
  term : TermId
  deriving Repr, DecidableEq, Inhabited

/-- Rule order for one term: descending priority, then ascending rule id (source order). -/
def ruleBefore (a b : Rule) : Bool :=
  a.prio > b.prio || (a.prio == b.prio && a.id < b.id)

structure Program where
  name : String
  files : Array String
  types : Array TypeDef
  terms : Array Term
  rules : Array Rule
  consts : Array Const
  converters : Array Converter
  specs : Array SpecDef
  /-- For each term, the ids of its rules in `ruleBefore` order. -/
  rulesByTerm : Array (Array RuleId)
  deriving Inhabited

/-- Build a program, computing the per-term rule index. -/
def Program.build (name : String) (files : Array String) (types : Array TypeDef)
    (terms : Array Term) (rules : Array Rule) (consts : Array Const)
    (converters : Array Converter) (specs : Array SpecDef) : Program :=
  let buckets : Array (Array Rule) := rules.foldl
    (fun acc r => if r.term < acc.size then acc.modify r.term (·.push r) else acc)
    (Array.replicate terms.size #[])
  { name, files, types, terms, rules, consts, converters, specs
    rulesByTerm := buckets.map fun rs => (rs.qsort ruleBefore).map (·.id) }

namespace Program

def term? (p : Program) (t : TermId) : Option Term := p.terms[t]?
def type? (p : Program) (t : TypeId) : Option TypeDef := p.types[t]?
def rule? (p : Program) (r : RuleId) : Option Rule := p.rules[r]?

def termName (p : Program) (t : TermId) : String :=
  match p.term? t with
  | some t => t.name
  | none => s!"<term {t}>"

def typeName (p : Program) (t : TypeId) : String :=
  match p.type? t with
  | some t => t.name
  | none => s!"<type {t}>"

def termByName? (p : Program) (n : String) : Option Term := p.terms.find? (·.name == n)
def ruleByName? (p : Program) (n : String) : Option Rule := p.rules.find? (·.name == n)

/-- Rules of a term, in matching order. -/
def rulesOf (p : Program) (t : TermId) : List Rule :=
  ((p.rulesByTerm[t]?).getD #[]).toList.filterMap p.rule?

/-- Specs attached to a term. -/
def specsOf (p : Program) (t : TermId) : List SpecDef :=
  p.specs.toList.filter fun s => s.kind == .spec && s.term == some t

end Program

namespace Term

/-- Rust function of an extern constructor, if any. -/
def externCtor? (t : Term) : Option String :=
  match t.kind with
  | .decl _ (some (.external f)) _ => some f
  | _ => none

/-- Rust function of an extern extractor, if any. -/
def externExtractor? (t : Term) : Option String :=
  match t.kind with
  | .decl _ _ (some (.external f _)) => some f
  | _ => none

/-- Has an extern Rust constructor or extractor (unverified helper code, PLAN.md §6). -/
def isExtern (t : Term) : Bool := t.externCtor?.isSome || t.externExtractor?.isSome

def hasInternalCtor (t : Term) : Bool :=
  match t.kind with
  | .decl _ (some .internal) _ => true
  | _ => false

def flags (t : Term) : TermFlags :=
  match t.kind with
  | .decl f _ _ => f
  | _ => ⟨true, false, false, false⟩

end Term

/-! ## Closure reports (`FV/Isle/Generated/Closure.lean`) -/

/-- A rule in the closure of the emitter subset. `tags` are the VeriISLE tags on the rule, its
root term and every term it mentions; `defaultExcludedBy` is their intersection with the
`veri --default-excludes` tags (non-empty: every expansion containing this rule is skipped by
the default VeriISLE run). `lhsReasons` lists syntactic LHS facts (non-E opcode, non-`i8..i64`
type constant, vector/float type extractor) that make the rule's main pattern unmatchable in an
E program; for non-root rules this is only a hint (see the contract). -/
structure ClosureRule where
  rule : RuleId
  name : String
  term : TermId
  isRoot : Bool
  tags : List String
  defaultExcludedBy : List String
  lhsReasons : List String
  deriving Repr, DecidableEq, Inhabited

inductive ClosureTermKind where
  | enumVariant | struct | decl
  deriving Repr, DecidableEq, Inhabited

/-- A term mentioned by closure rules: its extern Rust constructor/extractor (if any), whether
VeriISLE has a `spec` for it, whether it carries the VeriISLE `chain` attribute, and its tags. -/
structure ClosureTerm where
  term : TermId
  name : String
  kind : ClosureTermKind
  externCtor : Option String
  externExtractor : Option String
  hasSpec : Bool
  chain : Bool
  tags : List String
  deriving Repr, DecidableEq, Inhabited

end Isle
