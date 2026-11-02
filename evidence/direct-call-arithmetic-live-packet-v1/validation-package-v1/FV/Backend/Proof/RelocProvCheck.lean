import FV.Backend.Proof.IselFlowCheck

/-!
# Name provenance of the ISLE lowering: the abstract interpretation (L1e, #216)

Names enter ISLE values only through two extern extractors, `func_ref_data` (an external
function's name) and `symbol_value_data` (a symbol global value's name and offset); no rule
constant is a name. An abstract value `NA` describes the names, the integer leaves and the
`MInst`s inside an ISLE value (meaning: `RelocProvModel`):

* `e`/`g`/`u`: its names may be external function names / symbol names / anything;
* `i`: every integer leaf is one of the function's reference offsets (`refOffs`: `0` or a
  global value's offset);
* `s`: every `MInst` inside has its references in the function (`VGood`).

The transfer functions: the two extractors give `e` and `g` (and offsets: `i`); every other known
extractor gives no names; constructors pass their arguments' names on (an extern constructor
builds no name) and no offsets; building `MInst` data checks the referencing variants
(`refChk`: a call's `CallInfo` holds external names only, an address load's name is declared,
a `LoadExtNameNear`'s offset is an offset).

The abstract evaluation (`aPat`, `aExpr`, `aRule`, `chkTab`) and the soundness model (`Model`)
are V1's flow analysis (`IselFlowCheck`) over this domain; integer constants are abstracted by
their value (`cInt`: `i` iff the constant is `0`).
-/

namespace Backend.Proof.RelocProv

open Backend Isle Isle.Interp Isle.Aarch64

/-! ## The abstract domain -/

/-- An abstract value: name sources `e` (external functions), `g` (symbol global values), `u`
(anything), offsets `i`, references `s`. -/
structure NA where
  e : Bool
  g : Bool
  u : Bool
  i : Bool
  s : Bool
  deriving DecidableEq, Repr, Inhabited

namespace NA
/-- Least upper bound. -/
def join (a b : NA) : NA := ⟨a.e || b.e, a.g || b.g, a.u || b.u, a.i && b.i, a.s && b.s⟩
/-- The order: more name sources, fewer guarantees. -/
def le (a b : NA) : Bool :=
  (!a.e || b.e) && (!a.g || b.g) && (!a.u || b.u) && (!b.i || a.i) && (!b.s || a.s)
/-- Anything. -/
def top : NA := ⟨true, true, true, false, false⟩
/-- No names, no integer leaf outside the offsets, no `MInst` (constants). -/
def c0 : NA := ⟨false, false, false, true, true⟩
/-- An integer constant: its integer leaf is an offset if it is `0`. -/
def cInt (ty : TypeId) (i : Int) : NA := ⟨false, false, false, normInt ty i == 0, true⟩
end NA

/-- The join of a list (`c0` for none). -/
def joinAll (as : List NA) : NA := as.foldl NA.join NA.c0

/-- Pointwise order of two lists of the same length. -/
def leAll : List NA → List NA → Bool
  | [], [] => true
  | a :: as, b :: bs => a.le b && leAll as bs
  | _, _ => false

/-! ## Transfer functions -/

/-- `func_ref_data`'s outputs: a signature, an external function's name, a distance, a flag. -/
def aFuncRef : NA := ⟨true, false, false, true, true⟩
/-- `symbol_value_data`'s outputs: a symbol's name, a distance, its offset. -/
def aSymbol : NA := ⟨false, true, false, true, true⟩
/-- Outputs without names or `MInst`s (any integers). -/
def aPlain : NA := ⟨false, false, false, false, true⟩

/-- The abstract outputs of extern extractor `id` (every output). -/
def aext (id : TermId) (_ : NA) : NA :=
  if id == TId.func_ref_data then aFuncRef
  else if id == TId.symbol_value_data then aSymbol
  else if (tyPred id).isSome || Flow.clean0Ext.contains id || Flow.valueExt.contains id ||
      id == TId.inst_data_value || id == TId.first_result then aPlain
  else NA.top

/-- The reference check of `MInst` variant `k` built from fields `as`. -/
def refChk (k : Nat) (as : List NA) : Bool :=
  if k == VIdx.MInst.Call || k == VIdx.MInst.CallInd then
    match as with
    | [ci] => !ci.g && !ci.u
    | _ => false
  else if k == VIdx.MInst.LoadExtNameGot then
    match as with
    | [_, nm] => !nm.u
    | _ => false
  else if k == VIdx.MInst.LoadExtNameNear then
    match as with
    | [_, nm, o] => !nm.u && o.i
    | _ => false
  else true

/-- Building variant `k` of type `ty`: the join of the fields; an `MInst` passes `refChk`. -/
def amk (ty : TypeId) (k : Nat) (as : List NA) : NA :=
  let j := joinAll as
  if ty == tyMInst then { j with s := j.s && refChk k as } else j

/-- Extern constructor `id`: the arguments' names and references, no offsets. -/
def actor (_ : TermId) (as : List NA) : NA := { joinAll as with i := false }

/-- The precondition of an extern constructor call: with `strict`, `emit` of a value with
`s` set. -/
def apre (strict : Bool) (id : TermId) (as : List NA) : Bool :=
  !strict || id != TId.emit || as.all (·.s)

/-- Summary table: per internal term, the abstract inputs and output. -/
abbrev Tab := List (TermId × List NA × NA)

/-- The table entry of `t`. -/
def tabGet (tab : Tab) (t : TermId) : Option (List NA × NA) :=
  (tab.find? (·.1 == t)).map (·.2)

/-! ## Abstract evaluation -/

section Eval
variable (p : Program) (tab : Tab) (strict : Bool)

mutual
/-- Bind the variables of `q`, matched against a value `a` describes. -/
def aPat (a : NA) : Pattern → List NA → List NA
  | .bind _ x sub, env => aPat a sub (env.set x a)
  | .and _ ps, env => aPatAll a ps env
  | .term _ t args, env =>
    match termOf p t with
    | .ok term =>
      match term.kind with
      | .enumVariant _ | .struct => aPatAll a args env
      | .decl _ _ (some (.external _ _)) => aPatAll (aext term.id a) args env
      | _ => env
    | .error _ => env
  | _, env => env
/-- `aPat` of every pattern of a list, with the same abstract value. -/
def aPatAll (a : NA) : List Pattern → List NA → List NA
  | [], env => env
  | q :: qs, env => aPatAll a qs (aPat a q env)
end

/-- Patterns against abstract values pointwise (`top` past the end). -/
def aPatArgs : List NA → List Pattern → List NA → List NA
  | a :: as, q :: qs, env => aPatArgs as qs (aPat p a q env)
  | [], q :: qs, env => aPatArgs [] qs (aPat p NA.top q env)
  | _, [], env => env

/-- Abstract application of term `t` (result type `ty`) to abstract arguments. -/
def aApply (ty : TypeId) (t : TermId) (as : List NA) : Option NA :=
  match termOf p t with
  | .ok term =>
    match term.kind with
    | .enumVariant k => some (amk ty k as)
    | .struct => some (amk ty 0 as)
    | .decl _ (some (.external _)) _ =>
      if apre strict term.id as then some (actor term.id as) else none
    | .decl _ (some .internal) _ =>
      match tabGet tab t with
      | some (ins, out) => if leAll as ins then some out else none
      | none => none
    | _ => some NA.top
  | .error _ => some NA.top

mutual
/-- Abstract value of an expression (`none`: a check failed). -/
def aExpr : Isle.Expr → List NA → Option NA
  | .var _ x, env => some (env.getD x NA.top)
  | .constBool .., _ | .constPrim .., _ => some NA.c0
  | .constInt ty i, _ => some (NA.cInt ty i)
  | .let _ bs body, env =>
    match aBinds bs env with
    | some env' => aExpr body env'
    | none => none
  | .term ty t args, env =>
    match aArgs args env with
    | some as => aApply p tab strict ty t as
    | none => none
/-- Abstract values of arguments. -/
def aArgs : List Isle.Expr → List NA → Option (List NA)
  | [], _ => some []
  | e :: es, env =>
    match aExpr e env, aArgs es env with
    | some a, some as => some (a :: as)
    | _, _ => none
/-- Abstract `let*` bindings. -/
def aBinds : List (VarId × TypeId × Isle.Expr) → List NA → Option (List NA)
  | [], env => some env
  | (x, _, e) :: bs, env =>
    match aExpr e env with
    | some a => aBinds bs (env.set x a)
    | none => none
end

/-- Abstract if-lets. -/
def aIfLets : List IfLet → List NA → Option (List NA)
  | [], env => some env
  | il :: ils, env =>
    match aExpr p tab strict il.rhs env with
    | some a => aIfLets ils (aPat p a il.lhs env)
    | none => none

/-- The abstract environment after a rule's match phase. -/
def aRuleEnv (ins : List NA) (r : Rule) : Option (List NA) :=
  aIfLets p tab strict r.iflets (aPatArgs p ins r.args (List.replicate r.vars.length NA.top))

/-- Rule `r` checks with inputs `ins` and output `out`. -/
def aRule (ins : List NA) (out : NA) (r : Rule) : Bool :=
  match aRuleEnv p tab strict ins r with
  | some env =>
    match aExpr p tab strict r.rhs env with
    | some a => a.le out
    | none => false
  | none => false

/-- Every rule of every table term checks. -/
def chkTab : Bool :=
  tab.all fun e => (p.rulesOf e.1).all (aRule p tab strict e.2.1 e.2.2)

end Eval

/-! ## The model the soundness proof needs -/

section Model
variable {V σ : Type} (sem : Sem V σ)

/-- Abstract values describe values pointwise (same lengths). -/
def Holds2 (γ : NA → σ → V → Prop) (s : σ) : List NA → List V → Prop
  | [], [] => True
  | a :: as, v :: vs => γ a s v ∧ Holds2 γ s as vs
  | _, _ => False

/-- The abstract environment describes the bound variables (`top` past its end). -/
def EnvOK (γ : NA → σ → V → Prop) (s : σ) (aenv : List NA) (env : Isle.Interp.Env V) : Prop :=
  ∀ x w, env[x]? = some (some w) → γ (aenv.getD x NA.top) s w

/-- The meaning of the abstract values and the facts the soundness proof needs about the
embedding: `γ a s v` (in state `s`), a state invariant `Is`, a preorder `Rs` along runs. -/
structure Model (strict : Bool) where
  γ : NA → σ → V → Prop
  Is : σ → Prop
  Rs : σ → σ → Prop
  rs_refl : ∀ s, Rs s s
  rs_trans : ∀ a b c, Rs a b → Rs b c → Rs a c
  rs_ctor : ∀ term vs s v s', sem.ctor term vs s = .ok (v, s') → Rs s s'
  top : ∀ s v, γ NA.top s v
  le : ∀ a b s v, a.le b = true → γ a s v → γ b s v
  mono : ∀ a s s' v, Rs s s' → γ a s v → γ a s' v
  int : ∀ s ty i, γ (NA.cInt ty i) s (sem.int ty i)
  bool : ∀ s b, γ NA.c0 s (sem.bool b)
  prim : ∀ s ty n c, sem.prim ty n = some c → γ NA.c0 s c
  mkd : ∀ s ty k as vs, Holds2 γ s as vs → γ (amk ty k as) s (sem.mkData ty k vs)
  un : ∀ s a ty v k fs, γ a s v → sem.unData ty v = some (k, fs) → ∀ f ∈ fs, γ a s f
  ext : ∀ s a term v fs, γ a s v → sem.extract term v s = .ok fs → ∀ f ∈ fs, γ (aext term.id a) s f
  ctor : ∀ s as vs term v s', Holds2 γ s as vs → Is s → apre strict term.id as = true →
    sem.ctor term vs s = .ok (v, s') → γ (actor term.id as) s' v ∧ Is s'

end Model

end Backend.Proof.RelocProv
