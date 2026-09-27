import FV.Isle.Syntax

/-!
# Printing exported rules back to ISLE text

`Isle.Program.ruleText p r` renders a rule in ISLE surface syntax. It prints the analysed form:
internal extractors appear expanded and implicit converters appear as explicit terms, so it
reproduces the source text exactly only for rules that use neither (see
`FVTest/Isle/Pretty.lean`). `Isle.normalizeIsle` removes comments and normalises whitespace for
comparisons.
-/

namespace Isle

namespace Program

variable (p : Program)

private def varName (vars : List (String × TypeId)) (x : VarId) : String :=
  match vars[x]? with
  | some (n, _) => n
  | none => s!"v{x}"

private def paren (head : String) (args : List String) : String :=
  "(" ++ " ".intercalate (head :: args) ++ ")"

def patText (vars : List (String × TypeId)) : Pattern → String
  | .bind _ x (.wildcard _) => varName vars x
  | .bind _ x sub => varName vars x ++ " @ " ++ patText vars sub
  | .var _ x => varName vars x
  | .constBool _ b => if b then "true" else "false"
  | .constInt _ i => toString i
  | .constPrim _ n => "$" ++ n
  | .term _ t args => paren (p.termName t) (args.map (patText vars))
  | .wildcard _ => "_"
  | .and _ ps => paren "and" (ps.map (patText vars))

mutual
def exprText (vars : List (String × TypeId)) : Expr → String
  | .term _ t args => paren (p.termName t) (exprsText vars args)
  | .var _ x => varName vars x
  | .constBool _ b => if b then "true" else "false"
  | .constInt _ i => toString i
  | .constPrim _ n => "$" ++ n
  | .let _ binds body =>
    paren "let" ["(" ++ " ".intercalate (bindsText vars binds) ++ ")", exprText vars body]
def exprsText (vars : List (String × TypeId)) : List Expr → List String
  | [] => []
  | e :: es => exprText vars e :: exprsText vars es
def bindsText (vars : List (String × TypeId)) : List (VarId × TypeId × Expr) → List String
  | [] => []
  | (x, ty, e) :: bs => paren (varName vars x) [p.typeName ty, exprText vars e] :: bindsText vars bs
end

def ifLetText (vars : List (String × TypeId)) (il : IfLet) : String :=
  match il.lhs with
  | .wildcard _ => paren "if" [p.exprText vars il.rhs]
  | lhs => paren "if-let" [p.patText vars lhs, p.exprText vars il.rhs]

/-- ISLE text of a rule: `(rule [name] [prio] (term args..) iflets.. rhs)`. -/
def ruleText (r : Rule) : String :=
  let name := if r.explicitName then r.isleName.toList else []
  let prio := if r.prio == 0 then [] else [toString r.prio]
  let lhs := paren (p.termName r.term) (r.args.map (p.patText r.vars))
  paren "rule" (name ++ prio ++ [lhs] ++ r.iflets.map (p.ifLetText r.vars) ++
    [p.exprText r.vars r.rhs])

end Program

/-- Drop `;` comments and normalise whitespace: runs of whitespace become one space, and no
space follows `(` or precedes `)`. -/
def normalizeIsle (s : String) : String :=
  let noComments := "\n".intercalate (s.splitOn "\n" |>.map fun l => (l.splitOn ";").headD "")
  let ws (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'
  -- Collapse whitespace runs into single spaces, dropping leading/trailing whitespace.
  let (acc, _) := noComments.toList.foldl
    (fun (acc, pendingSpace) c =>
      if ws c then (acc, !acc.isEmpty)
      else ((if pendingSpace then acc.push ' ' else acc).push c, false))
    ((#[] : Array Char), false)
  let joined := String.ofList acc.toList
  (joined.replace "( " "(").replace " )" ")"

end Isle
