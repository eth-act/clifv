import FV.Isle

/-!
# The emitter-subset closure (`Isle.Aarch64.Closure`), cross-checked in Lean

The Rust exporter computes the closure; these checks recompute its defining properties from
the exported rules with independent Lean code:

* entries agree with the program (ids, names, extern flags, spec presence);
* it is closed: every internal-constructor term mentioned by a closure rule has all of its rules
  in the closure;
* every E opcode is handled by at least one root rule of the closure;
* excluded root rules really mention a non-E opcode, a non-`i8..i64` type constant or a
  vector/float type extractor in their main pattern.
-/

namespace Isle.Test.Closure
open Isle Isle.Aarch64

mutual
def patTerms : Pattern → List TermId
  | .bind _ _ p => patTerms p
  | .term _ t ps => t :: patsTerms ps
  | .and _ ps => patsTerms ps
  | _ => []
def patsTerms : List Pattern → List TermId
  | [] => []
  | p :: ps => patTerms p ++ patsTerms ps
end

mutual
def patConsts : Pattern → List String
  | .bind _ _ p => patConsts p
  | .term _ _ ps => patsConsts ps
  | .and _ ps => patsConsts ps
  | .constPrim _ n => [n]
  | _ => []
def patsConsts : List Pattern → List String
  | [] => []
  | p :: ps => patConsts p ++ patsConsts ps
end

mutual
def exprTerms : Expr → List TermId
  | .term _ t es => t :: exprsTerms es
  | .let _ bs body => bindsTerms bs ++ exprTerms body
  | _ => []
def exprsTerms : List Expr → List TermId
  | [] => []
  | e :: es => exprTerms e ++ exprsTerms es
def bindsTerms : List (VarId × TypeId × Expr) → List TermId
  | [] => []
  | (_, _, e) :: bs => exprTerms e ++ bindsTerms bs
end

def ruleTerms (r : Rule) : List TermId :=
  patsTerms r.args ++ (r.iflets.flatMap fun il => patTerms il.lhs ++ exprTerms il.rhs) ++
    exprTerms r.rhs

def inClosure (r : RuleId) : Bool := Closure.rules.any (·.rule == r)

-- Entries agree with the program.
#guard Closure.rules.all fun c =>
  (program.rule? c.rule).any fun r =>
    r.name == c.name && r.term == c.term &&
      c.isRoot == Closure.roots.contains (program.termName r.term)
#guard Closure.terms.all fun c =>
  (program.term? c.term).any fun t =>
    t.name == c.name && t.externCtor? == c.externCtor &&
      t.externExtractor? == c.externExtractor && c.hasSpec == !(program.specsOf t.id).isEmpty

-- Closed under term dependencies, and every mentioned term is listed.
#guard Closure.rules.all fun c =>
  (program.rule? c.rule).any fun r =>
    (ruleTerms r).all fun t =>
      Closure.terms.any (·.term == t) &&
        (!((program.term? t).any (·.hasInternalCtor)) ||
          (program.rulesOf t).all fun r' => inClosure r'.id)

-- Every E opcode is matched by some root rule of the closure.
def camel (op : String) : String :=
  "".intercalate ((op.splitOn "_").map String.capitalize)

#guard Closure.opcodes.all fun op =>
  Closure.rules.any fun c => c.isRoot &&
    (program.rule? c.rule).any fun r =>
      (patsTerms r.args).any fun t => program.termName t == s!"Opcode.{camel op}"

-- Excluded root rules: each reason is present in the rule's main pattern.
#guard Closure.excludedRootRules.all fun (n, why) =>
  !why.isEmpty && (program.ruleByName? n).any fun r =>
    let names := (patsTerms r.args).map program.termName
    why.all fun w => names.contains w || (patsConsts r.args).contains w

-- Root rules partition into closure roots and excluded roots.
#guard ((Closure.roots.filterMap program.termByName?).map fun t =>
  (program.rulesOf t.id).length).sum ==
    (Closure.rules.filter (·.isRoot)).size + Closure.excludedRootRules.size

end Isle.Test.Closure
