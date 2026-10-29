module

public import Corpus.Arith
public import Corpus.Vectors
public import Corpus.Errors
public import Corpus.Calls
public import Corpus.Maps
public import Corpus.Big
public import Corpus.Proofs

@[expose] public section

/-! The differential-testing corpus: every program with its test vectors. -/

namespace Corpus

/-- All corpus programs with `(args, expected)` vectors; see `docs/contracts/dsl.md`. -/
def all : List DSL.TestCase :=
  arithTests ++ vectorTests ++ errorTests ++ callTests ++ mapTests ++ bigTests

#guard all.all DSL.TestCase.passes
#guard all.length = 31
#guard (all.map (·.vectors.length)).sum = 79
#guard (all.map DSL.TestCase.errorVectors).sum = 30
#guard all.all fun tc => tc.fn.checkB

end Corpus
