import Corpus.All
import Corpus.Emit

/-! The emitter's differential-testing corpus: `Corpus.all` plus the emitter-owned additions
`Corpus.emitTests` (`corpus/dsl/Corpus/Emit.lean`). -/

namespace FVTest.Compile

def cases : List DSL.TestCase := Corpus.all ++ Corpus.emitTests

end FVTest.Compile
