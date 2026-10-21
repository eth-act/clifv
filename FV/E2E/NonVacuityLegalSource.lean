import FV.E2E.LegalSource

/-! # Non-vacuity of the source domain `SrcScopeB` (S2)

Inputs given by CLIF text (the parser runs, so the facts are decided by `native_decide`; the
kernel does not evaluate the parser's hash maps):

* `mixed`: `plain(i64) -> i64` (no `i128`: the legalisation is the identity) and
  `add128(i128, i128) -> i128` (legalised): in the source domain, and its compiled program is
  not its source program (`mixed_prog_ne`: the legalisation changed `add128`), while
  `LinkInput.prog_eq` relates them.
* Outside the domain, each for one conjunct: a `return_call` (`linkFreeB`), a function named like
  a `__*ti3` helper (`helperFreeB`), an `i128` indirect call (`legalOkB`: `Pre` fails), a
  declaration of a program function with another signature (`declSigB`).
-/

namespace E2E.LinkCheck.SrcScopeWitness

open E2E.LinkCheck Opt.Legalize128 E2E.LegalProgram

def plainT : String := "function %plain(i64) -> i64 {\nblock0(v0: i64):\n    return v0\n}\n"

def add128T : String :=
  "function %add128(i128, i128) -> i128 {\nblock0(v0: i128, v1: i128):\n    v2 = iadd v0, v1\n    return v2\n}\n"

def rcT : String :=
  "function %rc(i64) -> i64 {\n    fn0 = %plain(i64) -> i64\nblock0(v0: i64):\n    return_call fn0(v0)\n}\n"

def helperT : String := "function %__udivti3(i64) -> i64 {\nblock0(v0: i64):\n    return v0\n}\n"

def indT : String :=
  "function %ind(i64, i128) -> i128 {\n    sig0 = (i128) -> i128\nblock0(v0: i64, v1: i128):\n    v2 = call_indirect sig0, v0(v1)\n    return v2\n}\n"

def declT : String :=
  "function %caller(i64) -> i64 {\n    fn0 = %plain(i32) -> i32\nblock0(v0: i64):\n    v1 = ireduce.i32 v0\n    v2 = call fn0(v1)\n    v3 = uextend.i64 v2\n    return v3\n}\n"

/-- An input of one file per function (no oracle answers: `SrcScopeB` reads the CLIF only). -/
def mk (ts : List String) : LinkInput :=
  { funcs := ts.map fun t => { clif := t, ra := "" }, addrs := [], syms := [], raStar := 0, D := 0 }

def mixed : LinkInput := mk [plainT, add128T]

/-- **The identity-mixed input is in the source domain.** -/
theorem mixed_in : SrcScopeB mixed = true := by native_decide

/-- Its source mentions `i128`. -/
theorem mixed_mentions : mixed.srcProg.funcs.any mentions128 = true := by native_decide

/-- The compiled program is not the source program (the legalisation changed `add128`). -/
theorem mixed_prog_ne : mixed.prog ≠ mixed.srcProg := by
  rw [LinkInput.prog_eq]
  intro h
  have : (legalProg mixed.srcProg).funcs = mixed.srcProg.funcs := congrArg (·.funcs) h
  have hb : ((legalProg mixed.srcProg).funcs == mixed.srcProg.funcs) = false := by native_decide
  exact absurd this (by simpa using hb)

/-- A `return_call`: outside the domain (`linkFreeB`). -/
theorem returnCall_out : SrcScopeB (mk [plainT, rcT]) = false ∧
    (mk [plainT, rcT]).srcProg.funcs.all linkFreeB = false := by native_decide

/-- A function named `__udivti3`: outside the domain (`helperFreeB`). -/
theorem helperName_out : SrcScopeB (mk [plainT, helperT]) = false ∧
    helperFreeB (mk [plainT, helperT]).srcProg = false := by native_decide

/-- An `i128` indirect call: outside the domain (`legalOkB`, `Pre` fails). -/
theorem indI128_out : SrcScopeB (mk [indT]) = false ∧
    (mk [indT]).srcProg.funcs.all legalOkB = false := by native_decide

/-- A declaration of `plain` with another signature: outside the domain (`declSigB`). -/
theorem declSig_out : SrcScopeB (mk [plainT, declT]) = false ∧
    (mk [plainT, declT]).srcProg.funcs.all (declSigB (mk [plainT, declT]).srcProg) = false := by
  native_decide

end E2E.LinkCheck.SrcScopeWitness
