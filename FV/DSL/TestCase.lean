import FV.DSL.Denote

/-!
# Differential-testing vectors

`DSL.TestCase` packages a function with input/expected-output vectors. The corpus exports
`Corpus.all : List DSL.TestCase`; the emitter's differential tests (M1) run each vector through
`denote`, `Clif.run`, the Cranelift interpreter and native code and compare with `expected`.
-/

namespace DSL

/-- A typed value (for generic traversal of arguments and results). -/
abbrev Value := (t : Ty) × t.denote

/-- Arguments as a list of typed values, first parameter first. -/
def Env.values : (σ : List Ty) → Env σ → List Value
  | [], _ => []
  | t :: σ, (x, xs) => ⟨t, x⟩ :: Env.values σ xs

instance instReprEnv : (σ : List Ty) → Repr (Env σ)
  | [] => ⟨fun _ _ => "()"⟩
  | _ :: σ => ⟨fun (x, xs) _ => repr x ++ ", " ++ (instReprEnv σ).reprPrec xs 0⟩

structure TestVector (σ : List Ty) (τ : Ty) where
  args : Args σ
  expected : M τ.denote

structure TestCase where
  σ : List Ty
  τ : Ty
  fn : FlatFn σ τ
  vectors : List (TestVector σ τ)

/-- Build a test case; `vs` are `(args, expected)` pairs. -/
def TestCase.mk' {σ : List Ty} {τ : Ty} (fn : FlatFn σ τ) (vs : List (Args σ × M τ.denote)) :
    TestCase :=
  ⟨σ, τ, fn, vs.map fun (a, e) => ⟨a, e⟩⟩

/-- Every vector agrees with `denote`. -/
def TestCase.passes (tc : TestCase) : Bool :=
  tc.vectors.all fun v => decide (denote tc.fn v.args = v.expected)

/-- Number of vectors that end in `throw`. -/
def TestCase.errorVectors (tc : TestCase) : Nat :=
  (tc.vectors.filter fun v => match v.expected with | .error _ => true | .ok _ => false).length

end DSL
