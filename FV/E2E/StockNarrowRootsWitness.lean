import FV.E2E.StockNarrowWitness
import FV.E2E.StockAluRootsWitness

namespace E2E.StockNarrowRootsWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0 E2E.StockNarrowNIWitness
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- A narrow rotation whose amount is an original constant rather than a parameter. -/
def immediateFunction (config : Configuration) (ty : Clif.Ty) (op : Clif.BinaryOp) : Clif.Function :=
  let old := function config ⟨s!"immediate_{repr op}",ty,.binary op ty 1 8⟩
  {old with blocks := old.blocks.map fun b =>
    {b with body := [⟨[99],.iconst ty (BitVec.ofNat ty.width 3)⟩,⟨[100],.binary op ty 1 99⟩]}}

private def unary (op : Clif.UnaryOp) (ty : Clif.Ty) (config : Configuration) : Clif.Function :=
  function config ⟨s!"unary_{repr op}",ty,.unary op ty 1⟩

private def binary (op : Clif.BinaryOp) (ty : Clif.Ty) (config : Configuration) : Clif.Function :=
  function config ⟨s!"binary_{repr op}",ty,.binary op ty 1 8⟩

/-- Each narrow rotate/bit-count/bit-reverse/byte-swap root with one function that selects it. -/
def roots : List (Nat × (Configuration → Clif.Function)) :=
  [(899,binary .rotl .i8),(906,binary .rotr .i16),
   (900,fun config => immediateFunction config .i8 .rotl),
   (909,fun config => immediateFunction config .i16 .rotr),
   (915,unary .bitrev .i8),(916,unary .bitrev .i16),
   (919,unary .clz .i8),(920,unary .clz .i16),
   (924,unary .ctz .i8),(925,unary .ctz .i16),
   (932,unary .bswap .i16)]

def selected (id : Nat) (f : Clif.Function) : Bool :=
  match Stock.lower f with
  | .error _ => false
  | .ok result => (E2E.StockHighMulNIWitness.selectedRoots result).contains id

private def grid : Bool :=
  conventions.all fun config => roots.all fun (id,mk) =>
    checks (mk config) false && checks (mk config) true && selected id (mk config)

-- witness: native_decide (eleven fixed narrow functions in three conventions only)
theorem grid_true : grid = true := by native_decide

private theorem entry {config : Configuration} (hc : config ∈ conventions)
    {id : Nat} {mk : Configuration → Clif.Function} (member : (id,mk) ∈ roots) :
    checks (mk config) false = true ∧ checks (mk config) true = true ∧ selected id (mk config) = true := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp grid_true config hc) (id,mk) member
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1,h.1.2,h.2⟩

/-- Every listed narrow function inhabits the complete checked scalar pipeline. -/
theorem compiled_exists {config : Configuration} (hc : config ∈ conventions)
    {id : Nat} {mk : Configuration → Clif.Function} (member : (id,mk) ∈ roots) (cleanup : Bool) :
    Stock.Scalar.Domain (mk config) ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage (mk config) cleanup 0 result vcp rf af fa fb ∧
      CompiledSemanticNI (mk config) 0 result.code vcp rf af fa fb ∧
      Stock.Scalar.lowerValidated (mk config) = .ok result.code ∧
      DivBoundary.check (mk config).sig result.code = true ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp := by
  have h := entry hc member
  apply compiled_of_checks
  cases cleanup with
  | false => exact h.1
  | true => exact h.2.1

/-- The same production-class function actually selects its listed root. -/
theorem selected_roots_present {config : Configuration} (hc : config ∈ conventions)
    {id : Nat} {mk : Configuration → Clif.Function} (member : (id,mk) ∈ roots) :
    ∃ result, Stock.lower (mk config) = .ok result ∧
      id ∈ E2E.StockHighMulNIWitness.selectedRoots result := by
  have h := (entry hc member).2.2
  unfold selected at h
  cases lowered : Stock.lower (mk config) with
  | error message => simp [lowered] at h
  | ok result =>
    simp only [lowered] at h
    exact ⟨result,rfl,List.contains_iff_mem.mp h⟩
end E2E.StockNarrowRootsWitness

namespace E2E.StockNarrowRootsWitness
/-- The original select and return roots, selected in the ALU roots function. -/
def controlRoots : List Nat := [971,1037]

private def controlChecks (config : Backend.Stock.D0.Configuration) : Bool :=
  controlRoots.all fun id => selected id (E2E.StockAluRootsWitness.function config)

-- witness: native_decide (six fixed actual source/provenance checks only)
theorem control_checks_true : Backend.Stock.D0.configurations.all controlChecks = true := by native_decide

/-- Every ABI selects the select and return roots in a function that inhabits `Scalar.Domain`
(`E2E.StockAluRootsWitness.compiled_exists`). -/
theorem control_roots_present (config : Backend.Stock.D0.Configuration) :
    ∃ result, Backend.Stock.lower (E2E.StockAluRootsWitness.function config) = .ok result ∧
      ∀ id ∈ controlRoots, id ∈ E2E.StockHighMulNIWitness.selectedRoots result := by
  have h := List.all_eq_true.mp control_checks_true config
    (by cases config <;> simp [Backend.Stock.D0.configurations])
  cases lowered : Backend.Stock.lower (E2E.StockAluRootsWitness.function config) with
  | error message =>
    simp only [controlChecks,controlRoots,selected,lowered,List.all_cons,List.all_nil] at h
    cases h
  | ok result =>
    refine ⟨result,rfl,?_⟩
    intro id member
    have one := List.all_eq_true.mp h id member
    simp only [selected,lowered] at one
    exact List.contains_iff_mem.mp one
end E2E.StockNarrowRootsWitness
