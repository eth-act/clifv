import FV.Link.SemanticExeWith
import FV.Backend.Lowering.StockMixedNI
import FV.Clif.Print
import FV.E2E.StockProductionFixtures
import FV.Link.Ld.Plan

namespace E2E.SemanticMixedCompilerWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0 E2E.LinkCheck Link
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

def initial (config : Configuration) : LinkSpec := {
  funcs := [{clif := (StockMixedNIWitness.function config).print,ra := "null"}]
  names := []
  sizes := []
  outside := []
  symNames := ["stock_mixed_ni"]
  R := 0x200160 }

def spec (config : Configuration) (cleanup : Bool) : LinkSpec :=
  (initial config).placedProductionWith Stock.Mixed.lowerValidated cleanup

def plan (S : LinkSpec) : Link.Ld.Plan :=
  let size := 0x160 + S.size
  {base := 0x200000,entry := S.R,
   segs := [{kind := 1,vaddr := 0x200000,offset := 0,filesz := size,memsz := size}],
   tlsAddr := 0x200000+size,tlsOff := size,tlsFilesz := 0,tlsMemsz := 0,tlsAlign := 1,
   ehOff := 0,ehAddr := 0,ehSize := 0,size,pieces := [],secs := #[],
   syms := S.addrs.toArray.map fun (n,v) => {name := E2E.BinCheck.symName n,value := v,info := 18,shndx := 0xfff1}}

def file0 (config : Configuration) (cleanup : Bool) : ByteArray :=
  match Link.Ld.assemble (plan (spec config cleanup)) with | .ok image => image.write | .error _ => ByteArray.empty

def input (config : Configuration) (cleanup : Bool) : SemanticStackBound.CompilerInput :=
  SemanticCompilerWith.input Stock.Mixed.lowerValidated (spec config cleanup) cleanup

def attempt (config : Configuration) (cleanup : Bool) : Except String ByteArray :=
  SemanticCompilerWith.attempt Stock.Mixed.lowerValidated (spec config cleanup) (file0 config cleanup) cleanup

private def checks (config : Configuration) (cleanup : Bool) : Bool :=
  (attempt config cleanup).isOk && SemanticStackBound.okB (input config cleanup) &&
  (input config cleanup).results.all fun row =>
    match row.2 with
    | .error _ => false
    | .ok a => !lowerCheck row.1 a.vc

private def grid : Bool := configurations.all fun config => checks config false && checks config true

/-- Fixed compiler-data witness only: the real ELF byte writer and complete
semantic program checker succeed for every ABI/cleanup combination, using raw
Stock code beyond the old checker rather than taking legacy fallback. -/
theorem checks_true : grid = true := by native_decide

/-- The executable compiler succeeds jointly with the whole-program semantic
checker; the retained old validator rejects every actual program artifact. -/
theorem compiler_success (config : Configuration) (cleanup : Bool) :
    ∃ file, attempt config cleanup = .ok file ∧
      SemanticStackBound.okB (input config cleanup) = true ∧
      ((input config cleanup).results.all fun row => match row.2 with
        | .error _ => false
        | .ok a => !lowerCheck row.1 a.vc) = true := by
  have h : checks config cleanup = true := by
    have both := List.all_eq_true.mp checks_true config
      (by cases config <;> simp [configurations])
    simp only [Bool.and_eq_true] at both
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  simp only [checks,Bool.and_eq_true] at h
  cases compiled : attempt config cleanup with
  | error message =>
    have impossible := h.1.1
    simp only [compiled,Except.isOk,Except.toBool] at impossible
    cases impossible
  | ok file => exact ⟨file,rfl,h.1.2,h.2⟩

end E2E.SemanticMixedCompilerWitness
