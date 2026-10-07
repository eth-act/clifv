import Crates.AArith.Input
import FV.Link.Correct

/-! # Non-vacuity of the Lean linker's theorems (L2b) on a survey crate

`Link.leanLink` succeeds on `a_arith`'s 58 functions (`Crates.AArith.input`) placed at 16 MiB,
with the outside part's addresses of rust-lld's link and an executable whose outside part is
reduced to the region's placeholder (`placeholder`: a static ELF with one read-only executable
`PT_LOAD` segment of zeros at the region). So `Link.crate_correct_leanLink` (the crate theorem
without `linkerOkB`) and `Link.leanLink_code` (`ArtOk` of every function in the linked file)
have instances: `link_ok` and `inScope` by `native_decide` (`fvcheck` holds the compiled code of
`FV.Link.Image`). The `cargo fv --lean-link` executables of `a_arith` are linked by the same
definition (`lake exe lean-link`, docs/research/lean-linker.md). -/

namespace Crates.LeanLinkWitness

open E2E E2E.LinkCheck Link

/-- `a_arith`'s program for the Lean linker: its functions placed at 16 MiB, the other names
at rust-lld's addresses. -/
def spec : LinkSpec :=
  let I := Crates.AArith.input
  let names := I.funcs.map (·.func.name)
  { funcs := I.funcs, outside := I.addrs.filter (fun p => !names.contains p.1),
    symNames := I.syms.map (·.1), R := 0x1000000 }

/-- The `w` little-endian bytes of `v`. -/
def le (v w : Nat) : List UInt8 := (List.range w).map fun i => UInt8.ofNat (v >>> (8 * i))

/-- A static AArch64 executable with one read-only executable `PT_LOAD` segment: `n` zero bytes
at address `R`, file offset 4096. -/
def placeholder (R n : Nat) : ByteArray :=
  let ident : List UInt8 := [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1] ++ List.replicate 9 0
  let ehdr := ident ++ le 2 2 ++ le 183 2 ++ le 1 4 ++ le R 8 ++ le 64 8 ++ le 0 8 ++ le 0 4 ++
    le 64 2 ++ le 56 2 ++ le 1 2 ++ le 64 2 ++ le 0 2 ++ le 0 2
  let phdr := le 1 4 ++ le 5 4 ++ le 4096 8 ++ le R 8 ++ le R 8 ++ le n 8 ++ le n 8 ++ le 65536 8
  ⟨(ehdr ++ phdr ++ List.replicate (4096 - 120) 0 ++ List.replicate n 0).toArray⟩

/-- The executable before the Lean linker. -/
def file0 : ByteArray := placeholder spec.R spec.size

/-- **The Lean linker links `a_arith`.** -/
theorem link_ok : (leanLink spec file0).toBool = true := by native_decide

/-- The linked executable. -/
def file : ByteArray := getOk (leanLink spec file0)

theorem link_eq : leanLink spec file0 = .ok file := getOk_eq link_ok

/-- The input conditions of the placed program. -/
theorem inScope : InScopeP spec.input = true := by native_decide

/-- **`backend_correct_program` for every function of `a_arith` linked by the Lean linker**:
no `okB`, no `linkerOkB` premise. -/
theorem crate_correct (hD : SpillDefinedHyp) (n : String) : CrateStmtT spec.input n :=
  crate_correct_leanLink hD inScope link_eq n

/-- Every function's code is in the linked file, relocated (`ArtOk`), by construction. -/
theorem code : ∀ e ∈ tabOf spec.input.resultsT, BinCheck.ArtOk spec.input file e.2 :=
  leanLink_code link_eq

/-- `crate_correct` under definite assignment of `lowerFunction`'s VCode. -/
theorem crate_correct_lower (hM : LowerDefinedHyp) (n : String) : CrateStmtT spec.input n :=
  crate_correct_leanLink_lower hM inScope link_eq n

end Crates.LeanLinkWitness
