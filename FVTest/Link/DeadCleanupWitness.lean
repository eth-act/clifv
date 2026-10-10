import FV.Link.DeadCleanupExe
import FV.Link.DeadCleanupExeTotal

/-! Closed executable witness: the baseline and cleanup pipelines both link the
same nonempty source. Only the pure unused producer is removed. -/
namespace E2E.DeadCleanupExecutableWitness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend

def le (v w : Nat) : List UInt8 := (List.range w).map fun i => UInt8.ofNat (v >>> (8 * i))

/-- The string table of `ns` (a leading NUL, each name NUL-terminated) and each name's offset. -/
def strtab (ns : List String) : List UInt8 × List Nat :=
  ns.foldl (fun (t, os) n => (t ++ n.toUTF8.toList ++ [0], os ++ [t.length])) ([0], [])

/-- A static AArch64 executable with one read-only executable `PT_LOAD` segment, `n` zero bytes
at address `R` (file offset 4096), and a symbol table with the symbols `syms` (section index
`SHN_ABS`). -/
def placeholder (R n : Nat) (syms : List (String × Nat)) : ByteArray :=
  let (st, os) := strtab (syms.map (·.1))
  let symtab := List.replicate 24 0 ++ (syms.zip os).flatMap fun ((_, v), o) =>
    le o 4 ++ [0x10, 0] ++ le 0xfff1 2 ++ le v 8 ++ le 0 8
  let symOff := 4096 + n
  let strOff := symOff + symtab.length
  let shOff := strOff + st.length
  let shdr (ty off size link ent : Nat) : List UInt8 :=
    le 0 4 ++ le ty 4 ++ le 0 8 ++ le 0 8 ++ le off 8 ++ le size 8 ++ le link 4 ++ le 0 4 ++
      le 8 8 ++ le ent 8
  let ident : List UInt8 := [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1] ++ List.replicate 9 0
  let ehdr := ident ++ le 2 2 ++ le 183 2 ++ le 1 4 ++ le R 8 ++ le 64 8 ++ le shOff 8 ++ le 0 4 ++
    le 64 2 ++ le 56 2 ++ le 1 2 ++ le 64 2 ++ le 3 2 ++ le 0 2
  let phdr := le 1 4 ++ le 5 4 ++ le 4096 8 ++ le R 8 ++ le R 8 ++ le n 8 ++ le n 8 ++ le 65536 8
  ⟨(ehdr ++ phdr ++ List.replicate (4096 - 120) 0 ++ List.replicate n 0 ++ symtab ++ st ++
    List.replicate 64 0 ++ shdr 2 symOff symtab.length 2 24 ++ shdr 3 strOff st.length 0 0).toArray⟩


def fixture : FnInput :=
  { clif := "function %cleanup_unused() {\nblock0:\n v0 = iconst.i64 17\n return\n}\n", ra := "{}" }

def spec : LinkSpec :=
  { funcs := [fixture], names := [fixture.func.name],
    sizes := [(getOk (pipeCleanupT fixture.func fixture.k 0 (raJ fixture.ra fixture.j))).fb.words.size],
    outside := [], symNames := [], R := 0x1000000 }

def baselineSpec : LinkSpec :=
  { spec with sizes := [(getOk (pipeT fixture.func fixture.k 0 (raJ fixture.ra fixture.j))).fb.words.size] }

def file0 : ByteArray :=
  placeholder spec.R spec.size (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

def baselineFile0 : ByteArray :=
  placeholder baselineSpec.R baselineSpec.size
    (baselineSpec.addrs.map fun p => (BinCheck.symName p.1, p.2))

def checks : Bool :=
  (Link.compileExe baselineSpec baselineFile0).toBool &&
  (Link.DeadCleanup.compileExe spec file0).toBool &&
  decide (spec.sizes.sum < baselineSpec.sizes.sum)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Both actual executable compilations succeed and cleanup removes machine words. -/
theorem checks_true : checks = true := by native_decide

def file : ByteArray := getOk (Link.DeadCleanup.compileExe spec file0)

theorem compile_eq : Link.DeadCleanup.compileExe spec file0 = .ok file :=
by
  have h := checks_true
  simp only [checks, Bool.and_eq_true] at h
  exact getOk_eq h.1.2

theorem binary_checked : E2E.DeadCleanupBinCheck.BinOk spec.inputCleanup spec.data file :=
  Link.DeadCleanup.binOk_leanLink (Link.DeadCleanup.compileExe_spec compile_eq).2

end E2E.DeadCleanupExecutableWitness
