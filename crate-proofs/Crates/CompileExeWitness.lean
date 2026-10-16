import Crates.LeanLinkWitness
import FV.Link.Exe
import FV.Link.ExeTotal
import FV.Link.ExeInput
import FV.Link.ExeInputCleanup

/-! # Non-vacuity of the executable compiler's theorems (L1) on a survey crate

`Link.compileExe` succeeds on `a_arith`'s 58 functions (`Crates.LeanLinkWitness.spec`, with the
placeholder executable `file0`): `compile_eq`. `compileExe_correct`'s per-program premises are
then all discharged inside the theorem; its remaining premises are instantiated here for the
closed base environment (`BaseOk`, `HooksSim`) and a function of the program with no reachable
call cycle (`entry`): `correct_closed` leaves only the per-run premises of an outside call (the
boundary contract, the reference CLIF run, `TrapsExplicit`, the loader's image), which
`Crates.BinaryExecWitness` shows satisfiable for the panic=abort build of `a_arith`.
`total_witness`: every hypothesis of `compileExe_total` holds on this input.
`total_input_witness`: every hypothesis of `compileExe_total_input` holds on this input with the
Lean compiler's layout (`spec.placed`) and an executable with a `PT_TLS` segment (`file0T`);
`total_input_cleanup_witness`: the same for the shipped compiler (`DeadCleanup.compileExe`).
-/

namespace Crates.CompileExeWitness

open E2E E2E.LinkCheck E2E.Binary E2E.ExecBytes Link Crates.LeanLinkWitness

/-- **The executable compiler compiles `a_arith`.** -/
theorem compile_eq : compileExe spec file0 = .ok file := by
  have h : InScopeIn spec.input0 = true := by native_decide
  simp only [compileExe, inScopeInPar_eq, h, ↓reduceIte, link_eq]

/-- No function of the program uses TLS (the closed base environment has none). -/
theorem noTls : (progOf spec.input.results).funcs.all (fun g => !Backend.hasTls g) = true := by
  native_decide

/-- The closed base environment's premises. -/
theorem base_closed : BaseOk (sys spec.input closedBase) :=
  baseOk_closedR fun g hg => by simpa using List.all_eq_true.1 noTls g hg

/-- A function of the program from which no call cycle is reachable. -/
def n : String := (spec.names.find? fun m => StackBound.goodN spec.input m).getD ""

theorem good : StackBound.goodN spec.input n = true := by native_decide

theorem entry : ∃ f, (prog spec.input).func? n = some f ∧
    ¬ StackBound.CycleFrom (StackBound.Calls spec.input spec.input.results) f :=
  (StackBound.goodN_iff (okB_leanLink inScope link_eq)).1 good

/-- **`compileExe_correct` on `a_arith`** with the closed base environment: for the entry `f`,
every outside call satisfying the per-run premises is refined by the executable's run. -/
theorem correct_closed : ∃ f, (prog spec.input).func? n = some f ∧
    ∀ (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State},
      (imageOf file).Intact r →
      OutsideCall spec.input (BinCheck.roByte spec.input spec.data) f
        (StackBound.stackFn spec.input f) r args cs.mem →
      ClifRun spec.input closedBase f r args cs →
      TrapsExplicit (Clif.linkEnvN (prog spec.input) closedBase.env M)
        (prog spec.input).bare cs →
      ExecRefines (art spec.input f).fb (art spec.input f).base (xreg 30 r)
        (step spec.input closedBase file) r (BinCheck.RelocAt spec.input)
        (Clif.runLoop closedBase.env (prog spec.input) (M + 1) cs) := by
  obtain ⟨f, hf, hc⟩ := entry
  exact ⟨f, hf, fun M _ _ _ hX ho hr htr =>
    compileExe_correct compile_eq closedBase base_closed (hooksSim_closed _) hf hc M hX ho hr htr⟩

/-- The output's program headers. -/
def phs : List Elf.Phdr := (Elf.phdrs (Elf.fileRd file0)).getD []

theorem hph : Elf.phdrs (Elf.fileRd file0) = some phs := by native_decide

theorem placeOk : spec.placeOkB = true := by native_decide

theorem rangeB : (tabOf spec.input.resultsT).all (fun e =>
    e.2.fb.relocs.all (relocRangeB spec.input (Elf.tpOff phs) e.2)) = true := by native_decide

theorem regionOk : regionOkB file0 spec.R (regionOf spec (Elf.tpOff phs)).size
    (offsetOf phs spec.R) = true := by native_decide

theorem outsideOk : outsideOkB spec.input spec.data
    (patch file0 (offsetOf phs spec.R) (regionOf spec (Elf.tpOff phs))) = true := by native_decide

theorem names : spec.names = spec.funcs.map (·.func.name) := by native_decide

theorem sizes : spec.sizes = spec.sizesOf := by native_decide

/-- **Non-vacuity of `compileExe_total`**: its hypotheses hold on `a_arith`. -/
theorem total_witness :
    compileExe spec file0 = .ok (patch file0 (offsetOf phs spec.R) (regionOf spec (Elf.tpOff phs))) :=
  compileExe_total (by native_decide) placeOk
    names sizes (fun e he r hr => List.all_eq_true.1 (List.all_eq_true.1 rangeB e he) r hr) hph
    regionOk outsideOk

/-! ## `compileExe_total_input` on `a_arith` -/

/-- `Crates.LeanLinkWitness.placeholder` with a `PT_TLS` segment (empty, 16-byte aligned) after
its `PT_LOAD` segment: the executable rust-lld links for a program with thread-locals. -/
def placeholderTls (R n : Nat) (syms : List (String × Nat)) : ByteArray :=
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
    le 64 2 ++ le 56 2 ++ le 2 2 ++ le 64 2 ++ le 3 2 ++ le 0 2
  let phdr := le 1 4 ++ le 5 4 ++ le 4096 8 ++ le R 8 ++ le R 8 ++ le n 8 ++ le n 8 ++ le 65536 8
  let tls := le 7 4 ++ le 4 4 ++ le 0 8 ++ le 0 8 ++ le 0 8 ++ le 0 8 ++ le 0 8 ++ le 16 8
  ⟨(ehdr ++ phdr ++ tls ++ List.replicate (4096 - 176) 0 ++ List.replicate n 0 ++ symtab ++ st ++
    List.replicate 64 0 ++ shdr 2 symOff symtab.length 2 24 ++ shdr 3 strOff st.length 0 0).toArray⟩

/-- rust-lld's executable for the Lean compiler's layout of `a_arith`: the region's placeholder
of the layout's span, the layout's link map as the symbol table, a `PT_TLS` segment. -/
def file0T : ByteArray :=
  placeholderTls spec.R spec.placed.size (spec.placed.addrs.map fun p => (BinCheck.symName p.1, p.2))

def phsT : List Elf.Phdr := (Elf.phdrs (Elf.fileRd file0T)).getD []

theorem hphT : Elf.phdrs (Elf.fileRd file0T) = some phsT := by native_decide

theorem inScopeT : InScopeIn spec.placed.input0 = true := by native_decide

theorem layoutT : spec.placed.layoutOkB = true := by native_decide

theorem file0T_ok : spec.placed.file0OkB file0T phsT = true := by native_decide

theorem reachB : (tabOf spec.placed.input.resultsT).all (fun e => e.2.fb.relocs.all fun r =>
    decide (r.type = .tlsDescAdrPage21) || relocRangeB spec.placed.input (Elf.tpOff phsT) e.2 r) =
    true := by native_decide

theorem reach : CallPageReach spec phsT := fun e he r hr hne => by
  have := List.all_eq_true.1 (List.all_eq_true.1 reachB e he) r hr
  simpa [hne] using this

/-- **Non-vacuity of `compileExe_total_input`**: its hypotheses hold on `a_arith`, with the Lean
compiler's layout and an executable with a `PT_TLS` segment. -/
theorem total_input_witness :
    compileExe spec.placed file0T =
      .ok (patch file0T (offsetOf phsT spec.R) (regionOf spec.placed (Elf.tpOff phsT))) :=
  compileExe_total_input inScopeT layoutT hphT file0T_ok reach

/-- `placed_of_compileExe` on `a_arith`: the linked spec has the Lean compiler's layout. -/
theorem spec_placed : spec.placed = spec := placed_of_compileExe compile_eq

/-! ## `DeadCleanup.compileExe_total_input` on `a_arith` (the shipped compiler) -/

/-- rust-lld's executable for the shipped compiler's layout of `a_arith`. -/
def file0C : ByteArray :=
  placeholderTls spec.R (DeadCleanup.placed spec).size
    ((DeadCleanup.placed spec).addrs.map fun p => (BinCheck.symName p.1, p.2))

def phsC : List Elf.Phdr := (Elf.phdrs (Elf.fileRd file0C)).getD []

theorem hphC : Elf.phdrs (Elf.fileRd file0C) = some phsC := by native_decide

theorem inScopeC : InScopeP (DeadCleanup.placed spec).input0 = true := by native_decide

theorem layoutC : (DeadCleanup.placed spec).layoutOkB = true := by native_decide

theorem file0C_ok : (DeadCleanup.placed spec).file0OkB file0C phsC = true := by native_decide

theorem reachCB : (tabOf (DeadCleanup.placed spec).inputCleanup.resultsCleanupT).all (fun e =>
    e.2.fb.relocs.all fun r => decide (r.type = .tlsDescAdrPage21) ||
      relocRangeB (DeadCleanup.placed spec).inputCleanup (Elf.tpOff phsC) e.2 r) = true := by
  native_decide

theorem reachC : DeadCleanup.CallPageReach spec phsC := fun e he r hr hne => by
  have := List.all_eq_true.1 (List.all_eq_true.1 reachCB e he) r hr
  simpa [hne] using this

/-- **Non-vacuity of `DeadCleanup.compileExe_total_input`** on `a_arith`. -/
theorem total_input_cleanup_witness :
    DeadCleanup.compileExe (DeadCleanup.placed spec) file0C =
      .ok (patch file0C (offsetOf phsC spec.R)
        (DeadCleanup.regionOf (DeadCleanup.placed spec) (Elf.tpOff phsC))) :=
  DeadCleanup.compileExe_total_input inScopeC layoutC hphC file0C_ok reachC

end Crates.CompileExeWitness
