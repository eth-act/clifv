module

public import FV.Link.ExeUnwind
public import FV.Link.EhCheckWitness

@[expose] public section

/-!
# Witness: `compileExeU` succeeds and `compileExe_correct_unwind` applies (S10f)

A self-recursive function `%rec` (it calls itself, so it has a frame and unwind rows) placed at
16 MiB in a small static executable laid out as `cargo fv --lean-link` executables are: the
region's placeholder (`PT_LOAD` R+X), `.eh_frame_hdr` and `.eh_frame` in a read-only `PT_LOAD`
with the `PT_GNU_EH_FRAME` header (the region's FDEs as lean-backend writes them, `Backend.ehFrame`,
relocated as rust-lld does; the search table as rust-lld builds it, `ehSegOf`), and a symbol
table. `compileExeU` (what `lake exe lean-link` decides) succeeds (`compile_eq`, `native_decide`):

* `tables`: at every pc of the compiled `%rec`, libunwind's lookup in the written executable gives
  its address and its tables (`compileExeU_tables`);
* `unwind_applies`: `compileExe_correct_unwind` instantiated at this executable and `%rec` (open:
  its premises about the base environment, the budget and the entry).
-/

namespace Link.DeadCleanup.UnwindWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary Backend Backend.Proof Backend.Proof.UnwindTables
  Backend.Proof.EhFrameDecode Link.EhCheck.Witness Unw

/-! ## The unwind sections of compiled functions, as lean-backend and rust-lld write them -/

def lsdaOf (a : Art) : Option (List CallSite) := (callSites a.af a.fa).toOption.getD none
def rowsOf (a : Art) : List (Nat × Cfi) := (unwindRows a.af a.fa).toOption.getD []

/-- `.gcc_except_table`: the functions' LSDAs, and each function's LSDA offset. -/
def gccOf (arts : List Art) : List UInt8 × List (Option Nat) :=
  arts.foldl (fun (bs, los) a => match lsdaOf a with
    | some s => (bs ++ (lsdaBytes s).data.toList, los ++ [some bs.length])
    | none => (bs, los ++ [none])) ([], [])

/-- `.eh_frame_hdr` at `hdr` followed by `.eh_frame` (8-aligned, zero-terminated): the FDEs of
`arts` (`Backend.ehFrame`), relocated (`.text` at 0, `.gcc_except_table` at `gccAddr`,
`DW.ref` at `dwref`), and the search table sorted by address. -/
def ehSegOf (arts : List Art) (hdr gccAddr dwref : Nat) : List UInt8 :=
  let n := arts.length
  let ehAddr := (hdr + 12 + 8 * n + 7) / 8 * 8
  let fdes := (arts.zip (gccOf arts).2).map fun (a, lo) => (a.base.toNat, a.fb.size, rowsOf a, lo)
  let eb := ehFrame fdes 2 3
  let sym := fun i => if i = 1 then 0 else if i = 2 then gccAddr else dwref
  let eh := linkSection eb.1.data.toList eb.2 ehAddr sym
  let offs := (((entries eh).getD []).filter fun e => leNat (e.2.take 4) != 0).map (·.1)
  let tab := ((arts.zip offs).map fun (a, o) => (a.base.toNat, ehAddr + o)).mergeSort
    fun x y => decide (x.1 ≤ y.1)
  let hdrB := [1, 0x1b, 0x03, 0x3b] ++ leB (ehAddr - (hdr + 4)) 4 ++ leB n 4 ++
    tab.flatMap fun (l, f) => leB ((l + 2 ^ 32 - hdr) % 2 ^ 32) 4 ++ leB ((f + 2 ^ 32 - hdr) % 2 ^ 32) 4
  hdrB ++ List.replicate (ehAddr - hdr - hdrB.length) 0 ++ eh ++ [0, 0, 0, 0]

/-- The string table of `ns` and each name's offset. -/
def strtab (ns : List String) : List UInt8 × List Nat :=
  ns.foldl (fun (t, os) n => (t ++ n.toUTF8.toList ++ [0], os ++ [t.length])) ([0], [])

/-- Round up to a page. -/
def page (x : Nat) : Nat := (x + 4095) / 4096 * 4096

/-- **A static AArch64 executable** with the region's placeholder (`n` zero bytes at `R`, file
offset 4096, `R+X`), read-only `PT_LOAD` segments `segs` (address, bytes), the first one starting
with `.eh_frame_hdr` (`PT_GNU_EH_FRAME`, `hdrLen` bytes), and a symbol table with `syms`. -/
def exeWith (R n : Nat) (segs : List (Nat × List UInt8)) (hdrLen : Nat)
    (syms : List (String × Nat)) : ByteArray :=
  let (st, os) := strtab (syms.map (·.1))
  let symtab := List.replicate 24 0 ++ (syms.zip os).flatMap fun ((_, v), o) =>
    leB o 4 ++ [0x10, 0] ++ leB 0xfff1 2 ++ leB v 8 ++ leB 0 8
  -- file offsets of the segments
  let offs := (segs.foldl (fun (o, l) s => (page (o + s.2.length), l ++ [o])) (page (4096 + n), [])).2
  let segEnd := (segs.zip offs).foldl (fun e (s, o) => max e (o + s.2.length)) (4096 + n)
  let symOff := segEnd
  let strOff := symOff + symtab.length
  let shOff := strOff + st.length
  let phnum := 2 + segs.length
  let shdr (ty off size link ent : Nat) : List UInt8 :=
    leB 0 4 ++ leB ty 4 ++ leB 0 8 ++ leB 0 8 ++ leB off 8 ++ leB size 8 ++ leB link 4 ++ leB 0 4 ++
      leB 8 8 ++ leB ent 8
  let ident : List UInt8 := [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1] ++ List.replicate 9 0
  let ehdr := ident ++ leB 2 2 ++ leB 183 2 ++ leB 1 4 ++ leB R 8 ++ leB 64 8 ++ leB shOff 8 ++
    leB 0 4 ++ leB 64 2 ++ leB 56 2 ++ leB phnum 2 ++ leB 64 2 ++ leB 3 2 ++ leB 0 2
  let ph (ty fl off va sz : Nat) : List UInt8 :=
    leB ty 4 ++ leB fl 4 ++ leB off 8 ++ leB va 8 ++ leB va 8 ++ leB sz 8 ++ leB sz 8 ++ leB 65536 8
  let phs := ph 1 5 4096 R n ++ (segs.zip offs).flatMap (fun (s, o) => ph 1 4 o s.1 s.2.length) ++
    (match segs.head?, offs.head? with
      | some s, some o => ph 0x6474e550 4 o s.1 hdrLen
      | _, _ => [])
  let head := ehdr ++ phs
  let body := (segs.zip offs).foldl (fun b (s, o) => b ++ List.replicate (o - b.length) 0 ++ s.2)
    (head ++ List.replicate (4096 - head.length) 0 ++ List.replicate n 0)
  ⟨(body ++ List.replicate (symOff - body.length) 0 ++ symtab ++ st ++ List.replicate 64 0 ++
    shdr 2 symOff symtab.length 2 24 ++ shdr 3 strOff st.length 0 0).toArray⟩

/-! ## The program and its executable -/

/-- A self-recursive function: `rec(x, n) = n = 0 ? x : rec(x + x, n - 1)`. -/
def src : String := "function %rec(i64, i64) -> i64 system_v {
    fn0 = colocated %rec(i64, i64) -> i64 system_v
block0(v0: i64, v1: i64):
    brif v1, block1, block2
block1:
    v2 = iconst.i64 1
    v3 = isub v1, v2
    v4 = iadd v0, v0
    v5 = call fn0(v4, v3)
    return v5
block2:
    return v0
}
"

def fnInput : FnInput := { clif := src, ra := "{}" }

/-- `%rec` placed at 16 MiB with the size the cleanup pipeline compiles it to. -/
def spec : LinkSpec :=
  let fs := [fnInput]
  let names := fs.map (·.func.name)
  { funcs := fs, names,
    sizes := fs.map fun fi => (getOk (pipeCleanupT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size,
    outside := [], symNames := names, R := 0x1000000 }

/-- The compiled functions (`compileExe`'s, `parResultsCleanupT_input`). -/
def arts : List Art := (tabOf (parResultsCleanupT spec.input0)).map (·.2)

def hdrAddr : Nat := 0x2000000
def gccAddr : Nat := 0x2100000

/-- **The executable before the compiler**: the region's placeholder, the unwind sections
rust-lld writes for the region's objects, the link map's symbols. -/
def file0 : ByteArray :=
  exeWith spec.R spec.size
    [(hdrAddr, ehSegOf arts hdrAddr gccAddr 0x2200000), (gccAddr, (gccOf arts).1 ++ [0, 0, 0, 0])]
    (12 + 8 * arts.length) (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

theorem compile_ok : (compileExeU spec file0).toBool = true := by native_decide

/-- The executable. -/
def file : ByteArray := getOk (compileExeU spec file0)

/-- **The executable compiler with the unwind tables checked compiles `%rec` to `file`.** -/
theorem compile_eq : compileExeU spec file0 = .ok file := getOk_eq compile_ok

/-- The compiled `%rec`. -/
def f : Clif.Function := ((prog spec.inputCleanup).func? "rec").getD default

theorem f_mem : f ∈ (prog spec.inputCleanup).funcs := by
  have : ((prog spec.inputCleanup).func? "rec").isSome = true := by native_decide
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 this
  rw [show f = g by simp [f, hg]]
  exact (Clif.Program.func?_some hg).1

/-- **The unwinder reads `%rec`'s tables from the written executable** at every pc of its code. -/
theorem tables {pc : Nat} (h1 : (art spec.inputCleanup f).base.toNat ≤ pc)
    (h2 : pc < (art spec.inputCleanup f).base.toNat + (art spec.inputCleanup f).fb.size) :
    EhCheck.unwTables file pc =
      some ((art spec.inputCleanup f).base.toNat, (art spec.inputCleanup f).tables) :=
  compileExeU_tables compile_eq f_mem h1 h2

/-- The code is non-empty: `tables` is not vacuous. -/
theorem size_pos : 0 < (art spec.inputCleanup f).fb.size := by native_decide

/-- **`compileExe_correct_unwind` applies to `file`** (open: the premises about the base
environment, the budget and the entry). -/
theorem unwind_applies (B : BaseEnv) (F : BitVec 64 → Prop)
    (hB : BaseOk (LinkSys.ofInputCleanup spec.inputCleanup B F))
    (hF : ∀ a, (LinkSys.ofInputCleanup spec.inputCleanup B F).Img a → F a)
    (L : LinkSysU) (hLs : L.toLinkSys = LinkSys.ofInputCleanup spec.inputCleanup B F)
    (hb : BaseU L) (hNI : L.OkUNI) {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ)
    (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hFw : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicitX (L.stdX.envRX M f) L.P.bare cs) :
    ArmRefinesU (L.A f).fb (L.A f).base ra (L.machU M f) s
      (Clif.runLoopX L.envX L.P (M + 1) cs.toX) :=
  (compileExe_correct_unwind compile_eq B F hB hF L hLs hb hNI hκ
    (by rw [hLs]; exact f_mem) M hent hres hFw hgfree himg hbe hargs hcs hsav hrel hpl htr).2

end Link.DeadCleanup.UnwindWitness
