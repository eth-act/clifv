import FV.Link.EhCheck

/-!
# Witness: `ehOkR` holds on an executable and `ehOkR_sound` applies (S10f)

S10c's function (`UnwindTables.Witness`: a `try_call` with a landing pad, so the FDE has an LSDA)
compiled at `0x400000` (40 bytes), in a small static executable laid out as rust-lld lays out
`cargo fv --lean-link` executables: `.eh_frame_hdr` (one table entry) at `0x47ffe0` with its
`PT_GNU_EH_FRAME` header, `.eh_frame` at `0x480000` (the backend's `ehFrame`, relocated,
`EhFrameDecode.EhWitness`) in the same read-only segment, `.gcc_except_table` at `0x500000`.
The check holds (`ok`), and at every pc of the function the unwinder's lookup finds its address
and its tables (`unw`; the concrete pc `0x400014`, after the call, in `unw_call`).
-/

namespace Link.EhCheck.Witness

open E2E E2E.LinkCheck Backend Backend.Proof Backend.Proof.UnwindTables
  Backend.Proof.EhFrameDecode Unw

/-- Little-endian bytes. -/
def leB (v n : Nat) : List UInt8 := (List.range n).map fun i => UInt8.ofNat (v >>> (8 * i))

/-- `.eh_frame`: the backend's section for the function, relocated at `0x480000`. -/
def ehB : List UInt8 :=
  linkSection (ehFrame EhWitness.fdes 2 3).1.data.toList (ehFrame EhWitness.fdes 2 3).2 0x480000
    EhWitness.symAddr

/-- The FDE's address: the first entry of `.eh_frame` that is not a CIE. -/
def fdeAddr : Nat :=
  0x480000 + ((((entries ehB).getD []).find? fun e => leNat (e.2.take 4) != 0).map (·.1)).getD 0

def hdrAddr : Nat := 0x47ffe0

/-- `.eh_frame_hdr`: version 1, `eh_frame_ptr` (`pcrel | sdata4`), one entry (`udata4`), the
table (`datarel | sdata4`): the function's address and its FDE's. -/
def hdrB : List UInt8 :=
  [1, 0x1b, 0x03, 0x3b] ++ leB (0x480000 - (hdrAddr + 4)) 4 ++ leB 1 4 ++
    leB (0x400000 + 2 ^ 32 - hdrAddr) 4 ++ leB (fdeAddr - hdrAddr) 4

/-- A program header. -/
def phdrB (ty fl off va sz : Nat) : List UInt8 :=
  leB ty 4 ++ leB fl 4 ++ leB off 8 ++ leB va 8 ++ leB va 8 ++ leB sz 8 ++ leB sz 8 ++ leB 0x1000 8

def ehdrB : List UInt8 :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1] ++ List.replicate 9 0 ++ leB 2 2 ++ leB 183 2 ++ leB 1 4 ++
    leB 0x400000 8 ++ leB 64 8 ++ leB 0 8 ++ leB 0 4 ++ leB 64 2 ++ leB 56 2 ++ leB 4 2 ++
    leB 64 2 ++ leB 0 2 ++ leB 0 2

/-- The segment of `.eh_frame_hdr` and `.eh_frame`. -/
def ehSeg : List UInt8 := hdrB ++ List.replicate (0x20 - hdrB.length) 0 ++ ehB

/-- **The executable**: the code (zeros: `ehOkR` reads the tables only), `.eh_frame_hdr` +
`.eh_frame`, `.gcc_except_table`. -/
def file : ByteArray :=
  let hs := phdrB 1 5 0x1000 0x400000 40 ++ phdrB 1 4 0x2000 hdrAddr ehSeg.length ++
    phdrB 1 4 0x3000 0x500000 EhWitness.gccB.length ++ phdrB 0x6474e550 4 0x2000 hdrAddr 20
  let head := ehdrB ++ hs
  ⟨(head ++ List.replicate (0x1000 - head.length) 0 ++ List.replicate 40 0 ++
    List.replicate (0x1000 - 40) 0 ++ ehSeg ++ List.replicate (0x1000 - ehSeg.length) 0 ++
    EhWitness.gccB).toArray⟩

/-- The function's name. -/
def g : Clif.Function := { (default : Clif.Function) with name := "w" }

/-- The compiled function at `0x400000` (its frame and lines: `UnwindTables.Witness`). -/
def art : Art :=
  { k := 0, vc := default, vcp := default, rf := default, af := Witness.af, fa := Witness.fa,
    fb := { name := "w", words := Array.replicate 10 0, relocs := [], traps := [], insns := #[] },
    base := 0x400000 }

def R : Res := [(g, .ok art)]

theorem ok : ehOkR R file = true := by native_decide

theorem artOf_g : artOf R g = art := by simp [artOf, R, getOk]

/-- **`ehOkR_sound` applies**: at every pc of the function the unwinder's lookup in `file`
gives its address and the tables the theorems use. -/
theorem unw {pc : Nat} (h1 : 0x400000 ≤ pc) (h2 : pc < 0x400000 + 40) :
    unwTables file pc =
      some (0x400000, ⟨cieInsns, insnsFrom 0 Witness.rows, some (Witness.sites.map (·.entry))⟩) := by
  have hg : g ∈ (progOf R).funcs := by simp [R, progOf]
  obtain ⟨T, hT, hu⟩ := ehOkR_sound ok hg (pc := pc) (by rw [artOf_g]; exact h1)
    (by rw [artOf_g]; exact h2)
  rw [artOf_g] at hT hu
  obtain ⟨l, rows, h1, h2, rfl⟩ := tabsOf_spec hT
  rw [show art.af = Witness.af from rfl, show art.fa = Witness.fa from rfl, Witness.sites_ok]
    at h1
  rw [show art.af = Witness.af from rfl, show art.fa = Witness.fa from rfl, Witness.rows_ok] at h2
  cases h1
  cases h2
  exact hu

/-- At the return address of the function's call (offset 20) − 1. -/
theorem unw_call :
    unwTables file 0x400013 =
      some (0x400000, ⟨cieInsns, insnsFrom 0 Witness.rows, some (Witness.sites.map (·.entry))⟩) :=
  unw (by decide) (by decide)

end Link.EhCheck.Witness
