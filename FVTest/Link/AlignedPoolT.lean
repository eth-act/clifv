import FVTest.Link.FloatPlainCallsT

/-! Non-vacuity of the alignment-aware placement (#1061).

A program of three functions on the typed Stock route (`SemanticCompilerWith.attemptT`, the
route of `examples/deps`' executables): the Stock route's integer fixture `%stock_arithmetic_ni`
(37 words), `%g` (`fadd`, 30 words) and `%litpool` (`f64const 0x1.7b8bac710cb29p0`, loaded from
its literal pool: `lean-backend` gives its `.text` alignment 8, as Cranelift's `MachBuffer`).
Placed consecutively with one gap word each and no alignment (`offs`, the placement before
#1061), `%litpool` would start at `R + 276 ≡ 4 (mod 8)`; with its alignment (`aligns`, the
driver's: where `ld -r` starts it) the placement `offsA` starts it at `R + 280 ≡ 0 (mod 8)`,
the bytes `R + 276 … R + 279` before it are zeros (`udf #0`, rust-lld's filler), the compiled
code is loaded there, `attemptT` writes the executable and `attemptT_correct` (the binary
theorem of the route) applies to it.

`addrs_name_old_false`: the statement of `Link.LinkSpec.addrs_name` before #1061 (the link map
at `R + offs`) is false for a spec with an 8-aligned function after a function of 2 words.
Decided by `native_decide` (witness only). `lake build FVTest.Link.AlignedPoolT`.
-/

namespace E2E.AlignedPoolTWitness
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.Elf Link Backend
open E2E.DeadCleanupExecutableWitness (placeholder)
open E2E.FloatPlainCallsTWitness (fStock fG lower)

def srcLit : String := "function %litpool() -> f64 {
block0:
    v0 = f64const 0x1.7b8bac710cb29p0
    return v0
}
"

def fLit : FnInput := { clif := srcLit, ra := "{}" }

def fns : List FnInput := [fStock, fG, fLit]

/-- The driver's alignments: `%litpool`'s object is 8-aligned. -/
def initial : LinkSpec :=
  { funcs := fns, names := [], sizes := [], outside := [], symNames := [], R := 0x1000000,
    aligns := [4, 4, 8] }

/-- The Stock route's placement. -/
def spec : LinkSpec := initial.placedProductionWith lower true

def file0 : ByteArray :=
  placeholder spec.R spec.size (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

def input : SemanticStackBound.CompilerInput := SemanticCompilerWith.input lower spec true

/-- The load address of `name`'s compiled code. -/
def baseOf (name : String) : Option Nat :=
  (input.results.find? (·.1.name == name)).bind fun row => match row.2 with
    | .ok a => some a.base.toNat
    | .error _ => none

/-- `%litpool`'s prepared code loads from its literal pool. -/
def poolLoadB : Bool :=
  input.results.any fun row => row.1.name == "litpool" && match row.2 with
    | .ok a => a.vcp.blocks.any fun vb => vb.insts.any (·.isPoolLoad)
    | .error _ => false

def file : ByteArray := getOk (SemanticCompilerWith.attemptT lower spec file0)

def checks : Bool :=
  spec.sizes == [37, 30, 30] && poolLoadB &&
  -- without alignment: `R + 276 ≡ 4 (mod 8)`; aligned: `R + 280 ≡ 0 (mod 8)`
  (offs spec.sizes 0)[2]! == 276 && (offsA spec.sizes spec.aligns 0)[2]! == 280 &&
  spec.R % 8 == 0 && spec.addrs.lookup "litpool" == some (spec.R + 280) &&
  baseOf "litpool" == some (spec.R + 280) &&
  (SemanticCompilerWith.attemptT lower spec file0).toBool &&
  -- the padding before `%litpool` is zero bytes in the written executable
  (List.range 4).all (fun k => loadMem file (BitVec.ofNat 64 (spec.R + 276 + k)) == some 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide

theorem attemptT_eq : SemanticCompilerWith.attemptT lower spec file0 = .ok file := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true] at h
  exact getOk_eq h.1.2

/-- **The literal-pool function starts 8-aligned** (#1061): its link-map address and its
compiled code's load address are `R + 280 ≡ 0 (mod 8)`, where the unaligned placement `offs`
puts it at `R + 276 ≡ 4 (mod 8)`; the bytes in between are zeros in the written executable. -/
theorem lit_aligned : poolLoadB = true ∧
    spec.R + (offs spec.sizes 0)[2]! = 0x1000000 + 276 ∧
    spec.addrs.lookup "litpool" = some (0x1000000 + 280) ∧
    baseOf "litpool" = some (0x1000000 + 280) ∧ (0x1000000 + 280) % 8 = 0 ∧
    ∀ k < 4, loadMem file (BitVec.ofNat 64 (0x1000000 + 276 + k)) = some 0 := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hp⟩, ho⟩, -⟩, -⟩, ha⟩, hb⟩, -⟩, hz⟩ := h
  have hR' : spec.R = 0x1000000 := rfl
  rw [hR'] at ha hb hz
  exact ⟨hp, by rw [hR', ho], ha, hb, by decide, fun k hk => hz k hk⟩

/-- **Witness**: `Link.SemanticCompilerWith.attemptT_correct` (the route's binary theorem)
applies to the program with the 8-aligned literal-pool function. -/
theorem correct_spec :
    type_of% (@SemanticCompilerWith.attemptT_correct lower spec file0 file attemptT_eq) :=
  @SemanticCompilerWith.attemptT_correct lower spec file0 file attemptT_eq

/-- A spec whose second function is 8-aligned after a function of 2 words. -/
def tiny : LinkSpec :=
  { funcs := [default, default], names := ["f", "g"], sizes := [2, 1], outside := [],
    symNames := [], R := 4096, aligns := [4, 8] }

/-- **The statement of `Link.LinkSpec.addrs_name` before #1061 is false**: it gave the `i`-th
placed function the link-map address `R + offs_i` (consecutive, no alignment); `tiny`'s `g`
is at `R + 16`, not `R + offs [2, 1] 0 = R + 12`. -/
theorem addrs_name_old_false : ¬ ∀ (S : LinkSpec), PlaceOk S → ∀ i < S.funcs.length,
    S.addrs.lookup S.names[i]! = some (S.R + (offs S.sizes 0)[i]!) := by
  intro h
  have := h tiny (placeOk_of (by native_decide)) 1 (by decide)
  revert this
  native_decide

end E2E.AlignedPoolTWitness
