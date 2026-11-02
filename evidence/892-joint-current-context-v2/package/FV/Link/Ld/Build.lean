import FV.Link.Ld.Reloc
import FV.Link.Ld.Obj
import FV.Link.Ld.Write

/-! # Lean static linker: the body from placed pieces (L2b stage 3c)

The planner (`FV/Link/Ld/Layout.lean`) decides where every live input section, `.eh_frame`
record and synthesized table goes and resolves every relocation's inputs (`RelIn`: `S`, `A`, `P`,
the GOT slot, the thread-pointer offset). The body of the executable is then computed from that
plan alone:

* `applyRel b r`: the bytes a relocation patches (`relocWidth`) replaced by `relocVal`'s value,
  little-endian (`writeLE`);
* `Piece.relocated`: a piece's input bytes with its relocations applied in order;
* `buildBody size ps`: every piece's relocated bytes placed at its file offset, zeros elsewhere.

Its theorems (`FV/Link/Ld/BuildProof.lean`) state that each piece's bytes in the body are its
relocated input bytes: **the outside part's bytes are the relocated input bytes**.
-/

namespace Link.Ld

/-- `b` written into `dest` at `o`. -/
def place (dest : ByteArray) (o : Nat) (b : ByteArray) : ByteArray := b.copySlice 0 dest o b.size

/-- The `n` little-endian bytes of `v`. -/
def leBytes (n v : Nat) : ByteArray := ⟨((List.range n).map (leByte v)).toArray⟩

/-- `b` with the `n` little-endian bytes of `v` at `o`. -/
def writeLE (b : ByteArray) (o n v : Nat) : ByteArray := place b o (leBytes n v)

/-- A resolved relocation of a piece: offset in the piece, type, inputs. -/
structure Rel where
  off : Nat
  ty : Nat
  ri : RelIn
  deriving Inhabited, Repr

/-- **One relocation applied**: the patched bytes replaced by their relocated value. -/
def applyRel (b : ByteArray) (r : Rel) : Except String ByteArray :=
  let w := relocWidth r.ty
  if r.off + w ≤ b.size then (relocVal r.ty r.ri (rdLE b r.off w)).map (writeLE b r.off w)
  else .error s!"relocation type {r.ty} at {r.off} past the end of its section ({b.size} bytes)"

/-- A placed piece of the body: its load address, file offset, input bytes and relocations. -/
structure Piece where
  addr : Nat
  fo : Nat
  bytes : ByteArray
  rels : List Rel
  deriving Inhabited

/-- **A piece's relocated bytes.** -/
def Piece.relocated (p : Piece) : Except String ByteArray := p.rels.foldlM applyRel p.bytes

/-- One piece placed: its relocated bytes at its file offset. -/
def bodyStep (body : ByteArray) (p : Piece) : Except String ByteArray := do
  let b ← p.relocated
  if p.fo + b.size ≤ body.size then pure (place body p.fo b)
  else throw s!"a piece at file offset {p.fo} past the end of the body"

/-- **The body**: `size` zero bytes with every piece's relocated bytes at its file offset. -/
def buildBody (size : Nat) (ps : List Piece) : Except String ByteArray :=
  ps.foldlM bodyStep ⟨Array.replicate size 0⟩

end Link.Ld
