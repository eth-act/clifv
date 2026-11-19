/-
Handwritten executable models of the `rustc-hash` 2.1.1 functions used by the extracted code:
`FxHasher` (64-bit: `K = 0xf1357aea2e62a9c5`, `finish` = `rotate_left(26)`, `write` via
`hash_bytes`) and `FxBuildHasher`. Transcribed from `rustc-hash-2.1.1/src/lib.rs`
(`target_pointer_width = "64"`, feature `nightly` off).

`FxHasher` overrides `write_u8 .. write_u128` and `write_usize`; the Hasher trait model routes
`write_i*`, `write_length_prefix` and `write_str` through those by Rust's default methods.
-/
module
public import Aeneas
public import ClifvGen.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error clifv_extract_entry
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ClifvModels.RustcHash

/-- `const K: usize = 0xf1357aea2e62a9c5` (64-bit). -/
def K : UInt64 := 0xf1357aea2e62a9c5

def toUsize (x : UInt64) : Std.Usize := ⟨BitVec.ofNat _ x.toNat⟩

def ofUsize (x : Std.Usize) : UInt64 := UInt64.ofNat x.bv.toNat

/-- `FxHasher::add_to_hash`: `hash = hash.wrapping_add(i).wrapping_mul(K)`. -/
def addToHash (h : rustc_hash.FxHasher) (i : UInt64) : rustc_hash.FxHasher :=
  ⟨toUsize ((ofUsize h.hash + i) * K)⟩

def SEED1 : UInt64 := 0x243f6a8885a308d3
def SEED2 : UInt64 := 0x13198a2e03707344
def PREVENT_TRIVIAL_ZERO_COLLAPSE : UInt64 := 0xa4093822299f31d0

/-- `multiply_mix` (64-bit): xor of the low and high halves of the 128-bit product. -/
def multiplyMix (x y : UInt64) : UInt64 :=
  let full := x.toNat * y.toNat
  UInt64.ofNat full ^^^ UInt64.ofNat (full >>> 64)

/-- Little-endian `u64` from `n` bytes of `b` at `off`. -/
def readLE (b : Array UInt8) (off n : Nat) : UInt64 :=
  (List.range n).foldl (fun acc i => acc ||| ((b[off + i]!).toUInt64 <<< (8 * i).toUInt64)) 0

/-- `hash_bytes`. -/
def hashBytes (b : Array UInt8) : UInt64 := Id.run do
  let len := b.size
  let mut s0 := SEED1
  let mut s1 := SEED2
  if len ≤ 16 then
    if len ≥ 8 then
      s0 := s0 ^^^ readLE b 0 8
      s1 := s1 ^^^ readLE b (len - 8) 8
    else if len ≥ 4 then
      s0 := s0 ^^^ readLE b 0 4
      s1 := s1 ^^^ readLE b (len - 4) 4
    else if len > 0 then
      let lo := b[0]!
      let mid := b[len / 2]!
      let hi := b[len - 1]!
      s0 := s0 ^^^ lo.toUInt64
      s1 := s1 ^^^ ((hi.toUInt64 <<< 8) ||| mid.toUInt64)
  else
    let mut off := 0
    -- `while off < len - 16`: at most `len / 16` iterations.
    for _ in [0:len / 16 + 1] do
      if off < len - 16 then
        let x := readLE b off 8
        let y := readLE b (off + 8) 8
        let t := multiplyMix (s0 ^^^ x) (PREVENT_TRIVIAL_ZERO_COLLAPSE ^^^ y)
        s0 := s1
        s1 := t
        off := off + 16
    s0 := s0 ^^^ readLE b (len - 16) 8
    s1 := s1 ^^^ readLE b (len - 8) 8
  return multiplyMix s0 s1 ^^^ UInt64.ofNat len

end ClifvModels.RustcHash

open ClifvModels.RustcHash in
/-- [rustc_hash::{core::default::Default<rustc_hash::FxHasher>}::default]: `FxHasher { hash: 0 }`. -/
def rustc_hash.FxHasher.Insts.CoreDefaultDefault.default : Result rustc_hash.FxHasher :=
  ok ⟨toUsize 0⟩

/-- [rustc_hash::{core::default::Default<rustc_hash::FxBuildHasher>}::default]. -/
def rustc_hash.FxBuildHasher.Insts.CoreDefaultDefault.default : Result rustc_hash.FxBuildHasher :=
  ok ()

/-- [rustc_hash::{core::hash::BuildHasher<rustc_hash::FxBuildHasher, rustc_hash::FxHasher>}::build_hasher]:
`FxHasher::default()`. -/
def rustc_hash.FxBuildHasher.Insts.CoreHashBuildHasherFxHasher.build_hasher
  : rustc_hash.FxBuildHasher → Result rustc_hash.FxHasher :=
  fun _ => rustc_hash.FxHasher.Insts.CoreDefaultDefault.default

open ClifvModels.RustcHash in
/-- [rustc_hash::{core::hash::Hasher<rustc_hash::FxHasher>}::finish]: `hash.rotate_left(26)`. -/
def rustc_hash.FxHasher.Insts.CoreHashHasher.finish
  : rustc_hash.FxHasher → Result Std.U64 :=
  fun h =>
    let x := ofUsize h.hash
    ok ⟨BitVec.ofNat 64 ((x <<< 26) ||| (x >>> 38)).toNat⟩

open ClifvModels.RustcHash in
/-- [rustc_hash::{core::hash::Hasher<rustc_hash::FxHasher>}::write_u8]. -/
def rustc_hash.FxHasher.Insts.CoreHashHasher.write_u8
  : rustc_hash.FxHasher → Std.U8 → Result rustc_hash.FxHasher :=
  fun h i => ok (addToHash h (UInt64.ofNat i.bv.toNat))

open ClifvModels.RustcHash in
/-- [rustc_hash::{core::hash::Hasher<rustc_hash::FxHasher>}::write_u16]. -/
def rustc_hash.FxHasher.Insts.CoreHashHasher.write_u16
  : rustc_hash.FxHasher → Std.U16 → Result rustc_hash.FxHasher :=
  fun h i => ok (addToHash h (UInt64.ofNat i.bv.toNat))

open ClifvModels.RustcHash in
/-- [rustc_hash::{core::hash::Hasher<rustc_hash::FxHasher>}::write_u32]. -/
def rustc_hash.FxHasher.Insts.CoreHashHasher.write_u32
  : rustc_hash.FxHasher → Std.U32 → Result rustc_hash.FxHasher :=
  fun h i => ok (addToHash h (UInt64.ofNat i.bv.toNat))

open ClifvModels.RustcHash in
/-- [rustc_hash::{core::hash::Hasher<rustc_hash::FxHasher>}::write_u64]. -/
def rustc_hash.FxHasher.Insts.CoreHashHasher.write_u64
  : rustc_hash.FxHasher → Std.U64 → Result rustc_hash.FxHasher :=
  fun h i => ok (addToHash h (UInt64.ofNat i.bv.toNat))

open ClifvModels.RustcHash in
/-- [rustc_hash::{core::hash::Hasher<rustc_hash::FxHasher>}::write_u128]: low then high half. -/
def rustc_hash.FxHasher.Insts.CoreHashHasher.write_u128
  : rustc_hash.FxHasher → Std.U128 → Result rustc_hash.FxHasher :=
  fun h i =>
    let n := i.bv.toNat
    ok (addToHash (addToHash h (UInt64.ofNat n)) (UInt64.ofNat (n >>> 64)))

open ClifvModels.RustcHash in
/-- [rustc_hash::{core::hash::Hasher<rustc_hash::FxHasher>}::write_usize]. -/
def rustc_hash.FxHasher.Insts.CoreHashHasher.write_usize
  : rustc_hash.FxHasher → Std.Usize → Result rustc_hash.FxHasher :=
  fun h i => ok (addToHash h (ofUsize i))

open ClifvModels.RustcHash in
/-- [rustc_hash::{core::hash::Hasher<rustc_hash::FxHasher>}::write]: `write_u64(hash_bytes(bytes))`. -/
def rustc_hash.FxHasher.Insts.CoreHashHasher.write
  : rustc_hash.FxHasher → Slice Std.U8 → Result rustc_hash.FxHasher :=
  fun h bytes =>
    let b : Array UInt8 := (bytes.val.map fun x => UInt8.ofNat x.bv.toNat).toArray
    ok (addToHash h (hashBytes b))
