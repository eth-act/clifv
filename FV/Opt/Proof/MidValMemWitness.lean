import FV.Opt.Proof.MidValMem

/-!
# Non-vacuity of `Opt.MidVal`'s memory facts

A concrete memory with one live 8-byte allocation at `0x10010`: a native and a big-endian
`store.i64` there succeed (`store_ok`, `store_ok_big`: the premises of `Mem.load_of_store` hold),
the lemmas apply (`fwd_lemma`, `fwd_big_lemma`, `rle_lemma`), and their first disjunct is the
outcome (`fwd`, `fwd_big`, `rle`: the loads read the stored value back). Every premise is proved
by evaluation; no `native_decide`.
-/

namespace Clif.Mem.MidValWitness

open Clif

/-- One live, writable 8-byte allocation. -/
def m0 : Mem := { allocs := [{ base := 0x10010, size := 8 }] }

def x : BitVec 64 := 0x1122334455667788#64

/-- An `aligned notrap` load's flags. -/
def flA : MemFlags := { trapCode := none, aligned := true }

def flBig : MemFlags := { endianness := some .big }

theorem store_ok : m0.store {} 0x10010 8 x = .ok (m0.writeBits false 0x10010 8 x) := rfl

theorem store_ok_big : m0.store flBig 0x10010 8 x = .ok (m0.writeBits true 0x10010 8 x) := rfl

theorem fwd_lemma :
    (m0.writeBits false 0x10010 8 x).load flA 0x10010 8 (8 * 8) = .ok (x.setWidth (8 * 8)) ∨
      ∃ msg, (m0.writeBits false 0x10010 8 x).load flA 0x10010 8 (8 * 8) = .stuck msg :=
  load_of_store store_ok rfl

theorem fwd_big_lemma :
    (m0.writeBits true 0x10010 8 x).load flBig 0x10010 8 (8 * 8) = .ok (x.setWidth (8 * 8)) ∨
      ∃ msg, (m0.writeBits true 0x10010 8 x).load flBig 0x10010 8 (8 * 8) = .stuck msg :=
  load_of_store store_ok_big rfl

/-- The outcome: the forwarded load reads `x` (the address is 8-aligned, so not `stuck`). -/
theorem fwd : (m0.writeBits false 0x10010 8 x).load flA 0x10010 8 64 = .ok x := rfl

theorem fwd_big : (m0.writeBits true 0x10010 8 x).load flBig 0x10010 8 64 = .ok x := rfl

theorem rle_lemma :
    (m0.writeBits false 0x10010 8 x).load {} 0x10010 8 64 = .ok x ∨
      ∃ msg, (m0.writeBits false 0x10010 8 x).load {} 0x10010 8 64 = .stuck msg :=
  load_of_load fwd rfl

theorem rle : (m0.writeBits false 0x10010 8 x).load {} 0x10010 8 64 = .ok x := rfl

end Clif.Mem.MidValWitness
