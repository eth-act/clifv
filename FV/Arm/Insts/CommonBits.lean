/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Yan Peng, Nathan Wetzler
-/
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in
-- namespace Arm; the `bv_decide` proofs of the flag and alignment lemmas replaced by kernel proofs
-- (`toNat`/`toInt` arithmetic with `omega`).

-- Module system: the bit-mask functions of `FV.Arm.Insts.Common`, in their own module so that
-- `Common`'s dsimprocs can run them at elaboration time (`meta import`) while proofs and the
-- model use them as ordinary definitions.
module

public import FV.Arm.BitVec
import FV.Arm.State
import FV.Arm.MinTheory

@[expose] public section

namespace Arm

section Common

open _root_.BitVec Arm.BitVec

/- Find the index of the most significant set bit, if any, in `bv`.
This function differs from the Arm's HighestSetBit
(https://developer.arm.com/documentation/ddi0602/2022-03/Shared-Pseudocode/Shared-Functions?lang=en#impl-shared.HighestSetBit.1)
because it returns `n` when no set bit is found, instead of returning `-1`.
-/
def highest_set_bit (bv : BitVec n) : Nat :=
  go (n - 1) bv where
  go (i : Nat) (bv : BitVec n) :=
    if lsb bv i = 1#1 then
      i
    else
      if i = 0 then
        n
      else
        go (i - 1) bv

/- Find the index of the least significant set bit, if any, in `bv`.
This function matches Arm's LowestSetBit
(https://developer.arm.com/documentation/ddi0602/2022-03/Shared-Pseudocode/Shared-Functions?lang=en#impl-shared.LowestSetBit.1)
-- it returns `n` when no set bit is found.
-/
def lowest_set_bit (bv : BitVec n) : Nat :=
  go 0 bv where
  go (i : Nat) (bv : BitVec n) :=
    if i >= n then
      n
    else
      if lsb bv i = 1#1 then
        i
      else
        go (i + 1) bv
  termination_by (n - i)

def invalid_bit_masks (immN : BitVec 1) (imms : BitVec 6) (immediate : Bool)
  (M : Nat) : Bool :=
  let inp := immN ++ ~~~imms
  let len := highest_set_bit inp
  if len = BitVec.width inp then
    -- If no set bit is found in `inp`, then `highest_set_bit` returns the width
    -- of `inp`.
    true
  else if len < 1 ∧ M < (1 <<< len) then
   true
  else
    let levels := setWidth 6 (allOnes len)
    if immediate ∧ (imms &&& levels = levels) then
      true
    else
      let esize := 1 <<< len
      if esize * (M / esize) ≠ M then true else false

theorem M_divisible_by_esize_of_valid_bit_masks (immN : BitVec 1) (imms : BitVec 6)
  (immediate : Bool) (M : Nat):
  ¬ invalid_bit_masks immN imms immediate M →
  let len := highest_set_bit $ immN ++ ~~~imms
  let esize := 1 <<< len
  esize * (M / esize) = M := by
    unfold invalid_bit_masks
    simp only [Nat.lt_one_iff, ite_not, Bool.not_eq_true]
    split
    · simp only [Nat.reduceAdd, false_implies, Bool.true_eq_false]
    . simp_all only [Bool.ite_eq_false_distrib, ite_eq_left_iff, imp_false]
      split
      . simp only [Bool.true_eq_false, Nat.reduceAdd, false_implies]
      . split
        . simp only [Bool.true_eq_false, Nat.reduceAdd, false_implies]
        . simp only [Nat.reduceAdd, Bool.true_eq_false, imp_false,
            Decidable.not_not, imp_self]
    done

-- Resources on Arm bitmask immediate:
--   https://developer.arm.com/documentation/dui0802/b/A64-General-Instructions/MOV--bitmask-immediate-
--   https://kddnewton.com/2022/08/11/aarch64-bitmask-immediates.html
-- Arm Implementation:
--   https://developer.arm.com/documentation/ddi0602/2023-12/Shared-Pseudocode/aarch64-functions-bitmasks?lang=en#impl-aarch64.DecodeBitMasks.5
def decode_bit_masks (immN : BitVec 1) (imms immr : BitVec 6)
                     (immediate : Bool) (M : Nat) :
                     Option (BitVec M × BitVec M) :=
  if h0 : invalid_bit_masks immN imms immediate M then none
  else
    let len := Option.get! $ highest_set_bit $ immN ++ ~~~imms
    let levels := setWidth 6 (allOnes len)
    let s := imms &&& levels
    let r := immr &&& levels
    let diff := s - r
    let esize := 1 <<< len
    let d := extractLsb' 0 len diff
    let welem := setWidth esize (allOnes (s.toNat + 1))
    let telem := setWidth esize (allOnes (d.toNat + 1))
    let wmask := replicate (M/esize) $ rotateRight welem r.toNat
    let tmask := replicate (M/esize) telem
    have h : esize * (M / esize) = M := by
      apply M_divisible_by_esize_of_valid_bit_masks immN imms immediate M
      simp_all
    some (BitVec.cast h wmask, BitVec.cast h tmask)

end Common

end Arm
