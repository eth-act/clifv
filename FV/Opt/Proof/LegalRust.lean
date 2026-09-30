import FV.Opt.Proof.LegalExt
import FV.Clif.Rust

/-!
# The environment contracts of `Opt.Legal.check_refines` for `Clif.Rust.env`

`Clif.Rust.env` (the trusted Rust externs: `mem*`, the `__*ti3` division helpers, the
diverging panic entry points) satisfies the three contracts `FV/Opt/Proof/LegalExt.lean`
states:

* `helperOk_env`: the `__*ti3` helper of each `DivOp`, called on the `i64` halves of two
  128-bit operands, computes `Clif.Sem.div` at `i128` (`udiv`/`sdiv`/`urem`/`srem`), returning
  the halves of the result, and traps exactly where the opcode traps (`int_divz` on a zero
  divisor, `int_ovf` on `sdiv MIN, -1`). The helper's pair arithmetic (`div128`: unsigned and
  signed interpretations of `lo + hi·2^64`, truncated division on magnitudes) is matched to
  `BitVec.udiv/umod` by `toNat` and to `BitVec.sdiv/srem` by `toInt_sdiv`/`toInt_srem`
  (`core_op`).
* `extLegal_env`: every extern of the environment called with the arguments expanded by the
  ABI groups of its declared signature returns the expanded results and traps with the
  original code. The helpers accept both the `i128` and the pair form (`div128_wide`,
  `div128_pair`); `mem*` reads only its first three (`i64`) arguments, which the expansion
  leaves in place; panics trap unconditionally.
* `envKeepsAllocs_env`: no extern changes the allocations (`mem*` writes bytes only).
-/

namespace Clif.Rust

open Opt.Legalize128 (divHelper)

/-! ## The pair interpretation -/

theorem append_toNat (hi lo : BitVec 64) : (hi ++ lo).toNat = lo.toNat + hi.toNat * 2 ^ 64 := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]
  omega

theorem append_toInt (hi lo : BitVec 64) :
    (hi ++ lo).toInt = if hi.toNat ≥ 2 ^ 63 then ((lo.toNat + hi.toNat * 2 ^ 64 : Nat) : Int) - 2 ^ 128
      else ((lo.toNat + hi.toNat * 2 ^ 64 : Nat) : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, append_toNat]
  have ha := lo.isLt
  have hb := hi.isLt
  have e : (2 : Nat) ^ (64 + 64) = 2 ^ 128 := rfl
  rw [e]
  by_cases h : hi.toNat ≥ 2 ^ 63
  · rw [ite_eq_right (show ¬ 2 * (lo.toNat + hi.toNat * 2 ^ 64) < 2 ^ 128 by omega),
      ite_eq_left h, Int.natCast_pow]
    rfl
  · rw [ite_eq_right h, ite_eq_left (show 2 * (lo.toNat + hi.toNat * 2 ^ 64) < 2 ^ 128 by omega)]

/-! ## The helper's computation on two 128-bit operands -/

/-- `div128` on the operands `x`/`y` (unsigned and signed interpretations), the result
rendered by `q`: the body of `div128` after its argument decoding. -/
def core (signed isRem : Bool) (x y : BitVec 128) (q : Nat → List Val) :
    Option (List Val × Option TrapCode) :=
  let nu := x.toNat
  let ns := x.toInt
  let du := y.toNat
  let ds := y.toInt
  if du = 0 then some ([], some .intDivz)
  else if signed ∧ !isRem ∧ ns = -(2 ^ 127 : Int) ∧ du = 2 ^ 128 - 1 then
    some ([], some .intOvf)
  else if signed then
    let (m, d) := (ns.natAbs, ds.natAbs)
    let qv := m / d
    let rv := m % d
    let qv : Int := if (ns < 0) != (ds < 0) then -(qv : Int) else qv
    let rv : Int := if ns < 0 then -(rv : Int) else rv
    let mm := qv % (2 ^ 128 : Int)
    let mm := if mm < 0 then mm + 2 ^ 128 else mm
    if isRem then
      let rm := rv % (2 ^ 128 : Int)
      let rm := if rm < 0 then rm + 2 ^ 128 else rm
      some (q rm.toNat, none)
    else
      some (q mm.toNat, none)
  else
    let r := if isRem then nu % du else nu / du
    some (q r, none)

/-- The result of the `i128` form. -/
def outW (R : Nat) : List Val := [⟨.i128, BitVec.ofNat 128 R⟩]

/-- The result of the pair form. -/
def outP (R : Nat) : List Val :=
  [⟨.i64, BitVec.ofNat 64 (R % 2 ^ 64)⟩, ⟨.i64, BitVec.ofNat 64 (R / 2 ^ 64)⟩]

theorem div128_wide (s r : Bool) (x y : BitVec 128) :
    div128 s r [⟨.i128, x⟩, ⟨.i128, y⟩] = core s r x y outW := by
  unfold div128 core
  simp only [Val.as?, dite_true]
  rfl

theorem div128_pair (s r : Bool) (xl xh yl yh : BitVec 64) :
    div128 s r [⟨.i64, xl⟩, ⟨.i64, xh⟩, ⟨.i64, yl⟩, ⟨.i64, yh⟩] =
      core s r (xh ++ xl) (yh ++ yl) outP := by
  unfold div128 core
  simp only [Val.as?, dite_true]
  rw [append_toInt, append_toInt, append_toNat, append_toNat]
  rfl

theorem tdiv_natAbs (a b : Int) :
    (if (decide (a < 0) != decide (b < 0)) = true then -((a.natAbs / b.natAbs : Nat) : Int)
      else ((a.natAbs / b.natAbs : Nat) : Int)) = a.tdiv b := by
  rcases a with a | a <;> rcases b with b | b <;> simp [Int.tdiv, Int.negSucc_lt_zero] <;> omega

theorem tmod_natAbs (a b : Int) :
    (if a < 0 then -((a.natAbs % b.natAbs : Nat) : Int)
      else ((a.natAbs % b.natAbs : Nat) : Int)) = a.tmod b := by
  rcases a with a | a <;> rcases b with b | b <;> simp [Int.tmod, Int.negSucc_lt_zero] <;> omega

theorem emod_fix (i : Int) :
    (if i % 2 ^ 128 < 0 then i % 2 ^ 128 + 2 ^ 128 else i % 2 ^ 128).toNat =
      (BitVec.ofInt 128 i).toNat := by
  rw [ite_eq_right (Int.not_lt.2 (Int.emod_nonneg _ (by decide))), BitVec.toNat_ofInt]
  rfl

theorem sdiv_toNat (x y : BitVec 128) :
    (x.sdiv y).toNat = (BitVec.ofInt 128 (x.toInt.tdiv y.toInt)).toNat := by
  conv => lhs; rw [← BitVec.ofInt_toInt (x := x.sdiv y), BitVec.toInt_sdiv]
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  congr 1
  exact Int.bmod_emod

theorem srem_toNat (x y : BitVec 128) :
    (x.srem y).toNat = (BitVec.ofInt 128 (x.toInt.tmod y.toInt)).toNat := by
  conv => lhs; rw [← BitVec.ofInt_toInt (x := x.srem y), BitVec.toInt_srem]

/-- The helper flags of an opcode (`divOutcome`). -/
def sgnOf : DivOp → Bool | .sdiv | .srem => true | _ => false
def remOf : DivOp → Bool | .urem | .srem => true | _ => false

/-- **The helper arithmetic is the opcode's.** -/
theorem core_op (op : DivOp) (x y : BitVec 128) (q : Nat → List Val) :
    core (sgnOf op) (remOf op) x y q = match Sem.div op x y with
      | .ok r => some (q r.toNat, none) | .error c => some ([], some c) := by
  have hy : y = 0 ↔ y.toNat = 0 := by simp [BitVec.toNat_eq]
  cases op <;> simp only [core, sgnOf, remOf, Sem.div, Sem.udiv, Sem.sdiv, Sem.urem, Sem.srem]
  all_goals simp only [tdiv_natAbs, tmod_natAbs, emod_fix, Bool.false_eq_true, Bool.not_false,
    Bool.not_true, true_and, false_and, and_false, ite_false, ite_true]
  all_goals simp only [hy]
  all_goals by_cases h0 : y.toNat = 0
  all_goals simp only [h0, ite_true, ite_false, BitVec.toNat_udiv, BitVec.toNat_umod, srem_toNat]
  have hmin : x = BitVec.intMin 128 ↔ x.toInt = -2 ^ 127 := by
    rw [← BitVec.toInt_inj, BitVec.toInt_intMin]; rfl
  have hall : y = BitVec.allOnes 128 ↔ y.toNat = 2 ^ 128 - 1 := by
    rw [BitVec.toNat_eq, BitVec.toNat_allOnes]
  by_cases h1 : x.toInt = -2 ^ 127 ∧ y.toNat = 2 ^ 128 - 1
  · simp only [h1, hmin, hall, and_self, ite_true]
  · rw [ite_eq_right h1, ite_eq_right (by rw [hmin, hall]; exact h1)]
    exact congrArg (fun n => some (q n, none)) (sdiv_toNat x y).symm

theorem outP_toNat (r : BitVec 128) :
    outP r.toNat = [⟨.i64, r.extractLsb' 0 64⟩, ⟨.i64, r.extractLsb' 64 64⟩] := by
  have h1 : BitVec.ofNat 64 (r.toNat % 2 ^ 64) = r.extractLsb' 0 64 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat]
  have h2 : BitVec.ofNat 64 (r.toNat / 2 ^ 64) = r.extractLsb' 64 64 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  simp only [outP, h1, h2]

theorem outW_toNat (r : BitVec 128) : outW r.toNat = [⟨.i128, r⟩] := by
  simp [outW]

theorem halves_split (r : BitVec 128) : r = r.extractLsb' 64 64 ++ r.extractLsb' 0 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [append_toNat]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  have := r.isLt
  omega

/-! ## The helper lookup -/

theorem divOutcome_op (op : DivOp) (vals : List Val) (m : Mem) :
    divOutcome (divHelper op) vals m =
      match div128 (sgnOf op) (remOf op) vals with
      | none => .stuck s!"%{divHelper op}: argument types"
      | some (_, some c) => .trapped c
      | some (vs, none) => .returned vs m := by
  cases op <;> simp only [divOutcome, divHelper, sgnOf, remOf] <;> rfl

theorem isDivHelper_divHelper (op : DivOp) : isDivHelper (divHelper op) = true := by
  cases op <;> decide

theorem env_helper (op : DivOp) :
    env.extern (divHelper op) = some fun vals m => divOutcome (divHelper op) vals m := by
  simp only [env, isDivHelper_divHelper, ite_true]

theorem isDivHelper_iff {name : String} (h : isDivHelper name = true) :
    ∃ op, name = divHelper op := by
  simp only [isDivHelper, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h <;> subst h
  · exact ⟨.udiv, rfl⟩
  · exact ⟨.sdiv, rfl⟩
  · exact ⟨.urem, rfl⟩
  · exact ⟨.srem, rfl⟩

/-- **`HelperOk` for `Clif.Rust.env`.** -/
theorem helperOk_env : Opt.Legal.HelperOk env := by
  intro op
  refine ⟨_, env_helper op, fun xl xh yl yh m => ?_⟩
  simp only [divOutcome_op, div128_pair, core_op]
  split <;> rename_i h <;> simp only [h, outP_toNat]

/-! ## Argument shapes -/

theorem as?_some {v : Val} {t : Ty} {x : BitVec t.width} (h : v.as? t = some x) :
    v = ⟨t, x⟩ := by
  obtain ⟨vt, vb⟩ := v
  simp only [Val.as?] at h
  split at h
  · rename_i he
    subst he
    cases h
    rfl
  · cases h

theorem div128_shape {s r : Bool} {vals : List Val} {o : List Val × Option TrapCode}
    (h : div128 s r vals = some o) :
    (∃ x y : BitVec 128, vals = [⟨.i128, x⟩, ⟨.i128, y⟩]) ∨
      ∃ xl xh yl yh : BitVec 64, vals = [⟨.i64, xl⟩, ⟨.i64, xh⟩, ⟨.i64, yl⟩, ⟨.i64, yh⟩] := by
  rcases vals with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩
  · simp [div128] at h
  · simp [div128] at h
  · left
    cases ha : a.as? .i128 <;> cases hb : b.as? .i128 <;> simp [div128, ha, hb] at h
    rw [as?_some ha, as?_some hb]
    exact ⟨_, _, rfl⟩
  · simp [div128] at h
  · right
    cases ha : a.as? .i64 <;> cases hb : b.as? .i64 <;> cases hc : c.as? .i64 <;>
      cases hd : d.as? .i64 <;> simp [div128, ha, hb, hc, hd] at h
    rw [as?_some ha, as?_some hb, as?_some hc, as?_some hd]
    exact ⟨_, _, _, _, rfl⟩
  · simp [div128] at h

end Clif.Rust

namespace Opt.Legal

open Clif Opt.Legalize128

theorem expRel_refl : ∀ {ps : List AbiParam} {gs : List (List SlotEl)} {vs : List Val},
    GroupsOf ps gs → vs.map (·.ty) = ps.map (·.ty) → (∀ p ∈ ps, p.ty ≠ .i128) → ExpRel gs vs vs
  | [], [], [], _, _, _ => trivial
  | p :: ps, g :: gs, v :: vs, hg, ht, hn => by
    obtain ⟨hg1, hg2⟩ := hg
    simp only [List.map_cons, List.cons.injEq] at ht
    rcases hg1 with ⟨rfl, -⟩ | ⟨hpt, -⟩
    · exact ⟨rfl, expRel_refl hg2 ht.2 fun q hq => hn q (List.mem_cons_of_mem _ hq)⟩
    · exact absurd hpt (hn p (List.mem_cons_self ..))
  | [], _ :: _, _, hg, _, _ => by cases hg
  | _ :: _, [], _, hg, _, _ => by cases hg
  | [], [], _ :: _, _, ht, _ => by cases ht
  | _ :: _, _ :: _, [], _, ht, _ => by cases ht

theorem expRel_cons_val {p : AbiParam} {ps : List AbiParam} {g : List SlotEl}
    {gs : List (List SlotEl)} {v : Val} {vs vs' : List Val}
    (hg : GroupsOf (p :: ps) (g :: gs)) (hp : p.ty ≠ .i128) (h : ExpRel (g :: gs) (v :: vs) vs') :
    ∃ vs'', vs' = v :: vs'' ∧ GroupsOf ps gs ∧ ExpRel gs vs vs'' := by
  obtain ⟨hg1, hg2⟩ := hg
  rcases hg1 with ⟨rfl, -⟩ | ⟨hpt, -⟩
  · rcases vs' with _ | ⟨v', vs'⟩
    · simp [ExpRel] at h
    · obtain ⟨rfl, h⟩ := h
      exact ⟨vs', rfl, hg2, h⟩
  · exact absurd hpt hp

theorem groups_two128 {p1 p2 : AbiParam} {gs : List (List SlotEl)} (h1 : p1.ty = .i128)
    (h2 : p2.ty = .i128) (h : groups [p1, p2] = some gs) : gs = [[.lo, .hi], [.lo, .hi]] := by
  simp only [groups, expandGroups, expandGroups.go, h1, h2] at h
  (repeat' split at h) <;> simp_all [Except.toOption, bind, Except.bind, pure, Except.pure]

theorem groups_one128 {p : AbiParam} {gs : List (List SlotEl)} (h1 : p.ty = .i128)
    (h : groups [p] = some gs) : gs = [[.lo, .hi]] := by
  simp only [groups, expandGroups, expandGroups.go, h1] at h
  (repeat' split at h) <;> simp_all [Except.toOption, bind, Except.bind, pure, Except.pure]

end Opt.Legal

namespace Clif.Rust

open Opt.Legal Opt.Legalize128

/-! ## The helpers on both argument forms -/

theorem divOutcome_wide (op : DivOp) (x y : BitVec 128) (m : Mem) :
    divOutcome (divHelper op) [⟨.i128, x⟩, ⟨.i128, y⟩] m = match Sem.div op x y with
      | .ok r => .returned [⟨.i128, r⟩] m | .error c => .trapped c := by
  simp only [divOutcome_op, div128_wide, core_op]
  cases Sem.div op x y with
  | ok r => exact congrArg (Outcome.returned · m) (outW_toNat r)
  | error c => rfl

theorem divOutcome_pair (op : DivOp) (xl xh yl yh : BitVec 64) (m : Mem) :
    divOutcome (divHelper op) [⟨.i64, xl⟩, ⟨.i64, xh⟩, ⟨.i64, yl⟩, ⟨.i64, yh⟩] m =
      match Sem.div op (xh ++ xl) (yh ++ yl) with
      | .ok r => .returned (outP r.toNat) m | .error c => .trapped c := by
  simp only [divOutcome_op, div128_pair, core_op]
  cases Sem.div op (xh ++ xl) (yh ++ yl) <;> rfl

theorem div_shape_of {op : DivOp} {vals : List Val} {m : Mem} {o : Outcome}
    (h : divOutcome (divHelper op) vals m = o) (ho : ∀ msg, o ≠ .stuck msg) :
    (∃ x y : BitVec 128, vals = [⟨.i128, x⟩, ⟨.i128, y⟩]) ∨
      ∃ xl xh yl yh : BitVec 64, vals = [⟨.i64, xl⟩, ⟨.i64, xh⟩, ⟨.i64, yl⟩, ⟨.i64, yh⟩] := by
  rw [divOutcome_op] at h
  cases hdv : div128 (sgnOf op) (remOf op) vals with
  | none => rw [hdv] at h; exact absurd h.symm (ho _)
  | some o => exact div128_shape hdv

theorem noI128_of_tys {vs : List Val} {ps : List AbiParam} (h : vs.map (·.ty) = AbiParam.tys ps)
    (hv : ∀ v ∈ vs, v.ty ≠ .i128) : ∀ p ∈ ps, p.ty ≠ .i128 := by
  unfold AbiParam.tys at h
  intro p hp
  have hm : p.ty ∈ vs.map (·.ty) := by rw [h]; exact List.mem_map_of_mem hp
  obtain ⟨v, hv', he⟩ := List.mem_map.1 hm
  rw [← he]
  exact hv v hv'

/-- The `i128` form of a helper call, expanded by its declared signature: the pair form. -/
theorem wide_exp {sig : Signature} {gs : List (List SlotEl)} {x y : BitVec 128} {vals' : List Val}
    (hty : [(⟨.i128, x⟩ : Val), ⟨.i128, y⟩].map (·.ty) = AbiParam.tys sig.params)
    (hgs : groups sig.params = some gs) (hexp : ExpRel gs [⟨.i128, x⟩, ⟨.i128, y⟩] vals') :
    ∃ xl xh yl yh : BitVec 64,
      vals' = [⟨.i64, xl⟩, ⟨.i64, xh⟩, ⟨.i64, yl⟩, ⟨.i64, yh⟩] ∧ x = xh ++ xl ∧ y = yh ++ yl := by
  obtain ⟨p1, p2, hps, hp1, hp2⟩ :
      ∃ p1 p2 : AbiParam, sig.params = [p1, p2] ∧ p1.ty = .i128 ∧ p2.ty = .i128 := by
    rcases hps : sig.params with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, ps⟩⟩⟩ <;>
      simp [hps, AbiParam.tys] at hty
    exact ⟨p1, p2, rfl, hty.1.symm, hty.2.symm⟩
  rw [hps] at hgs
  cases groups_two128 hp1 hp2 hgs
  rcases vals' with _ | ⟨a1, _ | ⟨b1, _ | ⟨a2, _ | ⟨b2, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
    simp only [ExpRel, and_false] at hexp
  obtain ⟨⟨l1, h1, hx, rfl, rfl⟩, ⟨l2, h2, hy, rfl, rfl⟩, -⟩ := hexp
  exact ⟨l1, h1, l2, h2, rfl, eq_of_heq (Val.mk.inj hx).2, eq_of_heq (Val.mk.inj hy).2⟩

/-! ## `mem*` -/

theorem memArgs_some {vals : List Val} {t : Nat × Nat × Nat} (h : memArgs vals = some t) :
    ∃ a b c rest, vals = a :: b :: c :: rest ∧ a.ty = .i64 ∧ b.ty = .i64 ∧ c.ty = .i64 := by
  rcases vals with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [memArgs] at h
  · simp [memArgs] at h
  · simp [memArgs] at h
  · cases ha : a.as? .i64 <;> cases hb : b.as? .i64 <;> cases hc : c.as? .i64 <;>
      simp [memArgs, ha, hb, hc] at h
    exact ⟨a, b, c, rest, rfl, by rw [as?_some ha], by rw [as?_some hb], by rw [as?_some hc]⟩

theorem memOutcome_prefix (name : String) (a b c : Val) (r r' : List Val) (m : Mem) :
    memOutcome name (a :: b :: c :: r) m = memOutcome name (a :: b :: c :: r') m := rfl

theorem memcopy_allocs {m m' : Mem} {d s n : Nat} (h : memcopy m d s n = .ok m') :
    m'.allocs = m.allocs := by
  revert h
  unfold memcopy
  split
  · intro h; cases h; rfl
  · cases m.valid s n <;> cases m.valid d n <;> cases m.readonlyAt d n <;>
      simp [Res.check, bind, Res.bind] <;> (intro h; subst h; rfl)

theorem memstore_allocs {m m' : Mem} {d c n : Nat} (h : memstore m d c n = .ok m') :
    m'.allocs = m.allocs := by
  revert h
  unfold memstore
  cases m.valid d n <;> cases m.readonlyAt d n <;>
    simp [Res.check, bind, Res.bind] <;> (intro h; subst h; rfl)

theorem memOutcome_ret {name : String} {vals : List Val} {m m' : Mem} {rv : List Val}
    (h : memOutcome name vals m = .returned rv m') :
    (∀ v ∈ rv, v.ty ≠ .i128) ∧ m'.allocs = m.allocs := by
  unfold memOutcome at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · rename_i vs m2 hres
      cases h
      split at hres
      · cases hc : memcopy m _ _ _ <;> rw [hc] at hres <;> cases hres
        exact ⟨by simp [Val.ofInt], memcopy_allocs hc⟩
      · cases hc : memcopy m _ _ _ <;> rw [hc] at hres <;> cases hres
        exact ⟨by simp [Val.ofInt], memcopy_allocs hc⟩
      · cases hc : memstore m _ _ _ <;> rw [hc] at hres <;> cases hres
        exact ⟨by simp [Val.ofInt], memstore_allocs hc⟩
      · cases hc : memcmp m _ _ _ <;> rw [hc] at hres <;> cases hres
        exact ⟨by simp [Val.ofInt], rfl⟩
      · cases hres
    · cases h
    · cases h

/-! ## The contracts -/

/-- **`ExtLegal` for `Clif.Rust.env`.** -/
theorem extLegal_env : ExtLegal env := by
  intro name h hext sig gs rg hgs hrg vals vals' m hty hexp
  have hG := groups_spec hgs
  have hR := groups_spec hrg
  simp only [env] at hext
  by_cases hd : isDivHelper name = true
  · rw [ite_eq_left hd] at hext
    cases hext
    obtain ⟨op, rfl⟩ := isDivHelper_iff hd
    -- the pair form of the call: the arguments pass unchanged
    have hpair : ∀ xl xh yl yh : BitVec 64,
        vals = [⟨.i64, xl⟩, ⟨.i64, xh⟩, ⟨.i64, yl⟩, ⟨.i64, yh⟩] → vals' = vals := by
      intro xl xh yl yh hv
      subst hv
      exact expRel_val hG (noI128_of_tys hty (by simp)) hexp
    refine ⟨fun rv m' hr hrt => ?_, fun c hc => ?_⟩
    · dsimp only at hr ⊢
      rcases div_shape_of hr (by simp) with ⟨x, y, rfl⟩ | ⟨xl, xh, yl, yh, hv⟩
      · obtain ⟨xl, xh, yl, yh, rfl, rfl, rfl⟩ := wide_exp hty hgs hexp
        simp only [divOutcome_wide] at hr
        simp only [divOutcome_pair]
        split at hr
        · rename_i r hrr
          rw [hrr]
          simp only [Outcome.returned.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          refine ⟨_, rfl, ?_⟩
          obtain ⟨p, hps, hp⟩ : ∃ p : AbiParam, sig.returns = [p] ∧ p.ty = .i128 := by
            rcases hps : sig.returns with _ | ⟨p, _ | ⟨p2, ps⟩⟩ <;>
              simp [hps, AbiParam.tys] at hrt
            exact ⟨p, rfl, hrt.symm⟩
          rw [hps] at hrg
          cases groups_one128 hp hrg
          rw [outP_toNat]
          exact ⟨⟨_, _, by rw [← halves_split], rfl, rfl⟩, trivial⟩
        · cases hr
      · rw [hpair xl xh yl yh hv]
        refine ⟨rv, hr, expRel_refl hR hrt (noI128_of_tys hrt ?_)⟩
        subst hv
        simp only [divOutcome_pair] at hr
        split at hr
        · simp only [Outcome.returned.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          simp [outP]
        · cases hr
    · dsimp only at hc ⊢
      rcases div_shape_of hc (by simp) with ⟨x, y, rfl⟩ | ⟨xl, xh, yl, yh, hv⟩
      · obtain ⟨xl, xh, yl, yh, rfl, rfl, rfl⟩ := wide_exp hty hgs hexp
        simp only [divOutcome_wide] at hc
        simp only [divOutcome_pair]
        split at hc
        · cases hc
        · rename_i c' hrr
          rw [hrr]
          exact hc
      · rw [hpair xl xh yl yh hv]
        exact hc
  · rw [ite_eq_right hd] at hext
    by_cases hpn : isPanic name = true
    · rw [ite_eq_left hpn] at hext
      cases hext
      exact ⟨fun _ _ h _ => Outcome.noConfusion h, fun c h => h⟩
    · rw [ite_eq_right hpn] at hext
      by_cases hm : (name == "memcpy" || name == "memmove" || name == "memset" ||
          name == "memcmp") = true
      · rw [ite_eq_left hm] at hext
        cases hext
        have key : ∀ o, memOutcome name vals m = o → (∀ msg, o ≠ .stuck msg) →
            memOutcome name vals' m = o := by
          intro o ho hns
          cases hma : memArgs vals with
          | none =>
            simp only [memOutcome, hma] at ho
            exact absurd ho.symm (hns _)
          | some t =>
            obtain ⟨a, b, c, rest, rfl, ha, hb, hc⟩ := memArgs_some hma
            rcases hps : sig.params with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, ps⟩⟩⟩ <;>
              simp [hps, AbiParam.tys] at hty
            rw [hps] at hG
            rcases gs with _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, gs⟩⟩⟩ <;> try (simp [GroupsOf] at hG; done)
            obtain ⟨v1, rfl, hG1, he1⟩ := expRel_cons_val hG (by simp [← hty.1, ha]) hexp
            obtain ⟨v2, rfl, hG2, he2⟩ := expRel_cons_val hG1 (by simp [← hty.2.1, hb]) he1
            obtain ⟨v3, rfl, -, -⟩ := expRel_cons_val hG2 (by simp [← hty.2.2.1, hc]) he2
            rw [← ho]
            exact memOutcome_prefix ..
        exact ⟨fun rv m' hr hrt =>
            ⟨rv, key _ hr (by simp), expRel_refl hR hrt (noI128_of_tys hrt (memOutcome_ret hr).1)⟩,
          fun c hc => key _ hc (by simp)⟩
      · rw [ite_eq_right hm] at hext
        cases hext

/-- **`EnvKeepsAllocs` for `Clif.Rust.env`.** -/
theorem envKeepsAllocs_env : EnvKeepsAllocs env := by
  intro name h hext vals m rv m' hr
  simp only [env] at hext
  by_cases hd : isDivHelper name = true
  · rw [ite_eq_left hd] at hext
    cases hext
    simp only [divOutcome] at hr
    split at hr <;> cases hr
    rfl
  · rw [ite_eq_right hd] at hext
    by_cases hpn : isPanic name = true
    · rw [ite_eq_left hpn] at hext
      cases hext
      cases hr
    · rw [ite_eq_right hpn] at hext
      by_cases hm : (name == "memcpy" || name == "memmove" || name == "memset" ||
          name == "memcmp") = true
      · rw [ite_eq_left hm] at hext
        cases hext
        exact (memOutcome_ret hr).2
      · rw [ite_eq_right hm] at hext
        cases hext

end Clif.Rust
