import FV.Opt.Proof.RuleAuto

/-!
# Embedding lemmas and template variants for `opts/bitops.isle`

Lemmas: `all_zero ty` (Cranelift 0.136) is the extractor `inst_data_value_tupled (all_zero_etor
ty)`: the tupled node multi-extractor (`extractMulti_idvt`, one `.pair type node` per presented
node) and the `iconst 0` recogniser (`extract_all_zero_etor`, `ofInst_iconst_any`,
`imm64OfBits_eq_zero`); `iconst_s ty c` (`extract_iconst_sextend_etor`, `toInt_eq_neg_one`);
the constant arithmetic of the `iconst_u`/`iconst_s`/`all_zero`/`cmp_true` constructors on
presented types and at `i128` (where they build `uextend`/`sextend` of an `i64` constant);
`bswap`/`bitrev`/`popcnt` identities per width.

Template variants (the base template is `rule_auto`, `FV/Opt/Proof/RuleAuto.lean`):
- `rule_auto_b`: `rule_finish_b`, i.e. `rule_bits` with `Clif.Val` locals split
  (`opt_cases_val`), if-let conditions / `Option` equations normalised (`cond_simp`) and the
  reversal identities (`sem_simp_b`).
- `rule_auto_z`: `rule_auto_b` after splitting every type on `= .i128` (`opt_split_i128`).
- `rule_auto_i`: rules with if-lets: `rule_iflets` evaluates them after the left-hand side,
  splitting stuck `match`es and closed `if`s under binders (`opt_split_ite`).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

section
variable {σ : Type} (G : EGraph σ)

theorem extractMulti_idvt_eq (n : Nat) (s : St σ) :
    (sem G).extractMulti T.«inst_data_value_tupled» (.value n) s = match G.typeOf s.inner n with
      | some t => .ok (((G.enodes s.inner n).filterMap fun i =>
          (ofInst i).map (CTy.ofClif t, ·)).map fun (t, d) => [.pair t d])
      | none => .unmodeled s!"value_type: v{n} has no type" := by
  rw [sem_extractMulti]
  cases h : G.typeOf s.inner n <;> simp [h, Term.externExtractor?, T.«inst_data_value_tupled»,
    extractMultiFn, nodesOf, valueType, bind, Except.bind, pure, Except.pure, throw,
    throwThe, MonadExceptOf.throw]

/-- The `inst_data_value_tupled` multi-extractor on an e-class: one `[.pair type node]` per
presented node. -/
@[opt_match] theorem extractMulti_idvt (n : Nat) (s : St σ) (Q : List V → Prop) :
    (∃ fss, (sem G).extractMulti T.«inst_data_value_tupled» (.value n) s = .ok fss ∧
      ∃ fs ∈ fss, Q fs) ↔
    ∃ t, G.typeOf s.inner n = some t ∧ ∃ i ∈ G.enodes s.inner n, ∃ d, ofInst i = some d ∧
      Q [.pair (CTy.ofClif t) d] := by
  cases h : G.typeOf s.inner n with
  | none => simp [extractMulti_idvt_eq, h]
  | some t =>
    rw [extractMulti_idvt_eq, h]
    simp only [ExtResult.ok.injEq, exists_eq_left']
    constructor
    · rintro ⟨fs, hfs, hq⟩
      simp only [List.mem_map, List.mem_filterMap, Option.map_eq_some_iff] at hfs
      obtain ⟨⟨t', d⟩, ⟨i, hi, d', hd, he⟩, rfl⟩ := hfs
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨t, rfl, i, hi, d', hd, hq⟩
    · rintro ⟨t', ht, i, hi, d, hd, hq⟩
      cases ht
      refine ⟨_, ?_, hq⟩
      simp only [List.mem_map, List.mem_filterMap, Option.map_eq_some_iff]
      exact ⟨(CTy.ofClif t, d), ⟨i, hi, d, hd, rfl⟩, rfl⟩

/-- `all_zero_etor` on a `(type, node)` pair: the node is `iconst 0`. -/
@[opt_match] theorem extract_all_zero_etor (t : CTy) (d : V) (s : St σ) (fs : List V) :
    (sem G).extract T.«all_zero_etor» (.pair t d) s = .ok fs ↔
      ∃ a b, d = .data a 35 [.data b 57 [], .int 0] ∧ fs = [.ty t] := by
  rw [sem_extract]
  simp only [Term.externExtractor?, T.«all_zero_etor»]
  unfold extractFn
  simp only
  split
  · rename_i t' a' b' imm heq
    simp only [V.pair.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    by_cases h : imm = 0
    · subst h; simp [toExt, pure, Except.pure, eq_comm]
    · simp [toExt, pure, Except.pure, h]
  · rename_i t' d' hne heq
    simp only [V.pair.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [toExt, pure, Except.pure, reduceCtorEq, false_iff, not_exists, not_and]
    intro a b hd _
    exact hne a b 0 hd
  · rename_i hne
    exact absurd rfl (hne t d)

/-- `iconst_sextend_etor` on a `(type, node)` pair: the node is an `iconst`; its immediate
sign-extended from the type's width. -/
@[opt_match] theorem extract_iconst_sextend_etor (t : CTy) (d : V) (s : St σ) (fs : List V) :
    (sem G).extract T.«iconst_sextend_etor» (.pair t d) s = .ok fs ↔
      ∃ a b k, d = .data a 35 [.data b 57 [], .int k] ∧
        fs = [.ty t, .int (Rust.i64SextendImm64 t k)] := by
  rw [sem_extract]
  simp only [Term.externExtractor?, T.«iconst_sextend_etor»]
  unfold extractFn
  simp only
  split
  · rename_i t' a' b' imm heq
    simp only [V.pair.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [toExt, pure, Except.pure, ExtResult.ok.injEq]
    constructor
    · rintro rfl; exact ⟨_, _, _, rfl, rfl⟩
    · rintro ⟨_, _, _, h, rfl⟩
      simp only [V.data.injEq, List.cons.injEq, V.int.injEq] at h
      obtain ⟨-, -, ⟨-, -⟩, rfl, -⟩ := h
      rfl
  · rename_i t' d' hne heq
    simp only [V.pair.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [toExt, pure, Except.pure, reduceCtorEq, false_iff, not_exists, not_and]
    intro a b k hd _
    exact hne a b k hd
  · rename_i hne
    exact absurd rfl (hne t d)

end

/-- A presented node of the `iconst` shape (any type ids). -/
@[opt_match] theorem ofInst_iconst_any {i : Inst} {a b : Nat} {k : Int} :
    ofInst i = some (.data a 35 [.data b 57 [], .int k]) ↔
      ∃ t imm, t ≠ .i128 ∧ i = .iconst t imm ∧ a = 53 ∧ b = TyId.«Opcode» ∧ imm64OfBits imm = k := by
  constructor
  · intro h
    cases i
    case iconst t imm =>
      cases t <;> simp (config := {decide := true}) [ofInst, idata, opcode] at h ⊢ <;>
        obtain ⟨rfl, rfl, h⟩ := h <;> exact ⟨_, by decide, imm, ⟨rfl, HEq.rfl⟩, rfl, rfl, h⟩
    all_goals (try simp (config := {decide := true}) [ofInst, idata, opcode] at h)
    case extend op t x => cases op <;> simp [ofInst, idata, opcode] at h
  · rintro ⟨t, imm, ht, rfl, rfl, rfl, rfl⟩
    cases t <;> first | rfl | exact absurd rfl ht

/-- The zero immediate of a presented `iconst`. -/
@[opt_match] theorem imm64OfBits_eq_zero {t : Ty} (ht : t ≠ .i128) (b : BitVec t.width) :
    imm64OfBits b = 0 ↔ b = 0#t.width := by
  constructor
  · intro h
    rw [← ofInt_imm64OfBits ht b, h]
    rfl
  · rintro rfl
    cases t <;> first | rfl | exact absurd rfl ht

/-- The all-ones immediate (`iconst_s ty -1`). -/
@[opt_match] theorem toInt_eq_neg_one {t : Ty} (b : BitVec t.width) :
    b.toInt = -1 ↔ b = BitVec.allOnes t.width := by
  rw [← BitVec.toInt_inj, BitVec.toInt_allOnes]
  cases t <;> simp [Ty.width]

/-- The sign-extended immediate of a presented `iconst` is its signed value. -/
@[opt_match, opt_monad] theorem i64SextendImm64_imm64OfBits {t : Ty} (ht : t ≠ .i128)
    (b : BitVec t.width) : Rust.i64SextendImm64 (CTy.ofClif t) (imm64OfBits b) = b.toInt := by
  cases t
  all_goals first | exact absurd rfl ht | skip
  all_goals (unfold Rust.i64SextendImm64; rw [ofClif_bits]; exact sext_imm64OfBits (by decide) b)

/-- A type compared with an unknown environment value (a pattern variable bound twice). -/
@[opt_match] theorem V.beq_ty_left (a : CTy) (v : V) : V.beq (.ty a) v = true ↔ v = .ty a := by
  cases v
  case ty b => simp only [V.beq, beq_iff_eq, V.ty.injEq]; exact eq_comm
  all_goals (simp only [V.beq]; simp)

/-! ## Type helpers on presented types -/

@[opt_monad, opt_imm] theorem laneType_ofClif (t : Ty) : (CTy.ofClif t).laneType = CTy.ofClif t := by
  cases t <;> rfl

@[opt_monad, opt_imm] theorem tyBits_ofClif (t : Ty) : Rust.tyBits (CTy.ofClif t) = .ok (t.width : Int) := by
  cases t <;> rfl

/-- `ty_shift_mask`: `ty_bits - 1` never underflows. -/
@[opt_monad, opt_imm] theorem checkedSubU_width (fn : String) (t : Ty) :
    Rust.checkedSubU fn (t.width : Int) 1 = .ok ((t.width : Int) - 1) := by
  cases t <;> rfl

section
variable {σ : Type} (G : EGraph σ)

/-! ## Float type constants (the `all_zero` constructor's float arms never match a presented
type) -/

@[opt_match, opt_monad] theorem sem_prim_F16 : (sem G).prim 14 "F16" = some (.ty (.float 16)) := rfl
@[opt_match, opt_monad] theorem sem_prim_F32 : (sem G).prim 14 "F32" = some (.ty (.float 32)) := rfl
@[opt_match, opt_monad] theorem sem_prim_F64 : (sem G).prim 14 "F64" = some (.ty (.float 64)) := rfl
@[opt_match, opt_monad] theorem sem_prim_F128 : (sem G).prim 14 "F128" = some (.ty (.float 128)) := rfl

end

@[opt_match, opt_monad] theorem CTy.ofClif_beq_float (t : Ty) (b : Nat) :
    (CTy.ofClif t == .float b) = false := by
  cases t <;> rfl

@[opt_match, opt_monad] theorem V.beq_ty_ofClif_float (t : Ty) (b : Nat) :
    V.beq (.ty (CTy.ofClif t)) (.ty (.float b)) = false := by
  cases t <;> rfl

/-! ## `iconst_u ty 0` and `i128` (the `ty_int` arm of `all_zero` builds `iconst_u ty 0`; at
`i128` that is `uextend.i128 (iconst_u.i64 0)`) -/

@[opt_monad, opt_imm] theorem tyUmax_ofClif {t : Ty} (ht : t ≠ .i128) :
    Rust.tyUmax (CTy.ofClif t) = .ok (2 ^ t.width - 1) := by
  cases t <;> first | rfl | exact absurd rfl ht

@[opt_monad, opt_imm] theorem tyUmax_ofClif_i64 :
    Rust.tyUmax (CTy.ofClif .i64) = .ok (2 ^ 64 - 1) := rfl

@[opt_monad, opt_imm] theorem zero_le_umax (w : Nat) : ((0 : Int) ≤ 2 ^ w - 1) ↔ True := by
  simp only [iff_true]
  have h : 0 < 2 ^ w := Nat.two_pow_pos w
  have : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by simp
  omega

/-- The `Unary` opcodes that are not `Clif.UnaryOp`s (`toInst` of `uextend`, `sextend`,
`bmask`, `ireduce`), before `unaryOfIdx?` is unfolded. -/
@[opt_monad ↓] theorem unaryOfIdx?_uextend : unaryOfIdx? 141 = none := rfl
@[opt_monad ↓] theorem unaryOfIdx?_sextend : unaryOfIdx? 142 = none := rfl
@[opt_monad ↓] theorem unaryOfIdx?_bmask : unaryOfIdx? 130 = none := rfl
@[opt_monad ↓] theorem unaryOfIdx?_ireduce : unaryOfIdx? 131 = none := rfl

@[opt_monad, opt_imm] theorem fitsIn64_ofClif_i64 :
    Rust.fitsIn64 (CTy.ofClif .i64) = some (CTy.ofClif .i64) := rfl

@[opt_monad, opt_imm] theorem asI64_zero : Rust.asI64 0 = 0 := by decide
@[opt_monad, opt_imm] theorem asI64_one : Rust.asI64 1 = 1 := by decide

@[opt_monad, opt_imm] theorem one_le_umax (w : Nat) : ((1 : Int) ≤ 2 ^ (w + 1) - 1) ↔ True := by
  simp only [iff_true]
  have h : 2 ≤ 2 ^ (w + 1) := by
    rw [Nat.pow_succ]; have := Nat.two_pow_pos w; omega
  have : ((2 ^ (w + 1) : Nat) : Int) = (2 : Int) ^ (w + 1) := by simp
  omega

@[opt_monad, opt_imm] theorem one_le_umax_ty (t : Ty) : ((1 : Int) ≤ 2 ^ t.width - 1) ↔ True := by
  cases t <;> decide

@[opt_monad, opt_imm] theorem Ty.beq_i128_self : (Clif.Ty.i128 == Clif.Ty.i128) = true := rfl
@[opt_monad, opt_imm] theorem Ty.beq_i64_i128 : (Clif.Ty.i64 == Clif.Ty.i128) = false := rfl
@[opt_monad, opt_imm] theorem Ty.beq_i32_i128 : (Clif.Ty.i32 == Clif.Ty.i128) = false := rfl
@[opt_monad, opt_imm] theorem Ty.beq_i16_i128 : (Clif.Ty.i16 == Clif.Ty.i128) = false := rfl
@[opt_monad, opt_imm] theorem Ty.beq_i8_i128 : (Clif.Ty.i8 == Clif.Ty.i128) = false := rfl

@[opt_monad, opt_imm] theorem tyUmax_ofClif_i8 :
    Rust.tyUmax (CTy.ofClif .i8) = .ok (2 ^ 8 - 1) := rfl

@[opt_monad, opt_imm] theorem fitsIn64_ofClif_i8 :
    Rust.fitsIn64 (CTy.ofClif .i8) = some (CTy.ofClif .i8) := rfl

end Opt.Proof

namespace Opt.Proof
open Lean Meta Elab Tactic

/-- `opt_split_i128_one`: for the first local `t : Clif.Ty` without a hypothesis `t ≠ .i128`,
split on `t = .i128` (substituted) or `t ≠ .i128`; fails if there is none. -/
elab "opt_split_i128_one" : tactic => withMainContext do
  let lctx ← getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isConstOf ``Clif.Ty do continue
    let x := d.toExpr
    let isI128 (e : Expr) : Bool := e.isConstOf ``Clif.Ty.i128
    let mut has := false
    for d' in lctx do
      if d'.isImplementationDetail then continue
      let t ← instantiateMVars d'.type
      -- `x ≠ .i128` or `¬ x = .i128` (syntactically)
      let t := if t.isAppOfArity ``Not 1 then t.appArg! else t
      if (t.isAppOfArity ``Ne 3 || t.isAppOfArity ``Eq 3) && t.appFn!.appArg! == x &&
          isI128 t.appArg! && d'.type.isAppOfArity ``Eq 3 == false then
        has := true
        break
    if has then continue
    let xs ← Term.exprToSyntax d.toExpr
    evalTactic (← `(tactic| ((rcases Classical.em ($xs = Clif.Ty.i128) with h128 | h128) <;>
      try subst h128)))
    return
  throwError "opt_split_i128_one: nothing to split"

/-- Split every `Clif.Ty` local on `= .i128`. -/
macro "opt_split_i128" : tactic => `(tactic| repeat (any_goals opt_split_i128_one))

end Opt.Proof

namespace Opt.Proof
open Lean Meta Elab Tactic

/-- `opt_cases_val`: `cases` every local `Clif.Val` (a class value read without a type, e.g. the
operand of `bmask`), so that its type can be split by `opt_cases_ty`. -/
elab "opt_cases_val" : tactic => do
  let rec go (g : MVarId) (fuel : Nat) : MetaM (List MVarId) := g.withContext do
    if fuel = 0 then return [g]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.isConstOf ``Clif.Val then
        let gs ← g.cases d.fvarId
        return (← gs.toList.mapM fun s => go s.mvarId (fuel - 1)).flatten
    return [g]
  let gs ← getGoals
  let mut out := []
  for g in gs do out := out ++ (← go g 10)
  setGoals out

end Opt.Proof

namespace Opt.Proof

open Isle Isle.Opt Clif

/-! ## `iconst_s ty -1` (the constructor's if-lets on a presented type) -/

@[opt_monad, opt_imm] theorem asU64_neg_one : Rust.asU64 (-1) = 2 ^ 64 - 1 := by decide

@[opt_monad, opt_imm] theorem band64_umax {t : Ty} (ht : t ≠ .i128) :
    Rust.band64 (2 ^ 64 - 1) (2 ^ t.width - 1) = 2 ^ t.width - 1 := by
  cases t <;> first | decide | exact absurd rfl ht

@[opt_monad, opt_imm] theorem band64_umax_i64 :
    Rust.band64 (2 ^ 64 - 1) (2 ^ 64 - 1) = 2 ^ 64 - 1 := by decide

@[opt_monad, opt_imm] theorem i64SextendU64_umax {t : Ty} (ht : t ≠ .i128) :
    Rust.i64SextendU64 (CTy.ofClif t) (2 ^ t.width - 1) = .ok (-1) := by
  cases t <;> first | rfl | exact absurd rfl ht

@[opt_monad, opt_imm] theorem i64SextendU64_umax_i64 :
    Rust.i64SextendU64 (CTy.ofClif .i64) (2 ^ 64 - 1) = .ok (-1) := rfl

@[opt_monad, opt_imm] theorem int_beq_neg_one : ((-1 : Int) == -1) = true := by decide

@[opt_monad, opt_imm] theorem ofInt_asI64_umax {t : Ty} (ht : t ≠ .i128) :
    BitVec.ofInt t.width (Rust.asI64 (2 ^ t.width - 1)) = BitVec.allOnes t.width := by
  cases t <;> first | decide | exact absurd rfl ht

@[opt_monad, opt_imm] theorem ofInt_asI64_umax_i64 :
    BitVec.ofInt Clif.Ty.i64.width (Rust.asI64 (2 ^ 64 - 1)) = BitVec.allOnes Clif.Ty.i64.width := by
  decide

/-! ## Byte and bit reversal (standalone, so that the rule proofs do not unroll them) -/

macro "bswap_unroll" : tactic => `(tactic| simp only [Clif.Sem.bswap, Clif.Sem.popcnt,
  List.range_succ, List.range_zero, List.foldl, List.nil_append, List.cons_append, Nat.reduceDiv,
  Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub])

theorem bswap_bswap_8 (x : BitVec 8) : Clif.Sem.bswap (Clif.Sem.bswap x) = x := by
  bswap_unroll; bv_decide
theorem popcnt_bswap_8 (x : BitVec 8) : Clif.Sem.popcnt (Clif.Sem.bswap x) = Clif.Sem.popcnt x := by
  bswap_unroll; bv_decide
theorem bswap_bswap_16 (x : BitVec 16) : Clif.Sem.bswap (Clif.Sem.bswap x) = x := by
  bswap_unroll; bv_decide
theorem popcnt_bswap_16 (x : BitVec 16) : Clif.Sem.popcnt (Clif.Sem.bswap x) = Clif.Sem.popcnt x := by
  bswap_unroll; bv_decide
theorem bswap_bswap_32 (x : BitVec 32) : Clif.Sem.bswap (Clif.Sem.bswap x) = x := by
  bswap_unroll; bv_decide
theorem popcnt_bswap_32 (x : BitVec 32) : Clif.Sem.popcnt (Clif.Sem.bswap x) = Clif.Sem.popcnt x := by
  bswap_unroll; bv_decide
theorem bswap_bswap_64 (x : BitVec 64) : Clif.Sem.bswap (Clif.Sem.bswap x) = x := by
  bswap_unroll; bv_decide
theorem popcnt_bswap_64 (x : BitVec 64) : Clif.Sem.popcnt (Clif.Sem.bswap x) = Clif.Sem.popcnt x := by
  bswap_unroll; bv_decide
theorem bswap_bswap_128 (x : BitVec 128) : Clif.Sem.bswap (Clif.Sem.bswap x) = x := by
  bswap_unroll; bv_decide
theorem popcnt_bswap_128 (x : BitVec 128) : Clif.Sem.popcnt (Clif.Sem.bswap x) = Clif.Sem.popcnt x := by
  bswap_unroll; bv_decide

theorem bswap_bswap (t : Clif.Ty) (x : BitVec t.width) : Clif.Sem.bswap (Clif.Sem.bswap x) = x := by
  cases t
  · exact bswap_bswap_8 x
  · exact bswap_bswap_16 x
  · exact bswap_bswap_32 x
  · exact bswap_bswap_64 x
  · exact bswap_bswap_128 x

theorem popcnt_bswap (t : Clif.Ty) (x : BitVec t.width) :
    Clif.Sem.popcnt (Clif.Sem.bswap x) = Clif.Sem.popcnt x := by
  cases t
  · exact popcnt_bswap_8 x
  · exact popcnt_bswap_16 x
  · exact popcnt_bswap_32 x
  · exact popcnt_bswap_64 x
  · exact popcnt_bswap_128 x

theorem bitrev_bitrev {w : Nat} (x : BitVec w) : Clif.Sem.bitrev (Clif.Sem.bitrev x) = x :=
  BitVec.reverse_reverse_eq

theorem popcnt_bitrev {w : Nat} (x : BitVec w) :
    Clif.Sem.popcnt (Clif.Sem.bitrev x) = Clif.Sem.popcnt x :=
  BitVec.cpop_reverse x

/-- An `Int` immediate comparison on the bits of an `iconst` (if-let conditions). -/
theorem natCast_toNat_eq_int {w : Nat} (a : BitVec w) (k : Int) :
    ((a.toNat : Int) = k) ↔ (0 ≤ k ∧ a.toNat = k.toNat) := by
  omega

/-- The Boolean if-let conditions and `Option` equations of the context, normalised for
`bv_decide`. -/
macro "cond_simp" : tactic => `(tactic| (try simp (config := {decide := true}) only [beq_true,
    beq_iff_eq, natCast_toNat_eq_int, Int.cast_ofNat_Int, Int.reduceSub, Int.reduceToNat, Int.reduceLE,
    toNat_eq_iff_ofNat, true_and, Option.some.injEq, Nat.reducePow, Nat.reduceLT, BitVec.ofInt_ofNat,
    Int.reduceNeg] at *))

/-- `sem_simp` plus the bit-reordering operations (`bswap` unrolled at a literal width,
`bitrev` = `BitVec.reverse`, `popcnt` = `BitVec.cpop`, both read by `bv_decide`). -/
macro "sem_simp_b" : tactic => `(tactic| (
  cond_simp
  (try sem_simp)
  cond_simp
  (try simp only [Clif.Sem.bswap, Clif.Sem.bitrev, Clif.Sem.popcnt, List.range_succ, List.range_zero,
    List.foldl, List.nil_append, List.cons_append, List.foldl_cons, List.foldl_nil, Nat.reduceDiv,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.reverse_reverse_eq])))

/-- `rule_bits` with `Val` locals split and `sem_simp_b`. -/
macro "rule_bits_b" : tactic => `(tactic| (
  try simp (disch := assumption) only [asU64_imm64OfBits, Int.natCast_eq_zero, Int.natCast_inj,
    toNat_eq_iff_ofNat, ofInt_imm64OfBits, bne_iff_ne, ne_eq, toNat_eq_zero_iff] at *
  opt_destruct
  all_goals subst_vars
  all_goals first
    | (simp only [val_some_eq, val_mk_same]; done)
    | rfl
    | (first | apply some_val_congr | apply val_congr | skip
       first
         | (simp only [Clif.Sem.binary, Clif.Sem.unary, Clif.Sem.iadd, Clif.Sem.imul, Clif.Sem.band,
              Clif.Sem.bor, Clif.Sem.bxor]
            ac_rfl)
         | (simp only [Clif.Sem.unary, bswap_bswap, popcnt_bswap, bitrev_bitrev, popcnt_bitrev]; done)
         | (opt_cases_val <;> opt_cases_ty <;> opt_widths <;> sem_simp_b <;> first | ac_rfl | bv_decide))))

set_option hygiene false in
macro "rule_finish_var_b" : tactic => `(tactic| (
  try dsimp only
  apply Valuation.le_trans hle1 hle3
  opt_rw_lhs
  rule_bits_b))

set_option hygiene false in
macro "rule_finish_make_b" : tactic => `(tactic| (
  try dsimp only
  apply GraphOk.make_val hG (by opt_P)
  opt_node
  all_goals rule_bits_b))

macro "rule_finish_b" : tactic => `(tactic| first | rule_finish_var_b | rule_finish_make_b)

/-- A `toInst` match split after the fact leaves `some i = some j`: substitute. -/
macro "opt_some_subst" : tactic => `(tactic| (try (simp only [Option.some.injEq] at *; subst_vars)))

/-- `rule_auto` with `rule_finish_b`. -/
syntax "rule_auto_b " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_b $r:ident) => `(tactic| rule_auto_b $r [])
  | `(tactic| rule_auto_b $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_no_iflets
      rule_lhs hG
      all_goals (rule_rhs [$ts,*]; opt_some_subst; rule_finish_b)))

/-- `rule_auto_b` with the `i128` split before the right-hand side (constructors such as
`iconst_u`/`all_zero` take another arm at `i128`). -/
syntax "rule_auto_z " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_z $r:ident) => `(tactic| rule_auto_z $r [])
  | `(tactic| rule_auto_z $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_no_iflets
      rule_lhs hG
      all_goals opt_split_i128
      all_goals (rule_rhs [$ts,*]; opt_some_subst; rule_finish_b)))

end Opt.Proof

namespace Opt.Proof
open Lean Meta Elab Tactic

/-- `opt_split_ite h`: find the first closed `if c then _ else _` in `h` (also under binders,
where `split` does not look) and split on `c`, rewriting it away. -/
elab "opt_split_ite " h:ident : tactic => withMainContext do
  let some ld := (← getLCtx).findFromUserName? h.getId | throwError "opt_split_ite: no {h}"
  let ty ← instantiateMVars ld.type
  let found? := ty.find? fun e => e.isAppOfArity ``ite 5 && !(e.getArg! 1).hasLooseBVars
  let some e := found? | throwError "opt_split_ite: no closed if"
  let c ← Term.exprToSyntax (e.getArg! 1)
  evalTactic (← `(tactic| (by_cases hc : $c <;>
    simp only [hc, ite_true, ite_false, not_false_eq_true, reduceIte] at $h:ident)))

end Opt.Proof

namespace Opt.Proof

set_option hygiene false in
/-- Phase 3 for rules with if-lets: evaluate them (after the left-hand side), split on every
stuck `match`/`if` (a Boolean if-let condition becomes a hypothesis), drop the failing branches. -/
macro "rule_iflets" : tactic => `(tactic| (
  opt_eval hil
  repeat' ((first | split at hil | opt_split_ite hil) <;> try opt_eval hil)
  all_goals (try (simp at hil; done))
  all_goals (
    simp only [Except.ok.injEq, Prod.mk.injEq] at hil
    obtain ⟨rfl, rfl, rfl⟩ := hil
    simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at henv2)
  all_goals subst henv2))

/-- The template for rules with if-lets. -/
syntax "rule_auto_i " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_i $r:ident) => `(tactic| rule_auto_i $r [])
  | `(tactic| rule_auto_i $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs hG
      all_goals rule_iflets
      all_goals (rule_rhs [$ts,*]; opt_some_subst; rule_finish_b)))

end Opt.Proof
