import FV.Opt.Proof.RuleBase
import FV.Opt.Proof.RuleData
import FV.Opt.Proof.RuleNode
import FV.Opt.Proof.RuleTactic

/-!
# The mid-end embedding, for unfolding rule patterns

Simp lemmas (`opt_match`) that turn the relational reading of a rule's left-hand side
(`ArgsRel`/`PatRel` on the rule's concrete patterns, `FV/Opt/Proof/InterpMatch.lean`) into
facts about the e-graph: the `inst_data_value` multi-extractor yields one `(type, node)` per
node of the class (`extractMulti_idv`), `InstructionData` values are presented nodes
(`ofInst_*` inversion), extern extractors are their Lean transcriptions (`extractFn_*`, by
`rfl`), and enum/opcode indices are decided.
-/

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

attribute [opt_match] PatRel ArgsRel AllRel except_pure_eq_ok

section
variable {σ : Type} (G : EGraph σ)

@[opt_match] theorem sem_unData {ty k : Nat} {v : V} {fs : List V} :
    (sem G).unData ty v = some (k, fs) ↔ v = .data ty k fs := by
  cases v with
  | data ty' k' fs' =>
    simp only [sem, V.data.injEq]
    constructor
    · intro h
      split at h
      · rename_i hty
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨(beq_iff_eq.1 hty).symm, rfl, rfl⟩
      · cases h
    · rintro ⟨rfl, rfl, rfl⟩
      simp
  | _ => simp [sem]

@[opt_match] theorem sem_int (ty : TypeId) (i : Int) : (sem G).int ty i = .int (normInt ty i) := rfl
@[opt_match] theorem sem_bool (b : Bool) : (sem G).bool b = .bool b := rfl
@[opt_match] theorem sem_eq (a b : V) : (sem G).eq a b = V.beq a b := rfl
@[opt_match] theorem sem_mkData (ty k : Nat) (fs : List V) : (sem G).mkData ty k fs = .data ty k fs := rfl

theorem sem_extractMulti (t : Term) (v : V) (s : St σ) :
    (sem G).extractMulti t v s = match t.externExtractor? with
      | some fn => match extractMultiFn G fn v s with
        | .ok vs => .ok vs
        | .error e => .unmodeled e
      | none => .unmodeled s!"{t.name} has no extern extractor" := rfl

theorem sem_extract (t : Term) (v : V) (s : St σ) :
    (sem G).extract t v s = match t.externExtractor? with
      | some fn => toExt (extractFn G fn v s)
      | none => .unmodeled s!"{t.name} has no extern extractor" := rfl

theorem sem_ctor (t : Term) (args : List V) (s : St σ) :
    (sem G).ctor t args s = match t.externCtor? with
      | some fn => toExt (ctorFn G fn args s)
      | none => .unmodeled s!"{t.name} has no extern constructor" := rfl

@[opt_match] theorem toExt_eq_ok {α : Type} {r : R (Option α)} {a : α} :
    toExt r = .ok a ↔ r = .ok (some a) := by
  unfold toExt
  split <;> simp_all

theorem extractMulti_idv_eq (n : Nat) (s : St σ) :
    (sem G).extractMulti T.«inst_data_value» (.value n) s = match G.typeOf s.inner n with
      | some t => .ok (((G.enodes s.inner n).filterMap fun i =>
          (ofInst i).map (CTy.ofClif t, ·)).map fun (t, d) => [.ty t, d])
      | none => .unmodeled s!"value_type: v{n} has no type" := by
  rw [sem_extractMulti]
  cases h : G.typeOf s.inner n <;> simp [h, Term.externExtractor?, T.«inst_data_value»,
    extractMultiFn, nodesOf, valueType, bind, Except.bind, pure, Except.pure, throw,
    throwThe, MonadExceptOf.throw]

/-- The `inst_data_value` multi-extractor on an e-class: one `[type, node]` per presented node. -/
@[opt_match] theorem extractMulti_idv (n : Nat) (s : St σ) (Q : List V → Prop) :
    (∃ fss, (sem G).extractMulti T.«inst_data_value» (.value n) s = .ok fss ∧ ∃ fs ∈ fss, Q fs) ↔
    ∃ t, G.typeOf s.inner n = some t ∧ ∃ i ∈ G.enodes s.inner n, ∃ d, ofInst i = some d ∧
      Q [.ty (CTy.ofClif t), d] := by
  cases h : G.typeOf s.inner n with
  | none => simp [extractMulti_idv_eq, h]
  | some t =>
    rw [extractMulti_idv_eq, h]
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

/-- `extractMulti_idv` with the model's facts about the class and each node (for a state
satisfying the caller's invariant). -/
theorem extractMulti_idv_sem {P : σ → Prop} {den : σ → Valuation} {fr : Frame}
    {mem : Mem} (hG : GraphOk G P den fr mem) {s : St σ} (hP : P s.inner) (n : Nat)
    (Q : List V → Prop) :
    (∃ fss, (sem G).extractMulti T.«inst_data_value» (.value n) s = .ok fss ∧ ∃ fs ∈ fss, Q fs) ↔
    ∃ t, G.typeOf s.inner n = some t ∧ (∀ c, den s.inner n = some c → c.ty = t) ∧
      ∃ i ∈ G.enodes s.inner n,
        (∀ c, den s.inner n = some c → evalNode { fr with regs := den s.inner } mem i = some c) ∧
        ∃ d, ofInst i = some d ∧ Q [.ty (CTy.ofClif t), d] := by
  rw [extractMulti_idv]
  constructor
  · rintro ⟨t, ht, i, hi, d, hd, hq⟩
    exact ⟨t, ht, fun c hc => hG.model.types _ _ _ _ hP ht hc, i, hi,
      fun c hc => hG.model.nodes _ _ _ hP hc i hi, d, hd, hq⟩
  · rintro ⟨t, ht, -, i, hi, -, d, hd, hq⟩
    exact ⟨t, ht, i, hi, d, hd, hq⟩

/-- The model's fact about a node of a class with a known value (added by `opt_model`). -/
theorem GraphOk.node_val {G : EGraph σ} {P : σ → Prop} {den : σ → Valuation} {fr : Frame} {mem : Mem}
    (hG : GraphOk G P den fr mem) {st : σ} {x : Nat} {i : Inst} {c : Val}
    (hm : i ∈ G.enodes st x) (hc : den st x = some c) :
    P st → evalNode { fr with regs := den st } mem i = some c :=
  fun hP => hG.model.nodes st x c hP hc i hm

/-- The model's fact about the type of a class with a known value (added by `opt_model`). -/
theorem GraphOk.type_val {G : EGraph σ} {P : σ → Prop} {den : σ → Valuation} {fr : Frame} {mem : Mem}
    (hG : GraphOk G P den fr mem) {st : σ} {x : Nat} {t : Ty} {c : Val}
    (ht : G.typeOf st x = some t) (hc : den st x = some c) : P st → c.ty = t :=
  fun hP => hG.model.types st x t c hP ht hc

/-! ### `make` in the model -/

theorem GraphOk.make_P {G : EGraph σ} {P : σ → Prop} {den : σ → Valuation} {fr : Frame}
    {mem : Mem} (hG : GraphOk G P den fr mem) {st : σ} (hP : P st) (i : Inst) :
    P (G.make st i).2 := (hG.make st i hP).1

theorem GraphOk.make_le {G : EGraph σ} {P : σ → Prop} {den : σ → Valuation} {fr : Frame}
    {mem : Mem} (hG : GraphOk G P den fr mem) {st : σ} (hP : P st) (i : Inst) :
    Valuation.Le (den st) (den (G.make st i).2) := (hG.make st i hP).2.1

theorem GraphOk.make_val {G : EGraph σ} {P : σ → Prop} {den : σ → Valuation} {fr : Frame}
    {mem : Mem} (hG : GraphOk G P den fr mem) {st : σ} (hP : P st) {i : Inst} {b : Val}
    (h : evalNode { fr with regs := den st } mem i = some b) :
    den (G.make st i).2 (G.make st i).1 = some b := (hG.make st i hP).2.2 b h

/-! ### Single extern extractors (each `rfl` to its transcription, then `toExt`) -/

theorem toExt_ok_some {α : Type} (a : α) : toExt (.ok (some a) : R (Option α)) = .ok a := rfl

@[opt_match] theorem extract_value_type (n : Nat) (s : St σ) (fs : List V) :
    (sem G).extract T.«value_type» (.value n) s = .ok fs ↔
      ∃ t, G.typeOf s.inner n = some t ∧ fs = [.ty (CTy.ofClif t)] := by
  have : (sem G).extract T.«value_type» (.value n) s =
      toExt (valueType G s (.value n) >>= fun t => pure (some [.ty t])) := rfl
  rw [this]
  cases h : G.typeOf s.inner n <;>
    simp [valueType, h, toExt, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw, eq_comm]

theorem extract_value_type_sem {P : σ → Prop} {den : σ → Valuation} {fr : Frame}
    {mem : Mem} (hG : GraphOk G P den fr mem) {s : St σ} (hP : P s.inner) (n : Nat)
    (fs : List V) :
    (sem G).extract T.«value_type» (.value n) s = .ok fs ↔
      ∃ t, G.typeOf s.inner n = some t ∧ (∀ c, den s.inner n = some c → c.ty = t) ∧
        fs = [.ty (CTy.ofClif t)] := by
  rw [extract_value_type]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, fun c hc => hG.model.types _ _ _ _ hP ht hc, rfl⟩
  · rintro ⟨t, ht, -, rfl⟩; exact ⟨t, ht, rfl⟩

/-- An extractor on a `Type` that is `Option.map (fun t => [.ty t])` of a Rust predicate. -/
theorem extract_tyIf {t : Term} {fn : String} (ht : t.externExtractor? = some fn)
    {f : CTy → Option CTy} (hf : ∀ (ty : CTy) (s : St σ), extractFn G fn (.ty ty) s =
      .ok ((f ty).map fun t => [.ty t])) (ty : CTy) (s : St σ) (fs : List V) :
    (sem G).extract t (.ty ty) s = .ok fs ↔ ∃ t', f ty = some t' ∧ fs = [.ty t'] := by
  rw [sem_extract, ht]
  simp only
  rw [hf]
  cases f ty <;> simp [toExt, eq_comm]

@[opt_match] theorem extract_fits_in_64 (ty : CTy) (s : St σ) (fs : List V) :
    (sem G).extract T.«fits_in_64» (.ty ty) s = .ok fs ↔
      ∃ t', Rust.fitsIn64 ty = some t' ∧ fs = [.ty t'] :=
  extract_tyIf G rfl (fun _ _ => rfl) ty s fs

@[opt_match] theorem extract_ty_int_ref_scalar_64 (ty : CTy) (s : St σ) (fs : List V) :
    (sem G).extract T.«ty_int_ref_scalar_64_extract» (.ty ty) s = .ok fs ↔
      ∃ t', Rust.tyIntRefScalar64 ty = some t' ∧ fs = [.ty t'] :=
  extract_tyIf G rfl (fun _ _ => rfl) ty s fs

@[opt_match] theorem extract_ty_int (ty : CTy) (s : St σ) (fs : List V) :
    (sem G).extract T.«ty_int» (.ty ty) s = .ok fs ↔
      ∃ t', Rust.tyInt ty = some t' ∧ fs = [.ty t'] :=
  extract_tyIf G rfl (fun _ _ => rfl) ty s fs

@[opt_match] theorem extract_ty_vec128 (ty : CTy) (s : St σ) (fs : List V) :
    (sem G).extract T.«ty_vec128» (.ty ty) s = .ok fs ↔
      ∃ t', Rust.tyVec128 ty = some t' ∧ fs = [.ty t'] :=
  extract_tyIf G rfl (fun _ _ => rfl) ty s fs

@[opt_match] theorem extract_ty_vector (ty : CTy) (s : St σ) (fs : List V) :
    (sem G).extract T.«ty_vector» (.ty ty) s = .ok fs ↔
      ∃ t', Rust.tyVector ty = some t' ∧ fs = [.ty t'] :=
  extract_tyIf G rfl (fun _ _ => rfl) ty s fs

@[opt_match] theorem extract_u64_from_imm64 (k : Int) (s : St σ) (fs : List V) :
    (sem G).extract T.«u64_from_imm64» (.int k) s = .ok fs ↔ fs = [.int (Rust.asU64 k)] := by
  have : (sem G).extract T.«u64_from_imm64» (.int k) s = toExt (.ok (some [.int (Rust.asU64 k)])) :=
    rfl
  rw [this, toExt_ok_some]; simp [eq_comm]

@[opt_match] theorem extract_imm64_power_of_two (k : Int) (s : St σ) (fs : List V) :
    (sem G).extract T.«imm64_power_of_two» (.int k) s = .ok fs ↔
      ∃ e, Rust.imm64PowerOfTwo k = some e ∧ fs = [.int e] := by
  have : (sem G).extract T.«imm64_power_of_two» (.int k) s =
      toExt (.ok ((Rust.imm64PowerOfTwo k).map fun i => [.int i])) := rfl
  rw [this]
  cases Rust.imm64PowerOfTwo k <;> simp [toExt, eq_comm]

@[opt_match] theorem extract_u32_matches_non_zero (k : Int) (s : St σ) (fs : List V) :
    (sem G).extract T.«u32_matches_non_zero» (.int k) s = .ok fs ↔ fs = [.bool (k != 0)] := by
  have : (sem G).extract T.«u32_matches_non_zero» (.int k) s = toExt (.ok (some [.bool (k != 0)])) :=
    rfl
  rw [this, toExt_ok_some]; simp [eq_comm]

@[opt_match] theorem extract_u64_matches_non_zero (k : Int) (s : St σ) (fs : List V) :
    (sem G).extract T.«u64_matches_non_zero» (.int k) s = .ok fs ↔ fs = [.bool (k != 0)] := by
  have : (sem G).extract T.«u64_matches_non_zero» (.int k) s = toExt (.ok (some [.bool (k != 0)])) :=
    rfl
  rw [this, toExt_ok_some]; simp [eq_comm]

@[opt_match] theorem extract_i64_matches_non_zero (k : Int) (s : St σ) (fs : List V) :
    (sem G).extract T.«i64_matches_non_zero» (.int k) s = .ok fs ↔ fs = [.bool (k != 0)] := by
  have : (sem G).extract T.«i64_matches_non_zero» (.int k) s = toExt (.ok (some [.bool (k != 0)])) :=
    rfl
  rw [this, toExt_ok_some]; simp [eq_comm]

@[opt_match] theorem extract_u64_matches_power_of_two (k : Int) (s : St σ) (fs : List V) :
    (sem G).extract T.«u64_matches_power_of_two» (.int k) s = .ok fs ↔
      fs = [.bool (Rust.isPow2 k)] := by
  have : (sem G).extract T.«u64_matches_power_of_two» (.int k) s =
      toExt (.ok (some [.bool (Rust.isPow2 k)])) := rfl
  rw [this, toExt_ok_some]; simp [eq_comm]

@[opt_match] theorem extract_i32_from_i64 (k : Int) (s : St σ) (fs : List V) :
    (sem G).extract T.«i32_from_i64» (.int k) s = .ok fs ↔ Rust.inI32 k = true ∧ fs = [.int k] := by
  have : (sem G).extract T.«i32_from_i64» (.int k) s =
      toExt (.ok (if Rust.inI32 k then some [.int k] else none)) := rfl
  rw [this]
  cases Rust.inI32 k <;> simp [toExt, eq_comm]

@[opt_match] theorem extract_u32_from_u64 (k : Int) (s : St σ) (fs : List V) :
    (sem G).extract T.«u32_from_u64» (.int k) s = .ok fs ↔ Rust.inU32 k = true ∧ fs = [.int k] := by
  have : (sem G).extract T.«u32_from_u64» (.int k) s =
      toExt (.ok (if Rust.inU32 k then some [.int k] else none)) := rfl
  rw [this]
  cases Rust.inU32 k <;> simp [toExt, eq_comm]

@[opt_match] theorem extract_value_array_2 (a b : V) (s : St σ) (fs : List V) :
    (sem G).extract T.«value_array_2» (.values [a, b]) s = .ok fs ↔ fs = [a, b] := by
  have : (sem G).extract T.«value_array_2» (.values [a, b]) s = toExt (.ok (some [a, b])) := rfl
  rw [this, toExt_ok_some]; simp [eq_comm]

@[opt_match] theorem extract_value_array_3 (a b c : V) (s : St σ) (fs : List V) :
    (sem G).extract T.«value_array_3» (.values [a, b, c]) s = .ok fs ↔ fs = [a, b, c] := by
  have : (sem G).extract T.«value_array_3» (.values [a, b, c]) s = toExt (.ok (some [a, b, c])) := rfl
  rw [this, toExt_ok_some]; simp [eq_comm]

end

/-! ## `ofInst` inversion -/

set_option hygiene false in
/-- The forward direction of an `ofInst` inversion: `cases` on the node (and its extend op /
`iconst` type), compute `ofInst`, then close the matching disjunct. -/
macro "ofInst_fwd" : tactic => `(tactic| (
  intro h
  cases i
  case iconst t imm =>
    cases t <;> simp (config := {decide := true}) [ofInst, idata] at h <;>
      exact ⟨_, _, by decide, rfl, h.symm⟩
  case extend op t x =>
    cases op <;> (try simp (config := {decide := true}) [ofInst, idata] at h) <;> (subst h; simp)
  all_goals (try simp (config := {decide := true}) [ofInst, idata] at h)
  all_goals (subst h; simp; try exact ⟨_, _, _, _, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩)))

@[opt_match] theorem ofInst_unaryImm {i : Inst} {fs : List V} :
    ofInst i = some (.data 53 35 fs) ↔
      ∃ t imm, t ≠ .i128 ∧ i = .iconst t imm ∧
        fs = [opcode 57, .int (imm64OfBits imm)] := by
  constructor
  · ofInst_fwd
  · rintro ⟨t, imm, ht, rfl, rfl⟩
    cases t <;> first | rfl | exact absurd rfl ht

@[opt_match] theorem ofInst_unary {i : Inst} {fs : List V} :
    ofInst i = some (.data 53 29 fs) ↔
      (∃ op t x, i = .unary op t x ∧ fs = [opcode (unaryIdx op), .value x]) ∨
      (∃ t x, i = .bmask t x ∧ fs = [opcode 130, .value x]) ∨
      (∃ t x, i = .extend .uextend t x ∧ fs = [opcode 141, .value x]) ∨
      (∃ t x, i = .extend .sextend t x ∧ fs = [opcode 142, .value x]) ∨
      (∃ t x, i = .ireduce t x ∧ fs = [opcode 131, .value x]) := by
  constructor
  · ofInst_fwd
  · rintro (⟨_, _, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩ |
      ⟨_, _, rfl, rfl⟩) <;> rfl

@[opt_match] theorem ofInst_binary {i : Inst} {fs : List V} :
    ofInst i = some (.data 53 2 fs) ↔
      (∃ op t x y, i = .binary op t x y ∧
        fs = [opcode (binaryIdx op), .values [.value x, .value y]]) ∨
      (∃ t x y, i = .iconcat t x y ∧
        fs = [opcode 155, .values [.value x, .value y]]) := by
  constructor
  · ofInst_fwd
  · rintro (⟨_, _, _, _, rfl, rfl⟩ | ⟨_, _, _, rfl, rfl⟩) <;> rfl

/-! ## `V.beq` on constructors -/

@[opt_match] theorem V.beq_ty (a b : CTy) : V.beq (.ty a) (.ty b) = (a == b) := rfl
@[opt_match] theorem V.beq_int (a b : Int) : V.beq (.int a) (.int b) = (a == b) := rfl
@[opt_match] theorem V.beq_value (a b : Nat) : V.beq (.value a) (.value b) = (a == b) := rfl
@[opt_match] theorem V.beq_bool (a b : Bool) : V.beq (.bool a) (.bool b) = (a == b) := rfl

/-! ## Types and immediates -/

@[opt_match] theorem CTy.ofClif_inj {a b : Ty} : CTy.ofClif a = CTy.ofClif b ↔ a = b := by
  cases a <;> cases b <;> simp [CTy.ofClif]

/-- The `u64` of a presented (non-`i128`) `iconst` immediate is its bits. -/
theorem asU64_imm64OfBits {t : Ty} (ht : t ≠ .i128) (b : BitVec t.width) :
    Rust.asU64 (imm64OfBits b) = b.toNat := by
  have hw : t.width ≤ 64 := by cases t <;> simp_all [Ty.width]
  have hlt : b.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) hw)
  simp only [Rust.asU64, imm64OfBits, Rust.asI64]
  rw [BitVec.toNat_ofInt]
  simp only [BitVec.toInt, BitVec.toNat_ofInt]
  split <;> simp_all <;> omega

theorem toNat_eq_zero_iff {w : Nat} (b : BitVec w) : b.toNat = 0 ↔ b = 0#w := by
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (by simpa using h)
  · rintro rfl; simp

/-! ## Opcode indices -/

theorem unaryIdx_inj {a b : UnaryOp} : unaryIdx a = unaryIdx b ↔ a = b := by
  cases a <;> cases b <;> decide

theorem binaryIdx_inj {a b : BinaryOp} : binaryIdx a = binaryIdx b ↔ a = b := by
  cases a <;> cases b <;> decide

theorem unaryIdx_eq_iff {op : UnaryOp} {k : Nat} : unaryIdx op = k ↔ unaryOfIdx? k = some op := by
  cases op <;> constructor <;> (try rintro rfl) <;> (try rfl) <;> intro h <;>
    (unfold unaryOfIdx? at h; split at h <;> simp_all [unaryIdx])

theorem binaryIdx_eq_iff {op : BinaryOp} {k : Nat} : binaryIdx op = k ↔ binaryOfIdx? k = some op := by
  cases op <;> constructor <;> (try rintro rfl) <;> (try rfl) <;> intro h <;>
    (unfold binaryOfIdx? at h; split at h <;> simp_all [binaryIdx])

@[opt_match] theorem opcode_eq_data {k k' : Nat} {fs : List V} :
    opcode k = .data 52 k' fs ↔ k = k' ∧ fs = [] := by
  simp [opcode, eq_comm]

end Opt.Proof
