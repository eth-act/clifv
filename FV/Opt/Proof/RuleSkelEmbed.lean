import FV.Opt.Proof.RuleRestEmbed
import FV.Opt.Proof.RuleSkel

/-!
# The `simplify_skeleton` rule template

The obligation of a skeleton rule (`SkelRuleOk`, `FV/Opt/Proof/RuleSkel.lean`) is proven like a
`simplify` rule's (`FV/Opt/Proof/RuleAuto.lean`): the left-hand side becomes e-graph facts in the
start state `s0`, the values the instruction reads (`Opt.skelReads`) are defined there
(`SkelReadsDef`), so the model gives them the values of their matched nodes, and these values
persist into every later state. The right-hand side is evaluated to a `SkeletonInstSimplification`
value, and the refinement (`Opt.SkelRefines`) is reduced by an *outcome lemma* per shape to facts
about the read values:

* `skel_div_rwv`: `div` replaced by a value (`RemoveWithVal`): no trap (`divOk`) and the value
  is the quotient/remainder (`divVal`);
* `skel_trapz_remove`, `skel_trapnz_remove`: a conditional trap that never traps;
* `skel_brif_jump`, `skel_brTable_jump`: a branch with a known target;
* `skel_brif_cond`, `skel_trapz_cond`, `skel_trapnz_cond`: the condition replaced by one with the
  same truthiness;
* `skel_brif_two_then`, `skel_brif_two_else`: a branch to a trap block replaced by a conditional
  trap and a jump.

The `truthy` if-let of `skeleton.isle` 50/53/56 (a multi term: its results cannot be unfolded
over the abstract e-graph) is handled by the soundness of its rules (`truthy_iflet`).

Embedding lemmas (`opt_match`): `inst_data` on the skeleton instruction (`extract_inst_data`)
and the inversion of `ofSkel` per `InstructionData` variant.
-/

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

/-! ## The skeleton instruction as `InstructionData` -/

section
variable {σ : Type} (G : EGraph σ)

@[opt_match] theorem extract_inst_data (i : SkelInst) (s : St σ) (fs : List V) :
    (sem G).extract T.«inst_data» (.inst (some i)) s = .ok fs ↔
      ∃ d, ofSkel i = some d ∧ fs = [d] := by
  have : (sem G).extract T.«inst_data» (.inst (some i)) s = toExt (.ok ((ofSkel i).map ([·]))) :=
    rfl
  rw [this]
  cases ofSkel i <;> simp [toExt, eq_comm]

@[opt_match] theorem extract_block_array_2 (a b : V) (s : St σ) (fs : List V) :
    (sem G).extract T.«block_array_2» (.values [a, b]) s = .ok fs ↔ fs = [a, b] := by
  have : (sem G).extract T.«block_array_2» (.values [a, b]) s = toExt (.ok (some [a, b])) := rfl
  rw [this, toExt_ok_some]; simp [eq_comm]

end

set_option hygiene false in
/-- The forward direction of an `ofSkel` inversion. -/
macro "ofSkel_fwd" : tactic => `(tactic| (
  intro h
  rcases i with i | t
  · cases i <;> simp (config := {decide := true}) [ofSkel, idata] at h
    all_goals subst h
    all_goals first
      | exact ⟨_, _, _, _, rfl, rfl⟩
      | exact .inl ⟨_, _, rfl, rfl⟩
      | exact .inr ⟨_, _, rfl, rfl⟩
  · cases t <;> simp (config := {decide := true}) [ofSkel, idata] at h
    all_goals subst h
    all_goals exact ⟨_, _, _, rfl, rfl⟩))

@[opt_match] theorem ofSkel_binary {i : SkelInst} {fs : List V} :
    ofSkel i = some (.data 53 2 fs) ↔
      ∃ op t x y, i = .inst (.div op t x y) ∧
        fs = [opcode (divIdx op), .values [.value x, .value y]] := by
  constructor
  · ofSkel_fwd
  · rintro ⟨_, _, _, _, rfl, rfl⟩; rfl

@[opt_match] theorem ofSkel_condTrap {i : SkelInst} {fs : List V} :
    ofSkel i = some (.data 53 8 fs) ↔
      (∃ c code, i = .inst (.trapz c code) ∧ fs = [opcode 5, .value c, .trapCode code]) ∨
      (∃ c code, i = .inst (.trapnz c code) ∧ fs = [opcode 6, .value c, .trapCode code]) := by
  constructor
  · ofSkel_fwd
  · rintro (⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) <;> rfl

@[opt_match] theorem ofSkel_brif {i : SkelInst} {fs : List V} :
    ofSkel i = some (.data 53 5 fs) ↔
      ∃ c th el, i = .term (.brif c th el) ∧
        fs = [opcode 1, .value c, .values [.blockCall th, .blockCall el]] := by
  constructor
  · ofSkel_fwd
  · rintro ⟨_, _, _, rfl, rfl⟩; rfl

@[opt_match] theorem ofSkel_branchTable {i : SkelInst} {fs : List V} :
    ofSkel i = some (.data 53 4 fs) ↔
      ∃ x d tbl, i = .term (.brTable x d tbl) ∧ fs = [opcode 2, .value x, .jumpTable d tbl] := by
  constructor
  · ofSkel_fwd
  · rintro ⟨_, _, _, rfl, rfl⟩; rfl

@[opt_match] theorem divIdx_eq_iff {op : DivOp} {k : Nat} :
    divIdx op = k ↔ (k = 82 ∧ op = .udiv) ∨ (k = 83 ∧ op = .sdiv) ∨ (k = 84 ∧ op = .urem) ∨
      (k = 85 ∧ op = .srem) := by
  have h1 : divIdx .udiv = 82 := rfl
  have h2 : divIdx .sdiv = 83 := rfl
  have h3 : divIdx .urem = 84 := rfl
  have h4 : divIdx .srem = 85 := rfl
  cases op <;> simp [h1, h2, h3, h4] <;> omega

/-! ## Outcome lemmas -/

/-- `div op` does not trap on `a`, `b`. -/
def divOk {w : Nat} (op : DivOp) (a b : BitVec w) : Bool :=
  match op with
  | .sdiv => !(b == 0#w) && !(a == BitVec.intMin w && b == BitVec.allOnes w)
  | _ => !(b == 0#w)

/-- The result of `div op` on `a`, `b` (when `divOk`). -/
def divVal {w : Nat} (op : DivOp) (a b : BitVec w) : BitVec w :=
  match op with
  | .udiv => a / b | .sdiv => a.sdiv b | .urem => a % b | .srem => a.srem b

theorem div_of_ok {w : Nat} {op : DivOp} {a b : BitVec w} (h : divOk op a b = true) :
    Sem.div op a b = .ok (divVal op a b) := by
  cases op <;> simp_all [divOk, divVal, Sem.div, Sem.udiv, Sem.sdiv, Sem.urem, Sem.srem]
  intro h1 h2; simp_all

section
variable {tb : BlockId → Option TrapCode} {fr : Frame} {mem : Mem}

theorem getMany_ne_trap (l : List ValueId) (c : TrapCode) : fr.getMany l ≠ .trap c := by
  induction l with
  | nil => simp [Frame.getMany]
  | cons x xs ih =>
    simp only [Frame.getMany, Frame.get]
    cases fr.regs x <;> simp only [Res.ofOption_some, Res.ofOption_none, Res.ok_bind,
      Res.stuck_bind, ne_eq, reduceCtorEq, not_false_eq_true]
    cases h : fr.getMany xs <;> simp_all [bind, Res.bind]

theorem getAs_eq {x : ValueId} {t : Ty} {v : Val} (hx : fr.regs x = some v) :
    fr.getAs x t = Res.ofOption "" (v.as? t) ∨ ∃ m, fr.getAs x t = .stuck m := by
  simp only [Frame.getAs, Frame.get, hx, Res.ofOption_some, Res.ok_bind]
  cases v.as? t <;> simp

/-- `div` replaced by a value: it does not trap and the value is its result. -/
theorem skel_div_rwv {op : DivOp} {t : Ty} {x y w : ValueId} {vx vy : Val}
    (hx : fr.regs x = some vx) (hy : fr.regs y = some vy)
    (h : ∀ a b : BitVec t.width, vx = ⟨t, a⟩ → vy = ⟨t, b⟩ →
      divOk op a b = true ∧ fr.regs w = some ⟨t, divVal op a b⟩) :
    SkelRefines tb fr mem (.inst (.div op t x y)) (.removeWithVal w) := by
  simp only [SkelRefines, evalInst, Frame.getAs, Frame.get, hx, hy, Res.ofOption_some,
    Res.ok_bind]
  cases ha : vx.as? t with
  | none => simp [Res.ofOption]
  | some a =>
    cases hb : vy.as? t with
    | none => simp [Res.ofOption]
    | some b =>
      rw [Val.as?_eq_some] at ha hb
      obtain ⟨hok, hw⟩ := h a b ha hb
      simp [div_of_ok hok, hw]

/-- A `trapz` whose condition is true never traps. -/
theorem skel_trapz_remove {c : ValueId} {code : TrapCode} {vc : Val}
    (hc : fr.regs c = some vc) (h : Sem.truthy vc.bits = true) :
    SkelRefines tb fr mem (.inst (.trapz c code)) .remove := by
  simp [SkelRefines, evalInst, Frame.get, hc, h]

/-- A `trapnz` whose condition is false never traps. -/
theorem skel_trapnz_remove {c : ValueId} {code : TrapCode} {vc : Val}
    (hc : fr.regs c = some vc) (h : Sem.truthy vc.bits = false) :
    SkelRefines tb fr mem (.inst (.trapnz c code)) .remove := by
  simp [SkelRefines, evalInst, Frame.get, hc, h]

/-- A `brif` whose condition is true jumps to its `then` target. -/
theorem skel_brif_jump_then {c : ValueId} {th el : BlockCall} {vc : Val}
    (hc : fr.regs c = some vc) (h : Sem.truthy vc.bits = true) :
    SkelRefines tb fr mem (.term (.brif c th el)) (.replace (.term (.jump th))) := by
  simp only [SkelRefines, BrRefines, termEval, Frame.get, hc, Res.ofOption_some, Res.ok_bind, h,
    ite_true]
  exact ⟨fun _ _ _ e => .inl e, fun _ e => e⟩

/-- A `brif` whose condition is false jumps to its `else` target. -/
theorem skel_brif_jump_else {c : ValueId} {th el : BlockCall} {vc : Val}
    (hc : fr.regs c = some vc) (h : Sem.truthy vc.bits = false) :
    SkelRefines tb fr mem (.term (.brif c th el)) (.replace (.term (.jump el))) := by
  simp only [SkelRefines, BrRefines, termEval, Frame.get, hc, Res.ofOption_some, Res.ok_bind, h,
    Bool.false_eq_true, ite_false]
  exact ⟨fun _ _ _ e => .inl e, fun _ e => e⟩

/-- A `br_table` whose index is known jumps to the table's entry. -/
theorem skel_brTable_jump {x : ValueId} {dflt d : BlockCall} {tbl : List BlockCall} {vx : Val}
    (hx : fr.regs x = some vx) (h : tbl[vx.toNat]?.getD dflt = d) :
    SkelRefines tb fr mem (.term (.brTable x dflt tbl)) (.replace (.term (.jump d))) := by
  simp only [SkelRefines, BrRefines, termEval, Frame.get, hx, Res.ofOption_some, Res.ok_bind, h]
  exact ⟨fun _ _ _ e => .inl e, fun _ e => e⟩

/-- A `brif` condition replaced by one with the same truthiness. -/
theorem skel_brif_cond {c c' : ValueId} {th el : BlockCall} {vc vc' : Val}
    (hc : fr.regs c = some vc) (hc' : fr.regs c' = some vc')
    (h : Sem.truthy vc'.bits = Sem.truthy vc.bits) :
    SkelRefines tb fr mem (.term (.brif c th el)) (.replaceBranchCond c') := by
  simp only [SkelRefines, BrRefines, termEval, Frame.get, hc, hc', Res.ofOption_some, Res.ok_bind,
    h]
  exact ⟨fun _ _ _ e => .inl e, fun _ e => e⟩

/-- A `trapz` condition replaced by one with the same truthiness. -/
theorem skel_trapz_cond {c c' : ValueId} {code : TrapCode} {vc vc' : Val}
    (hc : fr.regs c = some vc) (hc' : fr.regs c' = some vc')
    (h : Sem.truthy vc'.bits = Sem.truthy vc.bits) :
    SkelRefines tb fr mem (.inst (.trapz c code)) (.replaceBranchCond c') := by
  simp only [SkelRefines, ResRefines, evalInst, Frame.get, hc, hc', Res.ofOption_some,
    Res.ok_bind, h]
  exact ⟨fun _ e => e, fun _ e => e⟩

/-- A `trapnz` condition replaced by one with the same truthiness. -/
theorem skel_trapnz_cond {c c' : ValueId} {code : TrapCode} {vc vc' : Val}
    (hc : fr.regs c = some vc) (hc' : fr.regs c' = some vc')
    (h : Sem.truthy vc'.bits = Sem.truthy vc.bits) :
    SkelRefines tb fr mem (.inst (.trapnz c code)) (.replaceBranchCond c') := by
  simp only [SkelRefines, ResRefines, evalInst, Frame.get, hc, hc', Res.ofOption_some,
    Res.ok_bind, h]
  exact ⟨fun _ e => e, fun _ e => e⟩

/-- A `brif` whose `then` target is a trap block: `trapnz` of the condition, then a jump to the
`else` target. -/
theorem skel_brif_two_then {c : ValueId} {th el : BlockCall} {code : TrapCode}
    (h : tb th.block = some code) :
    SkelRefines tb fr mem (.term (.brif c th el))
      (.replaceWithTwo (.inst (.trapnz c code)) (.term (.jump el))) := by
  simp only [SkelRefines, BrRefines, termEval, seqEval, evalInst, Frame.get]
  cases hc : fr.regs c with
  | none => simp [Res.ofOption]
  | some vc =>
    cases ht : Sem.truthy vc.bits
    · simp only [Res.ofOption_some, Res.ok_bind, ht, Bool.false_eq_true, ite_false]
      exact ⟨fun _ _ _ e => .inl e, fun _ e => e⟩
    · simp only [Res.ofOption_some, Res.ok_bind, ht, ite_true]
      refine ⟨fun b vs m e => .inr ⟨code, ?_, rfl⟩, fun c' e => ?_⟩
      · cases hg : fr.getMany th.args <;> simp [hg, bind, Res.bind] at e
        obtain ⟨rfl, -⟩ := e; exact h
      · cases hg : fr.getMany th.args <;> simp [hg, bind, Res.bind] at e
        exact absurd hg (getMany_ne_trap _ _)

/-- A `brif` whose `else` target is a trap block: `trapz` of the condition, then a jump to the
`then` target. -/
theorem skel_brif_two_else {c : ValueId} {th el : BlockCall} {code : TrapCode}
    (h : tb el.block = some code) :
    SkelRefines tb fr mem (.term (.brif c th el))
      (.replaceWithTwo (.inst (.trapz c code)) (.term (.jump th))) := by
  simp only [SkelRefines, BrRefines, termEval, seqEval, evalInst, Frame.get]
  cases hc : fr.regs c with
  | none => simp [Res.ofOption]
  | some vc =>
    cases ht : Sem.truthy vc.bits
    · simp only [Res.ofOption_some, Res.ok_bind, ht, Bool.false_eq_true, ite_false]
      refine ⟨fun b vs m e => .inr ⟨code, ?_, rfl⟩, fun c' e => ?_⟩
      · cases hg : fr.getMany el.args <;> simp [hg, bind, Res.bind] at e
        obtain ⟨rfl, -⟩ := e; exact h
      · cases hg : fr.getMany el.args <;> simp [hg, bind, Res.bind] at e
        exact absurd hg (getMany_ne_trap _ _)
    · simp only [Res.ofOption_some, Res.ok_bind, ht, ite_true]
      exact ⟨fun _ _ _ e => .inl e, fun _ e => e⟩

end

/-! ## The template -/

/-- An `Int` cast compared with a literal (immediate facts `asU64 imm = k` after
`asU64_imm64OfBits`). -/
theorem int_natCast_eq_lit {n k : Nat} :
    (n : Int) = (no_index (OfNat.ofNat k) : Int) ↔ n = OfNat.ofNat k :=
  Int.ofNat_inj

theorem int_natCast_bne_zero (n : Nat) : ((n : Int) != 0) = (n != 0) := by
  rw [Bool.eq_iff_iff]; simp

theorem toNat_bne_zero {w : Nat} (b : BitVec w) : (b.toNat != 0) = (b != 0#w) := by
  rw [Bool.eq_iff_iff]; simp [BitVec.toNat_eq]

theorem int_natCast_beq_zero (n : Nat) : ((n : Int) == 0) = (n == 0) := by
  rw [Bool.eq_iff_iff]; simp

/-- The immediate facts of the matched `iconst`s as `BitVec` equations. -/
macro "skel_imm" : tactic => `(tactic| (
  try simp (disch := assumption) only [asU64_imm64OfBits, i64SextendImm64_imm64OfBits,
    int_natCast_eq_lit, Int.natCast_eq_zero, toNat_eq_iff_ofNat, toInt_eq_one,
    toInt_eq_neg_one, int_natCast_bne_zero, toNat_bne_zero, int_natCast_beq_zero,
    toNat_beq_zero] at *
  opt_destruct
  all_goals subst_vars))

set_option hygiene false in
/-- Phase 1: introduce the obligation, fix the fuel as `k + 1000`, unfold the rule's data. -/
macro "skel_intro " r:ident : tactic => `(tactic| (
  intro σ G P den fr mem tb hG htb i s0 hP hI env1 hrel n hn s1 tr1 envs2 s2 tr2 hP1 hle1 hil
    env2 henv2 s3 tr3 ws s4 tr4 hP3 hle3 hev w hw
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1000 := ⟨n - 1000, by simp [fuelMin] at hn; omega⟩
  unfold $r:ident at hrel hil hev
  dsimp only at hrel hil hev))

set_option hygiene false in
/-- After the left-hand side: the reads of the (now concrete) instruction are defined in `s0`;
their values become hypotheses `den s0.inner y = some v`, so `rule_lhs` adds the model facts of
their matched nodes. -/
macro "skel_reads" : tactic => `(tactic| (
  all_goals (simp only [SkelReadsDef, skelReads, operands, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hI)
  opt_destruct))

/-- After `rule_iflets`: drop the branches with a contradictory integer fact, turn extern results
(`toExt`, `Option.map`) into equations. -/
macro "skel_iflets" : tactic => `(tactic| (
  all_goals (try (exfalso; omega))
  all_goals (try simp only [toExt_eq_ok, Except.ok.injEq, Option.map_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq, Int.toNat_natCast] at *)
  opt_destruct
  all_goals subst_vars))

set_option hygiene false in
/-- Phase 3: evaluate the right-hand side to its result `w`. -/
macro "skel_rhs" : tactic => `(tactic| (
  opt_eval hev
  repeat' (split at hev <;> try opt_norm hev)
  all_goals (try simp only [Option.map_eq_some_iff, Option.map_eq_none_iff] at *)
  opt_destruct
  all_goals subst_vars
  all_goals (
    simp only [Except.ok.injEq, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hw <;>
    subst hw)
  all_goals opt_types
  all_goals (try (exfalso; omega))))

set_option hygiene false in
/-- Phase 4: the simplification `c` read off the result, in a later state `st`. -/
macro "skel_good" : tactic => `(tactic| (
  intro c hc st hst hle4
  simp (config := {decide := true}) only [skelSimp?, toSkel, ite_false, Option.some.injEq] at hc
  subst hc))

set_option hygiene false in
/-- The value of a class in the later state `st` (an old class or a made node). -/
macro "skel_val" : tactic => `(tactic| (
  try dsimp only
  apply hle4
  rule_finish))

set_option hygiene false in
/-- Phase 4 for `div` replaced by a value: the read values are split into bits, the
immediate facts normalised; no trap (`divOk`) and the value (`divVal`). -/
macro "skel_div" : tactic => `(tactic| (
  apply skel_div_rwv (hle4 _ _ (by opt_den)) (hle4 _ _ (by opt_den))
  intro a b ha hb
  subst ha
  opt_destruct
  skel_imm
  refine ⟨?_, ?_⟩
  · simp only [divOk]
    rule_bits
  · simp only [divVal]
    skel_val))

/-- A Boolean goal about the read values (a truthiness): normalise the immediates, decide. -/
macro "skel_bool" : tactic => `(tactic| (
  skel_imm
  try simp only [Sem.truthy, BitVec.ofNat_eq_ofNat] at *
  first
    | assumption
    | (simp only [bne_iff_ne, ne_eq, beq_iff_eq] at *; first | assumption | (opt_cases_ty <;> opt_widths <;> bv_decide))
    | (opt_cases_ty <;> opt_widths <;> (try sem_simp) <;> bv_decide)))

set_option hygiene false in
/-- Phase 4 for branches and conditional traps: the outcome lemmas in turn. -/
macro "skel_br" : tactic => `(tactic| first
  | (apply skel_trapz_remove (hle4 _ _ (by opt_den)); skel_bool)
  | (apply skel_trapnz_remove (hle4 _ _ (by opt_den)); skel_bool)
  | (apply skel_brif_jump_then (hle4 _ _ (by opt_den)); skel_bool)
  | (apply skel_brif_jump_else (hle4 _ _ (by opt_den)); skel_bool)
  | (apply skel_brTable_jump (hle4 _ _ (by opt_den)); skel_imm; simp_all [Val.toNat])
  | (apply skel_brif_cond (hle4 _ _ (by opt_den)) (hle4 _ _ (by opt_den)); skel_bool)
  | (apply skel_trapz_cond (hle4 _ _ (by opt_den)) (hle4 _ _ (by opt_den)); skel_bool)
  | (apply skel_trapnz_cond (hle4 _ _ (by opt_den)) (hle4 _ _ (by opt_den)); skel_bool)
  | (apply skel_brif_two_then; rw [← htb _ hP1]; assumption)
  | (apply skel_brif_two_else; rw [← htb _ hP1]; assumption))

set_option hygiene false in
/-- The whole template for a branch or conditional-trap rule (with or without if-lets). -/
macro "skel_auto_br " r:ident : tactic => `(tactic| (
  skel_intro $r
  rule_lhs hG
  skel_reads
  rule_lhs hG
  all_goals (first | rule_no_iflets | (rule_iflets; skel_iflets))
  all_goals opt_split_i128
  all_goals (skel_rhs; skel_good; skel_br)))

set_option hygiene false in
/-- The whole template for a `div` rule without if-lets. -/
macro "skel_auto_div " r:ident : tactic => `(tactic| (
  skel_intro $r
  rule_no_iflets
  rule_lhs hG
  skel_reads
  rule_lhs hG
  all_goals (skel_rhs; skel_good; skel_div)))

set_option hygiene false in
/-- The whole template for a `div` rule with if-lets. -/
macro "skel_auto_div_i " r:ident : tactic => `(tactic| (
  skel_intro $r
  rule_lhs hG
  skel_reads
  rule_lhs hG
  all_goals rule_iflets
  all_goals (skel_rhs; skel_good; skel_div)))

/-! ## `truthy` in an if-let

`(if-let x (truthy c))` calls the multi term `truthy` (`bitops.isle` 110-122): each of its rules
is proven to return a class with `c`'s truthiness (`TruthyOk`, the generic `RuleSpecAt` at fuel
`truthyFuel`), `truthy_sound` lifts them with `applyMulti_genAt`, and `truthy_iflet` gives the
if-let's environments. -/

/-- The result property of `truthy c` (`vc` the value of `c`): a class whose value has the
truthiness of `vc`. -/
def TruthyRes {σ : Type} (den : σ → Valuation) (vc : Val) (w : V) (s : St σ) : Prop :=
  ∃ m vm, w = .value m ∧ den s.inner m = some vm ∧ Sem.truthy vm.bits = Sem.truthy vc.bits

/-- The fuel the `truthy` rules are proven at: the if-let calls the multi term with the fuel
of a skeleton rule (at least `fuelMin`) minus a few interpreter steps. -/
def truthyFuel : Nat := 900

/-- The obligation of one rule of the multi term `truthy` (`bitops.isle` 111-122). -/
def TruthyOk (p : Isle.Program) (r : Rule) : Prop :=
  ∀ (σ : Type) (G : EGraph σ) (P : σ → Prop) (den : σ → Valuation) (fr : Frame) (mem : Mem),
  GraphOk G P den fr mem → ∀ c vc, RuleSpecAt truthyFuel p G P den (.value c)
    (fun s => den s.inner c = some vc) (fun _ w s => TruthyRes den vc w s) r

set_option hygiene false in
/-- The template of a `truthy` rule: the left-hand side, then the operand's truthiness per type. -/
macro "truthy_auto " r:ident : tactic => `(tactic| (
  intro σ G P den fr mem hG c vc s0 hP hv env1 hrel n hn s1 tr1 envs2 s2 tr2 hP1 hle1 hil env2
    henv2 s3 tr3 ws s4 tr4 hP3 hle3 hev w hw
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 900 := ⟨n - 900, by simp [truthyFuel] at hn; omega⟩
  unfold $r:ident at hrel hil hev
  dsimp only at hrel hil hev
  rule_no_iflets
  rule_lhs hG
  all_goals (
    opt_eval hev
    simp only [Except.ok.injEq, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    simp only [List.mem_singleton] at hw
    subst hw
    refine ⟨_, _, rfl, by apply Valuation.le_trans hle1 hle3; assumption, ?_⟩
    skel_imm
    opt_some_subst
    try simp only [bne_iff_ne, ne_eq] at *
    opt_cases_val
    opt_cases_ty <;> (try simp only [Ty.width] at *) <;> (try omega) <;> opt_widths <;>
      (try sem_simp) <;> (try (simp only [Option.some.injEq] at *; subst_vars)) <;> (try bswap_unroll) <;> (try simp only [Sem.bitrev] at *) <;> bv_decide)))

set_option maxHeartbeats 4000000 in
theorem ok_truthy_bitops_111 {p : Isle.Program} (hd : Data p) : TruthyOk p rule_bitops_111 := by
  truthy_auto rule_bitops_111

set_option maxHeartbeats 4000000 in
theorem ok_truthy_bitops_112 {p : Isle.Program} (hd : Data p) : TruthyOk p rule_bitops_112 := by
  truthy_auto rule_bitops_112

set_option maxHeartbeats 4000000 in
theorem ok_truthy_bitops_113 {p : Isle.Program} (hd : Data p) : TruthyOk p rule_bitops_113 := by
  truthy_auto rule_bitops_113

set_option maxHeartbeats 4000000 in
theorem ok_truthy_bitops_114 {p : Isle.Program} (hd : Data p) : TruthyOk p rule_bitops_114 := by
  truthy_auto rule_bitops_114

set_option maxHeartbeats 4000000 in
theorem ok_truthy_bitops_115 {p : Isle.Program} (hd : Data p) : TruthyOk p rule_bitops_115 := by
  truthy_auto rule_bitops_115

set_option maxHeartbeats 4000000 in
theorem ok_truthy_bitops_116 {p : Isle.Program} (hd : Data p) : TruthyOk p rule_bitops_116 := by
  truthy_auto rule_bitops_116

set_option maxHeartbeats 4000000 in
theorem ok_truthy_bitops_117 {p : Isle.Program} (hd : Data p) : TruthyOk p rule_bitops_117 := by
  truthy_auto rule_bitops_117

set_option maxHeartbeats 4000000 in
theorem ok_truthy_bitops_118 {p : Isle.Program} (hd : Data p) : TruthyOk p rule_bitops_118 := by
  truthy_auto rule_bitops_118

set_option maxHeartbeats 4000000 in
theorem ok_truthy_bitops_119 {p : Isle.Program} (hd : Data p) : TruthyOk p rule_bitops_119 := by
  truthy_auto rule_bitops_119

set_option maxHeartbeats 4000000 in
theorem ok_truthy_bitops_120 {p : Isle.Program} (hd : Data p) : TruthyOk p rule_bitops_120 := by
  truthy_auto rule_bitops_120

set_option maxHeartbeats 4000000 in
theorem ok_truthy_bitops_122 {p : Isle.Program} (hd : Data p) : TruthyOk p rule_bitops_122 := by
  truthy_auto rule_bitops_122


section
variable {σ : Type} {G : EGraph σ} {P : σ → Prop} {den : σ → Valuation} {fr : Frame} {mem : Mem}

/-- **`truthy` is sound**: every result of the multi term on a class `c` with value `vc` is a class
with `vc`'s truthiness, in the end state. -/
theorem truthy_sound {p : Isle.Program} (hd : Data p) (hG : GraphOk G P den fr mem) (c : Nat)
    (vc : Val) (n : Nat) (hn : truthyFuel + 11 ≤ n) (s : St σ) (tr : Array RuleId)
    (res : List (RuleId × V)) (s' : St σ) (tr' : Array RuleId) (hP : P s.inner)
    (hv : den s.inner c = some vc)
    (h : (applyMulti p (sem G) cfg n T.«truthy» [rule_bitops_111, rule_bitops_112, rule_bitops_113,
      rule_bitops_114, rule_bitops_115, rule_bitops_116, rule_bitops_117, rule_bitops_118,
      rule_bitops_119, rule_bitops_120, rule_bitops_122] [.value c]).run (s, tr) =
      .ok (res, (s', tr'))) :
    P s'.inner ∧ Valuation.Le (den s.inner) (den s'.inner) ∧
      ∀ rid w, (rid, w) ∈ res → TruthyRes den vc w s' := by
  obtain ⟨h1, h2, h3⟩ := applyMulti_genAt p hG (fun _ => true) (.value c)
    (fun s => den s.inner c = some vc) (fun _ w s => TruthyRes den vc w s)
    (fun _ _ h hle => hle _ _ h)
    (fun _ _ _ _ h hle => let ⟨m, vm, e, hm, ht⟩ := h; ⟨m, vm, e, hle _ _ hm, ht⟩)
    T.«truthy» truthyFuel (by decide) _ (by
      intro r hr _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok_truthy_bitops_111 hd σ G P den fr mem hG c vc
      · exact ok_truthy_bitops_112 hd σ G P den fr mem hG c vc
      · exact ok_truthy_bitops_113 hd σ G P den fr mem hG c vc
      · exact ok_truthy_bitops_114 hd σ G P den fr mem hG c vc
      · exact ok_truthy_bitops_115 hd σ G P den fr mem hG c vc
      · exact ok_truthy_bitops_116 hd σ G P den fr mem hG c vc
      · exact ok_truthy_bitops_117 hd σ G P den fr mem hG c vc
      · exact ok_truthy_bitops_118 hd σ G P den fr mem hG c vc
      · exact ok_truthy_bitops_119 hd σ G P den fr mem hG c vc
      · exact ok_truthy_bitops_120 hd σ G P den fr mem hG c vc
      · exact ok_truthy_bitops_122 hd σ G P den fr mem hG c vc)
    n (by simpa using hn) s tr res s' tr' hP hv h
  exact ⟨h1, h2, fun rid w hm => h3 rid w hm rfl⟩

/-- `bindAll` of a state-preserving singleton function. -/
theorem bindAll_pure_single {α β : Type} (g : α → β) :
    ∀ l : List α, bindAll (fun a => (pure [g a] : M (St σ) (List β))) l = pure (l.map g)
  | [] => rfl
  | a :: as => by
    simp only [bindAll, bindAll_pure_single g as, List.map_cons]
    rfl

/-- The if-let `(if-let x (truthy c))` of the skeleton rules: it keeps the model and binds `x`
(variable 1) to classes with `c`'s truthiness. -/
theorem truthy_iflet {p : Isle.Program} (hd : Data p) (hG : GraphOk G P den fr mem)
    {env : Interp.Env V} {c : Nat} {vc : Val} (he : env[0]? = some (some (.value c)))
    (hsz : 1 < env.size) {n : Nat} (hn : 1000 ≤ n) {s : St σ} {tr : Array RuleId}
    {envs : List (Interp.Env V)} {s' : St σ} {tr' : Array RuleId} (hP : P s.inner)
    (hv : den s.inner c = some vc)
    (h : (matchIfLetsN p (sem G) cfg n [⟨.bind 15 1 (.wildcard 15), .term 15 235 [.var 15 0]⟩]
      env).run (s, tr) = .ok (envs, (s', tr'))) :
    P s'.inner ∧ Valuation.Le (den s.inner) (den s'.inner) ∧
      ∀ e ∈ envs, ∃ m vm, e = env.set! 1 (some (.value m)) ∧ den s'.inner m = some vm ∧
        Sem.truthy vm.bits = Sem.truthy vc.bits := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1000 := ⟨n - 1000, by omega⟩
  opt_eval h [he]
  have hb : ∀ v, (do
      let x ← (get : M (St σ) (St σ × Array RuleId))
      let envs ← liftM (matchPatN p (sem G) x.fst (Pattern.bind 15 1 (Pattern.wildcard 15)) v env)
      bindAll (fun e => matchIfLetsN p (sem G) cfg (n + 999) [] e) envs) =
      (pure [env.set! 1 (some v)] : M (St σ) (List (Interp.Env V))) := by
    intro v
    funext st
    simp [matchPatN, hsz, matchIfLetsN, bindAll, liftM, bind, StateT.bind, get, getThe,
      MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure, monadLift, MonadLift.monadLift,
      StateT.lift, Except.bind]
  simp only [hb, bindAll_pure_single] at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i a ha
    obtain ⟨vals, s1, tr1⟩ := a
    obtain ⟨h1, h2, h3⟩ := truthy_sound hd hG c vc _ (by simp [truthyFuel]) s tr vals s1 tr1 hP hv ha
    simp only [StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨h1, h2, fun e he' => ?_⟩
    simp only [List.map_map, List.mem_map, Function.comp] at he'
    obtain ⟨⟨rid, w⟩, hm, rfl⟩ := he'
    obtain ⟨m, vm, rfl, hm', ht⟩ := h3 rid w hm
    exact ⟨m, vm, rfl, hm', ht⟩
end

set_option hygiene false in
/-- The whole template for a condition stripped by `truthy` (`skeleton.isle` 50, 53, 56). -/
macro "skel_auto_truthy " r:ident : tactic => `(tactic| (
  skel_intro $r
  rule_lhs hG
  skel_reads
  rule_lhs hG
  obtain ⟨hP2, hle2, hx⟩ := truthy_iflet hd hG (by simp <;> rfl) (by simp) (by omega) hP1
    (hle1 _ _ ‹den s0.inner _ = some _›) hil
  obtain ⟨m, vm, rfl, hm, ht⟩ := hx env2 henv2
  skel_rhs
  skel_good
  first
    | exact skel_brif_cond (hle4 _ _ (hle3 _ _ (hle2 _ _ (hle1 _ _ ‹den s0.inner _ = some _›))))
        (hle4 _ _ (hle3 _ _ hm)) ht
    | exact skel_trapz_cond (hle4 _ _ (hle3 _ _ (hle2 _ _ (hle1 _ _ ‹den s0.inner _ = some _›))))
        (hle4 _ _ (hle3 _ _ hm)) ht
    | exact skel_trapnz_cond (hle4 _ _ (hle3 _ _ (hle2 _ _ (hle1 _ _ ‹den s0.inner _ = some _›))))
        (hle4 _ _ (hle3 _ _ hm)) ht))

end Opt.Proof
