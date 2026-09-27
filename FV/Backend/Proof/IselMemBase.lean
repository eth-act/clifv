import FV.Backend.Proof.IselCmpTerms
import FV.Backend.Proof.IselTermsImm
import FV.Backend.Proof.IselCtlCall
import FV.Backend.Proof.IselMemArm

/-!
# Memory family (M4Mem): extern helpers and the inversion tactic

`iff` forms of the extern extractors/constructors used by the memory rules and their address
helpers (`amode`, `amode_no_more_iconst`, `amode_reg_scaled`, `amode_add`, `compute_stack_addr`,
`load_ext_name`), and `mem_inv hp [lemmas] at h…`: the inverse-evaluation `simp` of `isel_inv`
with these lemmas at every round, unfolding the rule constants found in the hypotheses and
passing only the data facts `hp.tN` of the terms they mention.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

section Extern
variable (ctx : Ctx) (st : LState)

theorem ext_little_or_native_endian_iff (f : Clif.MemFlags) (fs : List V) :
    externExtract ctx T.little_or_native_endian (.op (.memFlags f)) st = .ok fs ↔
      f.endianness ≠ some .big ∧ fs = [.op (.memFlags f)] := by
  have : externExtract ctx T.little_or_native_endian (.op (.memFlags f)) st =
    if (f.endianness == some .big) = true then .fail else .ok [.op (.memFlags f)] := rfl
  rw [this]
  by_cases h : f.endianness = some .big
  · simp [h]
  · simp only [beq_iff_eq, h, ↓reduceIte, ExtResult.ok.injEq, ne_eq, not_false_eq_true, true_and]
    exact eq_comm

theorem ext_i64_from_iconst_iff (x : Nat) (fs : List V) :
    externExtract ctx T.i64_from_iconst (.value x) st = .ok fs ↔
      ∃ ty imm, ctx.defClif? x = some (.iconst ty imm) ∧
        fs = [.int (sextFrom ty.width (imm64OfIconst ty imm))] := by
  have : externExtract ctx T.i64_from_iconst (.value x) st = match ctx.defClif? x with
    | some (.iconst ty imm) => .ok [.int (sextFrom ty.width (imm64OfIconst ty imm))]
    | _ => .fail := rfl
  rw [this]
  split
  · rename_i ty imm h
    simp only [ExtResult.ok.injEq, h, Option.some.injEq]
    constructor
    · intro e; exact ⟨ty, imm, rfl, e.symm⟩
    · rintro ⟨ty', imm', he, rfl⟩
      cases he; rfl
  · rename_i hne
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro ty imm h; exact absurd h (hne ty imm)

theorem ext_i32_from_i64_iff (i : Int) (fs : List V) :
    externExtract ctx T.i32_from_i64 (.int i) st = .ok fs ↔
      (-2147483648 ≤ i ∧ i < 2147483648) ∧ fs = [.int i] := by
  have : externExtract ctx T.i32_from_i64 (.int i) st =
    if -(2 ^ 31 : Int) ≤ i ∧ i < 2 ^ 31 then .ok [.int i] else .fail := rfl
  rw [this]
  rw [show (2 : Int) ^ 31 = 2147483648 by decide]
  by_cases h : -2147483648 ≤ i ∧ i < 2147483648
  · rw [if_pos h]; simp [h, eq_comm]
  · rw [if_neg h]; simp only [reduceCtorEq, false_iff, not_and]; intro h1; exact absurd h1 h

theorem ctor_is_sinkable_inst (v : V) (w : V) (st' : LState) :
    externCtor ctx T.is_sinkable_inst [v] st ≠ .ok (w, st') := by
  have : externCtor ctx T.is_sinkable_inst [v] st = .fail := rfl
  rw [this]; simp

theorem ctor_offset32_to_i32' (i : Int) (v : V) (st' : LState) :
    externCtor ctx T.offset32_to_i32 [.int i] st = .ok (v, st') ↔ v = .int i ∧ st' = st := by
  have : externCtor ctx T.offset32_to_i32 [.int i] st = .ok (.int i, st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_i32_into_i64' (i : Int) (v : V) (st' : LState) :
    externCtor ctx T.i32_into_i64 [.int i] st = .ok (v, st') ↔ v = .int i ∧ st' = st := by
  have : externCtor ctx T.i32_into_i64 [.int i] st = .ok (.int i, st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_i64_cast_unsigned' (i : Int) (v : V) (st' : LState) :
    externCtor ctx T.i64_cast_unsigned [.int i] st = .ok (v, st') ↔ v = .int (u64 i) ∧ st' = st := by
  have : externCtor ctx T.i64_cast_unsigned [.int i] st = .ok (.int (u64 i), st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_ty_bytes' (t : CTy) (v : V) (st' : LState) :
    externCtor ctx T.ty_bytes [.ty t] st = .ok (v, st') ↔ v = .int t.bytes ∧ st' = st := by
  have : externCtor ctx T.ty_bytes [.ty t] st = .ok (.int t.bytes, st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_u16_into_u64' (i : Int) (v : V) (st' : LState) :
    externCtor ctx T.u16_into_u64 [.int i] st = .ok (v, st') ↔ v = .int i ∧ st' = st := by
  have : externCtor ctx T.u16_into_u64 [.int i] st = .ok (.int i, st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_u8_into_u32' (i : Int) (v : V) (st' : LState) :
    externCtor ctx T.u8_into_u32 [.int i] st = .ok (v, st') ↔ v = .int i ∧ st' = st := by
  have : externCtor ctx T.u8_into_u32 [.int i] st = .ok (.int i, st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_shift_masked_imm' (t : CTy) (i : Int) (v : V) (st' : LState) :
    externCtor ctx T.shift_masked_imm [.ty t, .int i] st = .ok (v, st') ↔
      v = .int (Nat.land (u64 i % 256) (t.laneBits - 1)) ∧ st' = st := by
  have : externCtor ctx T.shift_masked_imm [.ty t, .int i] st =
    .ok (.int (Nat.land (u64 i % 256) (t.laneBits - 1)), st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_u64_wrapping_shl' (a b : Int) (v : V) (st' : LState) :
    externCtor ctx T.u64_wrapping_shl [.int a, .int b] st = .ok (v, st') ↔
      v = .int (u64 (a * 2 ^ (b.toNat % 64))) ∧ st' = st := by
  have : externCtor ctx T.u64_wrapping_shl [.int a, .int b] st =
    .ok (.int (u64 (a * 2 ^ (b.toNat % 64))), st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_u64_eq' (a b : Int) (v : V) (st' : LState) :
    externCtor ctx T.u64_eq [.int a, .int b] st = .ok (v, st') ↔ v = .bool (a == b) ∧ st' = st := by
  have : externCtor ctx T.u64_eq [.int a, .int b] st = .ok (.bool (a == b), st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_i32_checked_add_iff (a b : Int) (v : V) (st' : LState) :
    externCtor ctx T.i32_checked_add [.int a, .int b] st = .ok (v, st') ↔
      (-2147483648 ≤ a + b ∧ a + b < 2147483648) ∧ v = .int (a + b) ∧ st' = st := by
  have : externCtor ctx T.i32_checked_add [.int a, .int b] st =
    if -(2 ^ 31 : Int) ≤ a + b ∧ a + b < 2 ^ 31 then .ok (.int (a + b), st) else .fail := rfl
  rw [this]
  rw [show (2 : Int) ^ 31 = 2147483648 by decide]
  by_cases h : -2147483648 ≤ a + b ∧ a + b < 2147483648
  · rw [if_pos h]; simp [h, eq_comm]
  · rw [if_neg h]; simp only [reduceCtorEq, false_iff, not_and]; intro h1; exact absurd h1 h

theorem ctor_simm9_from_i64_iff (i : Int) (v : V) (st' : LState) :
    externCtor ctx T.simm9_from_i64 [.int i] st = .ok (v, st') ↔
      (-256 ≤ i ∧ i ≤ 255) ∧ v = .op (.simm9 i) ∧ st' = st := by
  have : externCtor ctx T.simm9_from_i64 [.int i] st =
    match (simm9? i).map (V.op ∘ Opnd.simm9) with
    | some v => .ok (v, st)
    | none => .fail := rfl
  rw [this]; unfold simm9?
  by_cases h : -256 ≤ i ∧ i ≤ 255
  · rw [if_pos h]; simp [h, eq_comm]
  · rw [if_neg h]; simp only [Option.map_none, reduceCtorEq, false_iff, not_and]
    intro h1; exact absurd h1 h

theorem ctor_uimm12_scaled_from_i64_iff (i : Int) (t : CTy) (v : V) (st' : LState) :
    externCtor ctx T.uimm12_scaled_from_i64 [.int i, .ty t] st = .ok (v, st') ↔
      (0 ≤ i ∧ i ≤ 4095 * t.bytes ∧ i.toNat % t.bytes = 0) ∧ v = .op (.uimm12Scaled i.toNat) ∧
        st' = st := by
  have : externCtor ctx T.uimm12_scaled_from_i64 [.int i, .ty t] st =
    match (uimm12Scaled? i t.bytes).map (V.op ∘ Opnd.uimm12Scaled) with
    | some v => .ok (v, st)
    | none => .fail := rfl
  rw [this]; unfold uimm12Scaled?
  by_cases h : 0 ≤ i ∧ i ≤ 4095 * (t.bytes : Int) ∧ (i.toNat % t.bytes == 0) = true
  · rw [if_pos h]
    simp only [beq_iff_eq] at h
    simp [h, eq_comm]
  · rw [if_neg h]
    simp only [Option.map_none, reduceCtorEq, false_iff, not_and]
    intro h1; exact absurd ⟨h1.1, h1.2.1, by simpa using h1.2.2⟩ h

theorem ctor_uimm12_scaled_nonzero_from_i64_iff (i : Int) (t : CTy) (v : V) (st' : LState) :
    externCtor ctx T.uimm12_scaled_nonzero_from_i64 [.int i, .ty t] st = .ok (v, st') ↔
      i ≠ 0 ∧ (0 ≤ i ∧ i ≤ 4095 * t.bytes ∧ i.toNat % t.bytes = 0) ∧
        v = .op (.uimm12Scaled i.toNat) ∧ st' = st := by
  have e : externCtor ctx T.uimm12_scaled_nonzero_from_i64 [.int i, .ty t] st =
    if (i == 0) = true then .fail else externCtor ctx T.uimm12_scaled_from_i64 [.int i, .ty t] st :=
    rfl
  rw [e]
  by_cases h : i = 0
  · simp [h]
  · simp only [beq_iff_eq, h, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
    exact ctor_uimm12_scaled_from_i64_iff ctx st i t v st'

theorem ctor_abi_stackslot_offset_iff (s : Nat) (a b : Int) (v : V) (st' : LState) :
    externCtor ctx T.abi_stackslot_offset_into_slot_region [.op (.stackSlot s), .int a, .int b] st =
      .ok (v, st') ↔
      ∃ base, ctx.slotOff.lookup s = some base ∧ v = .int (base + a + b) ∧ st' = st := by
  have : externCtor ctx T.abi_stackslot_offset_into_slot_region [.op (.stackSlot s), .int a, .int b]
      st = match ctx.slotOff.lookup s with
      | some base => .ok (.int (base + a + b), st)
      | none => .unmodeled s!"stack slot ss{s}" := rfl
  rw [this]
  cases ctx.slotOff.lookup s <;> simp [eq_comm]

theorem ctor_abi_stackslot_addr_iff (rd : V) (s : Nat) (off : Int) (v : V) (st' : LState) :
    externCtor ctx T.abi_stackslot_addr [rd, .op (.stackSlot s), .int off] st = .ok (v, st') ↔
      ∃ base, ctx.slotOff.lookup s = some base ∧
        v = .data tyMInst VIdx.MInst.LoadAddr [rd, .data tyAMode VIdx.AMode.SlotOffset
          [.int (base + off)]] ∧ st' = st := by
  have : externCtor ctx T.abi_stackslot_addr [rd, .op (.stackSlot s), .int off] st =
      match ctx.slotOff.lookup s with
      | some base => .ok (.data tyMInst VIdx.MInst.LoadAddr [rd, .data tyAMode VIdx.AMode.SlotOffset
          [.int (base + off)]], st)
      | none => .unmodeled s!"stack slot ss{s}" := rfl
  rw [this]
  cases ctx.slotOff.lookup s <;> simp [eq_comm]

theorem ext_symbol_value_data_iff (gv : Nat) (fs : List V) :
    externExtract ctx T.symbol_value_data (.op (.globalValue gv)) st = .ok fs ↔
      ∃ name off colocated, ctx.func.globals.lookup gv = some (.symbol name off colocated) ∧
        fs = [.op (.extName name),
          .data tyRelocDistance (if colocated then VIdx.RelocDistance.Near else VIdx.RelocDistance.Far) [],
          .int off] := by
  have : externExtract ctx T.symbol_value_data (.op (.globalValue gv)) st =
    match ctx.func.globals.lookup gv with
    | some (.symbol name off colocated) =>
      .ok [.op (.extName name),
           .data tyRelocDistance (if colocated then VIdx.RelocDistance.Near else VIdx.RelocDistance.Far) [],
           .int off]
    | _ => .fail := rfl
  rw [this]
  split
  · rename_i name off col h
    simp only [ExtResult.ok.injEq, h, Option.some.injEq]
    constructor
    · intro e; exact ⟨name, off, col, rfl, e.symm⟩
    · rintro ⟨n', o', c', he, rfl⟩
      cases he; rfl
  · rename_i hne
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro n o c h; exact absurd h (hne n o c)

end Extern

/-! ## The inversion tactic -/

/-- The inverse-evaluation `simp` set of `isel_inv` plus the memory family's extern lemmas. -/
syntax "mem_inv_simp" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| mem_inv_simp [$ts,*] $[$loc]?) => `(tactic| isel_inv_simp [
        Backend.Proof.ext_little_or_native_endian_iff, Backend.Proof.ext_i64_from_iconst_iff,
        Backend.Proof.ext_i32_from_i64_iff, Backend.Proof.ctor_offset32_to_i32',
        Backend.Proof.ctor_i32_into_i64', Backend.Proof.ctor_i64_cast_unsigned',
        Backend.Proof.ctor_ty_bytes', Backend.Proof.ctor_u16_into_u64',
        Backend.Proof.ctor_u8_into_u32', Backend.Proof.ctor_shift_masked_imm',
        Backend.Proof.ctor_u64_wrapping_shl', Backend.Proof.ctor_u64_eq',
        Backend.Proof.ctor_i32_checked_add_iff, Backend.Proof.ctor_simm9_from_i64_iff,
        Backend.Proof.ctor_uimm12_scaled_from_i64_iff,
        Backend.Proof.ctor_uimm12_scaled_nonzero_from_i64_iff,
        Backend.Proof.ctor_abi_stackslot_offset_iff, Backend.Proof.ctor_abi_stackslot_addr_iff,
        Backend.Proof.ext_symbol_value_data_iff, Backend.Proof.ctor_box_external_name_iff,
        Backend.Proof.ctor_is_pic_iff, Backend.V.op.injEq, Backend.V.bool.injEq,
        Backend.Opnd.memFlags.injEq, $ts,*] $[$loc]?)

open Lean Elab Tactic Meta in
/-- The term ids a rule constant mentions (`.term _ t _` patterns and expressions). -/
def memRuleTermIds (rule : Name) : MetaM (Array Nat) := do
  let some ci := (← getEnv).find? rule | return #[]
  let some v := ci.value? | return #[]
  let acc ← IO.mkRef (#[] : Array Nat)
  v.forEach fun e => do
    if e.isAppOfArity ``Isle.Pattern.term 3 || e.isAppOfArity ``Isle.Expr.term 3 then
      match e.getArg! 1 with
      | .lit (.natVal n) => acc.modify (·.push n)
      | a => match a.nat? with
        | some n => acc.modify (·.push n)
        | none => pure ()
  return (← acc.get)

open Lean Elab Tactic Meta in
/-- The rule constants occurring in hypotheses `hs`, plus the data facts `hp.tN` of the terms
they mention, plus `ls`. -/
def memInvLemmas (hp : Ident) (ls : Array Lean.Term) (hs : Array Ident) :
    TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := withMainContext do
  let mut rules : Array Name := #[]
  for h in hs do
    let ty ← instantiateMVars (← inferType (← getLocalDeclFromUserName h.getId).toExpr)
    for c in ty.getUsedConstants do
      if let some ci := (← getEnv).find? c then
        if ci.type.isConstOf ``Isle.Rule && !rules.contains c then rules := rules.push c
  let mut ids : Array Nat := #[]
  for r in rules do
    ids := ids ++ (← memRuleTermIds r)
  let env ← getEnv
  let mut lemmas : Array (TSyntax `term) := #[]
  for t in ids.toList.eraseDups do
    if env.contains (Name.mkStr ``Backend.Proof.Data s!"t{t}") then
      lemmas := lemmas.push (mkIdent (hp.getId ++ Name.mkSimple s!"t{t}"))
  for r in rules do lemmas := lemmas.push (mkIdent r)
  for l in ls do lemmas := lemmas.push l
  lemmas.mapM fun l => `(Lean.Parser.Tactic.simpLemma| $l:term)

open Lean Elab Tactic Meta in
/-- `mem_inv hp [lemmas] at h₁ … hₙ`: invert the matches/evaluations `hᵢ` to a fixpoint
(simp with the inverse lemmas, the rules' data facts and `lemmas`; split; substitute). -/
elab "mem_inv " hp:ident " [" ls:term,* "]" " at " hs:(ppSpace colGt ident)+ : tactic => do
  let lemmaStx ← memInvLemmas hp ls.getElems hs
  evalTactic (← `(tactic| (mem_inv_simp [$lemmaStx,*] at $hs* <;> isel_destruct <;> subst_vars <;>
      repeat (mem_inv_simp [$lemmaStx,*] at * <;> isel_destruct <;> subst_vars))))

open Lean Elab Tactic Meta in
/-- `mem_refute hp at h`: one inversion pass; closes the goal when `h` is impossible. -/
elab "mem_refute " hp:ident " [" ls:term,* "]" " at " h:ident : tactic => do
  let lemmaStx ← memInvLemmas hp ls.getElems #[h]
  evalTactic (← `(tactic| mem_inv_simp [and_assoc, $lemmaStx,*] at $h:ident))

open Lean in
/-- `mem_split hp hc h t`: split the internal call `h : ApplyInternal … t …` into one goal per
rule of term `t`, with `hm` (the match), `he` (the right-hand side) and `hpre` (the earlier rules
failed); `hp` is kept (for `mem_inv`). -/
macro "mem_split " hp:ident hc:ident h:ident t:num : tactic => do
  let tN := mkIdent (hp.getId ++ Name.mkSimple s!"t{t.getNat}")
  let rN := mkIdent (hp.getId ++ Name.mkSimple s!"r{t.getNat}")
  let kN := mkIdent (Name.mkStr `Backend.Proof s!"term_{t.getNat}_kind")
  let hm := mkIdent `hm
  let he := mkIdent `he
  let hpre := mkIdent `hpre
  let hL := mkIdent `hL
  `(tactic| (
    obtain ⟨_, _, _, $hL, $hpre, _, _, _, _, _, _, $hm, $he, rfl, rfl⟩ :=
      internal_split_first $hc $tN $kN rfl (by rw [$rN:ident]; simp; omega) $h
    rw [$rN:ident] at $hL:ident
    isel_rule_cases $hL))

end Backend.Proof
