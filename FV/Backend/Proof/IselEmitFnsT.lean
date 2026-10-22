import FV.Backend.Proof.IselEmitFns
import FV.Backend.Proof.IselCovFnsT

/-!
# The emission analysis over float-capable contexts: the transfer functions

`aextET`: `aextE` with the value-type extractors widened (`aextT`, `IselCovFnsT`);
`actorET`: `actorE` with the register-producing constructors class-aware (`actorC`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Aarch64

/-- **Extern extractors** for the emission analysis over float-capable contexts. -/
def aextET (id : TermId) (a : AW) : List AW :=
  if id == TId.imm12_from_u64 then [.num .imm12 4096]
  else if id == TId.u8_from_u64 then [.num .int 256]
  else aextT id a

/-- **Extern constructors** for the emission analysis over float-capable contexts. -/
def actorET (id : TermId) (as : List AW) : AW :=
  if id == TId.imm_shift_from_imm64 then
    match as with
    | [t, _] => match tyB t shB with
      | some b => .num .immShift b
      | none => .num .immShift 64
    | _ => actorC id as
  else if id == TId.imm_shift_from_u8 then
    match as with
    | [.num .int b] => .num .immShift (min b 64)
    | _ => .num .immShift 64
  else if id == TId.u8_into_uimm5 then .num .uimm5 32
  else if id == TId.u8_into_imm12 then .num .imm12 4096
  else if id == TId.move_wide_const_from_u64 || id == TId.move_wide_const_from_inverted_u64 then
    match as with
    | [t, _] => match tyB t mwB with
      | some b => .num .mwc b
      | none => .num .mwc 4
    | _ => actorC id as
  else if id == TId.lshl_from_imm64 || id == TId.ashr_from_u64 then
    match as with
    | [t, _] => match tyB t shB with
      | some b => .num .shiftAmt b
      | none => .num .shiftAmt 64
    | _ => actorC id as
  else if id == TId.a64_extr_imm then
    match as with
    | [_, .num .immShift b] => .num .shiftAmt b
    | _ => actorC id as
  else if id == TId.bfm_immr || id == TId.bfm_imms then
    match as with
    | t :: _ => match tyB t (fun t => max t.laneBits 1) with
      | some b => .num .uimm6 b
      | none => actorC id as
    | _ => actorC id as
  else if id == TId.negate_imm_shift then
    match as with
    | [t, _] => match tyB t (fun t => max t.bits 1) with
      | some b => .num .immShift b
      | none => actorC id as
    | _ => actorC id as
  else if id == TId.rotr_opposite_amount then
    match as with
    | [t, _] => match tyB t (fun t => min (t.bits + 1) 64) with
      | some b => .num .immShift b
      | none => .num .immShift 64
    | _ => actorC id as
  else if id == TId.test_and_compare_bit_const then
    match as with
    | [t, _] => match tyB t (fun t => min t.bits 64) with
      | some b => .num .int b
      | none => .num .int 64
    | _ => actorC id as
  else if id == TId.ty_bits then
    match as with
    | [t] => match tyB t (fun t => t.bits + 1) with
      | some b => .num .int b
      | none => actorC id as
    | _ => actorC id as
  else if id == TId.shift_masked_imm then
    match as with
    | [t, _] => match tyB t (fun t => max t.laneBits 1) with
      | some b => .num .int b
      | none => actorC id as
    | _ => actorC id as
  else if id == TId.imm_size_from_type then .num .int 65
  else if id == TId.cond_code then condsOk
  else if id == TId.invert_cond then
    match as with
    | [c] => if condA c then condsOk else actorC id as
    | _ => actorC id as
  else if id == TId.gen_call_info then .num .callInfo 0
  else if id == TId.gen_call_ind_info then
    match as with
    | [_, r, _, _, _] => if r.isV then .num .callInfo 0 else actorC id as
    | _ => actorC id as
  else if id == TId.u8_into_u32 || id == TId.u8_into_u64 || id == TId.u16_into_u64 ||
      id == TId.u32_into_u64 || id == TId.i32_into_i64 then
    match as with
    | [.num .int b] => .num .int b
    | _ => actorC id as
  else actorC id as

end Backend.Proof.Cov
