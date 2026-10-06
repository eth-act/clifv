import FV.Backend.Proof.IselCovCheck

/-!
# Form coverage of the ISLE lowering (V3): the transfer functions of the extern helpers

`actor id as`: what extern constructor `id` returns on arguments `as` describes; `aext id a`:
what extern extractor `id` returns, position by position; `apre id as`: the precondition of a
constructor call (`emit` of a covered instruction, stack-argument stores of int vregs);
`aOracle`: `operand_size` on a single type. Their soundness is `IselCovExt`.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

/-- The register kinds of fresh registers of the types `ts`. -/
def clsMask (ts : List CTy) : Nat :=
  ts.foldl (fun m t => m ||| match t.regClass? with
    | some .int => 1
    | some .float => 2
    | none => 0) 0

/-- The operand size an `ImmLogic` built for one of the types `ts` has (`f`: the size per type). -/
def oneSize (ts : List CTy) (g : CTy → Option OperandSize) : AW :=
  match ts.filterMap g with
  | [] => .bot
  | s :: rest => if rest.all (· == s) then .logic s else .c0

/-- The size of a logical immediate for type `t` (`imm_logic_from_u64`). -/
def logicSize (t : CTy) : Option OperandSize :=
  if t == .int 32 then some .size32 else if t == .int 64 then some .size64 else none

/-- The size of a logical immediate for type `t` (`imm_logic_from_imm64`). -/
def logicSize64 (t : CTy) : Option OperandSize :=
  logicSize (if t.bits < 32 then CTy.int 32 else t)

/-- The scale of an unsigned offset for one of the types `ts`. -/
def oneScale (ts : List CTy) : AW :=
  match ts.map CTy.bytes with
  | b :: rest => if rest.all (· == b) then .scale b else .c0
  | [] => .bot

def tysOf : AW → Option (List CTy)
  | .ty ts => some ts
  | _ => none

/-- **Extern constructors** other than the type predicates. -/
def actorRest (id : TermId) (as : List AW) : AW :=
  if id == TId.temp_writable_reg then
    match as with
    | [a] => match tysOf a with
      | some ts => .reg (clsMask ts)
      | none => .reg 3
    | _ => .top
  else if id == TId.put_in_reg || id == TId.put_extended_in_reg || id == TId.load_constant_full then
    .reg 1
  else if id == TId.put_in_regs || id == TId.put_in_regs_vec || id == TId.gen_call_output then
    .flat 1 true
  else if id == TId.zero_reg || id == TId.writable_zero_reg then .reg 4
  else if id == TId.is_pic then .bool true
  else if id == TId.use_fp16 then .bool false
  else if id == TId.emit then .c0
  else if id == TId.writable_reg_to_reg then
    match as with
    | [a] => a
    | _ => .top
  else if id == TId.value_regs_get then
    match as with
    | [a, _] => .reg (AW.deep a).1
    | _ => .top
  else if id == TId.value_reg || id == TId.value_regs || id == TId.output || id == TId.output_vec ||
      id == TId.output_none then
    .flat (AW.deepL as).1 (AW.deepL as).2
  else if id == TId.imm_logic_from_u64 || id == TId.u64_into_imm_logic then
    match as with
    | [t, _] => match tysOf t with
      | some ts => oneSize ts logicSize
      | none => .c0
    | _ => .c0
  else if id == TId.imm_logic_from_imm64 then
    match as with
    | [t, _] => match tysOf t with
      | some ts => oneSize ts logicSize64
      | none => .c0
    | _ => .c0
  else if id == TId.shift_mask || id == TId.rotr_mask then .logic .size32
  else if id == TId.uimm12_scaled_from_i64 || id == TId.uimm12_scaled_nonzero_from_i64 then
    match as with
    | [_, t] => match tysOf t with
      | some ts => oneScale ts
      | none => .c0
    | _ => .c0
  else if id == TId.simm9_from_i64 then .simm9
  else if id == TId.abi_stackslot_addr then
    match as with
    | [rd, _, _] => .data tyMInst VIdx.MInst.LoadAddr [rd, .data tyAMode VIdx.AMode.SlotOffset [.c0]]
    | _ => .top
  else if id == TId.cond_br_zero then
    match as with
    | [r, s] => .data tyCondBrKind VIdx.CondBrKind.Zero [r, s]
    | _ => .top
  else if id == TId.cond_br_not_zero then
    match as with
    | [r, s] => .data tyCondBrKind VIdx.CondBrKind.NotZero [r, s]
    | _ => .top
  else if id == TId.cond_br_cond then
    match as with
    | [c] => .data tyCondBrKind VIdx.CondBrKind.Cond [c]
    | _ => .top
  else .flat 15 (AW.deepL as).2

/-- **Extern constructors.** -/
def actor (id : TermId) (as : List AW) : AW :=
  match tyPred id, as with
  | some q, [a] => match tysOf a with
    | some ts => .ty (ts.filter q)
    | none => .c0
  | _, _ => actorRest id as

theorem actor_none {id : TermId} (h : tyPred id = none) (as : List AW) :
    actor id as = actorRest id as := by
  unfold actor; rw [h]

/-- **Extern extractors**, output by output. -/
def aext (id : TermId) (a : AW) : List AW :=
  match tyPred id with
  | some q => match tysOf a with
    | some ts => [.ty (ts.filter q)]
    | none => [.top]
  | none =>
  if id == TId.value_type then [.ty eCTys]
  else if id == TId.inst_data_value then
    [.ty (.invalid :: eCTys), match a with
      | .xv .inst => .xv .data
      | _ => .c0]
  else if id == TId.def_inst then [.xv .inst]
  else if id == TId.maybe_uextend || id == TId.is_second_result || id == TId.first_result then
    [.xv .value]
  else if id == TId.value_array_2 then [.xv .value, .xv .value]
  else if id == TId.value_array_3 then [.xv .value, .xv .value, .xv .value]
  else if id == TId.value_slice_unwrap then [.xv .value, .c0]
  else if id == TId.multi_lane then
    match tysOf a with
    | some ts => if ts.any (·.laneCount > 1) then [.c0, .c0] else [.bot, .bot]
    | none => [.c0, .c0]
  else if id == TId.dynamic_lane then [.bot, .bot]
  else if id == TId.tls_model then [.data tyTlsModel VIdx.TlsModel.ElfGd []]
  else [.c0, .c0, .c0, .c0]

/-- **Preconditions** of extern constructor calls: an `emit`ted instruction is covered, the
argument registers `gen_call_args` stores are int vregs. -/
def apre (id : TermId) (as : List AW) : Bool :=
  if id == TId.emit then
    match as with
    | [a] => (AW.deep a).2
    | _ => false
  else if id == TId.gen_call_args then
    match as with
    | [_, a] => (AW.deep a).1 &&& 14 == 0
    | _ => false
  else true

/-- `operand_size` on a single type. -/
def aOracle (t : TermId) (as : List AW) : Option AW :=
  if t == TId.operand_size then
    match as with
    | [.ty [t1]] =>
      some (if t1.bits ≤ 32 then .data tyOperandSize VIdx.OperandSize.Size32 []
        else if t1.bits ≤ 64 then .data tyOperandSize VIdx.OperandSize.Size64 [] else .bot)
    | _ => some .c0
  else none

end Backend.Proof.Cov
