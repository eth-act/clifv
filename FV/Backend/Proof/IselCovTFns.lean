import FV.Backend.Proof.IselCovTSound
import FV.Backend.Proof.IselCovFns

/-!
# Form coverage over float-capable contexts (typed V3): the transfer functions

`IselCovFns` for the typed domain. What changes: a value's register is of its type's class
(`put_in_reg`/`put_in_regs`/`put_in_regs_vec` of `val ts`: `vcls ts`), an extended operand of an
integer value gives an int vreg (`put_extended_in_reg` of `extv`), the zero `movi` immediate of
the 32-bit form is `movi`; the extractors follow the typed atoms: `value_type` of `val ts` is
`ty ts`, `inst_data_value` of `inst fs` gives the families' result types and data, `def_inst`
of `val ts` the families that may define such a value, `value_array_*`/`value_slice_unwrap`
the typed positions; `extended_value_from_value` gives `extv`.
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (clsMask logicSize logicSize64)

/-- The operand size an `ImmLogic` built for one of the types `ts` has. -/
def oneSize (ts : List CTy) (g : CTy → Option OperandSize) : AT :=
  match ts.filterMap g with
  | [] => .bot
  | s :: rest => if rest.all (· == s) then .logic s else .c0

/-- The scale of an unsigned offset for one of the types `ts`. -/
def oneScale (ts : List CTy) : AT :=
  match ts.map CTy.bytes with
  | b :: rest => if rest.all (· == b) then .scale b else .c0
  | [] => .bot

/-- The register kinds of the vregs of values of the types `ts` (`valClass`: an int vreg for a
type without a class). -/
def vcls (ts : List CTy) : Nat :=
  ts.foldl (fun m t => m ||| match t.valClass with
    | .int => 1
    | .float => 2) 0

/-- The register kinds of the vregs of the values a `.values` list describes. -/
def vclsL (tss : List (List CTy)) : Nat := tss.foldl (fun m ts => m ||| vcls ts) 0

/-- The types of a type atom. -/
def tysOf' : AT → Option (List CTy)
  | .ty ts => some ts
  | _ => none

/-- **Extern constructors** other than the type predicates. -/
def actorRest (id : TermId) (as : List AT) : AT :=
  if id == TId.temp_writable_reg then
    match as with
    | [a] => match tysOf' a with
      | some ts => .reg (clsMask ts)
      | none => .reg 3
    | _ => .top
  else if id == TId.put_in_reg then
    match as with
    | [.val ts] => .reg (vcls ts)
    | _ => .reg 3
  else if id == TId.put_extended_in_reg then
    match as with
    | [.extv] => .reg 1
    | _ => .reg 3
  else if id == TId.load_constant_full then .reg 1
  -- `is_sinkable_inst` always fails (no load sinking)
  else if id == TId.is_sinkable_inst then .bot
  -- the literal pool's entry id (`emit_u64_le_const`, #565): an operand without registers
  else if id == TId.emit_u64_le_const then .c0
  else if id == TId.put_in_regs then
    match as with
    | [.val ts] => .flat (vcls ts) true
    | _ => .flat 3 true
  else if id == TId.put_in_regs_vec then
    match as with
    | [.vals tss] => .flat (vclsL tss) true
    | [.valsAll ts] => .flat (vcls ts) true
    | _ => .flat 3 true
  else if id == TId.asimd_mov_mod_imm_zero then
    match as with
    | [.data _ k []] => if k == VIdx.ScalarSize.Size32 then .movi else .c0
    | _ => .c0
  -- typed calls (S11e5a): one fresh vreg per ABI return, of its class
  else if id == TId.gen_call_output then .flat 3 true
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
    | [a, _] => .reg (AT.deep a).1
    | _ => .top
  else if id == TId.value_reg || id == TId.value_regs || id == TId.output || id == TId.output_vec ||
      id == TId.output_none then
    .flat (AT.deepL as).1 (AT.deepL as).2
  else if id == TId.imm_logic_from_u64 || id == TId.u64_into_imm_logic then
    match as with
    | [t, _] => match tysOf' t with
      | some ts => oneSize ts logicSize
      | none => .c0
    | _ => .c0
  else if id == TId.imm_logic_from_imm64 then
    match as with
    | [t, _] => match tysOf' t with
      | some ts => oneSize ts logicSize64
      | none => .c0
    | _ => .c0
  else if id == TId.shift_mask || id == TId.rotr_mask then .logic .size32
  else if id == TId.uimm12_scaled_from_i64 || id == TId.uimm12_scaled_nonzero_from_i64 then
    match as with
    | [_, t] => match tysOf' t with
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
  else .flat 15 (AT.deepL as).2

/-- **Extern constructors.** -/
def actor (id : TermId) (as : List AT) : AT :=
  match tyPred id, as with
  | some q, [a] => match tysOf' a with
    | some ts => .ty (ts.filter q)
    | none => .c0
  | _, _ => actorRest id as

theorem actor_none {id : TermId} (h : tyPred id = none) (as : List AT) :
    actor id as = actorRest id as := by
  unfold actor; rw [h]

/-- Every family. -/
@[irreducible] def allFams : List Nat := List.range famTab.length

theorem mem_allFams {i : Nat} (h : i < famTab.length) : i ∈ allFams := by
  unfold allFams; exact List.mem_range.mpr h

/-- The families an instruction atom names (every family for another value). -/
def instsOf : AT → List Nat
  | .inst fs => fs
  | _ => allFams

/-- The `inst_data_value` types of families `fs`. -/
def resOf (fs : List Nat) : List CTy := fs.flatMap fun i => (famTab.getD i default).res

/-- The data of families `fs`. -/
def dataOf : List Nat → AT
  | [i] => (famTab.getD i default).data
  | fs => .alts (fs.map fun i => (famTab.getD i default).data)

/-- A value of a type of `ts` may be a result of a family with result types `us`. -/
def compat (ts us : List CTy) : Bool :=
  ts.any (fun t => us.any fun u => decide (u = t)) ||
    (ts.any (fun t => t.regClass? == some .int) && us.any (fun t => t.regClass? == some .int))

/-- The families that may define a value of a type of `ts`. -/
def famsFor (ts : List CTy) : List Nat :=
  (List.range famTab.length).filter fun i => compat ts (famTab.getD i default).all

/-- The values of a `.values` list of length `n`. -/
def valsN (n : Nat) : AT → List AT
  | .vals tss => if tss.length == n then tss.map .val else List.replicate n vM
  | .valsAll ts => List.replicate n (.val ts)
  | _ => List.replicate n vM

/-- **Extern extractors**, output by output. -/
def aext (id : TermId) (a : AT) : List AT :=
  match tyPred id with
  | some q => match tysOf' a with
    | some ts => [.ty (ts.filter q)]
    | none => [.top]
  | none =>
  if id == TId.value_type then
    match a with
    | .val ts => [.ty ts]
    | _ => [.ty anyCTys]
  else if id == TId.inst_data_value then
    match a with
    | .inst fs => [.ty (resOf fs), dataOf fs]
    | _ => [.ty (.invalid :: anyCTys), .c0]
  else if id == TId.def_inst then
    match a with
    | .val ts => [.inst (famsFor ts)]
    | _ => [.inst allFams]
  else if id == TId.first_result then
    match a with
    | .inst fs => [.val (resOf fs)]
    | _ => [vM]
  else if id == TId.is_second_result then
    match a with
    | .val ts => [.val ts]
    | _ => [vM]
  else if id == TId.maybe_uextend then
    match a with
    | .val ts => [.val (ts ++ eCTys)]
    | _ => [vM]
  else if id == TId.value_array_2 then valsN 2 a
  else if id == TId.value_array_3 then valsN 3 a
  else if id == TId.value_slice_unwrap then
    match a with
    | .vals (ts :: rest) => [.val ts, .vals rest]
    | .valsAll ts => [.val ts, .valsAll ts]
    | _ => [vM, .valsAll anyCTys]
  else if id == TId.value_list_slice then
    match a with
    | .vals tss => [.vals tss]
    | .valsAll ts => [.valsAll ts]
    | _ => [.valsAll anyCTys]
  else if id == TId.extended_value_from_value then [.extv]
  else if flagOff id then
    match a with
    | .inst _ => [.bot]
    | _ => [.c0, .c0, .c0, .c0]
  else if id == TId.multi_lane then
    match tysOf' a with
    | some ts => if ts.any (·.laneCount > 1) then [.c0, .c0] else [.bot, .bot]
    | none => [.c0, .c0]
  else if id == TId.dynamic_lane then [.bot, .bot]
  else if id == TId.tls_model then [.data tyTlsModel VIdx.TlsModel.ElfGd []]
  else [.c0, .c0, .c0, .c0]

/-- **Preconditions** of extern constructor calls: an `emit`ted instruction is covered, the
argument registers `gen_call_args` stores are int vregs. -/
def apre (id : TermId) (as : List AT) : Bool :=
  if id == TId.emit then
    match as with
    | [a] => (AT.deep a).2
    | _ => false
  else if id == TId.gen_call_args then
    match as with
    | [_, a] => (AT.deep a).1 &&& 14 == 0
    | _ => false
  else true

/-- `operand_size` on a single type. -/
def aOracle (t : TermId) (as : List AT) : Option AT :=
  if t == TId.operand_size then
    match as with
    | [.ty [t1]] =>
      some (if t1.bits ≤ 32 then .data tyOperandSize VIdx.OperandSize.Size32 []
        else if t1.bits ≤ 64 then .data tyOperandSize VIdx.OperandSize.Size64 [] else .bot)
    | _ => some .c0
  else none

end Backend.Proof.CovT
