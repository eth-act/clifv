import FV.Backend.Proof.IselInterp

/-!
# The embedding `Backend.sem` and the extern helpers used by the probe's rules

Each lemma evaluates one extern helper (`Backend.externCtor` / `Backend.externExtract`, the
trusted Lean transcriptions of Cranelift's Rust helpers) on the argument shapes the rules pass.
They are proved by `rfl` (the helper's string-keyed `match` reduces by evaluation) plus a
rewrite with the context hypothesis: `simp [externCtor]` instead generates the equation lemmas
of a 100-alternative string match and exceeds the heartbeat limit.

`MInst.ofV` / `mkVariant` look enum variants up by *name* in the exported program's type table
(`variantNames`, `islTy`). Those lookups only touch `program.types` (one flat array), which
the kernel and `rfl` evaluate cheaply; `Meta`'s `whnf` needs a deeper recursion than the default
limit for the 153-element array, hence the local `maxRecDepth 4000` on those `rfl` proofs
(no kernel reduction of the rule data is involved).
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

/-! ## `Backend.sem` -/

section Sem
variable (ctx : Ctx)

@[isel_data] theorem sem_ctor : (sem ctx).ctor = externCtor ctx := rfl
@[isel_data] theorem sem_extract : (sem ctx).extract = externExtract ctx := rfl
@[isel_data] theorem sem_mkData (ty k fs) : (sem ctx).mkData ty k fs = .data ty k fs := rfl
@[isel_data] theorem sem_unData (ty t k fs) :
    (sem ctx).unData ty (.data t k fs) = if t = ty then some (k, fs) else none := by
  simp [sem]
@[isel_data] theorem sem_int (ty i) : (sem ctx).int ty i = .int (normInt ty i) := rfl
@[isel_data] theorem sem_bool (b) : (sem ctx).bool b = .bool b := rfl
@[isel_data] theorem sem_prim_type (n) : (sem ctx).prim 14 n = (CTy.ofName? n).map .ty := by
  simp [sem, typeName_14]

end Sem

attribute [isel_data] CTy.ofName? Option.map_some Option.map_none

/-! ## Extern extractors -/

section Extern
variable (ctx : Ctx) (st : LState)

theorem ext_inst_data_value {i : Nat} {info : IInfo} (h : ctx.insts[i]? = some info) :
    externExtract ctx term_209 (.inst i) st =
      .ok [.ty (info.resTys.head?.getD .invalid), info.data] := by
  have : externExtract ctx term_209 (.inst i) st = match ctx.insts[i]? with
    | some info => .ok [.ty (info.resTys.head?.getD .invalid), info.data]
    | none => .unmodeled s!"inst {i}" := rfl
  rw [this, h]

theorem ext_def_inst {v : Nat} : externExtract ctx term_1 (.value v) st =
    match ctx.defInst? v with
    | some i => .ok [.inst i]
    | none => .fail := rfl

theorem ext_def_inst_none {v : Nat} (h : ctx.defInst? v = none) :
    externExtract ctx term_1 (.value v) st = .fail := by
  rw [ext_def_inst, h]

theorem ext_def_inst_some {v i : Nat} (h : ctx.defInst? v = some i) :
    externExtract ctx term_1 (.value v) st = .ok [.inst i] := by
  rw [ext_def_inst, h]

theorem ext_value_type {v : Nat} {t : CTy} (h : ctx.valueType? v = some t) :
    externExtract ctx term_2 (.value v) st = .ok [.ty t] := by
  have : externExtract ctx term_2 (.value v) st = match ctx.valueType? v with
    | some ty => .ok [.ty ty]
    | none => .unmodeled s!"value_type of unknown v{v}" := rfl
  rw [this, h]

theorem ext_value_array_2 (x y : Nat) :
    externExtract ctx term_1614 (.values [x, y]) st = .ok [.value x, .value y] := rfl

theorem ext_u64_from_imm64 (i : Int) :
    externExtract ctx term_144 (.int i) st = .ok [.int (u64 i)] := rfl

theorem ext_imm12_from_u64 (i : Int) :
    externExtract ctx term_325 (.int i) st =
      match Imm12.ofNat? (u64 i) with
      | some imm => .ok [.op (.imm12 imm)]
      | none => .fail := rfl

/-! Type predicates (`tyPred`) on integer types. -/

theorem ext_ty_int_ref_scalar_64_extract {w : Nat} (hw : w ≤ 64) :
    externExtract ctx term_119 (.ty (.int w)) st = .ok [.ty (.int w)] := by
  have : externExtract ctx term_119 (.ty (.int w)) st =
    if (decide ((CTy.int w).bits ≤ 64) && !(CTy.int w).isFloat && !(CTy.int w).isVector) = true
    then .ok [.ty (.int w)] else .fail := rfl
  rw [this]; simp [CTy.bits, CTy.isFloat, CTy.isVector, hw]

theorem ext_ty_int (w : Nat) :
    externExtract ctx term_126 (.ty (.int w)) st = .ok [.ty (.int w)] := rfl

theorem ext_fits_in_16 (w : Nat) :
    externExtract ctx term_110 (.ty (.int w)) st = if w ≤ 16 then .ok [.ty (.int w)] else .fail := by
  have : externExtract ctx term_110 (.ty (.int w)) st =
    if decide ((CTy.int w).bits ≤ 16) = true then .ok [.ty (.int w)] else .fail := rfl
  rw [this]; by_cases h : w ≤ 16 <;> simp [CTy.bits, h]

theorem ext_fits_in_32 (w : Nat) :
    externExtract ctx term_111 (.ty (.int w)) st = if w ≤ 32 then .ok [.ty (.int w)] else .fail := by
  have : externExtract ctx term_111 (.ty (.int w)) st =
    if decide ((CTy.int w).bits ≤ 32) = true then .ok [.ty (.int w)] else .fail := rfl
  rw [this]; by_cases h : w ≤ 32 <;> simp [CTy.bits, h]

theorem ext_fits_in_64 (w : Nat) :
    externExtract ctx term_113 (.ty (.int w)) st = if w ≤ 64 then .ok [.ty (.int w)] else .fail := by
  have : externExtract ctx term_113 (.ty (.int w)) st =
    if decide ((CTy.int w).bits ≤ 64) = true then .ok [.ty (.int w)] else .fail := rfl
  rw [this]; by_cases h : w ≤ 64 <;> simp [CTy.bits, h]

theorem ext_ty_32_or_64 (w : Nat) :
    externExtract ctx term_120 (.ty (.int w)) st =
      if w = 32 ∨ w = 64 then .ok [.ty (.int w)] else .fail := by
  have : externExtract ctx term_120 (.ty (.int w)) st =
    if ((CTy.int w).bits == 32 || (CTy.int w).bits == 64) = true then .ok [.ty (.int w)]
    else .fail := rfl
  rw [this]; by_cases h : w = 32 ∨ w = 64 <;> simp [CTy.bits, h] <;> omega

/-! ## Extern constructors -/

theorem ctor_put_in_reg {x : Nat} {r : Reg} (h : ctx.valueReg? x = some r) :
    externCtor ctx term_182 [.value x] st = .ok (.reg r, st) := by
  have : externCtor ctx term_182 [.value x] st = match ctx.valueReg? x with
      | some r => .ok (.reg r, st)
      | none => .unmodeled s!"put_in_reg v{x}" := rfl
  rw [this, h]

theorem ctor_put_in_regs {x : Nat} {r : Reg} (h : ctx.valueReg? x = some r) :
    externCtor ctx term_183 [.value x] st = .ok (.regs [r], st) := by
  have : externCtor ctx term_183 [.value x] st = match ctx.valueReg? x with
      | some r => .ok (.regs [r], st)
      | none => .unmodeled s!"put_in_regs v{x}" := rfl
  rw [this, h]

theorem ctor_temp_writable_reg_i64 :
    externCtor ctx term_175 [.ty (.int 64)] st = .ok (.reg (st.fresh .int).1, (st.fresh .int).2) :=
  rfl

theorem ctor_writable_reg_to_reg (r : V) : externCtor ctx term_201 [r] st = .ok (r, st) := rfl
theorem ctor_value_reg (r : Reg) : externCtor ctx term_164 [.reg r] st = .ok (.regs [r], st) := rfl
theorem ctor_output (rs : List Reg) :
    externCtor ctx term_170 [.regs rs] st = .ok (.regsVec [rs], st) := rfl
theorem ctor_value_regs_get_0 (r : Reg) (rs : List Reg) :
    externCtor ctx term_185 [.regs (r :: rs), .int 0] st = .ok (.reg r, st) := rfl
theorem ctor_writable_zero_reg : externCtor ctx term_356 [] st = .ok (.reg .xzr, st) := rfl
theorem ctor_ty_bits (w : Nat) : externCtor ctx term_87 [.ty (.int w)] st = .ok (.int w, st) := rfl

theorem ctor_emit {v : V} {m : MInst} (h : MInst.ofV v = some m) :
    externCtor ctx term_235 [v] st = .ok (.op .unit, st.emit m) := by
  have : externCtor ctx term_235 [v] st = match MInst.ofV v with
      | some m => .ok (.op .unit, st.emit m)
      | none => .unmodeled s!"emit of {((v.variant?).map (·.2.1)).getD "?"}" := rfl
  rw [this, h]

set_option maxRecDepth 4000 in
theorem ctor_shift_mask_i8 :
    externCtor ctx term_704 [.ty (.int 8)] st = .ok (.op (.immLogic ⟨7, .size32⟩), st) := rfl

/-- `lower_condcode` on the `IntCC` of a CLIF `icmp` (total on CLIF condition codes). -/
def condOf : Clif.IntCC → Cond
  | .eq => .eq | .ne => .ne | .slt => .lt | .sge => .ge | .sgt => .gt | .sle => .le
  | .ult => .lo | .uge => .hs | .ugt => .hi | .ule => .ls

set_option maxRecDepth 4000 in
theorem ctor_cond_code (cc : Clif.IntCC) :
    externCtor ctx term_592 [mkVariant tyIntCC (intccName cc)] st =
      .ok (mkVariant tyCond (condOf cc).name, st) := by
  cases cc <;> rfl

end Extern

/-! ## `MInst.ofV` on the instructions the probe's rules emit (register fields symbolic) -/

section OfV
variable (rd rn rm : Reg)

set_option maxRecDepth 4000 in
theorem ofV_aluRRR_add_32 :
    MInst.ofV (.data 58 2 [.data 59 0 [], .data 93 0 [], .reg rd, .reg rn, .reg rm]) =
      some (.aluRRR .add .size32 rd rn rm) := rfl
set_option maxRecDepth 4000 in
theorem ofV_aluRRR_add_64 :
    MInst.ofV (.data 58 2 [.data 59 0 [], .data 93 1 [], .reg rd, .reg rn, .reg rm]) =
      some (.aluRRR .add .size64 rd rn rm) := rfl
set_option maxRecDepth 4000 in
theorem ofV_aluRRR_subs_32 :
    MInst.ofV (.data 58 2 [.data 59 10 [], .data 93 0 [], .reg rd, .reg rn, .reg rm]) =
      some (.aluRRR .subS .size32 rd rn rm) := rfl
set_option maxRecDepth 4000 in
theorem ofV_aluRRR_subs_64 :
    MInst.ofV (.data 58 2 [.data 59 10 [], .data 93 1 [], .reg rd, .reg rn, .reg rm]) =
      some (.aluRRR .subS .size64 rd rn rm) := rfl
set_option maxRecDepth 4000 in
theorem ofV_aluRRR_lsr_32 :
    MInst.ofV (.data 58 2 [.data 59 16 [], .data 93 0 [], .reg rd, .reg rn, .reg rm]) =
      some (.aluRRR .lsr .size32 rd rn rm) := rfl
set_option maxRecDepth 4000 in
theorem ofV_aluRRImm12_add_32 (i : Imm12) :
    MInst.ofV (.data 58 4 [.data 59 0 [], .data 93 0 [], .reg rd, .reg rn, .op (.imm12 i)]) =
      some (.aluRRImm12 .add .size32 rd rn i) := rfl
set_option maxRecDepth 4000 in
theorem ofV_aluRRImm12_add_64 (i : Imm12) :
    MInst.ofV (.data 58 4 [.data 59 0 [], .data 93 1 [], .reg rd, .reg rn, .op (.imm12 i)]) =
      some (.aluRRImm12 .add .size64 rd rn i) := rfl
set_option maxRecDepth 4000 in
theorem ofV_aluRRImmLogic_and_32 (i : ImmLogic) :
    MInst.ofV (.data 58 5 [.data 59 4 [], .data 93 0 [], .reg rd, .reg rn, .op (.immLogic i)]) =
      some (.aluRRImmLogic .and .size32 rd rn i) := rfl
set_option maxRecDepth 4000 in
theorem ofV_extend_u8_32 :
    MInst.ofV (.data 58 28 [.reg rd, .reg rn, .bool false, .int 8, .int 32]) =
      some (.extend rd rn false 8 32) := rfl
set_option maxRecDepth 4000 in
theorem ofV_cset (c : Cond) :
    MInst.ofV (.data 58 33 [.reg rd, mkVariant tyCond c.name]) = some (.cset rd c) := by
  cases c <;> rfl

end OfV

end Backend.Proof
