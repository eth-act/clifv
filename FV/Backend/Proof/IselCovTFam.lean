import FV.Backend.Proof.IselCovTSem

/-!
# Form coverage over float-capable contexts (typed V3): instruction families

An instruction family `F` describes the instructions of a float-capable context the abstract
interpreter starts from: `F.res` the type `inst_data_value` gives (the first result's, `invalid`
without results), `F.all` the types of every result, `F.data` the `InstructionData` (opcode
alternatives, and typed value fields `val`/`vals`/`valsAll`). `famTab` lists the families of the
typed scope's instructions (`instData`'s formats, split where the operand or result classes differ:
float/integer `load`, `store`, `select` and `bitcast`) and of the terminators (`termData`,
`tryCallData`: the data of a terminator's slot in its context).

`instM f ctx fs`: the meaning of `inst fs`, an instruction of the context of one of the
families `fs` (its data described with `γP ctx noInst`, its result values typed). `γ f ctx` is
`γP ctx (instM f ctx)`; the shallow lemmas of `IselCovTSem` for it.

Whether every instruction of a function belongs to a family is `IselCovTFamCover`; nothing else
depends on the families' content, so a new family (a new float root) needs no new proof besides
its cover case.
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Aarch64

/-- The float value types. -/
def fCTys : List CTy := [.float 32, .float 64]

/-- The value types of the float-capable lowering (`mCTys`). -/
def anyCTys : List CTy := eCTys ++ fCTys

/-- An instruction family. -/
structure Fam where
  /-- the types `inst_data_value` gives (the first result's, `invalid` without results) -/
  res : List CTy
  /-- the types of every result -/
  all : List CTy
  /-- the `InstructionData` -/
  data : AT
  deriving Repr, Inhabited

/-- The opcodes of a family, as an enum value. -/
def opAlts (os : List Nat) : AT := .alts (os.map fun o => .data tyOpcode o [])

/-- An `InstructionData` of format `k`. -/
def idata (k : Nat) (fs : List AT) : AT := .data tyInstData k fs

/-- A value of an E type / a float type / any type of the float-capable lowering. -/
def vE : AT := .val eCTys
def vF : AT := .val fCTys
def vM : AT := .val anyCTys

/-- No result: `inst_data_value` gives `invalid`. -/
def noRes : List CTy := [.invalid]

/-- **The instruction families.** -/
def famTab : List Fam := [
  -- 0: `iconst` at E types
  ⟨eCTys, eCTys, idata VIdx.InstructionData.UnaryImm [opAlts [VIdx.Opcode.Iconst], .c0]⟩,
  -- 1: the integer unary operations
  ⟨eCTys, eCTys, idata VIdx.InstructionData.Unary [opAlts [VIdx.Opcode.Ineg, VIdx.Opcode.Bnot,
    VIdx.Opcode.Clz, VIdx.Opcode.Ctz, VIdx.Opcode.Popcnt, VIdx.Opcode.Bswap, VIdx.Opcode.Bitrev,
    VIdx.Opcode.Uextend, VIdx.Opcode.Sextend, VIdx.Opcode.Ireduce, VIdx.Opcode.Bmask], vE]⟩,
  -- 2: the integer binary operations
  ⟨eCTys, eCTys, idata VIdx.InstructionData.Binary [opAlts [VIdx.Opcode.Iadd, VIdx.Opcode.Isub,
    VIdx.Opcode.Imul, VIdx.Opcode.Umulhi, VIdx.Opcode.Smulhi, VIdx.Opcode.Band, VIdx.Opcode.Bor,
    VIdx.Opcode.Bxor, VIdx.Opcode.Ishl, VIdx.Opcode.Ushr, VIdx.Opcode.Sshr, VIdx.Opcode.Rotl,
    VIdx.Opcode.Rotr, VIdx.Opcode.Smin, VIdx.Opcode.Smax, VIdx.Opcode.Umin, VIdx.Opcode.Umax,
    VIdx.Opcode.Udiv, VIdx.Opcode.Sdiv, VIdx.Opcode.Urem, VIdx.Opcode.Srem], .vals [eCTys, eCTys]]⟩,
  -- 3: `icmp`
  ⟨eCTys, eCTys, idata VIdx.InstructionData.IntCompare [opAlts [VIdx.Opcode.Icmp],
    .vals [eCTys, eCTys], .c0]⟩,
  -- 4: integer loads
  ⟨eCTys, eCTys, idata VIdx.InstructionData.Load [opAlts [VIdx.Opcode.Load, VIdx.Opcode.Uload8,
    VIdx.Opcode.Sload8, VIdx.Opcode.Uload16, VIdx.Opcode.Sload16, VIdx.Opcode.Uload32,
    VIdx.Opcode.Sload32], vE, .c0, .c0]⟩,
  -- 5: float loads
  ⟨fCTys, fCTys, idata VIdx.InstructionData.Load [opAlts [VIdx.Opcode.Load], vE, .c0, .c0]⟩,
  -- 6: integer stores
  ⟨noRes, [], idata VIdx.InstructionData.Store [opAlts [VIdx.Opcode.Store, VIdx.Opcode.Istore8,
    VIdx.Opcode.Istore16, VIdx.Opcode.Istore32], .vals [eCTys, eCTys], .c0, .c0]⟩,
  -- 7: float stores
  ⟨noRes, [], idata VIdx.InstructionData.Store [opAlts [VIdx.Opcode.Store], .vals [fCTys, eCTys],
    .c0, .c0]⟩,
  -- 8: integer `select`
  ⟨eCTys, eCTys, idata VIdx.InstructionData.Ternary [opAlts [VIdx.Opcode.Select],
    .vals [eCTys, eCTys, eCTys]]⟩,
  -- 9: float `select`
  ⟨fCTys, fCTys, idata VIdx.InstructionData.Ternary [opAlts [VIdx.Opcode.Select],
    .vals [eCTys, fCTys, fCTys]]⟩,
  -- 10: `nop`, `fence`
  ⟨noRes, [], idata VIdx.InstructionData.NullAry [opAlts [VIdx.Opcode.Nop, VIdx.Opcode.Fence]]⟩,
  -- 11: `symbol_value`, `tls_value`
  ⟨eCTys, eCTys, idata VIdx.InstructionData.UnaryGlobalValue [opAlts [VIdx.Opcode.SymbolValue,
    VIdx.Opcode.TlsValue], .c0]⟩,
  -- 12: `stack_addr`
  ⟨eCTys, eCTys, idata VIdx.InstructionData.StackAddr [opAlts [VIdx.Opcode.StackAddr], .c0, .c0]⟩,
  -- 13: `call` (integer signatures)
  ⟨eCTys ++ noRes, eCTys, idata VIdx.InstructionData.Call [opAlts [VIdx.Opcode.Call],
    .valsAll eCTys, .c0]⟩,
  -- 14: `call_indirect` (integer signatures)
  ⟨eCTys ++ noRes, eCTys, idata VIdx.InstructionData.CallIndirect
    [opAlts [VIdx.Opcode.CallIndirect], .valsAll eCTys, .c0]⟩,
  -- 15: `func_addr`
  ⟨eCTys, eCTys, idata VIdx.InstructionData.FuncAddr [opAlts [VIdx.Opcode.FuncAddr], .c0]⟩,
  -- 16: `atomic_load`
  ⟨eCTys, eCTys, idata VIdx.InstructionData.LoadNoOffset [opAlts [VIdx.Opcode.AtomicLoad], vE,
    .c0]⟩,
  -- 17: `bitcast` to an integer
  ⟨eCTys, eCTys, idata VIdx.InstructionData.LoadNoOffset [opAlts [VIdx.Opcode.Bitcast], vM,
    .c0]⟩,
  -- 18: `atomic_store`
  ⟨noRes, [], idata VIdx.InstructionData.StoreNoOffset [opAlts [VIdx.Opcode.AtomicStore],
    .vals [eCTys, eCTys], .c0]⟩,
  -- 19: `atomic_rmw`
  ⟨eCTys, eCTys, idata VIdx.InstructionData.AtomicRmw [opAlts [VIdx.Opcode.AtomicRmw],
    .vals [eCTys, eCTys], .c0, .c0]⟩,
  -- 20: `atomic_cas`
  ⟨eCTys, eCTys, idata VIdx.InstructionData.AtomicCas [opAlts [VIdx.Opcode.AtomicCas],
    .vals [eCTys, eCTys, eCTys], .c0]⟩,
  -- 21: `f32const`
  ⟨[.float 32], [.float 32], idata VIdx.InstructionData.UnaryIeee32 [opAlts [VIdx.Opcode.F32const],
    .c0]⟩,
  -- 22: `f64const`
  ⟨[.float 64], [.float 64], idata VIdx.InstructionData.UnaryIeee64 [opAlts [VIdx.Opcode.F64const],
    .c0]⟩,
  -- 23: `bitcast` to a float
  ⟨fCTys, fCTys, idata VIdx.InstructionData.LoadNoOffset [opAlts [VIdx.Opcode.Bitcast], vM,
    .c0]⟩,
  -- terminators (`termData`, `tryCallData`; the slot of a terminator in its context)
  -- 24: `jump`
  ⟨noRes, [], idata VIdx.InstructionData.Jump [opAlts [VIdx.Opcode.Jump], .c0]⟩,
  -- 25: `brif` (an integer condition)
  ⟨noRes, [], idata VIdx.InstructionData.Brif [opAlts [VIdx.Opcode.Brif], vE, .c0]⟩,
  -- 26: `br_table` (an integer index)
  ⟨noRes, [], idata VIdx.InstructionData.BranchTable [opAlts [VIdx.Opcode.BrTable], vE, .c0]⟩,
  -- 27: `return`
  ⟨noRes, [], idata VIdx.InstructionData.MultiAry [opAlts [VIdx.Opcode.Return],
    .valsAll anyCTys]⟩,
  -- 28: `trap`
  ⟨noRes, [], idata VIdx.InstructionData.Trap [opAlts [VIdx.Opcode.Trap], .c0]⟩,
  -- 29: `try_call` (integer arguments)
  ⟨noRes, [], idata VIdx.InstructionData.TryCall [opAlts [VIdx.Opcode.TryCall],
    .valsAll eCTys, .c0, .c0]⟩,
  -- 30: `try_call_indirect` (integer callee and arguments)
  ⟨noRes, [], idata VIdx.InstructionData.TryCallIndirect [opAlts [VIdx.Opcode.TryCallIndirect],
    .valsAll eCTys, .c0]⟩,
  -- the S11f float operations of `Compile.instETF` (appended: the indices above are unchanged)
  -- 31: two-operand float arithmetic
  ⟨fCTys, fCTys, idata VIdx.InstructionData.Binary [opAlts [VIdx.Opcode.Fadd, VIdx.Opcode.Fsub,
    VIdx.Opcode.Fmul, VIdx.Opcode.Fdiv, VIdx.Opcode.Fmin, VIdx.Opcode.Fmax], .vals [fCTys, fCTys]]⟩,
  -- 32: one-operand float arithmetic and rounding
  ⟨fCTys, fCTys, idata VIdx.InstructionData.Unary [opAlts [VIdx.Opcode.Sqrt, VIdx.Opcode.Fneg,
    VIdx.Opcode.Fabs, VIdx.Opcode.Ceil, VIdx.Opcode.Floor, VIdx.Opcode.Trunc, VIdx.Opcode.Nearest,
    VIdx.Opcode.Fpromote, VIdx.Opcode.Fdemote], vF]⟩,
  -- 33: `fcvt_from_{u,s}int` (an integer operand)
  ⟨fCTys, fCTys, idata VIdx.InstructionData.Unary [opAlts [VIdx.Opcode.FcvtFromUint,
    VIdx.Opcode.FcvtFromSint], vE]⟩,
  -- 34: `fcvt_to_{u,s}int_sat` to `i32`/`i64` (a float operand)
  ⟨[.int 32, .int 64], [.int 32, .int 64], idata VIdx.InstructionData.Unary
    [opAlts [VIdx.Opcode.FcvtToUintSat, VIdx.Opcode.FcvtToSintSat], vF]⟩,
  -- 35: `fcmp` of two floats at a condition of `fccOk` (not `one` 7, `ueq` 9); an `i8` result
  ⟨[.int 8], [.int 8], idata VIdx.InstructionData.FloatCompare [opAlts [VIdx.Opcode.Fcmp],
    .vals [fCTys, fCTys],
    .alts ([0, 1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 13].map fun k => .data TyId.FloatCC k [])]⟩]

/-- A family describes an instruction entry of the context: the type `inst_data_value` gives,
the types of the results, the data. -/
def FamOk (ctx : Ctx) (F : Fam) (info : IInfo) : Prop :=
  info.resTys.head?.getD .invalid ∈ F.res ∧
    (∀ x ∈ info.results.head?, ValIn ctx x F.res) ∧ (∀ x ∈ info.results, ValIn ctx x F.all) ∧
    γP ctx noInst F.data info.data

/-- **The meaning of `inst fs`**: an instruction of the context, of a family of `fs`. -/
def instM (f : Clif.Function) (ctx : Ctx) (fs : List Nat) (v : V) : Prop :=
  ∃ j info, v = .inst j ∧ ctx.insts[j]? = some info ∧
    ∃ i ∈ fs, ∃ F, famTab[i]? = some F ∧ FamOk ctx F info

theorem instRef_instM (f : Clif.Function) (ctx : Ctx) : InstRef (instM f ctx) := by
  intro fs v h
  obtain ⟨j, -, rfl, -⟩ := h
  exact ⟨j, rfl⟩

/-- **The meaning of an abstract value** in the context `ctx` of `f`. -/
abbrev γ (f : Clif.Function) (ctx : Ctx) : AT → V → Prop := γP ctx (instM f ctx)
/-- Some abstract value of the list describes `v`. -/
abbrev γAny (f : Clif.Function) (ctx : Ctx) : List AT → V → Prop := γAnyP ctx (instM f ctx)
/-- Pointwise `γ`. -/
abbrev γL (f : Clif.Function) (ctx : Ctx) : List AT → List V → Prop := γLP ctx (instM f ctx)

variable {f : Clif.Function} {ctx : Ctx}

theorem γAny_iff {as : List AT} {v : V} : γAny f ctx as v ↔ ∃ a ∈ as, γ f ctx a v := γAnyP_iff

theorem γL_length {as : List AT} {vs : List V} (h : γL f ctx as vs) : as.length = vs.length :=
  γLP_length h

theorem γL_get {as : List AT} {vs : List V} (h : γL f ctx as vs) (i : Nat) (a : AT) (v : V)
    (ha : as[i]? = some a) (hv : vs[i]? = some v) : γ f ctx a v :=
  γLP_get h i a v ha hv

theorem mask_sound {a : AT} {r : Reg} (h : γ f ctx a (.reg r)) : r.kind &&& a.mask ≠ 0 :=
  mask_soundP (instRef_instM f ctx) h

theorem isV_sound {a : AT} (ha : a.isV = true) {r : Reg} (h : γ f ctx a (.reg r)) :
    ∃ n, r = .vreg n .int := isV_soundP (instRef_instM f ctx) ha h

theorem isF_sound {a : AT} (ha : a.isF = true) {r : Reg} (h : γ f ctx a (.reg r)) :
    ∃ n, r = .vreg n .float := isF_soundP (instRef_instM f ctx) ha h

theorem isVZ_sound {a : AT} (ha : a.isVZ = true) {r : Reg} (h : γ f ctx a (.reg r)) :
    (∃ n, r = .vreg n .int) ∨ r = .xzr := isVZ_soundP (instRef_instM f ctx) ha h

theorem enumsOf_sound {a : AT} {ks : List Nat} (ha : a.enumsOf = some ks) {v : V}
    (h : γ f ctx a v) : ∃ t k, v = .data t k [] ∧ k ∈ ks := enumsOf_soundP ha h

theorem enumAll_sound {a : AT} {p : Nat → Bool} (ha : a.enumAll p = true) {v : V}
    (h : γ f ctx a v) : ∃ t k, v = .data t k [] ∧ p k = true := enumAll_soundP ha h

/-- A family's data, described without instruction atoms, is described by `γ`. -/
theorem γ_of_noInst {a : AT} {v : V} (h : γP ctx noInst a v) : γ f ctx a v :=
  γP_mono (fun _ _ h => h.elim) a v h

end Backend.Proof.CovT
