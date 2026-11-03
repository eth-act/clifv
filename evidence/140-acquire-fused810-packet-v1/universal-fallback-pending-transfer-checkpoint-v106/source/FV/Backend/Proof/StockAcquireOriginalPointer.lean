import FV.Backend.Proof.StockAcquirePatternData
import FV.Backend.Proof.StockAcquireSinkCallRequest

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

private theorem data_fields (format : String) (fields : List V) {tag : Nat} {actual : List V}
    (encoded : (Except.ok (instDataV format fields) : Except String V) = .ok (.data 152 tag actual)) :
    actual = fields := by
  exact (mkVariant_eq_data (Except.ok.inj encoded)).2.2

/-- The actual mapped atomic producer fixes both original pointer and original flags. -/
theorem mapped_atomic_original_fields {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {producer pointer : Nat} {info : IInfo} {rest : List V}
    {ty : Clif.Ty} {flags : Clif.MemFlags}
    (installed : ctx.insts[producer]? = some info)
    (source : info.clif = some (.atomicLoad ty flags pointer))
    (integer : eTy ty = true) (little : flags.endianness ≠ some .big)
    (shape : info.data = .data 152 17 (.data 151 158 []::rest)) :
    info.data = .data 152 17 [.data 151 158 [],.value pointer,.op (.memFlags flags)] := by
  have encoded := mapped.data producer info _ installed source
  rw [shape] at encoded
  have endian : (flags.endianness == some .big) = false := by simpa using little
  simp only [instData,integer,Bool.not_true,Bool.false_eq_true,ite_false,endian,pure,Except.pure] at encoded
  have fields := data_fields "LoadNoOffset" [opcodeV "AtomicLoad",.value pointer,.op (.memFlags flags)] encoded
  have tail : rest = [.value pointer,.op (.memFlags flags)] := (List.cons.inj fields).2
  exact shape.trans (congrArg (fun xs => V.data 152 17 (.data 151 158 []::xs)) tail)

end Backend.Stock.Proof.Acquire810
