import FV.Backend.Proof.IselFamALUA
import FV.Backend.Proof.StockSourceView
import FV.Backend.Proof.IselCovForm
import FV.Backend.Proof.StockLogicalExtrRhs

namespace Backend.Stock.Proof.LogicalExtr
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private def literalPattern (slot : Nat) : Pattern :=
  .term 15 1 [.term 18 209 [.wildcard 14,.term 152 2482
    [.term 151 2341 [],.term 134 144 [.term 4 1527 [.bind 1 slot (.wildcard 1)]]]]]
private def wordPattern (left : Bool) (wordSlot countSlot : Nat) : Pattern :=
  .term 15 1 [.term 18 209 [.wildcard 14,.term 152 2449
    [.term 151 (if left then 2387 else 2388) [],.term 147 1614
      [.bind 15 wordSlot (.wildcard 15),literalPattern countSlot]]]]

/-- Both original source definitions are retained, including the shift count's
own typed literal definition. These are not caller-supplied lookthrough facts. -/
def WordSource (ctx : Ctx) (value : Nat) (left : Bool) : Prop :=
  ∃ (j x count k : Nat) (info literal : IInfo) (ty literalTy : Clif.Ty) (bits : BitVec literalTy.width),
    ctx.defInst? value = some j ∧ ctx.insts[j]? = some info ∧
    info.clif = some (.binary (if left then .ishl else .ushr) ty x count) ∧
    ctx.defInst? count = some k ∧ ctx.insts[k]? = some literal ∧
    literal.clif = some (.iconst literalTy bits)

private theorem word_source {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (left : Bool) {v wordSlot countSlot : Nat}
    {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchPat p (Backend.sem ctx) st (wordPattern left wordSlot countSlot)
      (.value v) env = .ok (some env')) : WordSource ctx v left := by
  have opTerm : termOf p (if left then 2387 else 2388) =
      .ok (if left then T.«Opcode.Ishl» else T.«Opcode.Ushr») := by
    cases left <;> first | exact hp.t2387 | exact hp.t2388
  have opKind : (if left then T.«Opcode.Ishl» else T.«Opcode.Ushr»).kind =
      .enumVariant (if left then 103 else 104) := by cases left <;> rfl
  obtain ⟨j,info,fs,env0,defined,found,data,rest⟩ :=
    defInst_match_inv hp ctx hp.t2449 term_2449_kind opTerm opKind matched
  obtain ⟨original,clif,raw⟩ := ctxInv_clif inv.identityView defined found
  rw [data] at raw
  have name : (variantNames 151)[if left then 103 else 104]? =
      some (if left then "Ishl" else "Ushr") := by
    cases left <;> decide +kernel
  have opcode : binaryOpcode (if left then .ishl else .ushr) =
      some (if left then "Ishl" else "Ushr") := by cases left <;> rfl
  obtain ⟨ty,x,count,rfl,_,rfl⟩ := instData_binary_inv name opcode raw
  obtain ⟨env1,_,constant⟩ := values2_match_inv hp ctx rest
  obtain ⟨k,literal,fields,env2,countDefined,countFound,literalData,_⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind constant
  obtain ⟨sourceLiteral,literalClif,literalRaw⟩ := ctxInv_clif inv.identityView countDefined countFound
  rw [literalData] at literalRaw
  obtain ⟨literalTy,bits,rfl,rfl⟩ := instData_iconst_inv literalRaw
  exact ⟨j,x,count,k,info,literal,ty,literalTy,bits,defined,found,clif,countDefined,countFound,literalClif⟩

/-- Actual successful Stock matches follow both original operands through their
shift and literal definitions, including the mirrored OR route. -/
theorem matched_sources {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (mirrored : Bool) {i a b n : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (data : info.data = .data 152 2 [.data 151 98 [],.values [a,b]])
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+20) (extrRule mirrored) [.inst i]).run (st,tr) =
      .ok (some env,middle)) : WordSource ctx a (!mirrored) ∧ WordSource ctx b mirrored := by
  have shape : (extrRule mirrored).args = [.term 18 209
    [.term 14 120 [.bind 14 0 (.wildcard 14)],.term 152 2449
      [.term 151 2382 [],.term 147 1614 [wordPattern (!mirrored) 1 2,wordPattern mirrored 3 4]]]] := by
    cases mirrored <;> rfl
  obtain ⟨initial,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs,shape] at args
  obtain ⟨e1,root,_⟩ := matchArgs_cons_inv args
  obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl root
  rw [Backend.Proof.sem_extract,ext_inst_data_value ctx st.base source,data] at extracted
  cases extracted
  obtain ⟨e2,_,tail⟩ := matchArgs_cons_inv patterns
  obtain ⟨e3,binary,_⟩ := matchArgs_cons_inv tail
  obtain ⟨fs,decoded,matchedFields⟩ := matchPat_enum_inv hp.t2449 term_2449_kind binary
  have decode : (Backend.sem ctx).unData 152 (.data 152 2 [.data 151 98 [],.values [a,b]]) =
      some (2,[.data 151 98 [],.values [a,b]]) := rfl
  rw [decode] at decoded
  cases decoded
  obtain ⟨e4,_,values⟩ := matchArgs_cons_inv matchedFields
  obtain ⟨e5,first,second⟩ := values2_match_inv hp ctx values
  exact ⟨word_source hp inv (!mirrored) first,word_source hp inv mirrored second⟩
end Backend.Stock.Proof.LogicalExtr
