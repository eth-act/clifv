import FV.Backend.Proof.StockAcquireSinkReceipts
import FV.Backend.Proof.StockDFG

namespace Backend.Stock.Proof.AcquireHelpers
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program

private theorem backend_unData_inv {ctx : Ctx} {ty tag : Nat} {value : V} {fields : List V}
    (decoded : (Backend.sem ctx).unData ty value = some (tag,fields)) :
    value = .data ty tag fields := by
  cases value <;> try cases decoded
  rename_i actualTy actualTag actualFields
  change (if actualTy == ty then some (actualTag,actualFields) else none) = some (tag,fields) at decoded
  split at decoded
  · rename_i same
    have typeEq : actualTy = ty := by simpa only [beq_iff_eq] using same
    subst actualTy
    cases Option.some.inj decoded
    rfl
  · cases decoded

/-- The actual helper match identifies its installed atomic opcode, without a caller shape certificate. -/
theorem sink_atomic_match_data {ctx : Ctx} {st matched : State} {before after : Array RuleId}
    {env : Isle.Interp.Env V} {n ii : Nat}
    (run : (matchRule program (Stock.sem ctx) {} (n+1) rule_inst_3905 [.inst ii]).run
      (st,before) = .ok (some env,matched,after)) :
    ∃ info rest,ctx.insts[ii]? = some info ∧ info.data = .data 152 17 (.data 151 158 [] :: rest) := by
  obtain ⟨initial,args,iflets⟩ := matchRule_some_inv run
  simp only [rule_inst_3905] at args
  obtain ⟨env1,head,tail⟩ := matchArgs_cons_inv args
  obtain ⟨_,inner⟩ := matchPat_bind_inv head
  obtain ⟨values,extracted,fields⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl inner
  change Backend.externExtract ctx T.inst_data_value (.inst ii) st.base = .ok values at extracted
  change (match ctx.insts[ii]? with
    | some info => ExtResult.ok [V.ty (info.resTys.head?.getD .invalid),info.data]
    | none => ExtResult.unmodeled s!"inst {ii}") = ExtResult.ok values at extracted
  cases installed : ctx.insts[ii]? with
  | none => rw [installed] at extracted; cases extracted
  | some info =>
    rw [installed] at extracted
    cases extracted
    obtain ⟨env2,_,remaining⟩ := matchArgs_cons_inv fields
    obtain ⟨env3,data,_⟩ := matchArgs_cons_inv remaining
    obtain ⟨items,decoded,arguments⟩ := matchPat_enum_inv data_program.t2464 rfl data
    cases items with
    | nil => cases arguments
    | cons opcode rest =>
      obtain ⟨env4,opMatch,_⟩ := matchArgs_cons_inv arguments
      obtain ⟨opArgs,opDecoded,emptyMatch⟩ := matchPat_enum_inv data_program.t2442 rfl opMatch
      have empty : opArgs = [] := by cases opArgs <;> simp_all [matchArgs]
      subst opArgs
      have outer : info.data = .data 152 17 (opcode :: rest) := backend_unData_inv (ctx := ctx) decoded
      have inner : opcode = .data 151 158 [] := backend_unData_inv (ctx := ctx) opDecoded
      exact ⟨info,rest,rfl,by simpa only [inner] using outer⟩

/-- Original mapped source data turns that actual atomic opcode into the admitted CLIF load. -/
theorem mapped_atomic_producer {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {ii : Nat} {info : IInfo} {original : Clif.Inst} {rest : List V}
    (installed : ctx.insts[ii]? = some info) (source : info.clif = some original)
    (shape : info.data = .data 152 17 (.data 151 158 [] :: rest)) :
    ∃ ty flags pointer,original = .atomicLoad ty flags pointer ∧
      eTy ty = true ∧ flags.endianness ≠ some .big := by
  have encoded := mapped.data ii info original installed source
  rw [shape] at encoded
  have names := instData_names_eq encoded atom_vn_LoadNoOffset atom_vn_AtomicLoad
  cases original <;> simp only [instNames,Prod.mk.injEq] at names
  all_goals try (simp at names; done)
  rename_i ty flags pointer
  simp only [instData] at encoded
  split at encoded
  · cases encoded
  · rename_i integer
    split at encoded
    · cases encoded
    · rename_i endian
      exact ⟨ty,flags,pointer,rfl,by simpa using integer,by simpa using endian⟩

/-- The actual helper call derives the precise atomic data shape internally. -/
theorem sink_atomic_call_data {ctx : Ctx} {st next : State} {before after : Array RuleId}
    {fuel ii : Nat} {out : V} (enough : 10 ≤ fuel)
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 27 564 [.inst ii]
      (st,before) out (next,after)) :
    ∃ info rest,ctx.insts[ii]? = some info ∧ info.data = .data 152 17 (.data 151 158 [] :: rest) := by
  unfold ApplyInternal at run
  obtain ⟨rule,member,matchFuel,env,matched,final,trace,bounded,matchedRun,evaluatedRun,finished⟩ :=
    applyTerm_internal_some (by rfl) data_program.t564 term_564_kind rfl run
  have same : rule = rule_inst_3905 := by simpa only [data_program.r564,List.mem_singleton] using member
  subst rule
  have enoughMatch : 0 < matchFuel := by
    rw [data_program.r564] at bounded
    simp only [List.length_cons,List.length_nil] at bounded
    omega
  obtain ⟨m,matchEq⟩ : ∃ m,matchFuel = m+1 := ⟨matchFuel-1,by omega⟩
  rw [matchEq] at matchedRun
  exact sink_atomic_match_data matchedRun

end Backend.Stock.Proof.AcquireHelpers
