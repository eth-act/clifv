import FV.Backend.Proof.StockCastBaseValues
import FV.Backend.Proof.StockRootOpcodeMatch
import FV.Backend.Proof.StockSourceStatementFamily
import FV.Backend.Proof.StockCastFamily
import FV.Backend.Proof.IselCtlUnmatch
namespace Backend.Stock.Proof.CastComplete
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Current source closure includes the base casts and five look-through roots (S11f added
`uextend (fcmp …)`, rule 812); none is silently omitted from the class dispatcher. -/
theorem opcode_inventory : sourceOpcodeIds 141 = [810,811,812,815,808] ∧
    sourceOpcodeIds 142 = [824,819] ∧ sourceOpcodeIds 131 = [946] := by
  unfold sourceOpcodeIds
  rw [show TId.lower = 686 from rfl,data_program.r686]
  decide +kernel

private theorem source_format {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} {inst : Clif.Inst} {k : Nat} {fs : List V}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some inst)
    (data : info.data = .data 152 k fs) : (variantNames 152)[k]? = some (instNames inst).1 := by
  have raw := inv.data i info inst source clif
  rw [data] at raw
  rcases instData_names raw with ⟨rest,normal⟩ | ⟨ty,imm,rfl,float,rest,shapes⟩
  · exact (mkVariant_eq_data normal.symm).1
  · have supported := inv.instE i info _ source clif
    cases ty <;> simp_all [Compile.instE,Compile.tyE,Clif.Ty.isFloat,Clif.Ty.isInt]

private theorem direct_format {p : Program} (hp : Data p) (ctx : Ctx) {q : Pattern}
    {fT : Nat} (format : fmtD q = some fT) {tf : Term} {k : Nat}
    (term : termOf p fT = .ok tf) (kind : tf.kind = .enumVariant k)
    {x : Nat} {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchPat p (Backend.sem ctx) st (.term 15 1 [q]) (.value x) env = .ok (some env')) :
    ∃ j info fs, ctx.defInst? x = some j ∧ ctx.insts[j]? = some info ∧ info.data = .data 152 k fs := by
  obtain ⟨fields,extracted,args⟩ := matchPat_extract_inv hp.t1 term_1_kind rfl matched
  rw [Backend.Proof.sem_extract] at extracted
  obtain ⟨j,defined,rfl⟩ := (ext_def_inst_iff ctx st _ _).mp extracted
  obtain ⟨e,pattern,_⟩ := matchArgs_cons_inv args
  obtain ⟨info,fs,found,data⟩ := fmtD_match_k hp format term kind pattern
  exact ⟨j,info,fs,defined,found,data⟩

private inductive Look where
  | direct | bound (slot : Nat) | typed (slot : Nat) (typePattern : Pattern)
private def lookPattern (look : Look) (q : Pattern) : Pattern :=
  match look with
  | .direct => .term 15 1 [q]
  | .bound slot => .bind 15 slot (.term 15 1 [q])
  | .typed slot typePattern => .bind 15 slot (.and 15 [typePattern,.term 15 1 [q]])
private theorem look_format {p : Program} (hp : Data p) (ctx : Ctx) (look : Look) {q : Pattern}
    {fT : Nat} (format : fmtD q = some fT) {tf : Term} {k : Nat}
    (term : termOf p fT = .ok tf) (kind : tf.kind = .enumVariant k)
    {x : Nat} {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchPat p (Backend.sem ctx) st (lookPattern look q) (.value x) env = .ok (some env')) :
    ∃ j info fs, ctx.defInst? x = some j ∧ ctx.insts[j]? = some info ∧ info.data = .data 152 k fs := by
  cases look with
  | direct => exact direct_format hp ctx format term kind matched
  | bound slot => exact direct_format hp ctx format term kind (matchPat_bind_inv matched).2
  | typed slot typePattern =>
    have both := matchPat_and_inv (matchPat_bind_inv matched).2
    obtain ⟨e,_,rest⟩ := matchAll_cons_inv both
    obtain ⟨e',pattern,_⟩ := matchAll_cons_inv rest
    exact direct_format hp ctx format term kind pattern

private theorem unary_operand {p : Program} (hp : Data p) (ctx : Ctx)
    {i x code opTerm : Nat} {info : IInfo} {tyPat child : Pattern}
    {st : LState} {env env' : Isle.Interp.Env V}
    (source : ctx.insts[i]? = some info)
    (data : info.data = .data 152 29 [.data 151 code [],.value x])
    (matched : matchPat p (Backend.sem ctx) st
      (.term 18 209 [tyPat,.term 152 2476 [.term 151 opTerm [],child]])
      (.inst i) env = .ok (some env')) :
    ∃ e,matchPat p (Backend.sem ctx) st child (.value x) e = .ok (some env') := by
  obtain ⟨fs,extracted,args⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl matched
  rw [Backend.Proof.sem_extract,ext_inst_data_value ctx st source] at extracted
  cases extracted
  obtain ⟨e0,_,args⟩ := matchArgs_cons_inv args
  obtain ⟨e1,unary,ending⟩ := matchArgs_cons_inv args
  have same := matchArgs_nil_nil ctx ending
  subst same
  obtain ⟨fields,decoded,args⟩ := matchPat_enum_inv hp.t2476 term_2476_kind unary
  rw [data,Backend.Proof.sem_unData] at decoded
  simp only [ite_true,Option.some.injEq,Prod.mk.injEq] at decoded
  obtain ⟨_,rfl⟩ := decoded
  obtain ⟨e2,_,args⟩ := matchArgs_cons_inv args
  obtain ⟨e3,pattern,ending⟩ := matchArgs_cons_inv args
  have same := matchArgs_nil_nil ctx ending
  subst same
  exact ⟨e2,pattern⟩

private theorem excludes_format {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (bad : String)
    (safe : ∀ (j : Nat) (info : IInfo) (cl : Clif.Inst),ctx.insts[j]? = some info → info.clif = some cl → (instNames cl).1 ≠ bad)
    {r : Rule} {tyPat q : Pattern} {opTerm : Nat} (look : Look)
    (args : r.args = [.term 18 209 [tyPat,.term 152 2476 [.term 151 opTerm [],lookPattern look q]]])
    {fT : Nat} (format : fmtD q = some fT) {tf : Term} {k : Nat}
    (term : termOf p fT = .ok tf) (kind : tf.kind = .enumVariant k)
    (name : (variantNames 152)[k]? = some bad)
    {i x code fuel : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (data : info.data = .data 152 29 [.data 151 code [],.value x])
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} fuel r [.inst i]).run (st,tr) = .ok (some env,middle)) : False := by
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨bound,patterns,_⟩ := matchRule_some_inv matched
    rw [args] at patterns
    obtain ⟨e,pattern,_⟩ := matchArgs_cons_inv patterns
    rw [stock_matchPat] at pattern
    obtain ⟨e',child⟩ := unary_operand hp ctx source data pattern
    obtain ⟨j,definition,fields,defined,found,raw⟩ := look_format hp ctx look format term kind child
    obtain ⟨cl,original⟩ := Option.isSome_iff_exists.mp (inv.defClif x j definition defined found)
    have actual := source_format inv found original raw
    have equal := Option.some.inj (actual.symm.trans name)
    exact safe j definition cl found original equal

/-- `excludes_format` at the level of argument patterns under the baseline embedding. -/
private theorem excludes_format_args {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (bad : String)
    (safe : ∀ (j : Nat) (info : IInfo) (cl : Clif.Inst),ctx.insts[j]? = some info → info.clif = some cl → (instNames cl).1 ≠ bad)
    {r : Rule} {tyPat q : Pattern} {opTerm : Nat} (look : Look)
    (args : r.args = [.term 18 209 [tyPat,.term 152 2476 [.term 151 opTerm [],lookPattern look q]]])
    {fT : Nat} (format : fmtD q = some fT) {tf : Term} {k : Nat}
    (term : termOf p fT = .ok tf) (kind : tf.kind = .enumVariant k)
    (name : (variantNames 152)[k]? = some bad)
    {i x code : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (data : info.data = .data 152 29 [.data 151 code [],.value x])
    {st : LState} {env0 env : Isle.Interp.Env V}
    (patterns : matchArgs p (Backend.sem ctx) st r.args [.inst i] env0 = .ok (some env)) : False := by
  rw [args] at patterns
  obtain ⟨e,pattern,_⟩ := matchArgs_cons_inv patterns
  obtain ⟨e',child⟩ := unary_operand hp ctx source data pattern
  obtain ⟨j,definition,fields,defined,found,raw⟩ := look_format hp ctx look format term kind child
  obtain ⟨cl,original⟩ := Option.isSome_iff_exists.mp (inv.defClif x j definition defined found)
  have actual := source_format inv found original raw
  have equal := Option.some.inj (actual.symm.trans name)
  exact safe j definition cl found original equal

section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem extend_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (sg : Bool) {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.extend (ScalarCast.extendOp sg) ty x)) :
    info.data = .data 152 29 [.data 151 (ScalarCast.extendOpcode sg) [],.value x] := by
  have supported : eTy ty = true := by
    simpa [ScalarCast.extendOp,Compile.instE,Compile.tyE,eTy] using inv.instE i info _ source clif
  have shape : instData f (.extend (ScalarCast.extendOp sg) ty x) =
      .ok (.data 152 29 [.data 151 (ScalarCast.extendOpcode sg) [],.value x]) := by
    cases sg <;> simp only [ScalarCast.extendOp,ScalarCast.extendOpcode,instData,supported,ite_true] <;> rfl
  exact Except.ok.inj ((inv.data i info _ source clif).symm.trans shape)
private theorem reduce_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.ireduce ty x)) :
    info.data = .data 152 29 [.data 151 131 [],.value x] := by
  have supported : eTy ty = true := by
    simpa [Compile.instE,Compile.tyE,eTy] using inv.instE i info _ source clif
  have shape : instData f (.ireduce ty x) = .ok (.data 152 29 [.data 151 131 [],.value x]) := by
    simp only [instData,supported,ite_true]; rfl
  exact Except.ok.inj ((inv.data i info _ source clif).symm.trans shape)
end Data

/-- In a context without `Load`/`LoadNoOffset` statements, the u/sextend-of-load look-through
roots (1272, 1300, 1359) cannot match an extend statement's arguments under the baseline
embedding. -/
theorem stock_extend_load_args_fail {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (noLoad : ∀ (j : Nat) (info : IInfo) (cl : Clif.Inst), ctx.insts[j]? = some info → info.clif = some cl →
      (instNames cl).1 ≠ "LoadNoOffset" ∧ (instNames cl).1 ≠ "Load")
    (sg : Bool) {i x : Nat} {info : IInfo} {ty : Clif.Ty} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.extend (ScalarCast.extendOp sg) ty x))
    {r : Rule} (hr : r = rule_lower_1272 ∨ r = rule_lower_1300 ∨ r = rule_lower_1359)
    (st : LState) (env : Isle.Interp.Env V) :
    matchArgs program (Backend.sem ctx) st r.args [.inst i] (Array.replicate r.vars.length none) ≠
      .ok (some env) := by
  have data := extend_data inv sg source clif
  intro patterns
  rcases hr with rfl | rfl | rfl
  · exact excludes_format_args data_program inv "LoadNoOffset"
      (fun j info cl found original => (noLoad j info cl found original).1)
      (.typed 3 (.term 15 2 [.bind 14 1 (.wildcard 14)])) rfl rfl data_program.t2464 term_2464_kind
      (by decide +kernel) source data patterns
  · exact excludes_format_args data_program inv "Load"
      (fun j info cl found original => (noLoad j info cl found original).2)
      (.bound 4) rfl rfl data_program.t2463 term_2463_kind (by decide +kernel) source data patterns
  · exact excludes_format_args data_program inv "Load"
      (fun j info cl found original => (noLoad j info cl found original).2)
      (.bound 4) rfl rfl data_program.t2463 term_2463_kind (by decide +kernel) source data patterns

/-- The `uextend (fcmp …)` look-through root (S11f) never fires on a subset-E source: `fcmp`
is a float instruction, outside `Compile.instE`. -/
private theorem floatCompare_not_E {cl : Clif.Inst} (h : Compile.instE cl = true) :
    (instNames cl).1 ≠ "FloatCompare" := by
  intro hn
  cases cl <;> first | (simp [Compile.instE] at h; done) | (simp [instNames] at hn)

/-- Actual class syntax excludes the effectful/comparison look-through roots;
original matched sources select the base cast internally. Old broader selected
variants remain available for subsequent family expansion. -/
theorem stock_lower_cast_selected_rule_of_formats {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastBody.SafeFormat stm.inst)
    (sg : Bool) {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : event.ctx.insts[i]? = some info) (clif : info.clif = some (.extend (ScalarCast.extendOp sg) ty x))
    {st next : State} {out : V} {trace : List RuleId} (selected : LowerSelection event.ctx i st out next trace) :
    selected.rule = ScalarCast.extendRule sg := by
  have inv := (stock_lower_record_context run scope events).1
  have safe : ∀ (j : Nat) (info : IInfo) (cl : Clif.Inst),event.ctx.insts[j]? = some info →
      info.clif = some cl → CastBody.SafeFormat cl := by
    intro j info cl found original
    exact stock_lower_source_statement_family run scope events CastBody.SafeFormat
      family found original
  have data := extend_data inv sg source clif
  have ids := stock_selected_source_opcode_ids inv source clif data selected
  cases sg with
  | false =>
    change selected.rule.id ∈ sourceOpcodeIds 141 at ids
    rw [opcode_inventory.1] at ids
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ids
    rcases ids with atomic | comparison | fcompare | load | base
    · have chosen : selected.rule = rule_lower_1272 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
        (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) atomic
      have matched := selected.matchedRun
      rw [chosen] at matched
      exact (excludes_format data_program inv "LoadNoOffset"
        (fun j info cl found original => (safe j info cl found original).1)
        (.typed 3 (.term 15 2 [.bind 14 1 (.wildcard 14)])) rfl rfl data_program.t2464 term_2464_kind (by decide +kernel) source data matched).elim
    · have chosen : selected.rule = rule_lower_1281 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
        (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) comparison
      have matched := selected.matchedRun
      rw [chosen] at matched
      exact (excludes_format data_program inv "IntCompare"
        (fun j info cl found original => (safe j info cl found original).2.2)
        .direct rfl rfl data_program.t2461 term_2461_kind (by decide +kernel) source data matched).elim
    · have chosen : selected.rule = rule_lower_1283 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
        (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) fcompare
      have matched := selected.matchedRun
      rw [chosen] at matched
      exact (excludes_format data_program inv "FloatCompare"
        (fun j info cl found original => floatCompare_not_E (inv.instE j info cl found original))
        .direct rfl rfl data_program.t2458 term_2458_kind (by decide +kernel) source data matched).elim
    · have chosen : selected.rule = rule_lower_1300 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
        (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) load
      have matched := selected.matchedRun
      rw [chosen] at matched
      exact (excludes_format data_program inv "Load"
        (fun j info cl found original => (safe j info cl found original).2.1)
        (.bound 4) rfl rfl data_program.t2463 term_2463_kind (by decide +kernel) source data matched).elim
    · exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem
        (by rw [ScalarCast.extendRule,show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) base
  | true =>
    change selected.rule.id ∈ sourceOpcodeIds 142 at ids
    rw [opcode_inventory.2.1] at ids
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ids
    rcases ids with load | base
    · have chosen : selected.rule = rule_lower_1359 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
        (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) load
      have matched := selected.matchedRun
      rw [chosen] at matched
      exact (excludes_format data_program inv "Load"
        (fun j info cl found original => (safe j info cl found original).2.1)
        (.bound 4) rfl rfl data_program.t2463 term_2463_kind (by decide +kernel) source data matched).elim
    · exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem
        (by rw [ScalarCast.extendRule,show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) base

/-- Memory-only format exclusion permits the original comparison look-through.
The older SafeFormat and its theorem remain unchanged. -/
def MemoryFormat (inst : Clif.Inst) : Prop :=
  (instNames inst).1 ≠ "LoadNoOffset" ∧ (instNames inst).1 ≠ "Load"

/-- Actual source dispatch retains the fused comparison root instead of
excluding original IntCompare syntax. Effectful look-through remains separate. -/
theorem stock_lower_cast_selected_rule_of_memory_formats {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MemoryFormat stm.inst)
    (sg : Bool) {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : event.ctx.insts[i]? = some info) (clif : info.clif = some (.extend (ScalarCast.extendOp sg) ty x))
    {st next : State} {out : V} {trace : List RuleId} (selected : LowerSelection event.ctx i st out next trace) :
    selected.rule = ScalarCast.extendRule sg ∨ sg = false ∧ selected.rule = rule_lower_1281 := by
  have inv := (stock_lower_record_context run scope events).1
  have safe : ∀ (j : Nat) (info : IInfo) (cl : Clif.Inst),event.ctx.insts[j]? = some info →
      info.clif = some cl → MemoryFormat cl := by
    intro j info cl found original
    exact stock_lower_source_statement_family run scope events MemoryFormat
      family found original
  have data := extend_data inv sg source clif
  have ids := stock_selected_source_opcode_ids inv source clif data selected
  cases sg with
  | false =>
    change selected.rule.id ∈ sourceOpcodeIds 141 at ids
    rw [opcode_inventory.1] at ids
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ids
    rcases ids with atomic | comparison | fcompare | load | base
    · have chosen : selected.rule = rule_lower_1272 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
        (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) atomic
      have matched := selected.matchedRun
      rw [chosen] at matched
      exact (excludes_format data_program inv "LoadNoOffset"
        (fun j info cl found original => (safe j info cl found original).1)
        (.typed 3 (.term 15 2 [.bind 14 1 (.wildcard 14)])) rfl rfl data_program.t2464 term_2464_kind (by decide +kernel) source data matched).elim
    · exact Or.inr ⟨rfl,eq_of_mem_of_id lower_ids_nodup selected.rule_mem
        (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) comparison⟩
    · have chosen : selected.rule = rule_lower_1283 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
        (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) fcompare
      have matched := selected.matchedRun
      rw [chosen] at matched
      exact (excludes_format data_program inv "FloatCompare"
        (fun j info cl found original => floatCompare_not_E (inv.instE j info cl found original))
        .direct rfl rfl data_program.t2458 term_2458_kind (by decide +kernel) source data matched).elim
    · have chosen : selected.rule = rule_lower_1300 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
        (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) load
      have matched := selected.matchedRun
      rw [chosen] at matched
      exact (excludes_format data_program inv "Load"
        (fun j info cl found original => (safe j info cl found original).2)
        (.bound 4) rfl rfl data_program.t2463 term_2463_kind (by decide +kernel) source data matched).elim
    · apply Or.inl
      exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem
        (by rw [ScalarCast.extendRule,show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) base
  | true =>
    change selected.rule.id ∈ sourceOpcodeIds 142 at ids
    rw [opcode_inventory.2.1] at ids
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ids
    rcases ids with load | base
    · have chosen : selected.rule = rule_lower_1359 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
        (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) load
      have matched := selected.matchedRun
      rw [chosen] at matched
      exact (excludes_format data_program inv "Load"
        (fun j info cl found original => (safe j info cl found original).2)
        (.bound 4) rfl rfl data_program.t2463 term_2463_kind (by decide +kernel) source data matched).elim
    · apply Or.inl
      exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem
        (by rw [ScalarCast.extendRule,show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) base

/-- Original reduction selection has one reachable source root, without a
fresh-result or selected-root input premise. -/

theorem stock_lower_cast_selected_rule {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastBody.Family stm.inst)
    (sg : Bool) {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : event.ctx.insts[i]? = some info) (clif : info.clif = some (.extend (ScalarCast.extendOp sg) ty x))
    {st next : State} {out : V} {trace : List RuleId} (selected : LowerSelection event.ctx i st out next trace) :
    selected.rule = ScalarCast.extendRule sg := by
  exact stock_lower_cast_selected_rule_of_formats run scope events (fun b block stm statement => CastBody.family_formats (family b block stm statement)) sg source clif selected

theorem stock_reduce_selected_rule {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.ireduce ty x))
    {st next : State} {out : V} {trace : List RuleId} (selected : LowerSelection ctx i st out next trace) :
    selected.rule = rule_lower_2146 := by
  have ids := stock_selected_source_opcode_ids inv source clif (reduce_data inv source clif) selected
  rw [opcode_inventory.2.2,List.mem_singleton] at ids
  exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem
    (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) ids
end Backend.Stock.Proof.CastComplete
