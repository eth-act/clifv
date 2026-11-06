import FV.Backend.Proof.StockMemorySinkExtRoot
import FV.Backend.Proof.StockCastDispatch

/-! First-match selection of the sinking extension roots. An extension of an
eligible plain-load result selects rule 815 (`uextend_load`) or 824
(`sextend_load`): the higher-priority look-through roots see a `Load` definition
and fail, and the sinking root precedes the base extension in rule order. -/
namespace Backend.Stock.Memory.SinkExtend
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Memory.ExtendedRoots (Kind)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Integer result types that `fits_in_64` accepts. -/
def narrow : Clif.Ty → Bool
  | .i8 | .i16 | .i32 | .i64 => true
  | _ => false

section SourceData
attribute [local semireducible] Isle.Aarch64.program

/-- Original extension syntax supplies the consumer's encoded data and result width. -/
theorem extend_source_data (kind : Kind) {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i y : Nat} {info : IInfo} {ty : Clif.Ty} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.extend (extendOp kind) ty y)) (small : narrow ty = true) :
    info.data = .data 152 29 [.data 151 (extendTag kind) [],.value y] ∧
      ∃ w,info.resTys.head? = some (.int w) ∧ w ≤ 64 := by
  have supported : eTy ty = true := by
    simpa [extendOp,ScalarCast.extendOp,Compile.instE,Compile.tyE,eTy] using inv.instE i info _ source clif
  have shape : instData f (.extend (extendOp kind) ty y) =
      .ok (.data 152 29 [.data 151 (extendTag kind) [],.value y]) := by
    cases kind <;> simp only [extendOp,extendTag,signed,ScalarCast.extendOp,ScalarCast.extendOpcode,
      instData,supported,ite_true] <;> rfl
  obtain ⟨types,typed,resTys,_⟩ := inv.resTys i info _ source clif
  change some [ty] = some types at typed
  cases typed
  refine ⟨Except.ok.inj ((inv.data i info _ source clif).symm.trans shape),?_⟩
  rw [resTys]
  cases ty <;> simp [narrow] at small <;> exact ⟨_,rfl,by decide⟩

/-- Original plain-load syntax supplies the load's encoded data, type and endianness. -/
theorem load_source_data (kind : Kind) {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {j x : Nat} {load : IInfo} {flags : Clif.MemFlags} (loaded : ctx.insts[j]? = some load)
    (clif : load.clif = some (.load .load (loadTy kind) flags x 0)) :
    flags.endianness ≠ some .big ∧
      load.data = .data 152 16 [.data 151 29 [],.value x,.op (.memFlags flags),.int 0] ∧
      load.resTys.head? = some (.int (loadTy kind).width) := by
  have data := inv.data j load _ loaded clif
  have little : flags.endianness ≠ some .big := by
    intro big
    cases kind <;> simp [instData,eTy,loadTy,big] at data
  have shape : instData f (.load .load (loadTy kind) flags x 0) =
      .ok (.data 152 16 [.data 151 29 [],.value x,.op (.memFlags flags),.int 0]) := by
    have small : (flags.endianness == some .big) = false := by simpa using little
    cases kind <;> simp only [instData,loadTy,eTy,small] <;> rfl
  obtain ⟨types,typed,resTys,_⟩ := inv.resTys j load _ loaded clif
  change some [loadTy kind] = some types at typed
  cases typed
  refine ⟨little,Except.ok.inj (data.symm.trans shape),?_⟩
  rw [resTys]
  cases kind <;> rfl

end SourceData

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

private theorem direct_format {p : Program} (hp : Data p) (ctx : Ctx) {q : Pattern}
    {fT : Nat} (format : fmtD q = some fT) {tf : Term} {k : Nat}
    (term : termOf p fT = .ok tf) (kind : tf.kind = .enumVariant k)
    {x : Nat} {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchPat p (Backend.sem ctx) st (.term 15 1 [q]) (.value x) env = .ok (some env')) :
    ∃ j info fs,ctx.defInst? x = some j ∧ ctx.insts[j]? = some info ∧ info.data = .data 152 k fs := by
  obtain ⟨fields,extracted,args⟩ := matchPat_extract_inv hp.t1 term_1_kind rfl matched
  rw [Backend.Proof.sem_extract] at extracted
  obtain ⟨j,defined,rfl⟩ := (ext_def_inst_iff ctx st _ _).mp extracted
  obtain ⟨e,pattern,_⟩ := matchArgs_cons_inv args
  obtain ⟨info,fs,found,data⟩ := fmtD_match_k hp format term kind pattern
  exact ⟨j,info,fs,defined,found,data⟩

private inductive Look where
  | direct | typed (slot : Nat) (typePattern : Pattern)

private def lookPattern (look : Look) (q : Pattern) : Pattern :=
  match look with
  | .direct => .term 15 1 [q]
  | .typed slot typePattern => .bind 15 slot (.and 15 [typePattern,.term 15 1 [q]])

private theorem look_format {p : Program} (hp : Data p) (ctx : Ctx) (look : Look) {q : Pattern}
    {fT : Nat} (format : fmtD q = some fT) {tf : Term} {k : Nat}
    (term : termOf p fT = .ok tf) (kind : tf.kind = .enumVariant k)
    {x : Nat} {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchPat p (Backend.sem ctx) st (lookPattern look q) (.value x) env = .ok (some env')) :
    ∃ j info fs,ctx.defInst? x = some j ∧ ctx.insts[j]? = some info ∧ info.data = .data 152 k fs := by
  cases look with
  | direct => exact direct_format hp ctx format term kind matched
  | typed slot typePattern =>
    have both := matchPat_and_inv (matchPat_bind_inv matched).2
    obtain ⟨e,_,rest⟩ := matchAll_cons_inv both
    obtain ⟨e',pattern,_⟩ := matchAll_cons_inv rest
    exact direct_format hp ctx format term kind pattern

/-- A look-through root that needs another instruction format cannot match an
extension whose operand is defined by a `Load`. -/
private theorem excludes_load_operand {p : Program} (hp : Data p) {ctx : Ctx}
    {r : Rule} {tyPat q : Pattern} {opTerm : Nat} (look : Look)
    (args : r.args = [.term 18 209 [tyPat,.term 152 2476 [.term 151 opTerm [],lookPattern look q]]])
    {fT : Nat} (format : fmtD q = some fT) {tf : Term} {k : Nat}
    (term : termOf p fT = .ok tf) (kind : tf.kind = .enumVariant k) (other : k ≠ 16)
    {i y j code fuel : Nat} {info load : IInfo} {fs : List V}
    (source : ctx.insts[i]? = some info) (data : info.data = .data 152 29 [.data 151 code [],.value y])
    (defined : ctx.defInst? y = some j) (loaded : ctx.insts[j]? = some load)
    (loadData : load.data = .data 152 16 fs)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} fuel r [.inst i]).run (st,tr) = .ok (some env,middle)) :
    False := by
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨bound,patterns,_⟩ := matchRule_some_inv matched
    rw [args] at patterns
    obtain ⟨e,pattern,_⟩ := matchArgs_cons_inv patterns
    rw [stock_matchPat] at pattern
    obtain ⟨e',child⟩ := unary_operand hp ctx source data pattern
    obtain ⟨j',definition,fields,defined',found,raw⟩ := look_format hp ctx look format term kind child
    rw [defined] at defined'
    cases defined'
    rw [loaded] at found
    cases found
    rw [loadData] at raw
    cases raw
    exact other rfl

/-- In a rule list without duplicate ids, a rule at an earlier index than the
selected rule belongs to the rejected prefix. -/
theorem mem_pre_of_index {L pre post : List Rule} {r a : Rule}
    (nodup : (L.map Rule.id).Nodup) (split : L = pre ++ r :: post) {i j : Nat}
    (selected : L[i]? = some r) (earlier : L[j]? = some a) (lt : j < i) : a ∈ pre := by
  have distinct : L.Nodup :=
    List.Pairwise.of_map Rule.id (fun a b different same => different (same ▸ rfl)) nodup
  have at_length : L[pre.length]? = some r := by
    rw [split]
    simp
  have inside : i < L.length := (List.getElem?_eq_some_iff.mp selected).1
  have same : i = pre.length :=
    distinct.eq_of_getElem?_eq inside (selected.trans at_length.symm)
  subst same
  rw [split,List.getElem?_append_left lt] at earlier
  exact List.mem_of_getElem? earlier

private theorem lower_count : (program.rulesOf T.lower.id).length = 517 := by
  rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl

/-- An extension of an eligible plain-load result selects the sinking root.
The original source data, the load definition and Stock's eligibility of the
operand determine the selected rule; no selected-rule premise is used. -/
theorem stock_selected_sink_extend_rule (kind : Kind) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i j x y : Nat} {ty : Clif.Ty} {info load : IInfo}
    {flags : Clif.MemFlags} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.extend (extendOp kind) ty y)) (small : narrow ty = true)
    (defined : ctx.defInst? y = some j) (loaded : ctx.insts[j]? = some load)
    (loadClif : load.clif = some (.load .load (loadTy kind) flags x 0))
    {st next : State} {out : V} {trace : List RuleId}
    (eligible : Stock.source ctx st y = some (j,true))
    (selected : LowerSelection ctx i st out next trace) : selected.rule = root kind := by
  obtain ⟨data,w,type,fits⟩ := extend_source_data kind inv source clif small
  obtain ⟨little,loadData,loadType⟩ := load_source_data kind inv loaded loadClif
  have ids := stock_selected_source_opcode_ids inv source clif data selected
  -- The base extension follows the sinking root, so the latter must have been rejected.
  have notBase : ∀ base : Rule,base ∈ program.rulesOf T.lower.id →
      ∀ b a : Nat,(program.rulesOf T.lower.id)[b]? = some base →
        (program.rulesOf T.lower.id)[a]? = some (root kind) → a < b → selected.rule ≠ base := by
    intro base _ b a atBase atRoot lt chosen
    have order := selected.candidates
    rw [chosen] at order
    have earlier := mem_pre_of_index lower_ids_nodup order (chosen ▸ atBase) atRoot lt
    obtain ⟨fuel,bound,after,failed⟩ := selected.rejected _ earlier
    have enough := bound
    rw [lower_count] at enough
    obtain ⟨n,rfl⟩ : ∃ n,fuel = n+5 := ⟨fuel-5,by omega⟩
    rw [stock_match_sink_extend data_program kind ctx source type fits data defined loaded loadType
      loadData little st eligible #[] n] at failed
    cases failed
  have rootMem : root kind ∈ program.rulesOf T.lower.id := by
    cases kind <;> rw [root,show T.lower.id = 686 from rfl,data_program.r686] <;> decide +kernel
  cases kind
  all_goals
    simp only [extendTag,signed,ScalarCast.extendOpcode,root,ite_true,ite_false,
      Bool.false_eq_true] at ids rootMem notBase ⊢
  all_goals first
    | (change selected.rule.id ∈ sourceOpcodeIds 141 at ids
       rw [CastComplete.opcode_inventory.1] at ids
       simp only [List.mem_cons,List.not_mem_nil,or_false] at ids
       rcases ids with atomic | comparison | fcompare | load | base
       · have chosen : selected.rule = rule_lower_1272 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
           (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) atomic
         have matched := selected.matchedRun
         rw [chosen] at matched
         exact (excludes_load_operand data_program (.typed 3 (.term 15 2 [.bind 14 1 (.wildcard 14)]))
           rfl rfl data_program.t2464 term_2464_kind (by decide) source data defined loaded loadData matched).elim
       · have chosen : selected.rule = rule_lower_1281 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
           (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) comparison
         have matched := selected.matchedRun
         rw [chosen] at matched
         exact (excludes_load_operand data_program .direct rfl rfl data_program.t2461 term_2461_kind
           (by decide) source data defined loaded loadData matched).elim
       · have chosen : selected.rule = rule_lower_1283 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
           (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) fcompare
         have matched := selected.matchedRun
         rw [chosen] at matched
         exact (excludes_load_operand data_program .direct rfl rfl data_program.t2458 term_2458_kind
           (by decide) source data defined loaded loadData matched).elim
       · exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem rootMem load
       · have chosen : selected.rule = rule_lower_1261 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
           (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) base
         exact (notBase rule_lower_1261 (by rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel)
           459 259 (by rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl)
           (by rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl) (by decide) chosen).elim)
    | (change selected.rule.id ∈ sourceOpcodeIds 142 at ids
       rw [CastComplete.opcode_inventory.2.1] at ids
       simp only [List.mem_cons,List.not_mem_nil,or_false] at ids
       rcases ids with load | base
       · exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem rootMem load
       · have chosen : selected.rule = rule_lower_1315 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
           (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) base
         exact (notBase rule_lower_1315 (by rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel)
           500 261 (by rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl)
           (by rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl) (by decide) chosen).elim)

/-- A successful actual root call on an extension of an eligible plain-load result
sinks the load and emits exactly one extending load from the load's address. Its
output register, state and selected root are determined; no rule receipt is a premise. -/
theorem stock_lower_sink_extend (kind : Kind) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i j x y nreg : Nat} {ty : Clif.Ty} {info load : IInfo}
    {flags : Clif.MemFlags} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.extend (extendOp kind) ty y)) (small : narrow ty = true)
    (defined : ctx.defInst? y = some j) (loaded : ctx.insts[j]? = some load)
    (loadClif : load.clif = some (.load .load (loadTy kind) flags x 0))
    (parameter : ctx.defInst? x = none) (mapped : ctx.valueReg? x = some (.vreg nreg .int))
    {st next : State} {out : V} {trace : List RuleId}
    (eligible : Stock.source ctx st y = some (j,true))
    (run : Stock.runTerm ctx "lower" [.inst i] st = .ok (some out,next,trace)) :
    Stock.externCtor ctx T.sink_inst [.inst j] st = .ok (.op .unit,sunkState st j) ∧
      out = .regsVec [[(st.base.fresh .int).1]] ∧
      next = {((sunkState st j).mark x) with base := ((st.base.fresh .int).2.emit
        (.load kind.loadOp (st.base.fresh .int).1 (.unsignedOffset (.vreg nreg .int) 0) flags))} ∧
      trace.getLast? = some (root kind).id := by
  obtain ⟨selected⟩ := stock_named_lower_selection run
  have chosen := stock_selected_sink_extend_rule kind inv source clif small defined loaded loadClif
    eligible selected
  obtain ⟨data,w,type,fits⟩ := extend_source_data kind inv source clif small
  obtain ⟨little,loadData,loadType⟩ := load_source_data kind inv loaded loadClif
  have found := selected.matchedRun
  rw [chosen] at found
  have enough := selected.fuelBound
  rw [lower_count] at enough
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+5 := ⟨selected.matchFuel-5,by omega⟩
  rw [fuelEq,stock_match_sink_extend data_program kind ctx source type fits data defined loaded loadType
    loadData little st eligible #[] m] at found
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at found
  obtain ⟨envEq,stateEq,traceEq⟩ := found
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← stateEq,← traceEq] at rhs
  have sink := stock_sink_extend_rhs_sinks kind ctx (n := 999991) rhs
  obtain ⟨computedTrace,computed⟩ := stock_sink_extend_rhs data_program kind ctx (cfg := {}) rfl parameter mapped
    flags st sink #[] 999879
  rw [computed] at rhs
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at rhs
  obtain ⟨outEq,nextEq,_⟩ := rhs
  refine ⟨sink,outEq.symm,nextEq.symm,?_⟩
  rw [selected.last_rule,chosen]

end Backend.Stock.Memory.SinkExtend
