import FV.Backend.Proof.StockCmpZeroLeftMatch
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
section Integers
attribute [local semireducible] Isle.Aarch64.program
private theorem zero (ctx : Ctx) : (Stock.sem ctx).int 4 0 = .int 0 := rfl
end Integers
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem unsigned_code (ctx : Ctx) (cc : Clif.IntCC) (st : State) :
    Stock.externCtor ctx T.unsigned_cond_code [.data 145 (ccIdx cc) []] st =
      if signedCC cc then .fail else .ok (.data 145 (ccIdx cc) [],st) := by
  rw [stock_ctor_baseOnly ctx T.unsigned_cond_code _ st (by decide)]
  cases cc <;> rfl
private theorem constant_extract {ctx : Ctx} {x : Nat} {st : LState} {node ty payload : V}
    (definition : externExtract ctx T.def_inst (.value x) st = .ok [node])
    (instruction : externExtract ctx T.inst_data_value node st =
      .ok [ty,.data 152 35 [.data 151 57 [],payload]]) :
    ∃ j info,ctx.defInst? x = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 35 [.data 151 57 [],payload] := by
  obtain ⟨j,defined,equal⟩ := (ext_def_inst_iff ctx st x [node]).mp definition
  have nodeEq := (List.cons.inj equal).1
  subst node
  obtain ⟨info,found,equal⟩ := (ext_inst_data_value_iff ctx st j _).mp instruction
  have fields := (List.cons.inj (List.cons.inj equal).2).1
  exact ⟨j,info,defined,found,fields.symm⟩
private theorem constant_integer {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {x j : Nat} {info : IInfo} {payload : V}
    (defined : ctx.defInst? x = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],payload]) : ∃ literal,payload = .int literal := by
  obtain ⟨original,clif,raw⟩ := ctxInv_clif inv.identityView defined found
  rw [data] at raw
  obtain ⟨ty,c,rfl,fields⟩ := instData_iconst_inv raw
  exact ⟨imm64OfIconst ty c,(List.cons.inj fields).1⟩
private def SignFact (cc : Clif.IntCC) (value : Bool) : Prop := signedCC cc = value
private theorem save_sign {cc : Clif.IntCC} {value : Bool} (h : signedCC cc = value) : SignFact cc value := h
private theorem sign_fact_elim {cc : Clif.IntCC} {value : Bool} (h : SignFact cc value) : signedCC cc = value := h
attribute [local irreducible] SignFact
private def ImmediateObservation (ctx : Ctx) (narrow : Bool) (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat)
    (st : State) (tr : Array RuleId) (env : Isle.Interp.Env V) (after : State × Array RuleId) : Prop :=
  ∃ j info literal imm,ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 35 [.data 151 57 [],.int literal] ∧
      Imm12.ofNat? (u64 literal) = some imm ∧ (narrow = true → signedCC cc = false) ∧
      env = #[some (.data 145 (ccIdx cc) []),some (.ty (.int ty.width)),some (.value x),some (.op (.imm12 imm))] ∧
      after = (st,tr)
private theorem immediate_observation_elim {ctx : Ctx} {narrow : Bool} {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (h : ImmediateObservation ctx narrow cc ty x y st tr env after) :
  ∃ j info literal imm,ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 35 [.data 151 57 [],.int literal] ∧
      Imm12.ofNat? (u64 literal) = some imm ∧ (narrow = true → signedCC cc = false) ∧
      env = #[some (.data 145 (ccIdx cc) []),some (.ty (.int ty.width)),some (.value x),some (.op (.imm12 imm))] ∧
      after = (st,tr) := by
  unfold ImmediateObservation at h
  exact h
attribute [local irreducible] ImmediateObservation
/-- Actual ordinary/narrow immediate matching supplies original constant data,
encoding, canonical operands/environment and complete state/trace preservation. -/
theorem stock_cmp_immediate_match_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {f : Clif.Function} (inv : MappedCtxInv f ctx) (narrow : Bool) (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat)
    (typed : ctx.valueType? x = some (.int ty.width))
    {st : State} {tr : Array RuleId} {n : Nat} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+20) (if narrow then rule_inst_5134 else rule_inst_5165)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) :
  ∃ j info literal imm,ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 35 [.data 151 57 [],.int literal] ∧
      Imm12.ofNat? (u64 literal) = some imm ∧ (narrow = true → signedCC cc = false) ∧
      env = #[some (.data 145 (ccIdx cc) []),some (.ty (.int ty.width)),some (.value x),some (.op (.imm12 imm))] ∧
      after = (st,tr) := by
  suffices observed : ImmediateObservation ctx narrow cc ty x y st tr env after by
    exact immediate_observation_elim observed
  have hp' := hp
  have lookup := ext_value_type ctx st.base typed
  have code := fun q => unsigned_code ctx cc q
  cases narrow
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at matched
  all_goals isel_inv_simp [lookup,code,hp'.t1,hp'.t2,hp'.t110,hp'.t120,hp'.t144,hp'.t160,hp'.t209,hp'.t325,hp'.t2341,hp'.t2482,
    rule_inst_5165,rule_inst_5134,sem_extract,sem_unData,sem_eq,sem_ctor] at matched
  all_goals isel_destruct <;> subst_vars
  all_goals isel_inv_simp [lookup,code,hp'.t1,hp'.t2,hp'.t110,hp'.t120,hp'.t144,hp'.t160,hp'.t209,hp'.t325,hp'.t2341,hp'.t2482,
    rule_inst_5165,rule_inst_5134,sem_extract,sem_unData,sem_eq,sem_ctor] at *
  all_goals isel_destruct <;> subst_vars
  all_goals obtain ⟨j,info,defined,found,data⟩ := constant_extract (by assumption) (by assumption)
  all_goals obtain ⟨literal,payload⟩ := constant_integer inv defined found data
  all_goals subst_vars
  all_goals isel_inv_simp [ext_u64_from_imm64,ext_imm12_from_u64_iff] at *
  all_goals isel_destruct <;> subst_vars
  all_goals have lookupAgain := ext_value_type ctx st.base typed
  all_goals have codeAgain := fun q => unsigned_code ctx cc q
  all_goals isel_inv_simp [typed,lookupAgain,codeAgain,ext_u64_from_imm64,ext_imm12_from_u64_iff,
    ext_ty_32_or_64_iff,ext_fits_in_16_iff] at *
  all_goals isel_destruct <;> subst_vars
  all_goals have normalized : u64 (u64 literal) = u64 literal := u64_ofNat (u64_lt' literal)
  all_goals simp only [normalized] at *
  all_goals cases sign : signedCC cc
  all_goals have savedSign := save_sign sign
  all_goals isel_inv_simp [sign,Bool.false_eq_true,ite_true,ite_false] at *
  all_goals isel_destruct <;> subst_vars
  all_goals unfold ImmediateObservation
  all_goals obtain ⟨imm,encoded⟩ : ∃ imm,Imm12.ofNat? (u64 literal) = some imm := ⟨_,by assumption⟩
  all_goals refine ⟨j,info,literal,imm,defined,found,data,encoded,?_,?_,?_⟩
  all_goals first
    | assumption
    | exact sign_fact_elim savedSign
    | rfl
    | (intro h; cases h)
    | (intro _; assumption)
    | (intro _; exact sign_fact_elim savedSign)
    | (apply Array.toList_inj.mp; simp_all [Array.toList_setIfInBounds,List.set,List.replicate])
    | (simp_all; exact sign_fact_elim savedSign)
  all_goals exact sign_fact_elim savedSign
end Backend.Stock.Proof.ScalarCmp
