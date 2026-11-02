import FV.Backend.Proof.StockCmpMachineValues
import FV.Backend.Proof.StockCmpCondition
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem resolved_renaming (aliases : Array (Option Nat)) :
    VRenaming (Backend.lowerFunction.resolve aliases (aliases.size+1)) (aliasNum aliases) := by
  refine ⟨fun n c => resolve_vreg aliases _ n c,?_⟩
  intro r nonVirtual
  cases r with
  | vreg n c => exact False.elim (nonVirtual n c rfl)
  | _ => simp [Backend.lowerFunction.resolve]
/-- Actual final-alias mapping transports a flag producer's specification under
any original register file; no renaming-invariance premise is added. -/
theorem stock_cmp_sets_flags_resolved {aliases : Array (Option Nat)} {m : MInst} {ρ : Nat → CV} {ps : Arm.PState}
    (flags : SetsFlags m (fun key => ρ (aliasNum aliases key)) ps) :
    SetsFlags (m.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))) ρ ps := by
  obtain ⟨ops,operands,noDefs,spec⟩ := flags
  have renamed := resolved_renaming aliases
  refine ⟨ops.map (rnOp (aliasNum aliases)),?_,?_,?_⟩
  · rw [operands_mapRegs renamed,operands]; rfl
  · simp only [Array.toList_map]
    rw [filter_map_rn _ Operand.isDef (fun _ => rfl),noDefs]
    rfl
  · intro world
    rw [ispec_mapRegs renamed, vuses_rename (D := fun _ => True) (by intro _ _; rfl) (by intro _ _ _; exact Or.inl trivial)]
    exact spec world
/-- Actual explicit-flag condition-result output executes through final aliases,
holds its established condition as original bool8, and preserves every other
register. Both code shape and full Stock state come from the real helper call. -/
theorem stock_cmp_flag_condition_values {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 119 ≤ fuel)
    {mi : V} {m : MInst} {condition : Cond} (decoded : MInst.ofV mi = some m)
    (valid : condition ≠ .al ∧ condition ≠ .nv) (noDefs : vdefs m = [])
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 27 715
      [.data 123 2 [.data 47 1 [mi],.data 96 condition.idx []]] (st,tr) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {ps : Arm.PState} {value : Bool}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (flags : SetsFlags m (fun key => ρ (aliasNum aliases key)) ps) (truth : condOn condition.bits ps = value) :
    ∃ d,out = .reg (.vreg d .int) ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [m,.cset (.vreg d .int) condition] ∧
      ∀ world,Runs F isem ([m,.cset (.vreg d .int) condition].map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 value⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  have shape : CondShape (.data 123 2 [.data 47 1 [mi],.data 96 condition.idx []]) (fun _ => True) :=
    Or.inr (Or.inr ⟨mi,m,condition,rfl,decoded,valid.1,valid.2,noDefs,fun _ _ => trivial⟩)
  obtain ⟨m',condition',selected,output,finish⟩ := stock_cmp_condition_observed hp ctx hc enough shape run
  rcases selected with ⟨_,_,_,impossible,_⟩ | ⟨_,_,_,impossible,_⟩ | ⟨mi',equal,decode'⟩
  · cases impossible
  · cases impossible
  · have both := List.cons.inj (V.data.inj equal).2.2
    have producerEq := (List.cons.inj (V.data.inj both.1).2.2).1
    cases producerEq
    have conditionEq := cond_idx_inj (V.data.inj (List.cons.inj both.2).1).2.1
    subst condition'
    have producer : m' = m := Option.some.inj (decode'.symm.trans decoded)
    subst m'
    let d := st.base.nextVreg
    have fresh : aliasNum aliases d = d := by
      apply chaseF_none
      rw [Array.getElem?_eq_none bounded]
      rfl
    have actual : (.cset (.vreg d .int) condition : MInst).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)) = .cset (.vreg d .int) condition := by
      simp only [MInst.mapRegs,resolve_vreg]
      change MInst.cset (.vreg (aliasNum aliases d) .int) condition = _
      rw [fresh]
    refine ⟨d,output,Nat.le_refl _,?_,?_,?_⟩
    · rw [finish]; simp [LState.fresh,LState.emit,d]
    · rw [finish]
      exact Frag.fresh_emit2 st.base noDefs (by change vdefs (.cset (.vreg st.base.nextVreg .int) condition) ⊆ _; rw [vdefs_cset]; simp)
    · intro world
      simp only [List.map_cons,List.map_nil,actual]
      exact (stock_cmp_flags_cset refines (stock_cmp_sets_flags_resolved flags) truth valid d world).imp
        (fun ρ' _ _ same => by
          subst ρ'
          refine ⟨?_,fun k different => by simp [upd,different]⟩
          rw [upd_same]
          exact vholds_bool8 _)
/-- Real Zero/NotZero condition-result calls execute their actual zero
comparison and cset through final aliases, with both boolean outcomes and a
complete outside-result register frame. -/
theorem stock_cmp_zero_condition_values {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 119 ≤ fuel)
    (nonzero : Bool) (sz : OperandSize) {i key : Nat} (size : OperandSize.ofIdx? i = some sz)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 27 715
      [.data 123 (if nonzero then 1 else 0) [.reg (.vreg key .int),.data 93 i []]] (st,tr) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg) :
    ∃ d,out = .reg (.vreg d .int) ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [cmpImm0 sz key,.cset (.vreg d .int) (if nonzero then .ne else .eq)] ∧
      ∀ world,Runs F isem ([cmpImm0 sz key,.cset (.vreg d .int) (if nonzero then .ne else .eq)].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (if nonzero then opnd sz (ρ (aliasNum aliases key)) != 0
            else opnd sz (ρ (aliasNum aliases key)) == 0)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  have shape : CondShape (.data 123 (if nonzero then 1 else 0) [.reg (.vreg key .int),.data 93 i []]) (fun _ => True) := by
    cases nonzero
    · exact Or.inl ⟨key,i,sz,rfl,size,trivial⟩
    · exact Or.inr (Or.inl ⟨key,i,sz,rfl,size,trivial⟩)
  obtain ⟨m,condition,selected,output,finish⟩ := stock_cmp_condition_observed hp ctx hc enough shape run
  have chosen : m = cmpImm0 sz key ∧ condition = if nonzero then .ne else .eq := by
    cases nonzero
    · rcases selected with ⟨k,j,sz',equal,size',rfl,rfl⟩ | ⟨_,_,_,impossible,_⟩ | ⟨_,impossible,_⟩
      · have args := List.cons.inj (V.data.inj equal).2.2
        have sameKey := (Reg.vreg.inj (V.reg.inj args.1)).1
        have sameIndex := (V.data.inj (List.cons.inj args.2).1).2.1
        subst k
        subst j
        have sameSize := Option.some.inj (size'.symm.trans size)
        subst sz'
        exact ⟨rfl,rfl⟩
      · cases impossible
      · cases impossible
    · rcases selected with ⟨_,_,_,impossible,_⟩ | ⟨k,j,sz',equal,size',rfl,rfl⟩ | ⟨_,impossible,_⟩
      · cases impossible
      · have args := List.cons.inj (V.data.inj equal).2.2
        have sameKey := (Reg.vreg.inj (V.reg.inj args.1)).1
        have sameIndex := (V.data.inj (List.cons.inj args.2).1).2.1
        subst k
        subst j
        have sameSize := Option.some.inj (size'.symm.trans size)
        subst sz'
        exact ⟨rfl,rfl⟩
      · cases impossible
  obtain ⟨rfl,rfl⟩ := chosen
  let d := st.base.nextVreg
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have code : ([cmpImm0 sz key,.cset (.vreg d .int) (if nonzero then .ne else .eq)].map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) =
      [cmpImm0 sz (aliasNum aliases key),.cset (.vreg d .int) (if nonzero then .ne else .eq)] := by
    simp only [cmpImm0,List.map_cons,List.map_nil,MInst.mapRegs,resolve_vreg]
    change [MInst.aluRRImm12 .subS sz .xzr (.vreg (aliasNum aliases key) .int) ⟨0,false⟩,
      .cset (.vreg (aliasNum aliases d) .int) (if nonzero then .ne else .eq)] = _
    rw [fresh]
  refine ⟨d,output,Nat.le_refl _,?_,?_,?_⟩
  · rw [finish]; simp [LState.fresh,LState.emit,d]
  · rw [finish]
    exact Frag.fresh_emit2 st.base rfl (by change vdefs (.cset (.vreg d .int) _) ⊆ _; rw [vdefs_cset]; simp [d])
  · intro world
    rw [code]
    have flags := setsFlags_cmp_imm0 sz (aliasNum aliases key) ρ
    have truth : condOn (if nonzero then Cond.ne else Cond.eq).bits
        (cmpFlags (opnd sz (ρ (aliasNum aliases key))) 0) =
        (if nonzero then opnd sz (ρ (aliasNum aliases key)) != 0 else opnd sz (ρ (aliasNum aliases key)) == 0) := by
      cases nonzero
      · exact stock_cmp_zero_flag _ _
      · have actual := stock_cmp_conditions (n := sz.bits) (by cases sz <;> simp [OperandSize.bits]) .ne
          (opnd sz (ρ (aliasNum aliases key))) 0
        exact actual
    have valid : (if nonzero then Cond.ne else Cond.eq) ≠ .al ∧ (if nonzero then Cond.ne else Cond.eq) ≠ .nv := by
      cases nonzero <;> decide
    exact (stock_cmp_flags_cset refines flags truth valid d world).imp (fun ρ' _ _ same => by
      subst ρ'
      refine ⟨?_,fun k different => by simp [upd,different]⟩
      rw [upd_same]
      exact vholds_bool8 _)
end Backend.Stock.Proof.ScalarCmp
