import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockCmpPredecessorUnsignedSourceValues
namespace Backend.Stock.Proof.ScalarCmp.PredecessorUnsignedSourceWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def literal (shift : Bool) : Int := if shift then 8193 else 3
private def constant (shift : Bool) : BitVec 64 := BitVec.ofInt 64 (literal shift)
private def immediate (shift : Bool) : Imm12 := ⟨2,shift⟩
private def function (shift : Bool) : Clif.Function := {
  name := "stock_predecessor_original_source"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],body := [⟨[31],.iconst .i64 (constant shift)⟩],term := .ret [7]}] }
private def built (shift : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function shift)).toOption.getD (sinkCtx,#[],sinkState)
private def frame (word : BitVec 64) (shift : Bool) : Clif.Frame := {
  func := function shift,regs := fun x => if x = 7 then some ⟨.i64,word⟩ else
    if x = 31 then some ⟨.i64,constant shift⟩ else none,
  slots := [],body := [],term := .ret [7] }
private def aliases : Array (Option Nat) := (Array.replicate 194 none).setIfInBounds 192 (some 1)
private def regs (word : BitVec 64) (n : Nat) : CV :=
  if n = 193 then BitVec.ofNat 128 (2^100+777) else BitVec.ofNat 128 (2^100+word.toNat)
private theorem scope (shift : Bool) : LowerScope (function shift) := lowerScope_of (by cases shift <;> decide +kernel)
private theorem build (shift : Bool) : Stock.buildCtx (function shift) = .ok (built shift) := by cases shift <;> rfl
private theorem dfg (word : BitVec 64) (shift : Bool) : DFGCons (built shift).1 (frame word shift) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases seven : x = 7
    · subst x
      have absent : (built shift).1.defInst? 7 = none := by cases shift <;> rfl
      rw [absent] at defined; cases defined
    · by_cases thirtyone : x = 31
      · subst x
        have index : (built shift).1.defInst? 31 = some 0 := by cases shift <;> rfl
        rw [index] at defined; cases defined
        obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
        subst info
        cases shift <;> cases original <;> cases lookup
        all_goals exact ⟨[⟨.i64,constant _⟩],fun cm => rfl,rfl⟩
      · simp [frame,seven,thirtyone] at lookup
  · intro x t v typed lookup
    by_cases present : x = 7 ∨ x = 31
    · rcases present with rfl | rfl
      · have type : (built shift).1.valueType? 7 = some (.int 64) := by cases shift <;> rfl
        rw [type] at typed; cases typed; cases lookup; rfl
      · have type : (built shift).1.valueType? 31 = some (.int 64) := by cases shift <;> rfl
        rw [type] at typed; cases typed; cases lookup; rfl
    · simp only [not_or] at present
      simp [frame,present.1,present.2] at lookup
private theorem held (word : BitVec 64) (shift : Bool) (st : State) (undemanded : st.demand[31]! = 0) :
    ValuesHeld (Demanded st) (built shift).1 (frame word shift) (fun key => regs word (aliasNum aliases key)) := by
  intro x needed val lookup
  by_cases seven : x = 7
  · subst x
    change some ⟨.i64,word⟩ = some val at lookup
    cases lookup
    refine ⟨192,?_,?_⟩
    · cases shift <;> rfl
    · change (regs word (aliasNum aliases 192)).setWidth 64 = word
      have alias : aliasNum aliases 192 = 1 := by decide +kernel
      rw [alias]
      change (BitVec.ofNat 128 (2^100+word.toNat)).setWidth 64 = word
      rw [BitVec.setWidth_ofNat_of_le (by decide)]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat,Nat.add_mod,show 2^100 % 2^64 = 0 from by decide +kernel,Nat.zero_add,Nat.mod_eq_of_lt word.isLt]
  · by_cases thirtyone : x = 31
    · subst x
      unfold Demanded at needed
      rw [undemanded] at needed
      omega
    · simp [frame,seven,thirtyone] at lookup
/-- An accepted original sparse-ID function inhabits the actual adjusted RHS
and715 source-value contracts for arbitrary64-bit inputs and both immediate
encoding forms, with dirty upper bits, a nonidentity alias and unmaterialized constant. -/
theorem stock_cmp_predecessor_unsigned_source_witness_all_values (word : BitVec 64) (shift : Bool) :
    ∃ condition middle emitTrace out next trace d,
      (evalExpr program (Stock.sem (built shift).1) {} 1000 rule_inst_5155.rhs
        #[some (.ty (.int 64)),some (.value 7),some (.int (literal shift)),some (.op (.imm12 (immediate shift)))]).run
        ((built shift).2.2,#[]) = .ok (some condition,middle,emitTrace) ∧
      ApplyInternal program (Stock.sem (built shift).1) {} 999 27 715 [condition]
        (middle,emitTrace) out (next,trace) ∧ out = .reg (.vreg d .int) ∧
      ∀ world,Runs (fun _ => True) ispec ([MInst.aluRRImm12 .subS .size64 .xzr (.vreg 192 .int) (immediate shift),
        .cset (.vreg d .int) (condOf .ugt)].map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
        (regs word) world (fun ρ' _ => VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc .uge word (constant shift))⟩ (ρ' d) ∧
          ∀ k,k ≠ d → ρ' k = regs word k) := by
  have safe : DemandAllowed (built shift).1 (built shift).2.2 7 := by
    intro j defined
    have absent : (built shift).1.defInst? 7 = none := by cases shift <;> rfl
    rw [absent] at defined; cases defined
  have mapped : (built shift).1.valueReg? 7 = some (.vreg 192 .int) := by cases shift <;> rfl
  have rhs := stock_cmp_predecessor_unsigned_rhs data_program (built shift).1 (cfg := {}) rfl .size64
    (built shift).2.2 #[] 900 7 (literal shift) (.vreg 192 .int) (immediate shift) mapped safe
  have decoded : MInst.ofV (.data 58 4 [.data 59 10 [],.data 93 1 [],.reg .xzr,.reg (.vreg 192 .int),.op (.imm12 (immediate shift))]) =
      some (.aluRRImm12 .subS .size64 .xzr (.vreg 192 .int) (immediate shift)) := rfl
  obtain ⟨trace,run⟩ := stock_cmp_condition_flags data_program (built shift).1 (cfg := {}) rfl
    ((built shift).2.2.mark 7) ((#[].push rule_inst_1593.id).push rule_inst_2774.id) 880 decoded (condOf .ugt)
  have conditionCall : ApplyInternal program (Stock.sem (built shift).1) {} 999 27 715 _ _ _ _ := run
  let info := (built shift).1.insts[0]!
  have found : (built shift).1.insts[0]? = some info := by cases shift <;> rfl
  have data : info.data = .data 152 35 [.data 151 57 [],.int (literal shift)] := by cases shift <;> decide +kernel
  have defined : (built shift).1.defInst? 31 = some 0 := by cases shift <;> rfl
  have extent : ∀ z r,(built shift).1.valueReg? z = some r → z < (built shift).2.2.demand.size := by
    intro z r mapped
    have sizeEq : (built shift).1.valReg.size = (built shift).2.2.demand.size := by cases shift <;> rfl
    rw [← sizeEq]
    by_cases bound : z < (built shift).1.valReg.size
    · exact bound
    · unfold Ctx.valueReg? at mapped
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt bound)] at mapped
      cases mapped
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨key,d,mapX,output,lower,upper,fragment,execution⟩ := stock_cmp_predecessor_unsigned_condition_source_values data_program
    (buildCtx_mappedInv (scope shift) (build shift)) (ty := .i64) (Or.inr rfl) (dfg word shift)
    (x := 7) (y := 31) (u := word) (v := constant shift) rfl rfl defined found data
    (by cases shift <;> decide +kernel) (by cases shift <;> decide +kernel) (by decide) rhs conditionCall self
    (aliases := aliases) (ρ := regs word) (by cases shift <;> decide +kernel) extent
    (held word shift _ (by cases shift <;> rfl))
  have keyEq : key = 192 := (Reg.vreg.inj (Option.some.inj (mapX.symm.trans mapped))).1
  subst key
  exact ⟨_,_,_,_,_,trace,d,rhs,conditionCall,output,execution⟩
end Backend.Stock.Proof.ScalarCmp.PredecessorUnsignedSourceWitness
