import FV.Backend.Proof.StockSelectComparisonDriverRuns
namespace Backend.Stock.Proof.ScalarSelect.ComparisonSourceWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
structure Case where
  cty : Clif.Ty
  ty : Clif.Ty
  extended : Bool
  comparisonWidth : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64
  width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64
  cint : cty.isInt = true
  int : ty.isInt = true
abbrev function (p : Case) := ComparisonDriver.function p.cty p.ty .ult p.extended
abbrev built (p : Case) := ComparisonDriver.built p.cty p.ty .ult p.extended
def index (p : Case) : Nat := if p.extended then 2 else 1
def conditionKey (p : Case) : Nat := if p.extended then 101 else 100
def conditionTy (p : Case) : Clif.Ty := if p.extended then .i64 else .i8
def conditionBits (p : Case) (a b : BitVec p.cty.width) : BitVec (conditionTy p).width :=
  BitVec.ofNat _ (if Clif.Sem.intcc .ult a b then 1 else 0)
def frame (p : Case) (a b : BitVec p.cty.width) : Clif.Frame := {
  func := function p
  regs := fun x => if x = 7 then some ⟨p.cty,a⟩ else if x = 31 then some ⟨p.cty,b⟩ else
    if x = 63 then some ⟨p.ty,7⟩ else if x = 95 then some ⟨p.ty,9⟩ else
    if x = 100 then some ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc .ult a b)⟩ else
    if x = 101 ∧ p.extended = true then some ⟨.i64,Clif.Sem.uextend 64 (Clif.Sem.bool8 (Clif.Sem.intcc .ult a b))⟩ else none
  slots := [],body := [⟨[102],.select p.ty (conditionKey p) 63 95⟩],term := .ret [102] }
def registers (p : Case) (a b : BitVec p.cty.width) (key : Nat) : CV :=
  BitVec.ofNat 128 (2^100 + if key = 192 then a.toNat else if key = 193 then b.toNat else if key = 194 then 7 else 9)
private theorem scope (p : Case) : LowerScope (function p) := by
  apply lowerScope_of
  rcases p with ⟨cty,ty,extended,hc,ht,ci,ti⟩
  cases cty <;> cases ty <;> cases extended <;> simp [Clif.Ty.width] at hc ht ci ti <;> rfl
private theorem getter {fr : Clif.Frame} {x : Nat} {ty : Clif.Ty} {bits : BitVec ty.width}
    (read : fr.regs x = some ⟨ty,bits⟩) : fr.getAs x ty = .ok bits := by
  unfold Clif.Frame.getAs Clif.Frame.get
  rw [read]
  simp [Clif.Res.ofOption]
private theorem dirty_word (ty : Clif.Ty) (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (word : BitVec ty.width) : (BitVec.ofNat 128 (2^100+word.toNat)).setWidth ty.width = word := by
  have bound : ty.width ≤ 128 := by omega
  have high : 2^100 % 2^ty.width = 0 := by rcases width with h | h | h | h <;> rw [h] <;> decide +kernel
  rw [BitVec.setWidth_ofNat_of_le bound]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,Nat.add_mod,high,Nat.zero_add,Nat.mod_eq_of_lt word.isLt]
private theorem absent (p : Case) (key : Nat) (present : key = 7 ∨ key = 31 ∨ key = 63 ∨ key = 95) :
    (built p).1.defInst? key = none := by
  rcases present with rfl | rfl | rfl | rfl
  all_goals rcases p with ⟨cty,ty,extended,hc,ht,ci,ti⟩
  all_goals cases cty <;> cases ty <;> cases extended <;> simp [Clif.Ty.width] at hc ht ci ti
  all_goals dsimp only [built,Case.cty,Case.ty,Case.extended,index,conditionKey]
  all_goals decide +kernel +revert
private theorem typed (p : Case) (key : Nat) (present : key = 7 ∨ key = 31 ∨ key = 63 ∨ key = 95 ∨ key = 100) :
    (built p).1.valueType? key = some (.int (if key = 100 then 8 else if key = 7 ∨ key = 31 then p.cty.width else p.ty.width)) := by
  rcases present with rfl | rfl | rfl | rfl | rfl
  all_goals rcases p with ⟨cty,ty,extended,hc,ht,ci,ti⟩
  all_goals cases cty <;> cases ty <;> cases extended <;> simp [Clif.Ty.width] at hc ht ci ti
  all_goals dsimp only [built,Case.cty,Case.ty,Case.extended,index,conditionKey]
  all_goals decide +kernel +revert
private theorem extension_typed (p : Case) (extended : p.extended = true) : (built p).1.valueType? 101 = some (.int 64) := by
  rcases p with ⟨cty,ty,ex,hc,ht,ci,ti⟩
  cases ex <;> simp at extended
  cases cty <;> cases ty <;> simp [Clif.Ty.width] at hc ht ci ti
  all_goals dsimp only [built,Case.cty,Case.ty,Case.extended,index,conditionKey]
  all_goals decide +kernel +revert
private theorem mapped_base (p : Case) (key : Nat) (present : key = 7 ∨ key = 31 ∨ key = 63 ∨ key = 95 ∨ key = 102) :
    (built p).1.valueReg? key = some (.vreg (if key = 7 then 192 else if key = 31 then 193 else if key = 63 then 194
      else if key = 95 then 195 else if p.extended then 198 else 197) .int) := by
  rcases present with rfl | rfl | rfl | rfl | rfl
  all_goals rcases p with ⟨cty,ty,extended,hc,ht,ci,ti⟩
  all_goals cases cty <;> cases ty <;> cases extended <;> simp [Clif.Ty.width] at hc ht ci ti
  all_goals dsimp only [built,Case.cty,Case.ty,Case.extended]
  all_goals decide +kernel +revert
private theorem source_base (p : Case) :
    ((built p).1.insts[index p]?).map minmaxSourceKey = some (some (.select p.ty (conditionKey p) 63 95),[102]) := by
  rcases p with ⟨cty,ty,extended,hc,ht,ci,ti⟩
  cases cty <;> cases ty <;> cases extended <;> simp [Clif.Ty.width] at hc ht ci ti
  all_goals dsimp only [built,Case.cty,Case.ty,Case.extended,index,conditionKey]
  all_goals decide +kernel +revert
private theorem comparison_base (p : Case) :
    (built p).1.defInst? 100 = some 0 ∧
      ((built p).1.insts[0]?).map minmaxSourceKey = some (some (.icmp .ult p.cty 7 31),[100]) := by
  rcases p with ⟨cty,ty,extended,hc,ht,ci,ti⟩
  cases cty <;> cases ty <;> cases extended <;> simp [Clif.Ty.width] at hc ht ci ti
  all_goals dsimp only [built,Case.cty,Case.ty,Case.extended,index,conditionKey]
  all_goals decide +kernel +revert
private theorem extension_base (p : Case) (extended : p.extended = true) :
    (built p).1.defInst? 101 = some 1 ∧
      ((built p).1.insts[1]?).map minmaxSourceKey = some (some (.extend .uextend .i64 100),[101]) := by
  rcases p with ⟨cty,ty,ex,hc,ht,ci,ti⟩
  cases ex <;> simp at extended
  cases cty <;> cases ty <;> simp [Clif.Ty.width] at hc ht ci ti
  all_goals dsimp only [built,Case.cty,Case.ty,Case.extended,index,conditionKey]
  all_goals decide +kernel +revert
private theorem dfg_base (p : Case) (a b : BitVec p.cty.width) : DFGCons (built p).1 (frame p a b) := by
  have getA : (frame p a b).getAs 7 p.cty = .ok a := getter rfl
  have getB : (frame p a b).getAs 31 p.cty = .ok b := getter (by simp [frame])
  constructor
  · intro x j info cl value defined found original pure lookup
    by_cases h7 : x = 7
    · subst x; rw [absent p 7 (by simp)] at defined; cases defined
    · by_cases h31 : x = 31
      · subst x; rw [absent p 31 (by simp)] at defined; cases defined
      · by_cases h63 : x = 63
        · subst x; rw [absent p 63 (by simp)] at defined; cases defined
        · by_cases h95 : x = 95
          · subst x; rw [absent p 95 (by simp)] at defined; cases defined
          · by_cases h100 : x = 100
            · subst x
              rw [(comparison_base p).1] at defined
              cases defined
              have key := (comparison_base p).2
              rw [found] at key
              have keys := Option.some.inj key
              have source := congrArg Prod.fst keys
              have results := congrArg Prod.snd keys
              change info.clif = some (.icmp .ult p.cty 7 31) at source
              change info.results = [100] at results
              rw [source] at original
              cases original
              simp [frame] at lookup
              subst value
              refine ⟨[⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc .ult a b)⟩],?_,?_⟩
              · intro env; simp [Clif.evalInst,Clif.Sem.icmp,getA,getB]
              · rw [results]; rfl
            · by_cases h101 : x = 101
              · subst x
                by_cases extended : p.extended = true
                · rw [(extension_base p extended).1] at defined
                  cases defined
                  have key := (extension_base p extended).2
                  rw [found] at key
                  have keys := Option.some.inj key
                  have source := congrArg Prod.fst keys
                  have results := congrArg Prod.snd keys
                  change info.clif = some (.extend .uextend .i64 100) at source
                  change info.results = [101] at results
                  rw [source] at original
                  cases original
                  simp [frame,extended] at lookup
                  subst value
                  refine ⟨[⟨.i64,Clif.Sem.uextend 64 (Clif.Sem.bool8 (Clif.Sem.intcc .ult a b))⟩],?_,?_⟩
                  · intro env
                    simp [Clif.evalInst,Clif.Frame.get,frame,Clif.Ty.width]
                  · rw [results]; rfl
                · simp [frame,extended] at lookup
              · simp [frame,h7,h31,h63,h95,h100,h101] at lookup
  · intro x t value type lookup
    by_cases h7 : x = 7
    · subst x; rw [typed p 7 (by simp)] at type; cases type; cases lookup; exact ofClif_int_width p.cint
    · by_cases h31 : x = 31
      · subst x; rw [typed p 31 (by simp)] at type; cases type
        simp [frame] at lookup; subst value; exact ofClif_int_width p.cint
      · by_cases h63 : x = 63
        · subst x; rw [typed p 63 (by simp)] at type; cases type
          simp [frame] at lookup; subst value; exact ofClif_int_width p.int
        · by_cases h95 : x = 95
          · subst x; rw [typed p 95 (by simp)] at type; cases type
            simp [frame] at lookup; subst value; exact ofClif_int_width p.int
          · by_cases h100 : x = 100
            · subst x; rw [typed p 100 (by simp)] at type; cases type
              simp [frame] at lookup; subst value; exact ofClif_int_width (by rfl)
            · by_cases h101 : x = 101
              · subst x
                by_cases extended : p.extended = true
                · rw [extension_typed p extended] at type; cases type
                  simp [frame,extended] at lookup; subst value; rfl
                · simp [frame,extended] at lookup
              · simp [frame,h7,h31,h63,h95,h100,h101] at lookup

structure SourceSetup (p : Case) : Prop where
  scope : LowerScope (function p)
  mapped : ∀ key,key = 7 ∨ key = 31 ∨ key = 63 ∨ key = 95 ∨ key = 102 →
    (built p).1.valueReg? key = some (.vreg (if key = 7 then 192 else if key = 31 then 193 else if key = 63 then 194
      else if key = 95 then 195 else if p.extended then 198 else 197) .int)
  source : ((built p).1.insts[index p]?).map minmaxSourceKey = some (some (.select p.ty (conditionKey p) 63 95),[102])
  dfg : ∀ a b : BitVec p.cty.width,DFGCons (built p).1 (frame p a b)
/-- Every scalar direct/uextended comparison-select fixture has its original
source scope, exact metadata and DFG-consistent frame over all operand words. -/
theorem stock_select_comparison_source_setup (p : Case) : SourceSetup p :=
  ⟨scope p,mapped_base p,source_base p,dfg_base p⟩
end Backend.Stock.Proof.ScalarSelect.ComparisonSourceWitness
