import FV.Backend.StockScalarCheck
import FV.Backend.Proof.StockLogicalCheck
import FV.Backend.Proof.StockScalarConstantDomain
import FV.Backend.Proof.StockScalarBnotDomain
import FV.Backend.Proof.StockScalarMulDomain
import FV.Backend.Proof.StockScalarShiftDomain
import FV.Backend.Proof.StockScalarCastDomain
import FV.Backend.Proof.StockScalarBitDomain
import FV.Backend.Proof.StockScalarPopcountDomain
import FV.Backend.Proof.StockScalarMinMaxDomain
import FV.Backend.Proof.StockScalarCmpDomain
import FV.Backend.Proof.StockScalarHighMulDomain
import FV.Backend.Proof.StockScalarDivDomain
import FV.Backend.Proof.StockScalarMixedDivDomain
import FV.Backend.Proof.StockScalarReturnedDivDomain
import FV.Backend.Proof.StockScalarGeneralDivDomain
import FV.Backend.Proof.StockScalarMaskDomain
import FV.Backend.Proof.StockTrapRefines

namespace Backend.Stock.Scalar
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem normal_abi {params : List Clif.AbiParam} (all : params.all abiEligible = true) :
    ∀ p ∈ params, p.purpose = .normal := by
  intro p member
  have good := List.all_eq_true.mp all p member
  simp only [abiEligible,Arithmetic.abiEligible, Bool.and_eq_true] at good
  have purpose : (p.purpose == .normal) = true := good.1
  exact beq_iff_eq.mp purpose

/-- The current scalar syntax is derived by the runtime classifier. -/
theorem bodyEligible_sound {stm : Clif.Stmt} (checked : bodyEligible stm = true) :
    Stock.Proof.ConstantBody.Family stm.inst := by
  simp only [bodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | constant
  · exact Or.inl (Logical.bodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [constantEligible,inst] at constant
    all_goals try contradiction
    next ty imm => exact Or.inr ⟨ty,imm,rfl⟩

/-- The extended classifier derives original NOT syntax; it adds no root premise. -/
theorem extendedBodyEligible_sound {stm : Clif.Stmt} (checked : extendedBodyEligible stm = true) :
    Stock.Proof.BnotBody.Family stm.inst := by
  simp only [extendedBodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | inverted
  · exact Or.inl (bodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [notEligible,inst] at inverted
    all_goals try contradiction
    next op ty x =>
      cases op <;> simp only [notEligible] at inverted
      all_goals try contradiction
      exact Or.inr ⟨ty,x,rfl⟩

theorem mulBodyEligible_sound {stm : Clif.Stmt} (checked : mulBodyEligible stm = true) :
    Stock.Proof.MulBody.Family stm.inst := by
  simp only [mulBodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | multiply
  · exact Or.inl (extendedBodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [mulEligible,inst] at multiply
    all_goals try contradiction
    next op ty x y =>
      cases op <;> simp only [mulEligible] at multiply
      all_goals try contradiction
      exact Or.inr ⟨ty,x,y,rfl⟩

/-- The shift classifier derives original syntax and keeps selection internal. -/
theorem shiftBodyEligible_sound {stm : Clif.Stmt} (checked : shiftBodyEligible stm = true) :
    Stock.Proof.ShiftBody.Family stm.inst := by
  simp only [shiftBodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | shift
  · exact Or.inl (mulBodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [shiftEligible,inst] at shift
    all_goals try contradiction
    next op ty x y =>
      cases op <;> simp only [shiftEligible] at shift
      all_goals try contradiction
      · exact Or.inr ⟨.lsl,ty,x,y,rfl⟩
      · exact Or.inr ⟨.lsr,ty,x,y,rfl⟩
      · exact Or.inr ⟨.asr,ty,x,y,rfl⟩

/-- Cast syntax is checked on the original statements, independently of selected roots. -/
theorem castBodyEligible_sound {stm : Clif.Stmt} (checked : castBodyEligible stm = true) :
    Stock.Proof.CastBody.Family stm.inst := by
  simp only [castBodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | cast
  · exact Or.inl (shiftBodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [castEligible,inst] at cast
    all_goals try contradiction
    · exact Or.inr (Or.inl ⟨_,_,_,rfl⟩)
    · exact Or.inr (Or.inr ⟨_,_,rfl⟩)

/-- The original source classifier derives bit/rotate syntax; no selected root is a premise. -/
theorem bitBodyEligible_sound {stm : Clif.Stmt} (checked : bitBodyEligible stm = true) :
    Stock.Proof.BitBody.Family stm.inst := by
  simp only [bitBodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | bit
  · exact Or.inl (castBodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [bitEligible,inst] at bit
    all_goals try contradiction
    next op ty x =>
      cases op <;> simp only [bitEligible] at bit
      all_goals try contradiction
      all_goals exact Or.inr (Or.inl ⟨_,_,_,by simp [Stock.Proof.BitBody.Unary],rfl⟩)
    next op ty x y =>
      cases op <;> simp only [bitEligible] at bit
      all_goals try contradiction
      all_goals first
        | exact Or.inr (Or.inr ⟨true,_,_,_,rfl⟩)
        | exact Or.inr (Or.inr ⟨false,_,_,_,rfl⟩)

/-- Original popcount syntax derives the universal source contract internally. -/
theorem popcountBodyEligible_sound {stm : Clif.Stmt} (checked : popcountBodyEligible stm = true) :
    Stock.Proof.PopcountBody.Family stm.inst := by
  simp only [popcountBodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | popcount
  · exact Or.inl (bitBodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [popcountEligible,inst] at popcount
    all_goals try contradiction
    next op ty x =>
      cases op <;> simp only [popcountEligible] at popcount
      all_goals try contradiction
      exact Or.inr ⟨ty,x,rfl⟩

/-- Actual original min/max syntax derives the reusable scalar source domain. -/
theorem minmaxBodyEligible_sound {stm : Clif.Stmt} (checked : minmaxBodyEligible stm = true) :
    Stock.Proof.MinMaxBody.Family stm.inst := by
  simp only [minmaxBodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | minmax
  · exact Or.inl (popcountBodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [minmaxEligible,inst] at minmax
    all_goals try contradiction
    next op ty x y =>
      cases op <;> simp only [minmaxEligible] at minmax
      all_goals try contradiction
      all_goals first
        | exact Or.inr ⟨false,false,_,_,_,rfl⟩
        | exact Or.inr ⟨false,true,_,_,_,rfl⟩
        | exact Or.inr ⟨true,false,_,_,_,rfl⟩
        | exact Or.inr ⟨true,true,_,_,_,rfl⟩

/-- Actual comparison syntax constructs the universal mixed source domain. -/
theorem cmpBodyEligible_sound {stm : Clif.Stmt} (checked : cmpBodyEligible stm = true) :
    Stock.Proof.CmpBody.Family stm.inst := by
  simp only [cmpBodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | cmp
  · exact Or.inl (minmaxBodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [cmpEligible,inst] at cmp
    all_goals try contradiction
    next cc ty x y => exact Or.inr ⟨cc,ty,x,y,rfl⟩

/-- Original signed/unsigned high-multiply syntax derives the universal mixed source domain. -/
theorem highmulBodyEligible_sound {stm : Clif.Stmt} (checked : highmulBodyEligible stm = true) :
    Stock.Proof.HighMulBody.Family stm.inst := by
  simp only [highmulBodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | highmul
  · exact Or.inl (cmpBodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [highmulEligible,inst] at highmul
    all_goals try contradiction
    next op ty x y =>
      cases op <;> simp only [highmulEligible] at highmul
      all_goals try contradiction
      all_goals first
        | exact Or.inr ⟨true,_,_,_,rfl⟩
        | exact Or.inr ⟨false,_,_,_,rfl⟩

/-- The classifier derives source shape and every prefix family internally. -/
theorem mixedDivEligible_sound {b : Clif.Block} (checked : mixedDivEligible b = true) :
    ∃ (front : List Clif.Stmt) (stm : Clif.Stmt) (op : Clif.DivOp) (ty : Clif.Ty) (x y z : Nat),
      b.body = front ++ [stm] ∧
      (∀ item ∈ front,Proof.HighMulBody.Family item.inst) ∧
      stm.inst = .div op ty x y ∧ stm.results = [z] ∧ b.term = .ret [z] := by
  unfold mixedDivEligible at checked
  split at checked
  next z op ty x y front z' body ret =>
    simp only [Bool.and_eq_true] at checked
    have equal : z = z' := beq_iff_eq.mp checked.1.1
    subst z'
    refine ⟨front.reverse,⟨[z],.div op ty x y⟩,op,ty,x,y,z,?_,?_,rfl,rfl,ret⟩
    · have reversed := congrArg List.reverse body
      simpa only [List.reverse_reverse,List.reverse_cons,List.reverse_nil,List.nil_append] using reversed
    · intro item member
      exact highmulBodyEligible_sound (List.all_eq_true.mp checked.2 item (List.mem_reverse.mp member))
  next => cases checked

/-- The finite source classifier supplies the original division and binder. -/
theorem singleDivEligible_sound {b : Clif.Block} (checked : singleDivEligible b = true) :
    ∃ (stm : Clif.Stmt) (op : Clif.DivOp) (ty : Clif.Ty) (x y z : Nat),
      b.body = [stm] ∧ stm.inst = .div op ty x y ∧ stm.results = [z] ∧ b.term = .ret [z] := by
  unfold singleDivEligible at checked
  split at checked
  next z op ty x y z' body ret =>
    simp only [Bool.and_eq_true] at checked
    have equal : z = z' := beq_iff_eq.mp checked.1
    subst z'
    exact ⟨⟨[z],.div op ty x y⟩,op,ty,x,y,z,body,rfl,rfl,ret⟩
  next => cases checked

/-- Match syntax supplies the original division and its unique result value. -/
theorem returnedDivAt_sound {stm : Clif.Stmt} {z : Nat} (checked : returnedDivAt stm z = true) :
    ∃ (op : Clif.DivOp) (ty : Clif.Ty) (x y : Nat),
      stm.inst = .div op ty x y ∧ stm.results = [z] := by
  unfold returnedDivAt at checked
  split at checked
  next z' op ty x y results inst =>
    simp only [Bool.and_eq_true] at checked
    have equal : z' = z := beq_iff_eq.mp checked.1
    exact ⟨op,ty,x,y,inst,by simpa only [equal] using results⟩
  next => cases checked

/-- Recursive source classification derives both scalar sides internally. -/
theorem returnedDivBodyEligible_sound {body : List Clif.Stmt} {z : Nat}
    (checked : returnedDivBodyEligible body z = true) :
    ∃ (front back : List Clif.Stmt) (stm : Clif.Stmt) (op : Clif.DivOp) (ty : Clif.Ty) (x y : Nat),
      body = front ++ stm :: back ∧
      (∀ item ∈ front,Proof.HighMulBody.Family item.inst) ∧
      (∀ item ∈ back,Proof.HighMulBody.Family item.inst) ∧
      stm.inst = .div op ty x y ∧ stm.results = [z] := by
  induction body with
  | nil => cases checked
  | cons item rest ih =>
    simp only [returnedDivBodyEligible,Bool.or_eq_true,Bool.and_eq_true] at checked
    rcases checked with ⟨here,suffix⟩ | ⟨scalar,tail⟩
    · obtain ⟨op,ty,x,y,division,results⟩ := returnedDivAt_sound here
      refine ⟨[],rest,item,op,ty,x,y,rfl,by simp,?_,division,results⟩
      intro next member
      exact highmulBodyEligible_sound (List.all_eq_true.mp suffix next member)
    · obtain ⟨front,back,stm,op,ty,x,y,shape,before,after,division,results⟩ := ih tail
      refine ⟨item :: front,back,stm,op,ty,x,y,?_,?_,after,division,results⟩
      · simpa only [List.cons_append] using congrArg (List.cons item) shape
      · intro next member
        rcases List.mem_cons.mp member with rfl | member
        · exact highmulBodyEligible_sound scalar
        · exact before next member

/-- Complete original-source layout for the new internal classifier. -/
theorem returnedDivEligible_sound {b : Clif.Block} (checked : returnedDivEligible b = true) :
    ∃ (front back : List Clif.Stmt) (stm : Clif.Stmt) (op : Clif.DivOp) (ty : Clif.Ty) (x y z : Nat),
      b.body = front ++ stm :: back ∧
      (∀ item ∈ front,Proof.HighMulBody.Family item.inst) ∧
      (∀ item ∈ back,Proof.HighMulBody.Family item.inst) ∧
      stm.inst = .div op ty x y ∧ stm.results = [z] ∧ b.term = .ret [z] := by
  unfold returnedDivEligible at checked
  split at checked
  next z ret =>
    obtain ⟨front,back,stm,op,ty,x,y,shape,before,after,division,results⟩ :=
      returnedDivBodyEligible_sound checked
    exact ⟨front,back,stm,op,ty,x,y,z,shape,before,after,division,results,ret⟩
  next => cases checked


/-- The original division operands and operation come directly from syntax. -/
theorem divisionBodyEligible_sound {stm : Clif.Stmt}
    (checked : divisionBodyEligible stm = true) :
    ∃ op ty x y, stm.inst = .div op ty x y := by
  unfold divisionBodyEligible at checked
  split at checked
  next op ty x y shape => exact ⟨op,ty,x,y,shape⟩
  next => cases checked

/-- The shared source domain receives a universal statement family. -/
theorem generalDivBodyEligible_sound {stm : Clif.Stmt}
    (checked : generalDivBodyEligible stm = true) :
    Proof.HighMulBody.Family stm.inst ∨ ∃ op ty x y,stm.inst = .div op ty x y := by
  simp only [generalDivBodyEligible,Bool.or_eq_true] at checked
  rcases checked with scalar | division
  · exact Or.inl (highmulBodyEligible_sound scalar)
  · exact Or.inr (divisionBodyEligible_sound division)


private theorem domain_of_eligible {f : Clif.Function} (eligible : eligible f = true)
    (scope : lowerScopeB f = true) (dominated : dominatedB f = true)
    (abi : sigAbiOk f.sig = true) : Domain f := by
  unfold Scalar.eligible at eligible
  split at eligible
  next b blocks =>
    simp only [Bool.and_eq_true] at eligible
    obtain ⟨⟨⟨body,terminal⟩,params⟩,returns⟩ := eligible
    have sourceShape : ∃ xs, b.term = .ret xs := by
      cases term : b.term <;> simp_all
    obtain ⟨xs,ret⟩ := sourceShape
    have noSret : f.sig.params.find? (·.purpose == .sret) = none := by
      apply List.find?_eq_none.mpr
      intro p member
      simp [(normal_abi params) p member]
    have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := by
      rw [sigRets,noSret]
      apply Bool.eq_false_iff.mpr
      intro any
      obtain ⟨p,member,sret⟩ := List.any_eq_true.mp any
      simpa [(normal_abi returns) p member] using sret
    simp only [Bool.or_eq_true] at body
    rcases body with (((old | divided) | mixed) | positioned) | general
    · have families : ∀ stm ∈ b.body, Stock.Proof.HighMulBody.Family stm.inst := by
        intro stm member
        have supported := List.all_eq_true.mp old stm member
        exact highmulBodyEligible_sound supported
      exact domain_of_highmul (lowerScope_of scope) (dominated_of dominated) abi blocks families ret ordinary
    · obtain ⟨stm,op,ty,x,y,z,singleton,division,results,ret'⟩ := singleDivEligible_sound divided
      exact domain_of_single_div (lowerScope_of scope) (dominated_of dominated) abi blocks
        singleton division results ret' ordinary
    · obtain ⟨front,stm,op,ty,x,y,z,shape,families,division,results,ret'⟩ := mixedDivEligible_sound mixed
      exact domain_of_mixed_div (lowerScope_of scope) (dominated_of dominated) abi blocks
        shape families division results ret' ordinary
    · obtain ⟨front,back,stm,op,ty,x,y,z,shape,before,after,division,results,ret'⟩ :=
        returnedDivEligible_sound positioned
      exact domain_of_returned_div (lowerScope_of scope) (dominated_of dominated) abi blocks
        shape before after division results ret' ordinary
    · exact domain_of_scalar_div (lowerScope_of scope) (dominated_of dominated) abi blocks
        (fun stm member => generalDivBodyEligible_sound (List.all_eq_true.mp general stm member)) ret ordinary
  next => cases eligible


/-- Narrow syntax supplies the same original-source family, with no new semantic premise. -/
theorem narrowBodyEligible_sound {stm : Clif.Stmt} (checked : narrowBodyEligible stm = true) :
    Proof.HighMulBody.Family stm.inst ∨ ∃ op ty x y,stm.inst = .div op ty x y := by
  cases inst : stm.inst <;> simp only [narrowBodyEligible,inst] at checked
  all_goals try contradiction
  case iconst ty imm =>
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨ty,imm,rfl⟩))))))))))
  case unary op ty x =>
    cases op <;> simp [narrowBodyEligible] at checked
    all_goals first
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨ty,x,rfl⟩)))))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨ty,x,rfl⟩))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨.ineg,ty,x,by simp [Proof.BitBody.Unary],rfl⟩))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨.clz,ty,x,by simp [Proof.BitBody.Unary],rfl⟩))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨.ctz,ty,x,by simp [Proof.BitBody.Unary],rfl⟩))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨.bitrev,ty,x,by simp [Proof.BitBody.Unary],rfl⟩))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨.bswap,ty,x,by simp [Proof.BitBody.Unary],rfl⟩))))))
  case binary op ty x y =>
    cases op <;> simp [narrowBodyEligible] at checked
    all_goals first
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨false,ty,x,y,rfl⟩)))))))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨true,ty,x,y,rfl⟩)))))))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨.band,ty,x,y,rfl⟩))))))))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨.bor,ty,x,y,rfl⟩))))))))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨.bxor,ty,x,y,rfl⟩))))))))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨ty,x,y,rfl⟩))))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨.lsl,ty,x,y,rfl⟩)))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨.lsr,ty,x,y,rfl⟩)))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨.asr,ty,x,y,rfl⟩)))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨false,ty,x,y,rfl⟩))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨true,ty,x,y,rfl⟩))))))
        | exact Or.inl (Or.inl (Or.inl (Or.inr ⟨false,false,ty,x,y,rfl⟩)))
        | exact Or.inl (Or.inl (Or.inl (Or.inr ⟨false,true,ty,x,y,rfl⟩)))
        | exact Or.inl (Or.inl (Or.inl (Or.inr ⟨true,false,ty,x,y,rfl⟩)))
        | exact Or.inl (Or.inl (Or.inl (Or.inr ⟨true,true,ty,x,y,rfl⟩)))
        | exact Or.inl (Or.inr ⟨false,ty,x,y,rfl⟩)
        | exact Or.inl (Or.inr ⟨true,ty,x,y,rfl⟩)
  case select ty c x y =>
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨ty,c,x,y,rfl⟩))))))))))))
  case icmp cc ty x y =>
    exact Or.inl (Or.inl (Or.inr ⟨cc,ty,x,y,rfl⟩))
  case extend op ty x =>
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨op,ty,x,rfl⟩)))))))
  case ireduce ty x =>
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨ty,x,rfl⟩)))))))
  case div op ty x y => exact Or.inr ⟨op,ty,x,y,rfl⟩

private theorem narrowMixedBodyEligible_sound {stm : Clif.Stmt}
    (checked : narrowMixedBodyEligible stm = true) :
    Proof.HighMulBody.Family stm.inst ∨ ∃ op ty x y,stm.inst = .div op ty x y := by
  simp only [narrowMixedBodyEligible,Bool.or_eq_true] at checked
  exact checked.elim generalDivBodyEligible_sound narrowBodyEligible_sound

private theorem normal_narrow_abi {params : List Clif.AbiParam}
    (all : params.all narrowAbiEligible = true) : ∀ p ∈ params,p.purpose = .normal := by
  intro p member
  have good := List.all_eq_true.mp all p member
  simp only [narrowAbiEligible,Bool.and_eq_true] at good
  exact beq_iff_eq.mp good.1

theorem domain_of_narrowEligible {f : Clif.Function} (eligible : narrowEligible f = true)
    (scope : lowerScopeB f = true) (dominated : dominatedB f = true)
    (abi : sigAbiOk f.sig = true) : Domain f := by
  unfold narrowEligible at eligible
  split at eligible
  next b blocks =>
    simp only [Bool.and_eq_true] at eligible
    obtain ⟨⟨⟨body,terminal⟩,params⟩,returns⟩ := eligible
    have sourceShape : ∃ xs,b.term = .ret xs := by
      cases term : b.term <;> simp_all
    obtain ⟨xs,ret⟩ := sourceShape
    have noSret : f.sig.params.find? (·.purpose == .sret) = none := by
      apply List.find?_eq_none.mpr
      intro p member
      simp [(normal_narrow_abi params) p member]
    have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := by
      rw [sigRets,noSret]
      apply Bool.eq_false_iff.mpr
      intro any
      obtain ⟨p,member,sret⟩ := List.any_eq_true.mp any
      simpa [(normal_narrow_abi returns) p member] using sret
    exact domain_of_scalar_div (lowerScope_of scope) (dominated_of dominated) abi blocks
      (fun stm member => narrowMixedBodyEligible_sound (List.all_eq_true.mp body stm member)) ret ordinary
  next => cases eligible

/-- Source classification for bmask and nop retains the independent input type;
actual matching and the original scope derive that type inside the body proof. -/
theorem maskMixedBodyEligible_sound {stm : Clif.Stmt} (checked : maskMixedBodyEligible stm = true) :
    Proof.MaskBody.Family stm.inst := by
  simp only [maskMixedBodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | extra
  · exact Or.inl (narrowMixedBodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [maskBodyEligible,inst] at extra
    all_goals try contradiction
    case bmask ty x => exact Or.inr (Or.inl ⟨ty,x,rfl⟩)
    case nop => exact Or.inr (Or.inr rfl)

theorem domain_of_maskEligible {f : Clif.Function} (eligible : maskEligible f = true)
    (scope : lowerScopeB f = true) (dominated : dominatedB f = true)
    (abi : sigAbiOk f.sig = true) : Domain f := by
  unfold maskEligible at eligible
  split at eligible
  next b blocks =>
    simp only [Bool.and_eq_true] at eligible
    obtain ⟨⟨⟨body,terminal⟩,params⟩,returns⟩ := eligible
    have sourceShape : ∃ xs,b.term = .ret xs := by
      cases term : b.term <;> simp_all
    obtain ⟨xs,ret⟩ := sourceShape
    have noSret : f.sig.params.find? (·.purpose == .sret) = none := by
      apply List.find?_eq_none.mpr
      intro p member
      simp [(normal_narrow_abi params) p member]
    have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := by
      rw [sigRets,noSret]
      apply Bool.eq_false_iff.mpr
      intro any
      obtain ⟨p,member,sret⟩ := List.any_eq_true.mp any
      simpa [(normal_narrow_abi returns) p member] using sret
    exact domain_of_mask (lowerScope_of scope) (dominated_of dominated) abi blocks
      (fun stm member => maskMixedBodyEligible_sound (List.all_eq_true.mp body stm member)) ret ordinary
  next => cases eligible

theorem domain_of_maskTrapEligible {f : Clif.Function} (eligible : maskTrapEligible f = true)
    (scope : lowerScopeB f = true) (dominated : dominatedB f = true)
    (abi : sigAbiOk f.sig = true) : Domain f := by
  unfold maskTrapEligible at eligible
  split at eligible
  next b blocks =>
    simp only [Bool.and_eq_true] at eligible
    obtain ⟨⟨⟨body,terminal⟩,params⟩,returns⟩ := eligible
    have sourceShape : ∃ c,b.term = .trap c := by
      cases term : b.term <;> simp_all
    obtain ⟨c,trap⟩ := sourceShape
    have noSret : f.sig.params.find? (·.purpose == .sret) = none := by
      apply List.find?_eq_none.mpr
      intro p member
      simp [(normal_narrow_abi params) p member]
    have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := by
      rw [sigRets,noSret]
      apply Bool.eq_false_iff.mpr
      intro any
      obtain ⟨p,member,sret⟩ := List.any_eq_true.mp any
      simpa [(normal_narrow_abi returns) p member] using sret
    exact domain_of_maskTrap (lowerScope_of scope) (dominated_of dominated) abi blocks
      (fun stm member => maskMixedBodyEligible_sound (List.all_eq_true.mp body stm member)) trap ordinary
  next => cases eligible

theorem sourceOk_sound {f : Clif.Function} (checked : sourceOk f = true) : Domain f := by
  simp only [sourceOk,productionEligible,Bool.and_eq_true,Bool.or_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  exact eligible.elim
    (fun returned => returned.elim
      (fun prior => prior.elim (fun old => domain_of_eligible old scope dominated abi)
        (fun narrow => domain_of_narrowEligible narrow scope dominated abi))
      (fun mask => domain_of_maskEligible mask scope dominated abi))
    (fun trap => domain_of_maskTrapEligible trap scope dominated abi)


theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ result, Domain f ∧ Stock.lower f = .ok result ∧ result.code = vc ∧
      result.edgeArgs.all (fun row => row.all (·.isEmpty)) = true := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  cases run : Stock.lower f with
  | error message => simp [run] at lowered
  | ok result =>
    simp only [run,Bool.and_eq_true,decide_eq_true_eq] at lowered
    exact ⟨result,sourceOk_sound source,rfl,lowered.1,lowered.2⟩
end Backend.Stock.Scalar
