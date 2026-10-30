import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockDivHelpers
import FV.Backend.Proof.StockExtendRequests
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData t k vs = .data t k vs := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem nonzero_observed (ctx : Ctx) (st : LState) {value out : V}
    (run : Backend.externExtract ctx T.nonzero_u64_from_imm64 value st = .ok [out]) :
    ∃ i,value = .int i ∧ i ≠ 0 ∧ out = .int (u64 i) := by
  cases value with
  | int i =>
    obtain ⟨nonzero,equal⟩ := (ext_nonzero_u64_iff ctx st i [out]).mp run
    exact ⟨i,rfl,nonzero,(List.cons.inj equal).1⟩
  | _ => simp [Backend.externExtract,T.nonzero_u64_from_imm64,tyPred] at run
private theorem ext_out_reg {ctx : Ctx} {y e w : Nat} {pass : List CTy} {st next : State} {out : V}
    (observed : ScalarShift.MappedExtOut ctx y (e == 0) w pass st next out) :
    ∃ r,out = .reg r ∧ ScalarShift.MappedExtOut ctx y (e == 0) w pass st next (.reg r) := by
  obtain ⟨t,type,safe,rx,mapped,alternatives⟩ := observed
  rcases alternatives with ⟨member,output,state⟩ | ⟨absent,width,output,state⟩
  · exact ⟨rx,output,t,type,safe,rx,mapped,Or.inl ⟨member,rfl,state⟩⟩
  · exact ⟨_,output,t,type,safe,rx,mapped,Or.inr ⟨absent,width,rfl,state⟩⟩
private theorem zero_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n : Nat} (enough : 39 ≤ n)
    {s s' : State × Array RuleId} {r : Reg} {sz : OperandSize} {v : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg n 27 559 [.reg r,.data 93 (sizeIndex sz) []] s v s') :
    v = .reg r ∧ s'.1 = {s.1 with base := s.1.base.emit (.trapIf (.zero r sz) .intDivz)} := by
  obtain ⟨st,tr⟩ := s
  obtain ⟨next,trace⟩ := s'
  obtain ⟨fuel,fuelEq⟩ : ∃ fuel,n+1 = fuel+40 := ⟨n-39,by omega⟩
  have forward := stock_div_zero_guard_helper hp ctx hc sz st tr fuel r
  unfold ApplyInternal at run
  rw [fuelEq,forward] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  exact ⟨run.1.symm,run.2.1.symm⟩
private theorem size_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n w : Nat} (enough : 7 ≤ n) (width : w ≤ 64)
    {s s' : State × Array RuleId} {v : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg n 93 305 [.ty (.int w)] s v s') :
    v = .data 93 (sizeIndex (szOf w)) [] ∧ s'.1 = s.1 := by
  obtain ⟨st,tr⟩ := s
  obtain ⟨next,trace⟩ := s'
  obtain ⟨fuel,fuelEq⟩ : ∃ fuel,n+1 = fuel+8 := ⟨n-7,by omega⟩
  unfold ApplyInternal at run
  rw [fuelEq] at run
  by_cases small : w ≤ 32
  · have forward := stock_div_pure_helper hp ctx hc (by decide)
      (operand_size_32 hp ctx hc st.base tr fuel small)
    rw [forward] at run
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
    exact ⟨by simpa only [szOf,small,ite_true,sizeIndex] using run.1.symm,run.2.1.symm⟩
  · have forward := stock_div_pure_helper hp ctx hc (by decide)
      (operand_size_64 hp ctx hc st.base tr fuel (by omega) width)
    rw [forward] at run
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
    exact ⟨by simpa only [szOf,small,ite_false,sizeIndex] using run.1.symm,run.2.1.symm⟩

def DivisorObserved (p : Program) (ctx : Ctx) (cfg : Config) (y e w : Nat)
    (s s' : State × Array RuleId) (out : V) : Prop :=
  (∃ j info i,ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
    info.data = .data 152 35 [.data 151 57 [],.int i] ∧ i ≠ 0 ∧
    ∃ fuel trace,ApplyInternal p (Stock.sem ctx) cfg fuel 27 553 (immArgs w e (u64 i)) s out (s'.1,trace)) ∨
  (w = 64 ∧ DemandAllowed ctx s.1 y ∧ ∃ ry,ctx.valueReg? y = some ry ∧ out = .reg ry ∧
    s'.1 = {s.1.mark y with base := s.1.base.emit (.trapIf (.zero ry .size64) .intDivz)}) ∨
  (w ≤ 32 ∧ ∃ r middle,ScalarShift.MappedExtOut ctx y (e == 0) 32 [.int 32,.int 64] s.1 middle (.reg r) ∧
    out = .reg r ∧ s'.1 = {middle with base := middle.base.emit (.trapIf (.zero r .size32) .intDivz)})
/-- Successful actual divisor requests expose their real immediate or guarded
register/widening path, including full state and original source look-through. -/
theorem stock_div_divisor_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n y e w : Nat} (enough : 120 ≤ n)
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (extension : e = 0 ∨ e = 1)
    {s s' : State × Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg n 27 698 [.value y,.data 125 e [],.ty (.int w)] s out s') :
    DivisorObserved p ctx cfg y e w s s' out := by
  obtain ⟨st,tr⟩ := s
  obtain ⟨next,trace⟩ := s'
  have widthBound : w ≤ 64 := by omega
  clear width extension
  have hp' := hp
  stock_split hp hc run 698
  all_goals clear hpre
  all_goals isel_inv' hp' [sem_ctor,sem_extract,sem_unData,sem_eq,sem_mkData,sem_prim] at hm he
  all_goals try simp only [stock_put_in_reg_iff,ext_nonzero_u64_iff] at *
  all_goals isel_destruct <;> subst_vars

  · obtain ⟨extracted⟩ : Nonempty (Backend.externExtract ctx T.nonzero_u64_from_imm64 _ st.base = .ok [_]) := ⟨by assumption⟩
    obtain ⟨i,rfl,nonzero,rfl⟩ := nonzero_observed ctx st.base extracted
    obtain ⟨materialized⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 27 553
      [V.ty (CTy.int w),V.data 122 1 [],V.int (u64 i)] (st,tr) out _) := ⟨by assumption⟩
    unfold DivisorObserved
    left
    exact ⟨_,_,i,by assumption,by assumption,Eq.symm (by assumption),nonzero,_,_,materialized⟩
  · obtain ⟨extracted⟩ : Nonempty (Backend.externExtract ctx T.nonzero_u64_from_imm64 _ st.base = .ok [_]) := ⟨by assumption⟩
    obtain ⟨i,rfl,nonzero,rfl⟩ := nonzero_observed ctx st.base extracted
    obtain ⟨materialized⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 27 553
      [V.ty (CTy.int w),V.data 122 0 [],V.int (u64 i)] (st,tr) out _) := ⟨by assumption⟩
    unfold DivisorObserved
    left
    exact ⟨_,_,i,by assumption,by assumption,Eq.symm (by assumption),nonzero,_,_,materialized⟩
  · have wide : w = 64 := CTy.int.inj (by assumption)
    subst w
    obtain ⟨sizeCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 93 305 [.ty (.int 64)] _ _ _) := ⟨by assumption⟩
    have size := size_observed hp' ctx hc (run := sizeCall) (by omega) (by decide)
    obtain ⟨rfl,sizeState⟩ := size
    obtain ⟨mapped⟩ : Nonempty (ctx.valueReg? y = some _) := ⟨by assumption⟩
    obtain ⟨guardCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 27 559
      [.reg _,.data 93 (sizeIndex .size64) []] _ out _) := ⟨by assumption⟩
    obtain ⟨output,finish⟩ := zero_observed hp' ctx hc (run := guardCall) (by omega)
    rw [sizeState] at finish
    exact Or.inr (Or.inl ⟨rfl,by assumption,_,mapped,output,finish⟩)
  · obtain ⟨extendCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 27 555 [.value y] (st,tr) _ _) := ⟨by assumption⟩
    have extended := ScalarShift.stock_sext32_out hp' (ctx := ctx) hc (h := extendCall) (by omega)
    have extended' : ScalarShift.MappedExtOut ctx y (0 == 0) 32 [.int 32,.int 64] st _ _ := extended
    obtain ⟨r,reg,shape⟩ := ext_out_reg extended'
    obtain ⟨sizeCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 93 305 [.ty (.int 32)] _ _ _) := ⟨by assumption⟩
    have size := size_observed hp' ctx hc (run := sizeCall) (by omega) (by decide)
    obtain ⟨rfl,sizeState⟩ := size
    obtain ⟨guardCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 27 559
      [V.reg r,V.data 93 (sizeIndex .size32) []] _ out _) := ⟨by rw [← reg]; assumption⟩
    obtain ⟨output,finish⟩ := zero_observed hp' ctx hc (run := guardCall) (by omega)
    rw [sizeState] at finish
    exact Or.inr (Or.inr ⟨by simpa only [CTy.bits] using (show (CTy.int w).bits ≤ 32 from by assumption),r,_,shape,output,finish⟩)
  · obtain ⟨extendCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 27 556 [.value y] (st,tr) _ _) := ⟨by assumption⟩
    have extended := ScalarShift.stock_zext32_out hp' (ctx := ctx) hc (h := extendCall) (by omega)
    have extended' : ScalarShift.MappedExtOut ctx y (1 == 0) 32 [.int 32,.int 64] st _ _ := extended
    obtain ⟨r,reg,shape⟩ := ext_out_reg extended'
    obtain ⟨sizeCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 93 305 [.ty (.int 32)] _ _ _) := ⟨by assumption⟩
    have size := size_observed hp' ctx hc (run := sizeCall) (by omega) (by decide)
    obtain ⟨rfl,sizeState⟩ := size
    obtain ⟨guardCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 27 559
      [V.reg r,V.data 93 (sizeIndex .size32) []] _ out _) := ⟨by rw [← reg]; assumption⟩
    obtain ⟨output,finish⟩ := zero_observed hp' ctx hc (run := guardCall) (by omega)
    rw [sizeState] at finish
    exact Or.inr (Or.inr ⟨by simpa only [CTy.bits] using (show (CTy.int w).bits ≤ 32 from by assumption),r,_,shape,output,finish⟩)
def DivisorObservedFuel (p : Program) (ctx : Ctx) (cfg : Config) (y e w : Nat)
    (s s' : State × Array RuleId) (out : V) : Prop :=
  (∃ j info i,ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
    info.data = .data 152 35 [.data 151 57 [],.int i] ∧ i ≠ 0 ∧
    ∃ fuel trace,39 ≤ fuel ∧ ApplyInternal p (Stock.sem ctx) cfg fuel 27 553 (immArgs w e (u64 i)) s out (s'.1,trace)) ∨
  (w = 64 ∧ DemandAllowed ctx s.1 y ∧ ∃ ry,ctx.valueReg? y = some ry ∧ out = .reg ry ∧
    s'.1 = {s.1.mark y with base := s.1.base.emit (.trapIf (.zero ry .size64) .intDivz)}) ∨
  (w ≤ 32 ∧ ∃ r middle,ScalarShift.MappedExtOut ctx y (e == 0) 32 [.int 32,.int 64] s.1 middle (.reg r) ∧
    out = .reg r ∧ s'.1 = {middle with base := middle.base.emit (.trapIf (.zero r .size32) .intDivz)})
/-- Successful actual divisor requests expose their real immediate or guarded
register/widening path, including full state and original source look-through. -/
theorem stock_div_divisor_observed_with_fuel {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n y e w : Nat} (enough : 120 ≤ n)
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (extension : e = 0 ∨ e = 1)
    {s s' : State × Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg n 27 698 [.value y,.data 125 e [],.ty (.int w)] s out s') :
    DivisorObservedFuel p ctx cfg y e w s s' out := by
  obtain ⟨st,tr⟩ := s
  obtain ⟨next,trace⟩ := s'
  have widthBound : w ≤ 64 := by omega
  clear width extension
  have hp' := hp
  stock_split hp hc run 698
  all_goals clear hpre
  all_goals isel_inv' hp' [sem_ctor,sem_extract,sem_unData,sem_eq,sem_mkData,sem_prim] at hm he
  all_goals try simp only [stock_put_in_reg_iff,ext_nonzero_u64_iff] at *
  all_goals isel_destruct <;> subst_vars

  · obtain ⟨extracted⟩ : Nonempty (Backend.externExtract ctx T.nonzero_u64_from_imm64 _ st.base = .ok [_]) := ⟨by assumption⟩
    obtain ⟨i,rfl,nonzero,rfl⟩ := nonzero_observed ctx st.base extracted
    obtain ⟨materialized⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 27 553
      [V.ty (CTy.int w),V.data 122 1 [],V.int (u64 i)] (st,tr) out _) := ⟨by assumption⟩
    unfold DivisorObservedFuel
    left
    exact ⟨_,_,i,by assumption,by assumption,Eq.symm (by assumption),nonzero,_,_,by omega,materialized⟩
  · obtain ⟨extracted⟩ : Nonempty (Backend.externExtract ctx T.nonzero_u64_from_imm64 _ st.base = .ok [_]) := ⟨by assumption⟩
    obtain ⟨i,rfl,nonzero,rfl⟩ := nonzero_observed ctx st.base extracted
    obtain ⟨materialized⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 27 553
      [V.ty (CTy.int w),V.data 122 0 [],V.int (u64 i)] (st,tr) out _) := ⟨by assumption⟩
    unfold DivisorObservedFuel
    left
    exact ⟨_,_,i,by assumption,by assumption,Eq.symm (by assumption),nonzero,_,_,by omega,materialized⟩
  · have wide : w = 64 := CTy.int.inj (by assumption)
    subst w
    obtain ⟨sizeCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 93 305 [.ty (.int 64)] _ _ _) := ⟨by assumption⟩
    have size := size_observed hp' ctx hc (run := sizeCall) (by omega) (by decide)
    obtain ⟨rfl,sizeState⟩ := size
    obtain ⟨mapped⟩ : Nonempty (ctx.valueReg? y = some _) := ⟨by assumption⟩
    obtain ⟨guardCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 27 559
      [.reg _,.data 93 (sizeIndex .size64) []] _ out _) := ⟨by assumption⟩
    obtain ⟨output,finish⟩ := zero_observed hp' ctx hc (run := guardCall) (by omega)
    rw [sizeState] at finish
    exact Or.inr (Or.inl ⟨rfl,by assumption,_,mapped,output,finish⟩)
  · obtain ⟨extendCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 27 555 [.value y] (st,tr) _ _) := ⟨by assumption⟩
    have extended := ScalarShift.stock_sext32_out hp' (ctx := ctx) hc (h := extendCall) (by omega)
    have extended' : ScalarShift.MappedExtOut ctx y (0 == 0) 32 [.int 32,.int 64] st _ _ := extended
    obtain ⟨r,reg,shape⟩ := ext_out_reg extended'
    obtain ⟨sizeCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 93 305 [.ty (.int 32)] _ _ _) := ⟨by assumption⟩
    have size := size_observed hp' ctx hc (run := sizeCall) (by omega) (by decide)
    obtain ⟨rfl,sizeState⟩ := size
    obtain ⟨guardCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 27 559
      [V.reg r,V.data 93 (sizeIndex .size32) []] _ out _) := ⟨by rw [← reg]; assumption⟩
    obtain ⟨output,finish⟩ := zero_observed hp' ctx hc (run := guardCall) (by omega)
    rw [sizeState] at finish
    exact Or.inr (Or.inr ⟨by simpa only [CTy.bits] using (show (CTy.int w).bits ≤ 32 from by assumption),r,_,shape,output,finish⟩)
  · obtain ⟨extendCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 27 556 [.value y] (st,tr) _ _) := ⟨by assumption⟩
    have extended := ScalarShift.stock_zext32_out hp' (ctx := ctx) hc (h := extendCall) (by omega)
    have extended' : ScalarShift.MappedExtOut ctx y (1 == 0) 32 [.int 32,.int 64] st _ _ := extended
    obtain ⟨r,reg,shape⟩ := ext_out_reg extended'
    obtain ⟨sizeCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 93 305 [.ty (.int 32)] _ _ _) := ⟨by assumption⟩
    have size := size_observed hp' ctx hc (run := sizeCall) (by omega) (by decide)
    obtain ⟨rfl,sizeState⟩ := size
    obtain ⟨guardCall⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) cfg _ 27 559
      [V.reg r,V.data 93 (sizeIndex .size32) []] _ out _) := ⟨by rw [← reg]; assumption⟩
    obtain ⟨output,finish⟩ := zero_observed hp' ctx hc (run := guardCall) (by omega)
    rw [sizeState] at finish
    exact Or.inr (Or.inr ⟨by simpa only [CTy.bits] using (show (CTy.int w).bits ≤ 32 from by assumption),r,_,shape,output,finish⟩)
end Backend.Stock.Proof.ScalarDiv
