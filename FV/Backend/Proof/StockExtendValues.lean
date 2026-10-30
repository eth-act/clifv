import FV.Backend.Proof.StockExtendSemantics
import FV.Backend.Proof.StockExtendRequests
namespace Backend.Stock.Proof.ScalarShift
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A mapped extension result describes the entire emitted fragment and its
original value through final aliases, including the pass-through case. -/
def ExtValueOut (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem) (sg : Bool) (toB : Nat)
    (ty : Clif.Ty) (bits : BitVec ty.width) (st next : State) (out : V)
    (aliases : Array (Option Nat)) (ρ : Nat → CV) : Prop :=
  ∃ (ms : List MInst) (r : Nat) (ρ' : Nat → CV), out = .reg (.vreg r .int) ∧
    next.base.emitted = st.base.emitted ++ ms.toArray ∧ st.base.nextVreg ≤ next.base.nextVreg ∧
    (∀ m ∈ ms,∀ d ∈ vdefs m,st.base.nextVreg ≤ d ∧ d < next.base.nextVreg) ∧
    PRun F isem (ms.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
    ExtHolds sg toB ⟨ty,bits⟩ (ρ' (aliasNum aliases r)) ∧
    ∀ n,n < st.base.nextVreg ∨ next.base.nextVreg ≤ n → ρ' n = ρ n

/-- Actual extension-call shape, mapped source type, guarded demand and frame
consistency establish the original extended value and all fresh-write bounds. -/
theorem stock_ext_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {sg : Bool} {toB : Nat} (target : toB = 32 ∨ toB = 64) {pass : List CTy}
    (allowedPass : ∀ t ∈ pass,t = .int 64 ∨ (t = .int 32 ∧ toB = 32))
    (passes32 : toB = 32 → .int 32 ∈ pass)
    {x : Nat} {ty : Clif.Ty} {bits : BitVec ty.width} {fr : Clif.Frame}
    (dfg : DFGCons ctx fr) (source : fr.getAs x ty = .ok bits)
    {st next : State} {out : V} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k)))
    (shape : MappedExtOut ctx x sg toB pass st next out) :
    ExtValueOut F isem sg toB ty bits st next out aliases ρ := by
  obtain ⟨t,typed,safe,rx,mapped,form⟩ := shape
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapped
  have typeEq : t = CTy.ofClif ty := (dfg.2 x t ⟨ty,bits⟩ typed (getAs_ok source)).symm
  have marked : Demanded (st.mark x) x := by
    rw [Demanded,(mark_demand st x (extent x _ mapped)).1]
    omega
  rcases form with ⟨passes,rfl,rfl⟩ | ⟨notPass,width,rfl,rfl⟩
  · have input := held.read marked (getAs_ok source) mapped
    have permitted : ty = .i64 ∨ (ty = .i32 ∧ toB = 32) := by
      rw [typeEq] at passes
      rcases allowedPass _ passes with wide | ⟨small,toEq⟩
      · left; cases ty <;> simp [CTy.ofClif] at wide ⊢
      · right; refine ⟨?_,toEq⟩; cases ty <;> simp [CTy.ofClif] at small ⊢
    exact ⟨[],nx,ρ,rfl,by simp [State.mark],Nat.le_refl _,by simp,prun_nil _,
      stock_ext_passthrough_holds sg permitted input,fun _ _ => rfl⟩
  · rw [typeEq,ofClif_bits] at width
    have sourceWidth : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 := by
      cases ty <;> simp [Clif.Ty.width] at width ⊢
    have grows : ty.width < toB := by
      rcases target with rfl | rfl
      · have forbids := passes32 rfl
        rw [typeEq] at notPass
        have int := isInt_of_ofClif_mem (typeEq ▸ inv.valTyE x t typed)
        cases ty <;> simp [Clif.Ty.width,CTy.ofClif] at width int ⊢
        exact False.elim (notPass forbids)
      · omega
    have operands : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)) := by
      apply held.mono
      intro z same; subst z; exact marked
    obtain ⟨ρ',execution,value,kept⟩ := stock_extend_resolved refines sg sourceWidth target grows bounded mapped operands source
    have fresh : aliasNum aliases st.base.nextVreg = st.base.nextVreg := by
      apply chaseF_none
      rw [Array.getElem?_eq_none bounded]
      rfl
    refine ⟨[.extend (.vreg st.base.nextVreg .int) (.vreg nx .int) sg ty.width toB],st.base.nextVreg,ρ',rfl,?_,?_,?_,?_,?_,?_⟩
    · rw [typeEq,ofClif_bits]
      simp only [State.mark,LState.fresh,LState.emit]
      apply Array.ext'; simp
    · simp only [State.mark,LState.fresh,LState.emit]; omega
    · intro m member d defined
      simp only [List.mem_singleton] at member
      subst m
      rw [vdefs_extend',List.mem_singleton] at defined
      subst d
      simp only [State.mark,LState.fresh,LState.emit]; omega
    · exact execution
    · rw [fresh]; exact value
    · intro n outside
      apply kept
      rcases outside with before | after
      · omega
      · simp only [State.mark,LState.fresh,LState.emit] at after; omega
def extTerm (sg wide : Bool) : Nat := if wide then (if sg then 557 else 558) else (if sg then 555 else 556)
def extTarget (wide : Bool) : Nat := if wide then 64 else 32
def extPass (wide : Bool) : List CTy := if wide then [.int 64] else [.int 32,.int 64]

/-- Every successful actual zero/sign-extension helper selection establishes
its mapped original value, complete fragment and fresh-write bounds. Type,
request and shape receipts are derived internally from the actual execution. -/
theorem stock_ext_helper_values {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (sg wide : Bool) {n x : Nat} (enough : 60 ≤ n)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {ty : Clif.Ty} {bits : BitVec ty.width}
    (source : fr.getAs x ty = .ok bits) {st next : State} {tr trace : Array RuleId} {out : V}
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k)))
    (run : ApplyInternal p (Stock.sem ctx) {} n 27 (extTerm sg wide) [.value x] (st,tr) out (next,trace)) :
    ExtValueOut F isem sg (extTarget wide) ty bits st next out aliases ρ := by
  have shape : MappedExtOut ctx x sg (extTarget wide) (extPass wide) st next out := by
    cases wide <;> cases sg
    · exact stock_zext32_out hp rfl enough run
    · exact stock_sext32_out hp rfl enough run
    · exact stock_zext64_out hp rfl enough run
    · exact stock_sext64_out hp rfl enough run
  apply stock_ext_values inv refines (by cases wide <;> simp [extTarget])
    (pass := extPass wide) ?_ ?_ dfg source bounded extent held shape
  · intro t member
    cases wide <;> simp only [extPass,extTarget,Bool.false_eq_true,ite_false,ite_true] at *
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> simp
    · exact Or.inl (List.mem_singleton.mp member)
  · intro small
    cases wide
    · simp [extPass]
    · change 64 = 32 at small; cases small

end Backend.Stock.Proof.ScalarShift
