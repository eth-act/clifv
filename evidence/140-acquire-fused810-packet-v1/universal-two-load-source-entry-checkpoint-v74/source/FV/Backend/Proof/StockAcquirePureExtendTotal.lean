import FV.Backend.Proof.StockAcquirePriorPendingEffects
import FV.Backend.Proof.StockExtendValues

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Legal extension forms execute for arbitrary machine values without a future source outcome.
The ordinary semantic hypothesis preserves the world and every register except the real destination. -/
theorem pure_extend_total {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {signed : Bool} {fromB toB dest pointer : Nat}
    (sourceWidth : fromB = 8 ∨ fromB = 16 ∨ fromB = 32)
    (targetWidth : toB = 32 ∨ toB = 64) (grows : fromB < toB) (regs : Nat → CV) :
    ∃ nextRegs,PRun F isem [MInst.extend (.vreg dest .int) (.vreg pointer .int) signed fromB toB] regs nextRegs ∧
      ∀ key,key ≠ dest → nextRegs key = regs key := by
  let value := ofX (if signed then (((lo64 (regs pointer)).setWidth fromB).signExtend toB).setWidth 64
    else (((lo64 (regs pointer)).setWidth fromB).setWidth toB).setWidth 64)
  refine ⟨upd regs dest value,?_,?_⟩
  · intro world
    obtain ⟨nextWorld,executed,same⟩ := refines _ _ _ _ _
      (ispec_extend (d := dest) (rn := .vreg pointer .int) (sg := signed) (x := regs pointer)
        (w := world) sourceWidth targetWidth grows)
    refine ⟨nextWorld,?_,same⟩
    simp only [seqRun,operands_extend']
    have uses : vuses #[⟨dest,.int,.def,.late,.reg⟩,⟨pointer,.int,.use,.early,.reg⟩] regs = [regs pointer] := rfl
    rw [uses,executed]
    rfl
  · intro key different
    simp only [upd,different,ite_false]

/-- Actual mapped extension shape derives a total fragment for every alias array and machine register file.
No source frame, successful later instruction, or new source admission is required. -/
theorem stock_ext_shape_total {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {signed : Bool} {toB : Nat} (target : toB = 32 ∨ toB = 64) {pass : List CTy}
    (passes32 : toB = 32 → .int 32 ∈ pass)
    {x : Nat} {st next : State} {out : V}
    (shape : ScalarShift.MappedExtOut ctx x signed toB pass st next out) :
    ∃ fragment : List MInst,
      next.base.emitted = st.base.emitted++fragment.toArray ∧
      ∀ (aliases : Array (Option Nat)) (regs : Nat → CV),∃ nextRegs,
        PRun F isem (fragment.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) regs nextRegs ∧
        ∀ key,(∀ inst ∈ fragment.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))),key ∉ vdefs inst) →
          nextRegs key = regs key := by
  obtain ⟨ty,typed,safe,rx,mapped,form⟩ := shape
  obtain ⟨pointer,rfl⟩ := inv.valueReg x rx mapped
  rcases form with ⟨passes,rfl,rfl⟩ | ⟨notPass,width,rfl,rfl⟩
  · refine ⟨[],?_,?_⟩
    · simp [State.mark]
    · intro aliases regs
      exact ⟨regs,prun_nil _,fun _ _ => rfl⟩
  · have types : ty = .int 8 ∨ ty = .int 16 ∨ ty = .int 32 ∨ ty = .int 64 := by
      simpa only [eCTys,List.mem_cons,List.not_mem_nil,or_false] using inv.valTyE x ty typed
    have sourceWidth : ty.bits = 8 ∨ ty.bits = 16 ∨ ty.bits = 32 := by
      rcases types with rfl | rfl | rfl | rfl <;> simp [CTy.bits] at width ⊢
    have grows : ty.bits < toB := by
      rcases target with rfl | rfl
      · have forbidden := passes32 rfl
        rcases types with rfl | rfl | rfl | rfl <;> simp [CTy.bits] at width ⊢
        exact False.elim (notPass forbidden)
      · omega
    let instruction := MInst.extend (.vreg st.base.nextVreg .int) (.vreg pointer .int) signed ty.bits toB
    refine ⟨[instruction],?_,?_⟩
    · simp only [State.mark,LState.fresh,LState.emit,instruction]
      apply Array.ext'
      simp
    · intro aliases regs
      let dest := aliasNum aliases st.base.nextVreg
      let use := aliasNum aliases pointer
      have code : instruction.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
          .extend (.vreg dest .int) (.vreg use .int) signed ty.bits toB := by
        change MInst.extend (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg st.base.nextVreg .int))
          (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg pointer .int)) signed ty.bits toB = _
        rw [resolve_vreg,resolve_vreg]
        rfl
      obtain ⟨nextRegs,executed,kept⟩ := pure_extend_total refines sourceWidth target grows (dest := dest) (pointer := use) regs
      refine ⟨nextRegs,?_,?_⟩
      · simpa only [List.map_cons,List.map_nil,code] using executed
      · intro key outside
        apply kept key
        intro equal
        apply outside _ (List.mem_cons_self ..)
        change key ∈ vdefs (instruction.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))
        rw [code]
        subst key
        rw [vdefs_extend']
        exact List.mem_singleton_self _

end Backend.Stock.Proof.Acquire810
