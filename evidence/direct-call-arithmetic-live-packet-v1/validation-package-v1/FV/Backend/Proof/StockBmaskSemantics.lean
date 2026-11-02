import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.IselAtomic

namespace Backend.Stock.Proof.ScalarMask
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def bmaskAlloc (wi : Nat) : Nat := if wi ≤ 16 then 2 else 1
def bmaskResultNum (wi d : Nat) : Nat := if wi ≤ 16 then d+1 else d
def bmaskCode (wi d x : Nat) : List MInst :=
  if wi ≤ 16 then
    [.aluRRImmLogic .and .size32 (.vreg d .int) (.vreg x .int) ⟨2^wi-1,.size32⟩,
     .aluRRImm12 .subS .size32 .xzr (.vreg d .int) ⟨0,false⟩,
     .csetm (.vreg (d+1) .int) .ne]
  else
    [.aluRRImm12 .subS (szOf wi) .xzr (.vreg x .int) ⟨0,false⟩,
     .csetm (.vreg d .int) .ne]

private theorem fresh_reg {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int) = .vreg d .int := by
  rw [resolve_vreg]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none; rw [Array.getElem?_eq_none bounded]; rfl
  change Reg.vreg (aliasNum aliases d) .int = _
  rw [fresh]

private theorem mapped_code (wi d x : Nat) (aliases : Array (Option Nat))
    (bounded : aliases.size ≤ d) :
    (bmaskCode wi d x).map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))) =
      bmaskCode wi d (aliasNum aliases x) := by
  unfold bmaskCode
  split
  all_goals simp only [List.map_cons,List.map_nil,MInst.mapRegs]
  all_goals rw [fresh_reg bounded]
  · rw [fresh_reg (by omega : aliases.size ≤ d+1),resolve_vreg]; rfl
  · rw [resolve_vreg]; rfl

/-- Every resolved write stays within the actual one- or two-register fresh
interval. This is the frame bound used for original-source value transfer. -/
theorem stock_bmask_defs {wi d x : Nat} {aliases : Array (Option Nat)}
    (bounded : aliases.size ≤ d) :
    ∀ m ∈ (bmaskCode wi d x).map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))),
      ∀ key ∈ vdefs m,d ≤ key ∧ key < d+bmaskAlloc wi := by
  rw [mapped_code wi d x aliases bounded]
  intro m member key defined
  unfold bmaskCode at member
  split at member
  · rename_i narrow
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change key ∈ [d] at defined
      simp only [List.mem_singleton] at defined
      subst key
      simp [bmaskAlloc,narrow]
    · rw [vdefs_cmpImm0'] at defined; cases defined
    · rw [vdefs_csetm] at defined
      simp only [List.mem_singleton] at defined
      subst key
      simp [bmaskAlloc,narrow]
  · rename_i wide
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · rw [vdefs_cmpImm0'] at defined; cases defined
    · rw [vdefs_csetm] at defined
      simp only [List.mem_singleton] at defined
      subst key
      simp [bmaskAlloc,wide]

/-- The real masked/unmasked templates execute through the final resolver,
hold the original source bmask value at its independent output type and retain
every register outside the exact fresh allocation interval. -/
theorem stock_bmask_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {wi : Nat} (input : wi = 8 ∨ wi = 16 ∨ wi = 32 ∨ wi = 64)
    {ty : Clif.Ty} (output : eTy ty = true) {value : Clif.Val}
    (inputType : CTy.ofClif value.ty = .int wi)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d x : Nat} (bounded : aliases.size ≤ d)
    (held : VHolds value (ρ (aliasNum aliases x))) (world : Arm.ArmState) :
    Runs F isem ((bmaskCode wi d x).map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
        VHolds ⟨ty,Clif.Sem.bmask value.bits⟩ (ρ' (bmaskResultNum wi d)) ∧
        ∀ n,n < d ∨ d+bmaskAlloc wi ≤ n → ρ' n = ρ n) := by
  rw [mapped_code wi d x aliases bounded]
  rcases input with rfl | rfl | rfl | rfl
  · have actual := runs_bmask_masked refines (2^8-1) rfl (aliasNum aliases x) d (d+1) ρ world
    change Runs F isem _ _ _ _
    simpa only [bmaskCode,bmaskResultNum,bmaskAlloc,show 8 ≤ 16 by decide,ite_true] using
      actual.imp (Q := fun ρ' _ =>
        VHolds ⟨ty,Clif.Sem.bmask value.bits⟩ (ρ' (d+1)) ∧
          ∀ n,n < d ∨ d+2 ≤ n → ρ' n = ρ n) (fun ρ' w' executed result => by
        refine ⟨?_,?_⟩
        · simp only [result,bmask_cond_816 (.inl rfl) inputType held]
          exact vholds_bmask output value.bits
        · intro n outside
          apply seqRun_fall_frame (sem := isem) _ executed
          intro m member
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl | rfl
          · change n ∉ [d]
            simp only [List.mem_singleton]
            omega
          · rw [vdefs_cmpImm0']; simp
          · rw [vdefs_csetm]
            simp only [List.mem_singleton]
            omega)
  · have actual := runs_bmask_masked refines (2^16-1) rfl (aliasNum aliases x) d (d+1) ρ world
    change Runs F isem _ _ _ _
    simpa only [bmaskCode,bmaskResultNum,bmaskAlloc,show 16 ≤ 16 by decide,ite_true] using
      actual.imp (Q := fun ρ' _ =>
        VHolds ⟨ty,Clif.Sem.bmask value.bits⟩ (ρ' (d+1)) ∧
          ∀ n,n < d ∨ d+2 ≤ n → ρ' n = ρ n) (fun ρ' w' executed result => by
        refine ⟨?_,?_⟩
        · simp only [result,bmask_cond_816 (.inr rfl) inputType held]
          exact vholds_bmask output value.bits
        · intro n outside
          apply seqRun_fall_frame (sem := isem) _ executed
          intro m member
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl | rfl
          · change n ∉ [d]
            simp only [List.mem_singleton]
            omega
          · rw [vdefs_cmpImm0']; simp
          · rw [vdefs_csetm]
            simp only [List.mem_singleton]
            omega)
  · have actual := runs_bmask refines (szOf 32) (aliasNum aliases x) d ρ world
    simpa only [bmaskCode,bmaskResultNum,bmaskAlloc,show ¬32 ≤ 16 by decide,ite_false] using
      actual.imp (Q := fun ρ' _ =>
        VHolds ⟨ty,Clif.Sem.bmask value.bits⟩ (ρ' (d)) ∧
          ∀ n,n < d ∨ d+1 ≤ n → ρ' n = ρ n) (fun ρ' w' executed result => by
        refine ⟨?_,?_⟩
        · simp only [result,bmask_cond_3264 (.inl rfl) inputType held]
          exact vholds_bmask output value.bits
        · intro n outside
          apply seqRun_fall_frame (sem := isem) _ executed
          intro m member
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl <;> simp [vdefs_cmpImm0',vdefs_csetm] <;> omega)
  · have actual := runs_bmask refines (szOf 64) (aliasNum aliases x) d ρ world
    simpa only [bmaskCode,bmaskResultNum,bmaskAlloc,show ¬64 ≤ 16 by decide,ite_false] using
      actual.imp (Q := fun ρ' _ =>
        VHolds ⟨ty,Clif.Sem.bmask value.bits⟩ (ρ' (d)) ∧
          ∀ n,n < d ∨ d+1 ≤ n → ρ' n = ρ n) (fun ρ' w' executed result => by
        refine ⟨?_,?_⟩
        · simp only [result,bmask_cond_3264 (.inr rfl) inputType held]
          exact vholds_bmask output value.bits
        · intro n outside
          apply seqRun_fall_frame (sem := isem) _ executed
          intro m member
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl <;> simp [vdefs_cmpImm0',vdefs_csetm] <;> omega)

end Backend.Stock.Proof.ScalarMask
