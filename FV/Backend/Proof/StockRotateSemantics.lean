import FV.Backend.Proof.IselFamAluBRot
import FV.Backend.Proof.StockRotateMath
import FV.Backend.Proof.StockAliasSemantics
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem fresh_reg {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int) = .vreg d .int := by
  rw [resolve_vreg]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none; rw [Array.getElem?_eq_none bounded]; rfl
  change Reg.vreg (aliasNum aliases d) .int = _
  rw [fresh]
def rotateWideCode (left : Bool) (sz : OperandSize) (d x y : Nat) : List MInst :=
  if left then
    [.aluRRR .sub sz (.vreg d .int) .xzr (.vreg y .int),
     .aluRRR .extr sz (.vreg (d+1) .int) (.vreg x .int) (.vreg d .int)]
  else [.aluRRR .extr sz (.vreg d .int) (.vreg x .int) (.vreg y .int)]
def rotateWideResult (left : Bool) (d : Nat) : Nat := if left then d+1 else d
def rotateWideAlloc (left : Bool) : Nat := if left then 2 else 1
def rotateWideBits {w : Nat} (left : Bool) (u : BitVec w) (amount : Nat) : BitVec w :=
  if left then u.rotateLeft (amount % w) else u.rotateRight (amount % w)
/-- Wide rotate templates read original values through final aliases and
preserve registers outside their allocation. Left rotation protects its source
from the preliminary count-negation write; retained source availability will
supply this internal noninterference fact. -/
theorem stock_rotate_wide_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (left : Bool) (sz : OperandSize)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d x y : Nat}
    (bounded : aliases.size ≤ d) (protectedX : left = true → aliasNum aliases x ≠ d)
    {u : BitVec sz.bits} (heldX : (ρ (aliasNum aliases x)).setWidth sz.bits = u)
    {amount : Clif.Val} (heldY : VHolds amount (ρ (aliasNum aliases y))) :
    ∃ ρ', PRun F isem ((rotateWideCode left sz d x y).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      (ρ' (rotateWideResult left d)).setWidth sz.bits = rotateWideBits left u amount.bits.toNat ∧
      ∀ n,n < d ∨ d+rotateWideAlloc left ≤ n → ρ' n = ρ n := by
  have ha := amt_of_holds (IW_bits sz) heldY
  cases left
  · let r := resX sz ((opnd sz (ρ (aliasNum aliases x))).rotateRight
        ((opnd sz (ρ (aliasNum aliases y))).toNat % sz.bits))
    refine ⟨upd ρ d r,?_,?_,?_⟩
    · simp only [rotateWideCode,Bool.false_eq_true,ite_false,List.map_cons,List.map_nil,MInst.mapRegs]
      rw [fresh_reg bounded,resolve_vreg,resolve_vreg]
      exact prun_rrr refines (operands_aluRRR _ _ _ _ _) (fun _ => ispec_rrr_extr_fb) (prun_nil _)
    · simp only [rotateWideResult,rotateWideBits,Bool.false_eq_true,ite_false,upd_same]
      exact (rot_fin sz _ _ _ ha).trans (congrArg (fun v => v.rotateRight (amount.bits.toNat % sz.bits)) heldX)
    · intro n outside
      simp only [rotateWideAlloc,Bool.false_eq_true,ite_false] at outside
      simp only [upd,show n ≠ d by omega,ite_false]
  · let r0 := resX sz (0 - opnd sz (ρ (aliasNum aliases y)))
    let mid := upd ρ d r0
    let r1 := resX sz ((opnd sz (mid (aliasNum aliases x))).rotateRight ((opnd sz (mid d)).toNat % sz.bits))
    refine ⟨upd mid (d+1) r1,?_,?_,?_⟩
    · simp only [rotateWideCode,ite_true,List.map_cons,List.map_nil,MInst.mapRegs]
      rw [fresh_reg bounded,fresh_reg (by omega : aliases.size ≤ d+1),
        resolve_vreg,resolve_vreg]
      have zero : Backend.lowerFunction.resolve aliases (aliases.size+1) Reg.xzr = Reg.xzr := rfl
      rw [zero]
      have negSpec : ∀ world,ispec (.aluRRR .sub sz (.vreg d .int) .xzr (.vreg (aliasNum aliases y) .int))
          [ρ (aliasNum aliases y)] world = some ([r0],world,.next) := by
        intro world; cases sz <;> rfl
      exact prun_rr refines rfl negSpec
        (prun_rrr refines (operands_aluRRR _ _ _ _ _) (fun _ => ispec_rrr_extr_fb) (prun_nil _))
    · simp only [rotateWideResult,rotateWideBits,ite_true,upd_same]
      change r1.setWidth sz.bits = _
      dsimp only [r1,mid]
      rw [upd_same,upd_ne_fb (protectedX rfl)]
      exact (rotl_fin sz _ _ _ ha).trans (congrArg (fun v => v.rotateLeft (amount.bits.toNat % sz.bits)) heldX)
    · intro n outside
      simp only [rotateWideAlloc,ite_true] at outside
      simp only [mid,upd,show n ≠ d by omega,show n ≠ d+1 by omega,ite_false]
/-- Pure narrow right-rotation code with preservation outside its complete
allocation interval, including already available later fresh producers. -/
def NarrowRotateRun (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem)
    (w xv a : Nat) (st st' : LState) (v : V) : Prop :=
  ∃ ms d,v = .reg (.vreg d .int) ∧ CodeShapeU st st' ms d [xv,a] ∧
    ∀ ρ,∃ ρ',PRun F isem ms ρ ρ' ∧
      (∀ z,z < st.nextVreg ∨ st'.nextVreg ≤ z → ρ' z = ρ z) ∧
      ∀ u : BitVec w,opnd .size32 (ρ xv) = u.setWidth 32 →
        (ρ' d).setWidth w = u.rotateRight ((ρ a).toNat % w)
theorem stock_small_rotate_run {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (hR : Refines F isem) {w : Nat} (hw : w = 8 ∨ w = 16) {imm : Imm12}
    (himm : imm.value = w) (hib : imm.bits < 4096) {xv a : Nat} {st st' : LState}
    (protectedX : xv < st.nextVreg ∨ st.nextVreg+6 ≤ xv)
    (hem : st'.emitted = st.emitted ++
      [MInst.aluRRImmLogic .and .size32 (.vreg st.nextVreg .int) (.vreg a .int) ⟨w - 1, .size32⟩,
       .aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 1) .int) (.vreg st.nextVreg .int) imm,
       .aluRRR .sub .size32 (.vreg (st.nextVreg + 2) .int) .xzr (.vreg (st.nextVreg + 1) .int),
       .aluRRR .lsr .size32 (.vreg (st.nextVreg + 3) .int) (.vreg xv .int) (.vreg st.nextVreg .int),
       .aluRRR .lsl .size32 (.vreg (st.nextVreg + 4) .int) (.vreg xv .int)
         (.vreg (st.nextVreg + 2) .int),
       .aluRRR .orr .size32 (.vreg (st.nextVreg + 5) .int) (.vreg (st.nextVreg + 4) .int)
         (.vreg (st.nextVreg + 3) .int)].toArray)
    (hnx : st'.nextVreg = st.nextVreg + 6) :
    NarrowRotateRun F isem w xv a st st' (.reg (.vreg (st.nextVreg + 5) .int)) := by
  have hW : IW w := by rcases hw with rfl | rfl <;> simp [IW]
  have hi : ImmLogic.ofNat? (w - 1) .size32 = some ⟨w - 1, .size32⟩ := by
    rcases hw with rfl | rfl <;> rfl
  refine ⟨_, _, rfl, codeShapeU_of hem hnx (by omega) (by code_facts_fb) (by code_facts_fb),
    fun ρ => ⟨_, prun_rr hR rfl (fun w => ispec_and_imm_fb hi)
      (prun_rr hR rfl (fun w => ispec_sub_imm_fb hib)
      (prun_rr hR rfl (fun w => ispec_sub_xzr_fb)
      (prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun w => ispec_rrr_shift_fb (.inr (.inl rfl)))
      (prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun w => ispec_rrr_shift_fb (.inl rfl))
      (prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun w => ispec_orr_fb) (prun_nil _)))))), ?_, ?_⟩⟩
  · intro z hz
    have h0 : z ≠ st.nextVreg := by omega
    have h1 : z ≠ st.nextVreg + 1 := by omega
    have h2 : z ≠ st.nextVreg + 2 := by omega
    have h3 : z ≠ st.nextVreg + 3 := by omega
    have h4 : z ≠ st.nextVreg + 4 := by omega
    have h5 : z ≠ st.nextVreg + 5 := by omega
    simp only [upd, h0, h1, h2, h3, h4, h5, ↓reduceIte]
  · intro u hu
    have hMlt : (ρ a).toNat % w < w := Nat.mod_lt _ hW.pos
    simp (disch := omega) only [upd_ne_fb, upd_same, opnd_resX, shiftF, hu]
    rw [setWidth_resX32 (by omega)]
    have hA := (small_rot_amt hw (opnd .size32 (ρ a))).trans (opnd_mod hW .size32 (ρ a))
    generalize opnd .size32 (ρ a) = A at hA ⊢
    revert A
    show ∀ A : BitVec 32, (A &&& BitVec.ofNat 32 (w - 1)).toNat = (ρ a).toNat % w →
      BitVec.setWidth w (BitVec.setWidth 32 u <<<
        ((0 - ((A &&& BitVec.ofNat 32 (w - 1)) - BitVec.ofNat 32 imm.value)).toNat % 32) |||
        BitVec.setWidth 32 u >>> ((A &&& BitVec.ofNat 32 (w - 1)).toNat % 32)) =
      u.rotateRight ((ρ a).toNat % w)
    intro A hA
    have hN := stock_small_rotate_neg hw _ (by rw [hA]; exact hMlt)
    rw [himm, hN, hA, Nat.mod_eq_of_lt (show w - (ρ a).toNat % w < 32 by omega),
      Nat.mod_eq_of_lt (show (ρ a).toNat % w < 32 by omega)]
    exact small_rot_fin hw u hMlt

/-- Immediate narrow rotation preserves all registers outside its three
fresh writes, including later producers above the allocation interval. -/
def NarrowRotateImmRun (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem)
    (w xv n : Nat) (st st' : LState) (v : V) : Prop :=
  ∃ ms d,v = .reg (.vreg d .int) ∧ CodeShapeU st st' ms d [xv] ∧
    ∀ ρ,∃ ρ',PRun F isem ms ρ ρ' ∧
      (∀ z,z < st.nextVreg ∨ st'.nextVreg ≤ z → ρ' z = ρ z) ∧
      ∀ u : BitVec w,opnd .size32 (ρ xv) = u.setWidth 32 →
        (ρ' d).setWidth w = u.rotateRight n
theorem stock_small_rotate_imm_run {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (hR : Refines F isem) {w : Nat} (hw : w = 8 ∨ w = 16) {n : Nat}
    (hn : n < w) {xv : Nat} {st st' : LState} (protectedX : xv < st.nextVreg ∨ st.nextVreg+3 ≤ xv)
    (hem : st'.emitted = st.emitted ++
      [MInst.aluRRImmShift .lsr .size32 (.vreg st.nextVreg .int) (.vreg xv .int) n,
       .aluRRImmShift .lsl .size32 (.vreg (st.nextVreg + 1) .int) (.vreg xv .int)
         (w - Nat.land n (w - 1)),
       .aluRRR .orr .size32 (.vreg (st.nextVreg + 2) .int) (.vreg (st.nextVreg + 1) .int)
         (.vreg st.nextVreg .int)].toArray)
    (hnx : st'.nextVreg = st.nextVreg + 3) :
    NarrowRotateImmRun F isem w xv n st st' (.reg (.vreg (st.nextVreg + 2) .int)) := by
  have hW : IW w := by rcases hw with rfl | rfl <;> simp [IW]
  have hL : Nat.land n (w - 1) = n := by rw [land_mask_mod hW, Nat.mod_eq_of_lt hn]
  rw [hL] at hem
  refine ⟨_, _, rfl, codeShapeU_of hem hnx (by omega) (by code_facts_fb) (by code_facts_fb),
    fun ρ => ⟨_, prun_rr hR rfl (fun _ => ispec_imm_shift_fb (.inr (.inl rfl))
        (show n < OperandSize.size32.bits by simp [OperandSize.bits]; omega))
      (prun_rr hR rfl (fun _ => ispec_imm_shift_fb (.inl rfl)
        (show w - n < OperandSize.size32.bits by simp [OperandSize.bits]; omega))
      (prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun _ => ispec_orr_fb) (prun_nil _))), ?_, ?_⟩⟩
  · intro z hz
    have h0 : z ≠ st.nextVreg := by omega
    have h1 : z ≠ st.nextVreg + 1 := by omega
    have h2 : z ≠ st.nextVreg + 2 := by omega
    simp only [upd, h0, h1, h2, ↓reduceIte]
  · intro u hu
    simp (disch := omega) only [upd_ne_fb, upd_same, opnd_resX, shiftF, hu]
    rw [setWidth_resX32 (by omega)]
    exact small_rot_fin hw u hn

def rotateImmediate (left : Bool) (w n : Nat) : Nat :=
  if left then (w-n)%w else n
/-- Wide immediate rotations execute through final aliases; count negation
for the left direction is modulo the physical/source width. -/
theorem stock_rotate_wide_imm_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (left : Bool) (sz : OperandSize) {n : Nat} (count : n < sz.bits)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d x : Nat} (bounded : aliases.size ≤ d)
    {u : BitVec sz.bits} (held : (ρ (aliasNum aliases x)).setWidth sz.bits = u) :
    ∃ ρ',PRun F isem
      [(MInst.aluRRImmShift .extr sz (.vreg d .int) (.vreg x .int) (rotateImmediate left sz.bits n)).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      (ρ' d).setWidth sz.bits = rotateWideBits left u n ∧ ∀ z,z ≠ d → ρ' z = ρ z := by
  have positive : 0 < sz.bits := by cases sz <;> decide
  have fits : rotateImmediate left sz.bits n < sz.bits := by
    cases left
    · exact count
    · exact Nat.mod_lt _ positive
  let r := resX sz ((opnd sz (ρ (aliasNum aliases x))).rotateRight (rotateImmediate left sz.bits n))
  refine ⟨upd ρ d r,?_,?_,?_⟩
  · simp only [MInst.mapRegs]
    rw [fresh_reg bounded,resolve_vreg]
    exact prun_rr refines rfl (fun _ => ispec_imm_extr_fb fits) (prun_nil _)
  · rw [upd_same]
    have value := (rot_imm_fin sz (ρ (aliasNum aliases x)) (rotateImmediate left sz.bits n)).trans
      (congrArg (fun v => v.rotateRight (rotateImmediate left sz.bits n)) held)
    change r.setWidth sz.bits = _
    apply value.trans
    cases left
    · simp only [rotateImmediate,rotateWideBits,Bool.false_eq_true,ite_false,Nat.mod_eq_of_lt count]
    · simp only [rotateImmediate,rotateWideBits,ite_true]
      apply rotr_neg positive
      simp only [Nat.mod_mod,Nat.mod_eq_of_lt count]
  · intro z different; simp only [upd,different,ite_false]
end Backend.Stock.Proof.ScalarRotate
