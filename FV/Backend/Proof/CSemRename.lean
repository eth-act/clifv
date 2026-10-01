import FV.Backend.Proof.RegallocCSem
import FV.Backend.Proof.LowerRename

/-!
# `ispec` and `csemWF` do not depend on vreg names

For a `VRenaming g`, `ispec (i.mapRegs g) = ispec i` and `csemWF ctx (i.mapRegs g) = csemWF ctx i`:
both only test registers for being `xzr`/a vreg of a class (and `defOut` only for being a vreg).
Proof: split every register into renamed vreg / fixed real register, the uses into their
shapes, the enumerations the patterns test, and compute.
-/

namespace Backend.Proof

open Backend Backend.Proof.Driver

variable {g : Reg → Reg} {gn : Nat → Nat}

theorem reg_cases (hg : VRenaming g gn) (r : Reg) :
    (∃ n c, r = .vreg n c ∧ g r = .vreg (gn n) c) ∨ g r = r := by
  cases r with
  | vreg n c => exact .inl ⟨n, c, rfl, hg.vreg n c⟩
  | _ => exact .inr (hg.real _ (by simp))

/-- Split a register into a renamed vreg or a fixed real register. -/
syntax "rg " ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rg $r) => `(tactic| (cases $r:ident <;> first | rw [hg.vreg] | rw [hg.real _ (by simp)]))

/-- Split the uses into the lengths `ispec` distinguishes. -/
syntax "us_cases" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| us_cases) => `(tactic| (rcases us with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩))

variable (hg : VRenaming g gn) (us : List CV) (w : Arm.ArmState)
include hg

/-- Close by computation, splitting the enumerations the patterns test when needed. -/
syntax "ren_fin" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| ren_fin) => `(tactic| (us_cases <;> first
      | rfl
      | (cases op <;> first | rfl | (cases sz <;> rfl))
      | (cases sz <;> rfl)))

set_option maxHeartbeats 4000000 in
theorem ispec_mapRegs (i : MInst) : ispec (i.mapRegs g) us w = ispec i us w := by
  cases i with
  | aluRRR op sz rd rn rm => simp only [MInst.mapRegs]; rg rd <;> rg rn <;> rg rm <;> ren_fin
  | aluRRRR op sz rd rn rm ra =>
    simp only [MInst.mapRegs]; rg rd <;> rg rn <;> rg rm <;> rg ra <;> ren_fin
  | aluRRImm12 op sz rd rn imm => simp only [MInst.mapRegs]; rg rd <;> rg rn <;> ren_fin
  | aluRRImmLogic op sz rd rn imm => simp only [MInst.mapRegs]; rg rd <;> rg rn <;> ren_fin
  | aluRRImmShift op sz rd rn imm => simp only [MInst.mapRegs]; rg rd <;> rg rn <;> ren_fin
  | aluRRRShift op sz rd rn rm sh =>
    simp only [MInst.mapRegs]; rg rd <;> rg rn <;> rg rm <;> ren_fin
  | aluRRRExtend op sz rd rn rm e =>
    simp only [MInst.mapRegs]; rg rd <;> rg rn <;> rg rm <;> ren_fin
  | bitRR op sz rd rn => simp only [MInst.mapRegs]; rg rd <;> rg rn <;> ren_fin
  | movWide op rd imm sz => simp only [MInst.mapRegs]; rg rd <;> ren_fin
  | movK rd rn imm sz => simp only [MInst.mapRegs]; rg rd <;> rg rn <;> ren_fin
  | extend rd rn sg fb tb =>
    simp only [MInst.mapRegs]; rg rd <;> rg rn <;> us_cases <;> (by_cases h1 : fb = 8 <;> by_cases h2 : tb = 16) <;>
      (try subst h1) <;> (try subst h2) <;> first | rfl | simp [ispec, defOut, *]
  | bitfieldMove sz op rd rn immr imms => simp only [MInst.mapRegs]; rg rd <;> rg rn <;> ren_fin
  | cset rd c => simp only [MInst.mapRegs]; rg rd <;> ren_fin
  | csetm rd c => simp only [MInst.mapRegs]; rg rd <;> ren_fin
  | csel rd rn rm c => simp only [MInst.mapRegs]; rg rd <;> rg rn <;> rg rm <;> ren_fin
  | ccmp sz rn rm nzcv c => simp only [MInst.mapRegs]; rg rn <;> rg rm <;> ren_fin
  | ccmpImm sz rn imm nzcv c => simp only [MInst.mapRegs]; rg rn <;> ren_fin
  | movToFpu rd rn sz => simp only [MInst.mapRegs]; rg rd <;> rg rn <;> ren_fin
  | movFromVec rd rn idx sz => simp only [MInst.mapRegs]; rg rd <;> rg rn <;> ren_fin
  | vecMisc op rd rn sz => simp only [MInst.mapRegs]; rg rd <;> rg rn <;> ren_fin
  | vecLanes op rd rn sz => simp only [MInst.mapRegs]; rg rd <;> rg rn <;> ren_fin
  | vecRRR op rd rn rm sz => simp only [MInst.mapRegs]; rg rd <;> rg rn <;> rg rm <;> ren_fin
  | load op rd m fl => simp only [MInst.mapRegs]; us_cases <;> rfl
  | store op rd m fl => simp only [MInst.mapRegs]; us_cases <;> rfl
  | mov sz rd rm => simp only [MInst.mapRegs]; us_cases <;> rfl
  | loadAddr rd m => simp only [MInst.mapRegs]; us_cases <;> rfl
  | condBr a b k => simp only [MInst.mapRegs]; cases k <;> us_cases <;> rfl
  | trapIf k c => simp only [MInst.mapRegs]; cases k <;> us_cases <;> rfl
  | _ => (try simp only [MInst.mapRegs]) <;> us_cases <;> rfl

end Backend.Proof

namespace Backend.Proof
open Backend Backend.Proof.Driver
variable {g : Reg → Reg} {gn : Nat → Nat}

/-- Split a register into a renamed vreg (with its class) or a fixed real register. -/
syntax "rgc " ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rgc $r) => `(tactic| (rg $r <;> try cases ‹RegClass›))

theorem memOk_mapRegs (hg : VRenaming g gn) (b : Nat) (m : AMode) :
    memOk b (m.mapRegs g) = memOk b m := by
  cases m with
  | regReg a c => simp only [AMode.mapRegs]; rgc a <;> rgc c <;> rfl
  | regScaled a c => simp only [AMode.mapRegs]; rgc a <;> rgc c <;> rfl
  | regScaledExtended a c e => simp only [AMode.mapRegs]; rgc a <;> rgc c <;> rfl
  | regExtended a c e => simp only [AMode.mapRegs]; rgc a <;> rgc c <;> rfl
  | unscaled a o => simp only [AMode.mapRegs]; rgc a <;> rfl
  | unsignedOffset a o => simp only [AMode.mapRegs]; rgc a <;> rfl
  | regOffset a o => simp only [AMode.mapRegs]; rgc a <;> rfl
  | _ => rfl

set_option maxHeartbeats 4000000 in
theorem formOk_mapRegs (hg : VRenaming g gn) (ctx : FnCtx) (i : MInst) :
    FormOk ctx (i.mapRegs g) = FormOk ctx i := by
  cases i with
  | aluRRR op sz rd rn rm => simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rgc rm <;> rfl
  | aluRRRR op sz rd rn rm ra =>
    simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rgc rm <;> rgc ra <;> rfl
  | aluRRImm12 op sz rd rn imm => simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rfl
  | aluRRImmLogic op sz rd rn imm => simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rfl
  | aluRRImmShift op sz rd rn imm => simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rfl
  | aluRRRShift op sz rd rn rm sh =>
    simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rgc rm <;> rfl
  | aluRRRExtend op sz rd rn rm e =>
    simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rgc rm <;> rfl
  | bitRR op sz rd rn => simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rfl
  | mov sz rd rn => simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rfl
  | movWide op rd imm sz => simp only [MInst.mapRegs]; rgc rd <;> rfl
  | movK rd rn imm sz => simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rfl
  | extend rd rn sg fb tb => simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rfl
  | bitfieldMove sz op rd rn immr imms => simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rfl
  | cset rd c => simp only [MInst.mapRegs]; rgc rd <;> rfl
  | csel rd rn rm c => simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rgc rm <;> rfl
  | ccmp sz rn rm nzcv c => simp only [MInst.mapRegs]; rgc rn <;> rgc rm <;> rfl
  | ccmpImm sz rn imm nzcv c => simp only [MInst.mapRegs]; rgc rn <;> rfl
  | movToFpu rd rn sz => simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rfl
  | movFromVec rd rn idx sz => simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rfl
  | vecMisc op rd rn sz => simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rfl
  | vecLanes op rd rn sz => simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rfl
  | vecRRR op rd rn rm sz => simp only [MInst.mapRegs]; rgc rd <;> rgc rn <;> rgc rm <;> rfl
  | load op rd m fl =>
    simp only [MInst.mapRegs]; rgc rd <;> simp only [FormOk, memOk_mapRegs hg]
  | store op rd m fl =>
    simp only [MInst.mapRegs]; rgc rd <;> simp only [FormOk, memOk_mapRegs hg]
  | loadAddr rd m => simp only [MInst.mapRegs]; rgc rd <;> cases m <;> rfl
  | csetm rd c => simp only [MInst.mapRegs]; rgc rd <;> rfl
  | loadAcquire ty rt rn fl => simp only [MInst.mapRegs]; rgc rt <;> rgc rn <;> rfl
  | storeRelease ty rt rn fl => simp only [MInst.mapRegs]; rgc rt <;> rgc rn <;> rfl
  | _ => (try simp only [MInst.mapRegs]) <;> rfl

theorem useCount_rn (ops : Array Operand) : useCount (ops.map (rnOp gn)) = useCount ops := by
  simp only [useCount, Array.toList_map, List.filter_map, List.length_map]
  rfl

theorem csemWF_mapRegs (hg : VRenaming g gn) (ctx : FnCtx) (i : MInst) (us : List CV) :
    csemWF ctx (i.mapRegs g) us = csemWF ctx i us := by
  unfold csemWF
  rw [formOk_mapRegs hg, operands_mapRegs hg]
  cases i.operands with
  | error e => rfl
  | ok ops => simp only [Except.map, useCount_rn]

theorem amodeAddr_mapRegs (hg : VRenaming g gn) (sb : Nat) (m : AMode) (b : Nat) (us : List CV)
    (w : Arm.ArmState) : amodeAddr sb (m.mapRegs g) b us w = amodeAddr sb m b us w := by
  cases m with
  | regReg a c => simp only [AMode.mapRegs]; rgc a <;> rgc c <;> us_cases <;> rfl
  | regScaled a c => simp only [AMode.mapRegs]; rgc a <;> rgc c <;> us_cases <;> rfl
  | regScaledExtended a c e => simp only [AMode.mapRegs]; rgc a <;> rgc c <;> us_cases <;> rfl
  | regExtended a c e => simp only [AMode.mapRegs]; rgc a <;> rgc c <;> us_cases <;> rfl
  | unscaled a o => simp only [AMode.mapRegs]; rgc a <;> us_cases <;> rfl
  | unsignedOffset a o => simp only [AMode.mapRegs]; rgc a <;> us_cases <;> rfl
  | regOffset a o => simp only [AMode.mapRegs]; rgc a <;> us_cases <;> rfl
  | _ => rfl

theorem mspec_other (sb : Nat) {i : MInst} (h : ∀ op rd am fl, i ≠ .load op rd am fl)
    (h2 : ∀ op rd am fl, i ≠ .store op rd am fl) (h3 : ∀ rd am, i ≠ .loadAddr rd am)
    (h4 : ∀ ty rt rn fl, i ≠ .loadAcquire ty rt rn fl)
    (h5 : ∀ ty rt rn fl, i ≠ .storeRelease ty rt rn fl) (us : List CV)
    (w : Arm.ArmState) : mspec sb i us w = ispec i us w := by
  unfold mspec
  split
  · exact absurd rfl (h _ _ _ _)
  · exact absurd rfl (h2 _ _ _ _)
  · exact absurd rfl (h3 _ _)
  · exact absurd rfl (h4 _ _ _ _)
  · exact absurd rfl (h5 _ _ _ _)
  · rfl

theorem mspec_mapRegs (hg : VRenaming g gn) (sb : Nat) (i : MInst) (us : List CV) (w : Arm.ArmState) :
    mspec sb (i.mapRegs g) us w = mspec sb i us w := by
  cases i with
  | load op rd am fl =>
    simp only [MInst.mapRegs]; rgc rd <;> first | rfl | simp only [mspec, amodeAddr_mapRegs hg]
  | store op rd am fl =>
    simp only [MInst.mapRegs]; rgc rd <;> us_cases <;> first | rfl | simp only [mspec, amodeAddr_mapRegs hg]
  | loadAddr rd am =>
    simp only [MInst.mapRegs]; rgc rd <;> cases am <;> us_cases <;> first | rfl | simp only [AMode.mapRegs]
  | loadAcquire ty rt rn fl =>
    simp only [MInst.mapRegs]; rgc rt <;> rgc rn <;> us_cases <;> rfl
  | storeRelease ty rt rn fl =>
    simp only [MInst.mapRegs]; rgc rt <;> rgc rn <;> us_cases <;> rfl
  | _ =>
    rw [mspec_other, mspec_other, ispec_mapRegs hg] <;>
      (try simp only [MInst.mapRegs]) <;> (intros; exact fun h => by cases h)

end Backend.Proof
