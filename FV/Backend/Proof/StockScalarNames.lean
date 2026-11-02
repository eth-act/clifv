import FV.Backend.Proof.StockLowerProgress
import FV.Backend.Lowering.StockScalar

/-!
# The scalar classifier admits only scalar statement names

Every statement of a function that `Scalar.productionEligible` accepts is a constant, unary,
binary, division, comparison, extension, reduction, selection, `bmask` or `nop` (`scalarInst`), so
its opcode and format names satisfy `ScalarNames`: no load format, no call, splat or return
opcode, and an extend opcode only on an extend.
-/

namespace Backend.Stock.Proof.LowerProjection
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The instruction kinds of the scalar classifier. -/
def scalarInst : Clif.Inst → Bool
  | .iconst .. | .unary .. | .binary .. | .div .. | .icmp .. | .extend .. | .ireduce .. | .select ..
  | .nop | .bmask .. => true
  | _ => false

/-- The names of a scalar instruction rule out the diverging rules of `lower`. -/
theorem scalarNames_of {cl : Clif.Inst} (h : scalarInst cl = true) : ScalarNames cl := by
  have names : ∀ n ∈ ["Call","CallIndirect","Splat","Return"], (instNames cl).2 ≠ n := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    cases cl <;> simp only [scalarInst, Bool.false_eq_true] at h
    case unary op _ _ => rcases hn with rfl | rfl | rfl | rfl <;> cases op <;> simp [instNames, unaryOpcode]
    case binary op _ _ _ =>
      rcases hn with rfl | rfl | rfl | rfl <;> cases op <;> simp [instNames, binaryOpcode]
    case div op _ _ _ => rcases hn with rfl | rfl | rfl | rfl <;> cases op <;> simp [instNames, divOpcode]
    case extend op _ _ => rcases hn with rfl | rfl | rfl | rfl <;> cases op <;> simp [instNames]
    all_goals rcases hn with rfl | rfl | rfl | rfl <;> simp [instNames]
  have extend : (instNames cl).2 = "Uextend" ∨ (instNames cl).2 = "Sextend" →
      ∃ sg ty x, cl = .extend (ScalarCast.extendOp sg) ty x := by
    intro hx
    cases cl <;> simp only [scalarInst, Bool.false_eq_true] at h
    case extend op ty x => exact ⟨op == .sextend, ty, x, by cases op <;> rfl⟩
    case unary op _ _ =>
      exfalso; rcases hx with hx | hx <;> cases op <;> simp [instNames, unaryOpcode] at hx
    case binary op _ _ _ =>
      exfalso; rcases hx with hx | hx <;> cases op <;> simp [instNames, binaryOpcode] at hx
    case div op _ _ _ =>
      exfalso; rcases hx with hx | hx <;> cases op <;> simp [instNames, divOpcode] at hx
    all_goals exfalso; rcases hx with hx | hx <;> simp [instNames] at hx
  refine ⟨?_, names, extend⟩
  cases cl <;> simp only [scalarInst, Bool.false_eq_true] at h <;> simp [instNames]

/-- Every statement of the widest scalar statement class is a scalar instruction. -/
theorem mask_scalar {stm : Clif.Stmt} (h : Scalar.maskMixedBodyEligible stm = true) :
    scalarInst stm.inst = true := by
  rcases stm with ⟨rs, inst⟩
  cases inst <;> first
    | rfl
    | (simp [Scalar.maskMixedBodyEligible, Scalar.narrowMixedBodyEligible,
        Scalar.generalDivBodyEligible, Scalar.highmulBodyEligible, Scalar.highmulEligible,
        Scalar.cmpBodyEligible, Scalar.cmpEligible, Scalar.minmaxBodyEligible, Scalar.minmaxEligible,
        Scalar.popcountBodyEligible, Scalar.popcountEligible, Scalar.bitBodyEligible,
        Scalar.bitEligible, Scalar.castBodyEligible, Scalar.castEligible, Scalar.shiftBodyEligible,
        Scalar.shiftEligible, Scalar.mulBodyEligible, Scalar.mulEligible,
        Scalar.extendedBodyEligible, Scalar.notEligible, Scalar.bodyEligible,
        Scalar.constantEligible, Logical.bodyEligible, Scalar.divisionBodyEligible,
        Scalar.narrowBodyEligible, Scalar.maskBodyEligible] at h)

private theorem highmul_scalar {stm : Clif.Stmt} (h : Scalar.highmulBodyEligible stm = true) :
    scalarInst stm.inst = true :=
  mask_scalar (by simp [Scalar.maskMixedBodyEligible, Scalar.narrowMixedBodyEligible,
    Scalar.generalDivBodyEligible, h])

private theorem returned_scalar {z : Nat} :
    ∀ {body : List Clif.Stmt}, Scalar.returnedDivBodyEligible body z = true →
      ∀ s ∈ body, scalarInst s.inst = true
  | [], h => by simp [Scalar.returnedDivBodyEligible] at h
  | stm :: rest, h => by
    intro s hs
    simp only [Scalar.returnedDivBodyEligible, Bool.or_eq_true, Bool.and_eq_true,
      List.all_eq_true] at h
    rcases List.mem_cons.mp hs with rfl | hs
    · rcases h with ⟨at_, -⟩ | ⟨hm, -⟩
      · rcases s with ⟨rs, inst⟩
        cases inst <;> first | rfl | (simp [Scalar.returnedDivAt] at at_; done) |
          (unfold Scalar.returnedDivAt at at_; split at at_ <;> simp_all)
      · exact highmul_scalar hm
    · rcases h with ⟨-, all⟩ | ⟨-, rest⟩
      · exact highmul_scalar (all s hs)
      · exact returned_scalar rest s hs

/-- **The scalar classifier admits only scalar statement names.** -/
theorem productionEligible_names {f : Clif.Function} (h : Scalar.productionEligible f = true) :
    ∀ cl, Prg.InstOf f cl → ScalarNames cl := by
  intro cl ⟨B, hB, s, hs, hcl⟩
  subst hcl
  apply scalarNames_of
  unfold Scalar.productionEligible at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · unfold Scalar.eligible at h
    split at h
    · rename_i b hb
      rw [hb, List.mem_singleton] at hB
      subst hB
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at h
      obtain ⟨⟨⟨body, -⟩, -⟩, -⟩ := h
      rcases body with (((all | single) | mixed) | returned) | general
      · exact highmul_scalar (all s hs)
      · unfold Scalar.singleDivEligible at single
        split at single
        · rename_i z ty x y z' shape _
          rw [shape, List.mem_singleton] at hs
          subst hs
          rfl
        · cases single
      · unfold Scalar.mixedDivEligible at mixed
        split at mixed
        · rename_i z op ty x y front z' shape _
          simp only [Bool.and_eq_true, List.all_eq_true] at mixed
          have hs' : s ∈ B.body.reverse := List.mem_reverse.mpr hs
          rw [shape] at hs'
          rcases List.mem_cons.mp hs' with rfl | hs'
          · rfl
          · exact highmul_scalar (mixed.2 s hs')
        · cases mixed
      · unfold Scalar.returnedDivEligible at returned
        split at returned
        · exact returned_scalar returned s hs
        · cases returned
      · simp only [Scalar.generalDivBodyEligible, Bool.or_eq_true] at general
        rcases general s hs with hm | hd
        · exact highmul_scalar hm
        · rcases s with ⟨rs, inst⟩
          cases inst <;> first | rfl | (simp [Scalar.divisionBodyEligible] at hd)
    · cases h
  · unfold Scalar.narrowEligible at h
    split at h
    · rename_i b hb
      rw [hb, List.mem_singleton] at hB
      subst hB
      simp only [Bool.and_eq_true, List.all_eq_true] at h
      exact mask_scalar (by simp [Scalar.maskMixedBodyEligible, h.1.1.1 s hs])
    · cases h
  · unfold Scalar.maskEligible at h
    split at h
    · rename_i b hb
      rw [hb, List.mem_singleton] at hB
      subst hB
      simp only [Bool.and_eq_true, List.all_eq_true] at h
      exact mask_scalar (h.1.1.1 s hs)
    · cases h

private def namesFixture : Clif.Function := {
  name := "stock_scalar_names"
  sig := { params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0, .i64), (1, .i64)], body := [⟨[2], .binary .iadd .i64 0 1⟩], term := .ret [2] }] }

/-- Non-vacuity: a real function is accepted by the scalar classifier, and its statements get
their names from `productionEligible_names`. -/
theorem productionEligible_names_witness :
    ∃ f : Clif.Function, Scalar.productionEligible f = true ∧ ∀ cl, Prg.InstOf f cl → ScalarNames cl :=
  have accepted : Scalar.productionEligible namesFixture = true := by decide
  ⟨namesFixture, accepted, productionEligible_names accepted⟩

end Backend.Stock.Proof.LowerProjection
