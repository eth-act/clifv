import FV.E2E.LinkArm
import FV.E2E.CallReturnPins
import FV.E2E.CompiledSemanticReturnPins

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The ABI result prefix uses the same physical registers as the proved machine return. -/
theorem ReturnPinMode.pins_prefix_of_valid {mode : ReturnPinMode} {f : Clif.Function}
    {us : List (Reg × Reg)} (valid : mode.Valid f us)
    (bound : (sigRets f.sig).length ≤ us.length) :
    mode.pins f (sigRets f.sig).length = (us.map (·.2)).take (sigRets f.sig).length := by
  cases mode with
  | ordinary =>
    change us.map (·.2) = (List.range us.length).map Reg.x at valid
    simp only [ReturnPinMode.pins,valid,← List.map_take,List.take_range,Nat.min_eq_left bound]
  | stockABI =>
    change Backend.Stock.Proof.returnPins f us.length = some (us.map (·.2)) at valid
    by_cases sret : (sigRets f.sig).any (·.purpose == .sret) = true
    · simp only [Backend.Stock.Proof.returnPins,sret,↓reduceIte,Option.some.injEq] at valid
      have positive : 0 < (sigRets f.sig).length := by
        obtain ⟨parameter,member,_⟩ := List.any_eq_true.mp sret
        exact List.length_pos_of_mem member
      simp only [ReturnPinMode.pins,Backend.Stock.Proof.returnPins,sret,↓reduceIte,Option.getD_some]
      rw [← valid]
      cases count : (sigRets f.sig).length with
      | zero => omega
      | succ n => simp
    · have absent : (sigRets f.sig).any (·.purpose == .sret) = false := Bool.eq_false_iff.mpr sret
      simp only [Backend.Stock.Proof.returnPins,absent,Bool.false_eq_true,↓reduceIte] at valid
      obtain ⟨within,equal⟩ := retRegs_eq valid
      have count : (sigRets f.sig).length ≤ 8 := Nat.le_trans bound within
      simp only [ReturnPinMode.pins,Backend.Stock.Proof.returnPins,absent,Bool.false_eq_true,↓reduceIte,
        retRegs,count,Option.getD_some,equal,← List.map_take,List.take_range,Nat.min_eq_left bound]

namespace LinkSys
variable (L : LinkSys)

open Classical in
/-- Read actual callee return pins from the same canonical linked call and unchanged guard. -/
noncomputable def progXWithPins (pins : Clif.Function → List Reg)
    (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop)
    (g : Clif.Function) (uses : List CV) (w : Arm.ArmState) : Option (List CV × Arm.ArmState) :=
  if L.Cond κ M F g uses w ∧ Arm.r .ERR (L.pcall M g (L.canon g uses w)) = .None then
    some ((pins g).map (regVal (L.pcall M g (L.canon g uses w))),
      L.pcall M g (L.canon g uses w))
  else none

/-- The previous linked-call model is exactly the ordinary-pin instance. -/
theorem progXWithPins_ordinary (κ : Nat → Clif.Function → Nat) (M : Nat)
    (F : BitVec 64 → Prop) (g : Clif.Function) (uses : List CV) (w : Arm.ArmState) :
    L.progXWithPins (fun f => (List.range (sigRets f.sig).length).map Reg.x) κ M F g uses w =
      L.progX κ M F g uses w := by
  simp only [progXWithPins,progX,List.map_map,Function.comp_def]

/-- A successful call keeps its actual linked world and returns its selected physical values. -/
theorem progXWithPins_some {pins : Clif.Function → List Reg} {κ : Nat → Clif.Function → Nat}
    {M : Nat} {F : BitVec 64 → Prop} {g : Clif.Function} {uses : List CV}
    {w next : Arm.ArmState} {values : List CV}
    (called : L.progXWithPins pins κ M F g uses w = some (values,next)) :
    next = L.pcall M g (L.canon g uses w) ∧ values = (pins g).map (regVal next) ∧
      L.Cond κ M F g uses w ∧ Arm.r .ERR next = .None := by
  classical
  unfold progXWithPins at called
  split at called
  next guard =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj called)
    exact ⟨rfl,rfl,guard.1,guard.2⟩
  next => cases called

/-- Actual return-pin agreement supplies every allocated result of the caller. -/
theorem progXWithPins_call_results {pins : Clif.Function → List Reg} {κ : Nat → Clif.Function → Nat}
    {M : Nat} {F : BitVec 64 → Prop} {g : Clif.Function} {uses : List CV}
    {w next actual : Arm.ArmState} {values : List CV}
    (called : L.progXWithPins pins κ M F g uses w = some (values,next))
    {definitions : List (Reg × Nat)} (matched : CallReturnPins definitions (pins g))
    {ops : Array Operand} {regs : Array Reg}
    (allocated : ((ops.zip regs).toList.filter (·.1.isDef)) =
      (callDefOps definitions).zip (definitions.map (·.1)))
    (same : ∀ pin ∈ pins g,regVal actual pin = regVal next pin) :
    ∀ pair ∈ defRegs ops regs values,regVal actual pair.1.2 = pair.2 := by
  obtain ⟨_,returned,_,_⟩ := L.progXWithPins_some called
  rw [returned]
  exact matched.defRegs allocated same

/-- Select return pins from the actual artifact's checker result and unchanged source signature. -/
def checkedReturnPins (g : Clif.Function) : List Reg :=
  (ReturnPinMode.checked g (L.A g).vc).pins g (sigRets g.sig).length

/-- The ABI-aware program call uses the existing canonical machine and call guard. -/
noncomputable def progXABI (κ : Nat → Clif.Function → Nat) (M : Nat)
    (F : BitVec 64 → Prop) (g : Clif.Function) (uses : List CV) (w : Arm.ArmState) :
    Option (List CV × Arm.ArmState) :=
  L.progXWithPins L.checkedReturnPins κ M F g uses w

/-- The previous checker branch retains exactly the previous program-call model. -/
theorem progXABI_previous {κ : Nat → Clif.Function → Nat} {M : Nat}
    {F : BitVec 64 → Prop} {g : Clif.Function} {uses : List CV} {w : Arm.ArmState}
    (old : SemanticNI.check g (L.A g).vc = true) :
    L.progXABI κ M F g uses w = L.progX κ M F g uses w := by
  simp only [progXABI,progXWithPins,checkedReturnPins,ReturnPinMode.checked,old,↓reduceIte,
    ReturnPinMode.pins,progX,List.map_map,Function.comp_def]

/-- A checked Stock sret artifact selects x8 without changing its original signature. -/
theorem checkedReturnPins_sret {g : Clif.Function}
    (old : SemanticNI.check g (L.A g).vc = false)
    (sret : (sigRets g.sig).any (·.purpose == .sret) = true) :
    L.checkedReturnPins g = [.x 8] := by
  simp only [checkedReturnPins,ReturnPinMode.checked,old,Bool.false_eq_true,↓reduceIte,
    ReturnPinMode.pins,Backend.Stock.Proof.returnPins,sret,Option.getD_some]

open Classical in
/-- Preserve direct, indirect, base, symbol, TLS and flag dispatch while selecting return pins. -/
noncomputable def XWithPins (pins : Clif.Function → List Reg)
    (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop) : ExtSem where
  call d uses w := match d with
    | some n => (match L.P.func? n with
      | some h => L.progXWithPins pins κ M F h uses w
      | none => L.Xb.call d uses w)
    | none => (match uses with
      | u :: args => (match symCallee L.Xb L.P (lo64 u) with
        | some h => if L.IndTo g h ∧ args.length = (regLocs h.sig).length then
            L.progXWithPins pins κ M F h args w else none
        | none => L.Xb.call none uses w)
      | [] => L.Xb.call none uses w)
  sym := L.Xb.sym
  tp := L.Xb.tp
  tlsFlags := L.Xb.tlsFlags

/-- Ordinary pins retain the entire old external semantics, including indirect calls. -/
theorem XWithPins_ordinary (κ : Nat → Clif.Function → Nat) (M : Nat)
    (g : Clif.Function) (F : BitVec 64 → Prop) :
    L.XWithPins (fun f => (List.range (sigRets f.sig).length).map Reg.x) κ M g F = L.X κ M g F := by
  simp only [XWithPins,X,progXWithPins_ordinary]
  rfl

/-- Return-pin selection keeps the exact base symbol, TLS and flag operations. -/
theorem XWithPins_base (pins : Clif.Function → List Reg)
    (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop) :
    (L.XWithPins pins κ M g F).sym = L.Xb.sym ∧
      (L.XWithPins pins κ M g F).tp = L.Xb.tp ∧
      (L.XWithPins pins κ M g F).tlsFlags = L.Xb.tlsFlags := ⟨rfl,rfl,rfl⟩

/-- A direct program call selects the same function and actual linked execution. -/
theorem XWithPins_prog {pins : Clif.Function → List Reg} {κ : Nat → Clif.Function → Nat}
    {M : Nat} {g h : Clif.Function} {F : BitVec 64 → Prop} {name : String}
    (found : L.P.func? name = some h) (uses : List CV) (w : Arm.ArmState) :
    (L.XWithPins pins κ M g F).call (some name) uses w =
      L.progXWithPins pins κ M F h uses w := by
  simp only [XWithPins,found]

end LinkSys
end E2E
