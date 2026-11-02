import FV.E2E.LinkReturnPins

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}
variable {modes : Clif.Function → ReturnPinMode}

/-- A physical return convention is internal to the compiled program interface. -/
def modeReturnPins (modes : Clif.Function → ReturnPinMode) (g : Clif.Function) : List Reg :=
  (modes g).pins g (sigRets g.sig).length

noncomputable def progXMode (modes : Clif.Function → ReturnPinMode)
    (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop)
    (g : Clif.Function) (uses : List CV) (w : Arm.ArmState) : Option (List CV × Arm.ArmState) :=
  L.progXWithPins (modeReturnPins modes) κ M F g uses w

noncomputable def XMode (modes : Clif.Function → ReturnPinMode)
    (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop) : ExtSem :=
  L.XWithPins (modeReturnPins modes) κ M g F

/-- The ordinary instance retains the complete previous call model. -/
theorem progXMode_ordinary (κ : Nat → Clif.Function → Nat) (M : Nat)
    (F : BitVec 64 → Prop) (g : Clif.Function) (uses : List CV) (w : Arm.ArmState) :
    L.progXMode (fun _ => .ordinary) κ M F g uses w = L.progX κ M F g uses w :=
  L.progXWithPins_ordinary κ M F g uses w

/-- The ordinary instance retains the complete previous external semantics. -/
theorem XMode_ordinary (κ : Nat → Clif.Function → Nat) (M : Nat)
    (g : Clif.Function) (F : BitVec 64 → Prop) :
    L.XMode (fun _ => .ordinary) κ M g F = L.X κ M g F :=
  L.XWithPins_ordinary κ M g F

theorem XMode_base {M : Nat} {g : Clif.Function} {n : String} (hn : L.P.func? n = none)
    (uses : List CV) (w : Arm.ArmState) (F : BitVec 64 → Prop) :
    (L.XMode modes κ M g F).call (some n) uses w = L.Xb.call (some n) uses w := by
  simp [XMode,XWithPins, hn]

theorem XMode_prog {M : Nat} {g : Clif.Function} {n : String} {h : Clif.Function}
    (hpf : L.P.func? n = some h) (uses : List CV) (w : Arm.ArmState) (F : BitVec 64 → Prop) :
    (L.XMode modes κ M g F).call (some n) uses w = L.progXMode modes κ M F h uses w := by
  simp [XMode,XWithPins,progXMode,hpf]

theorem XMode_none {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} {u : CV} {args : List CV}
    {w : Arm.ArmState} (hn : symCallee L.Xb L.P (lo64 u) = none) :
    (L.XMode modes κ M g F).call none (u :: args) w = L.Xb.call none (u :: args) w := by
  simp [XMode,XWithPins, hn]

open Classical in
theorem XMode_ind {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} {u : CV} {args : List CV}
    {w : Arm.ArmState}
    {h : Clif.Function} (hs : symCallee L.Xb L.P (lo64 u) = some h) :
    (L.XMode modes κ M g F).call none (u :: args) w = if L.IndTo g h ∧ args.length = (regLocs h.sig).length
      then L.progXMode modes κ M F h args w else none := by
  simp only [XMode,XWithPins,progXMode,hs]

theorem progXMode_ext {M : Nat} {F : BitVec 64 → Prop} {h : Clif.Function}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hx : L.progXMode modes κ M F h uses w = some (outs, w')) :
    Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  unfold progXMode progXWithPins at hx
  split at hx
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨-, rfl⟩ := hx
    exact ⟨hc.2, by rw [(L.pcall_pc M h _).1, L.program_canon]⟩
  · cases hx

def ThmReturnPins (modes : Clif.Function → ReturnPinMode) (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat)
    (rvals : List Clif.Val) (cm' : Clif.Mem), L.WorldEntry κ M g F vals cs w₀ →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
      ReturnPinMode.Valid (modes g) g us ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A g).vc.RetsSite us ∧
      (∀ G ra s, L.MachEntry κ M g F G ra s w₀ →
        ∃ n, ActRet ra F G us outs wf s (runX (L.mach M g) n s) ∧
          PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n) ∧
      (L.NeedNI → ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
        RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
          g (spv w₀) cs.frame.slots cs.mem w₀' →
        SameWorld (fun a => F a ∨ D a) w₀ w₀' →
        (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip vals → regVal w₀' r = regVal w₀ r) →
        (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip vals → ∀ k < v.ty.bytes,
          w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
            w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
        ∀ G ra s, L.MachEntry κ M g F G ra s w₀' →
          ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n s) ∧
            PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n)

end LinkSys
end E2E
