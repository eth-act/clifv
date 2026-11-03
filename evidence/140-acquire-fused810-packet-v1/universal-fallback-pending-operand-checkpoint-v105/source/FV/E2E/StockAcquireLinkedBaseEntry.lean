import FV.E2E.StockAcquireActEntryKeep

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The linked external semantics preserves the base external-return contract.
Program callees use the existing linked return construction. -/
theorem linked_ext_of_baseExt (L : LinkSys) {κ : Nat → Clif.Function → Nat}
    (baseExt : ∀ d uses w outs w', L.BaseDest d → L.Xb.call d uses w = some (outs,w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program)
    {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} {d : Option String}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hx : (L.X κ M g F).call d uses w = some (outs,w'))
    (herr : Arm.r .ERR w = .None) :
    Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  cases d with
  | some n =>
    cases hpf : L.P.func? n with
    | none =>
      rw [L.X_base hpf _ _ F] at hx
      exact baseExt _ _ _ _ _ (.inr ⟨n,rfl,hpf⟩) hx herr
    | some h =>
      rw [L.X_prog hpf _ _ F] at hx
      exact L.progX_ext hx
  | none =>
    cases uses with
    | nil => exact baseExt _ _ _ _ _ (.inl rfl) hx herr
    | cons u args =>
      cases hs : symCallee L.Xb L.P (lo64 u) with
      | none =>
        rw [L.X_none hs] at hx
        exact baseExt _ _ _ _ _ (.inl rfl) hx herr
      | some h =>
        rw [L.X_ind hs] at hx
        split at hx
        · exact L.progX_ext hx
        · cases hx

/-- The existing base hook-PC contract determines every linked hook-PC result. -/
theorem linked_pc_of_basePc (L : LinkSys)
    (basePc : ∀ d s, L.BaseDest d → Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
      Arm.r .PC (L.Hb.call d s) = Arm.r .PC s+4)
    (M : Nat) (d : Option String) (u : Arm.ArmState)
    (herr : Arm.r .ERR u = .None) (hal : Arm.CheckSPAlignment u) :
    Arm.r .PC ((L.hooks M).call d u) = Arm.r .PC u+4 := by
  cases d with
  | none =>
    cases hb : (blrTarget u).bind (symCallee L.Xb L.P) with
    | none =>
      rw [L.hooks_base (.inl rfl) u (fun _ => hb)]
      exact basePc _ _ (.inl rfl) herr hal
    | some h =>
      rw [L.hooks_none hb]
      exact (L.pcall_pc M h u).2
  | some n =>
    cases hpf : L.P.func? n with
    | none =>
      rw [L.hooks_base (.inr ⟨n,rfl,hpf⟩) u (fun h => by cases h)]
      exact basePc _ _ (.inr ⟨n,rfl,hpf⟩) herr hal
    | some h =>
      rw [L.hooks_some hpf]
      exact (L.pcall_pc M h u).2

/-- The exact physical-step definition uses the same hooks and symbol resolver.
This equality does not identify the external call semantics. -/
theorem linked_ArmStepX_eq_mach (L : LinkSys) (κ : Nat → Clif.Function → Nat)
    (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop) :
    ArmStepX (L.X κ M g F) (L.hooks M) (L.A g).fa = L.mach M g := by
  funext s
  unfold ArmStepX LinkSys.mach
  rfl

/-- Actual absence of calls and TLS discharges the site-dependent entry fields.
The original base fields discharge the unconditional hook and external-return fields. -/
theorem linked_actEntry_of_machEntry_no_calls_no_tls (L : LinkSys)
    {κ : Nat → Clif.Function → Nat} {M : Nat} {g : Clif.Function}
    {F G : BitVec 64 → Prop} {ra : BitVec 64} {s world : Arm.ArmState}
    (basePc : ∀ d s, L.BaseDest d → Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
      Arm.r .PC (L.Hb.call d s) = Arm.r .PC s+4)
    (baseExt : ∀ d uses w outs w', L.BaseDest d → L.Xb.call d uses w = some (outs,w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program)
    (entry : L.MachEntry κ M g F G ra s world)
    (noCall : ∀ info,¬ (L.A g).vcp.CallSite info) (noTls : (L.A g).vcp.hasTls = false) :
    ActEntry (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g)
      F G (L.X κ M g F) (L.hooks M) (L.A g).base ra s world := by
  refine ⟨entry.abi,entry.stack,entry.gfree,entry.hF,?_,?_,?_,entry.body⟩
  · refine ⟨fun ctx info site => (noCall info site).elim,?_,?_⟩
    · exact linked_pc_of_basePc L basePc M
    · exact fun _ _ _ _ _ hx herr => linked_ext_of_baseExt L baseExt hx herr
  · intro present ctx info ti site
    exact (noCall info site.callSite).elim
  · intro present
    rw [noTls] at present
    cases present

end E2E.StockAcquirePending
