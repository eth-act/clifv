import FV.E2E.LinkArmXPBT
import FV.E2E.ExtSemGuardRY
import FV.E2E.BackendPrefixI
import FV.E2E.LinkArmProgOsPRBRL

/-!
# The call contracts of the induction step's guarded semantics (SEM1 #537, #680 (3), stage 2)

`ActEntryPR.calls` for the induction step's `XI` asks `CalleeOkGP` of its call `n` at the
activation's call-`n` states. `calleeOkPRBRL` gives it for `XPRBT … n`; the guarded semantics
answers only `XPRBT`'s results where stage 2 holds, and stage 2 can hold only at the worlds of
the call states (the answer is computed from the prophecies `P n`, `R n` of those states). With
`CallPostNX` (#690) it cannot hold at unrelated calls (#692), so the guard is `CallPostNXR`:

* `csemV_of_call_subW`, **`CalleeOkGP.ofCallSubW`**, **`CalleeTryOkGP.ofCallSubW`**: the machine
  contracts are antitone in the call results *at the worlds of the states `P`* (`ofCallSub` asks
  it at every world);
* `XPBTGY` (`XPBTI` guarded by `CallPostNXR`), `XPBTGY_ext`, `XPBTGY_sub`;
* **`Stage2Y`**: stage 2 of call `n` at the states `Q` (where `CallPost` of the CLIF invocation of
  count `n` is not vacuous, `XPRBT … n` answers a `CallPost`-result);
* **`calleeOkXPBTGY`**, **`calleeTryOkXPBTGY`**: the contracts of `XPBTGY … n` at `Q` from
  `calleeOkPRBRL`/`calleeTryOkPRBRL` (induction hypothesis `ThmPRBRL`, #694) and `Stage2Y`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **Fewer call results at the world `w`, fewer instruction results at `w`.** -/
theorem csemV_of_call_subW {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {X : ExtSem} (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    {w : Arm.ArmState} (hc : ∀ d u r, c d u w = some r → X.call d u w = some r) {i : MInst}
    {uses : List CV} {r : List CV × Arm.ArmState × Ctl}
    (h : csemV gv F ctx { X with call := c } i uses w = some r) : csemV gv F ctx X i uses w = some r := by
  cases hi : i.isCallI
  · rw [← csemV_call_congr gv F ctx X c hi]; exact h
  · obtain ⟨info, hci⟩ := callLike_of_isCallI hi
    rcases hci with rfl | ⟨ti, rfl⟩
    · simp only [csemV] at h ⊢
      split at h
      · rename_i hg1
        have hg2 : gotGuard gv X info uses := hg1
        simp only [csem, Option.map_eq_some_iff] at h
        simp only [hg2, ↓reduceIte, csem, Option.map_eq_some_iff]
        obtain ⟨r', hr', e⟩ := h
        exact ⟨r', hc _ _ _ hr', e⟩
      · cases h
    · simp only [csemV] at h ⊢
      split at h
      · rename_i hg1
        have hg2 : gotGuard gv X info uses := hg1
        simp only [csem, Option.map_eq_some_iff, Option.filter_eq_some_iff] at h
        simp only [hg2, ↓reduceIte, csem, Option.map_eq_some_iff, Option.filter_eq_some_iff]
        obtain ⟨r', ⟨hr', hf⟩, e⟩ := h
        exact ⟨r', ⟨hc _ _ _ hr', hf⟩, e⟩
      · cases h

/-- **`CalleeOkGP.ofCallSub` at the worlds of the states `P`** (`ext` given). -/
theorem _root_.Backend.Proof.CalleeOkGP.ofCallSubW {P : Arm.ArmState → Prop}
    {F : BitVec 64 → Prop} {K : Nat} {G : BitVec 64 → Prop} {s0 : Arm.ArmState}
    {Pc : BitVec 64 → MInst → Prop} {X : ExtSem} {H : ArmHooks} {S : CallInfo → Prop}
    {gv : Nat → String → Prop} (h : CalleeOkGP P F K G s0 Pc X H S gv)
    (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    (hc : ∀ s w, P s → SameWorld F s w → ∀ d u r, c d u w = some r → X.call d u w = some r)
    (hext : ∀ d uses w outs w', c d uses w = some (outs, w') → Arm.r .ERR w = .None →
      Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    CalleeOkGP P F K G s0 Pc { X with call := c } H S gv :=
  ⟨fun ctx info hS s hP hK hF hG cc wh ops regs i' w outs w' hops hst hasg hpi hsw hal herr hsem =>
    h.os ctx info hS s hP hK hF hG cc wh ops regs i' w outs w' hops hst hasg hpi hsw hal herr
      (csemV_of_call_subW c (hc s w hP hsw) hsem),
    h.pc, hext⟩

/-- **`CalleeTryOkGP.ofCallSub` at the worlds of the states `P`.** -/
theorem _root_.Backend.Proof.CalleeTryOkGP.ofCallSubW {P : Arm.ArmState → Prop}
    {F : BitVec 64 → Prop} {K : Nat} {G : BitVec 64 → Prop} {s0 : Arm.ArmState}
    {Pc : BitVec 64 → MInst → Prop} {X : ExtSem} {H : ArmHooks} {S : CallInfo → TryInfo → Prop}
    {gv : Nat → String → Prop} (h : CalleeTryOkGP P F K G s0 Pc X H S gv)
    (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    (hc : ∀ s w, P s → SameWorld F s w → ∀ d u r, c d u w = some r → X.call d u w = some r) :
    CalleeTryOkGP P F K G s0 Pc { X with call := c } H S gv :=
  fun ctx info ti hS cc wh ops regs i' s w outs w' s' hP hK hF hG hops hst hasg hpi hsw hal herr
    hsem hex => h ctx info ti hS cc wh ops regs i' s w outs w' s' hP hK hF hG hops hst hasg hpi hsw
      hal herr (csemV_of_call_subW c (hc s w hP hsw) hsem) hex

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **`XPBTI` guarded by `CallPostNXR`** (#692): the `XI` of the induction step for
`backend_correct_world_*PRGY`. -/
noncomputable def XPBTGY (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
    (env : Clif.Env) (cs : Clif.State) (c : BitVec 64) : ExtSemI :=
  (L.XPBTI κ M g F P R).guardRI (CallPostNXR env L.P.bare cs (g.externs.map (·.2)) (indSigs g)
    (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
    L.Xb.sym)

/-- **`ext` of the guarded calls.** -/
theorem XPBTGY_ext (hL : L.Ok) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {env : Clif.Env} {cs : Clif.State}
    {c : BitVec 64} (n : Nat) :
    ∀ d uses w outs w', ((L.XPBTGY κ M g F P R env cs c).at n).call d uses w = some (outs, w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program :=
  guardRXRI_ext (L.XPBTI κ M g F P R) n fun _ _ _ _ _ hx herr => L.XPRBT_ext hL hx herr

/-- **Stage 2 of call `n` at the states `Q`**: at the world of a state `Q`, where `CallPost` of
the CLIF invocation of count `n` is not vacuous, `XPRBT … n` answers a `CallPost`-result. -/
def Stage2Y (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (env : Clif.Env) (cs : Clif.State)
    (c : BitVec 64) (Q : Arm.ArmState → Prop) (n : Nat) : Prop :=
  ∀ u w, Q u → SameWorld F u w → ∀ d uses,
    (¬ ∀ r, CallPost (env.only (InvokedN env L.P.bare cs n)) (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym d uses w r) →
    ∃ x, (L.XPRBT κ M g F P R n).call d uses w = some x ∧
      CallPost (env.only (InvokedN env L.P.bare cs n)) (g.externs.map (·.2)) (indSigs g)
        (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
        L.Xb.sym d uses w x

/-- **Stage 2 gives the answers**: at the world of a state `Q` where stage 2 holds, every answer
of `XPBTGY … n` is `XPRBT … n`'s. -/
theorem XPBTGY_sub (hL : L.Ok) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {env : Clif.Env} {cs : Clif.State}
    {c : BitVec 64} {Q : Arm.ArmState → Prop} {n : Nat} (h2 : L.Stage2Y κ M g F P R env cs c Q n)
    {u w : Arm.ArmState} (hu : Q u) (hsw : SameWorld F u w) {d : Option String} {uses : List CV}
    {r : List CV × Arm.ArmState}
    (hr : ((L.XPBTGY κ M g F P R env cs c).at n).call d uses w = some r) :
    (L.XPRBT κ M g F P R n).call d uses w = some r :=
  guardRXR_sub (X := (L.XPBTI κ M g F P R).at n)
    (fun _ _ hx herr => L.XPRBT_ext hL hx herr) (h2 u w hu hsw d uses) hr

/-- **The call contract of `XPBTGY … n`** at the states `Q` where stage 2 holds. -/
theorem calleeOkXPBTGY (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64}
    (h2 : L.Stage2Y κ M g F P R env cs c Q n) :
    CalleeOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F P R env cs c).at n) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) :=
  (L.calleeOkPRBRL hL hκ ih hdet hg he hQ).ofCallSubW _
    (fun _ _ hu hsw _ _ _ hr => L.XPBTGY_sub hL h2 hu hsw hr)
    (L.XPBTGY_ext hL n)

/-- **The try-call contract of `XPBTGY … n`** at the states `Q` where stage 2 holds. -/
theorem calleeTryOkXPBTGY (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64}
    (h2 : L.Stage2Y κ M g F P R env cs c Q n) :
    CalleeTryOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F P R env cs c).at n) (L.hooks M)
      (L.A g).vcp.TrySite (GotV (L.A g).vcp) :=
  (L.calleeTryOkPRBRL hL hκ ih hdet hg he hQ).ofCallSubW _
    (fun _ _ hu hsw _ _ _ hr => L.XPBTGY_sub hL h2 hu hsw hr)

end LinkSys

end E2E
