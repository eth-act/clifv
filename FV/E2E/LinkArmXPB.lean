import FV.E2E.LinkArmTableB
import FV.E2E.ExtSemGuardR

/-!
# Program calls under the slot-byte oracle (SEM1 #537, item (d), docs/plans/uninit.md §5.9,
Finding (UninitZ13), #680)

`progX` answers a call of a function of `P` only under `Cond`, whose CLIF witness memory is placed
with the oracle `none` (`PlaceAt`). Under the slot-byte oracle the run's CLIF memories are placed
with `PlaceAtB … (some ini)`, so at an actual call `Cond` need not hold. The answer itself (the
linked machine's call from `canon`) does not involve the CLIF side:

* `CondB`: `Cond` with the CLIF witness memory placed with some oracle `ini` (`PlaceAtB`);
  `cond_iff_condB` without program callees with slots;
* `progXB`, `progXPRB`, `XPRB`, `XPRBI'` (named `XPBI`): `progX`, `progXPR`, `XPR`, `XPRI` with
  `CondB`; `progXB_of_not_needSlots` (the same as `progX` without program callees with slots);
* `ExtSemI.guardRI`, `XPBG`: call `n` of `XPBI` guarded by the contracts of the CLIF invocation
  of call `n` with `ExtSem.guardR` (undefined calls stay undefined where no invocation is
  related); `hX_guardRI` (stage 1 for any `XI`), `XPBG_eq_of` (stage 2 interface).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **`XI` with call number `n` guarded by `Q n` with `ExtSem.guardR`.** -/
noncomputable def _root_.Backend.Proof.ExtSemI.guardRI (XI : ExtSemI)
    (Q : Nat → Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop) :
    ExtSemI where
  call n := ((XI.at n).guardR (Q n)).call
  sym := XI.sym
  tp := XI.tp
  tlsFlags := XI.tlsFlags

theorem _root_.Backend.Proof.ExtSemI.guardRI_at (XI : ExtSemI)
    (Q : Nat → Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop) (n : Nat) :
    (XI.guardRI Q).at n = (XI.at n).guardR (Q n) := rfl

/-- **The per-state callee contracts of the `guardR`-guarded semantics** (`hX_guardI`). -/
theorem hX_guardRI {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {Γ : Rel} {f : Clif.Function}
    {c : BitVec 64} (XI : ExtSemI) (hnrc : NoRetCall env p cs)
    (hR : InvokedRetOk env p cs exts sigs) :
    ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) exts (RelW Γ f c)
        ((XI.guardRI (CallPostN env p cs exts sigs (RelW Γ f c) XI.sym)).at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) sigs (RelW Γ f c)
        ((XI.guardRI (CallPostN env p cs exts sigs (RelW Γ f c) XI.sym)).at n) :=
  fun _ n hs => xCallsOk_guardR_only (invoked_sub_invokedN hnrc hs) (XI.at n)
    (callPost_invokedN_exists (hR n))

namespace LinkSys

variable (L : LinkSys)

/-- **`Cond` under the slot-byte oracle**: the CLIF witness memory placed with some oracle `ini`
that is the table of the canonical callee run one level down (`TableOf`), when program callees
have slots. -/
def CondB (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop) (g : Clif.Function)
    (uses : List CV) (w : Arm.ArmState) : Prop :=
  0 < M ∧ Arm.r .ERR w = .None ∧ (spv w).toNat % 16 = 0 ∧
  frameDrop (L.A g).af + κ (M - 1) g ≤ (spv w).toNat ∧
  (∀ a, StackBelow (frameDrop (L.A g).af + κ (M - 1) g) (spv w) a → F a ∧ ¬ L.Img a) ∧
  ∃ vals cm cs rvals cm' ini, MemRel F L.syms cm w ∧ ArgsAt g.sig vals uses w ∧
    StackArgsAvoid F g.sig vals w ∧
    (L.NeedSlots → L.PlaceAtB cm (spv w) ini ∧
      L.TableOf (M - 1) g (enterAt (L.A g) (L.canon g uses w)) ini) ∧
    Clif.initState L.P g.name vals cm = .ok cs ∧ L.crun M cs = .returned rvals cm'

/-- Without program callees with slots, `CondB` is `Cond`. -/
theorem cond_iff_condB {κ : Nat → Clif.Function → Nat} {M : Nat} {F : BitVec 64 → Prop}
    {g : Clif.Function} {uses : List CV} {w : Arm.ArmState} (hN : ¬ L.NeedSlots) :
    L.Cond κ M F g uses w ↔ L.CondB κ M F g uses w := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, vals, cm, cs, rvals, cm', h6, h7, h8, -, h10, h11⟩
    exact ⟨h1, h2, h3, h4, h5, vals, cm, cs, rvals, cm', ⟨fun _ _ => 0, 0⟩, h6, h7, h8,
      fun h => absurd h hN, h10, h11⟩
  · rintro ⟨h1, h2, h3, h4, h5, vals, cm, cs, rvals, cm', -, h6, h7, h8, -, h10, h11⟩
    exact ⟨h1, h2, h3, h4, h5, vals, cm, cs, rvals, cm', h6, h7, h8, fun h => absurd h hN, h10, h11⟩

open Classical in
/-- **`progX` with `CondB`**: the same answer (the linked machine's call from `canon`). -/
noncomputable def progXB (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop)
    (g : Clif.Function) (uses : List CV) (w : Arm.ArmState) : Option (List CV × Arm.ArmState) :=
  if L.CondB κ M F g uses w ∧ Arm.r .ERR (L.pcall M g (L.canon g uses w)) = .None then
    some ((List.range g.sig.returns.length).map fun j =>
        regVal (L.pcall M g (L.canon g uses w)) (.x j),
      L.pcall M g (L.canon g uses w))
  else none

theorem progXB_of_not_needSlots {κ : Nat → Clif.Function → Nat} {M : Nat} {F : BitVec 64 → Prop}
    {g : Clif.Function} (uses : List CV) (w : Arm.ArmState) (hN : ¬ L.NeedSlots) :
    L.progXB κ M F g uses w = L.progX κ M F g uses w := by
  have hc : L.CondB κ M F g uses w = L.Cond κ M F g uses w := propext (L.cond_iff_condB hN).symm
  unfold progXB progX
  rw [hc]

/-- `progXB` from `worldPR`. -/
noncomputable def progXPRB (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop)
    (g : Clif.Function) (uses : List CV) (Pn : BitVec 64 → BitVec 8) (Sn : Arm.ArmState)
    (w : Arm.ArmState) : Option (List CV × Arm.ArmState) :=
  L.progXB κ M F g uses (L.worldPR κ M g Pn Sn w)

open Classical in
/-- **`XPR` with `progXB`.** -/
noncomputable def XPRB (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (n : Nat) :
    ExtSem where
  call d uses w := match d with
    | some m => (match L.P.func? m with
      | some h => L.progXPRB κ M F h uses (P n) (R n) w
      | none => L.Xb.call d uses w)
    | none => (match uses with
      | u :: args => (match symCallee L.Xb L.P (lo64 u) with
        | some h => if L.IndTo g h ∧ args.length = (regLocs h.sig).length then
            L.progXPRB κ M F h args (P n) (R n) w else none
        | none => L.Xb.call none uses w)
      | [] => L.Xb.call none uses w)
  sym := L.Xb.sym
  tp := L.Xb.tp
  tlsFlags := L.Xb.tlsFlags

/-- **The calls of an activation with both prophecies under the slot-byte oracle.** -/
noncomputable def XPBI (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) : ExtSemI where
  call n := (L.XPRB κ M g F P R n).call
  sym := L.Xb.sym
  tp := L.Xb.tp
  tlsFlags := L.Xb.tlsFlags

theorem XPBI_at (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (n : Nat) :
    (L.XPBI κ M g F P R).at n = L.XPRB κ M g F P R n := rfl

/-- Without program callees with slots, `XPRB` is `XPR`. -/
theorem XPRB_of_not_needSlots {κ : Nat → Clif.Function → Nat} {M : Nat} {g : Clif.Function}
    {F : BitVec 64 → Prop} {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} (n : Nat)
    (hN : ¬ L.NeedSlots) : L.XPRB κ M g F P R n = L.XPR κ M g F P R n := by
  have hp : ∀ h args Pn Sn w, L.progXPRB κ M F h args Pn Sn w = L.progXPR κ M F h args Pn Sn w :=
    fun h args Pn Sn w => L.progXB_of_not_needSlots args _ hN
  unfold XPRB XPR
  congr 1
  funext d uses w
  rcases d with _ | m
  · rcases uses with _ | ⟨u, args⟩
    · rfl
    · rcases hs : symCallee L.Xb L.P (lo64 u) with _ | h <;> simp [hs, hp]
  · rcases hf : L.P.func? m with _ | h <;> simp [hf, hp]

/-- **The calls of an activation under the slot-byte oracle, guarded** (`guardR`) by the
contracts of the CLIF invocation of each call: the `XI` of the induction step of `ThmPRB`. -/
noncomputable def XPBG (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
    (env : Clif.Env) (cs : Clif.State) (c : BitVec 64) : ExtSemI :=
  (L.XPBI κ M g F P R).guardRI (CallPostN env L.P.bare cs (g.externs.map (·.2)) (indSigs g)
    (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
    L.Xb.sym)

/-- **Stage 2 interface**: where every non-vacuous contract of the invocation of call `n`
accepts `XPRB`'s result, every answer of `XPBG` is `XPRB`'s. -/
theorem XPBG_eq_of {κ : Nat → Clif.Function → Nat} {M : Nat} {g : Clif.Function}
    {F : BitVec 64 → Prop} {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState}
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64} {n : Nat} {d : Option String}
    {uses : List CV} {w : Arm.ArmState}
    (h : (¬ ∀ r, CallPostN env L.P.bare cs (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym n d uses w r) →
      ∃ x, (L.XPRB κ M g F P R n).call d uses w = some x ∧
        CallPostN env L.P.bare cs (g.externs.map (·.2)) (indSigs g)
          (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
          L.Xb.sym n d uses w x)
    {r : List CV × Arm.ArmState} (hr : ((L.XPBG κ M g F P R env cs c).at n).call d uses w = some r) :
    (L.XPRB κ M g F P R n).call d uses w = some r :=
  ExtSem.guardR_eq_of (X := (L.XPBI κ M g F P R).at n) h hr

end LinkSys

end E2E
