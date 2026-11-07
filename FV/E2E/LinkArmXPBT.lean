import FV.E2E.LinkArmXPB
import FV.E2E.LinkArmProgCallPRB

/-!
# Program calls under the slot-byte oracle, with the callee table (SEM1 #537, item (d),
`docs/plans/uninit.md` §5.9, #680 (3))

`CondB` (`FV/E2E/LinkArmXPB.lean`) places the CLIF witness memory with an oracle `ini` and asks
for the canonical callee run's table to be `ini`'s. `ThmPRB (M - 1)` (through `progCallPRB`)
needs more: the callee's CLIF entry memory is placed with `calleeIni h ini` (its own activation
takes table entry `ini.next + 1` when it has slots), so the canonical callee run's table must be
`calleeIni h ini`'s, also without program callees with slots (`TableOf` at depth `0` excludes
program calls), and the new slot bytes (`ini.bytes (ini.next + 1)`) must be the memory of the
call world. `CondBT` states that; the rest are `progXB`, `progXPRB`, `XPRB`, `XPBI`, `XPBG` on
`CondBT` (same answer: the linked machine's call from `canon`), with the lemmas `XPR_*` of
`LinkArmProgOsP` / `LinkArmProphReg`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **`Cond` under the slot-byte oracle with the callee table**: the CLIF witness memory placed
with some oracle `ini` whose next slot bytes are the call world's (under `NeedSlots`), and the
canonical callee run's table is the callee oracle's (`calleeIni g ini`). -/
def CondBT (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop) (g : Clif.Function)
    (uses : List CV) (w : Arm.ArmState) : Prop :=
  0 < M ∧ Arm.r .ERR w = .None ∧ (spv w).toNat % 16 = 0 ∧
  frameDrop (L.A g).af + κ (M - 1) g ≤ (spv w).toNat ∧
  (∀ a, StackBelow (frameDrop (L.A g).af + κ (M - 1) g) (spv w) a → F a ∧ ¬ L.Img a) ∧
  ∃ vals cm cs rvals cm' ini, MemRel F L.syms cm w ∧ ArgsAt g.sig vals uses w ∧
    StackArgsAvoid F g.sig vals w ∧
    (L.NeedSlots → L.PlaceAtB cm (spv w) ini ∧ ∀ a, L.SlotByte g (spv w) a →
      ini.bytes (ini.next + 1) a = w.mem (BitVec.ofNat 64 a)) ∧
    L.TableOf (M - 1) g (enterAt (L.A g) (L.canon g uses w)) (calleeIni g ini) ∧
    Clif.initState L.P g.name vals cm = .ok cs ∧ L.crun M cs = .returned rvals cm'

open Classical in
/-- **`progX` with `CondBT`**: the same answer (the linked machine's call from `canon`). -/
noncomputable def progXBT (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop)
    (g : Clif.Function) (uses : List CV) (w : Arm.ArmState) : Option (List CV × Arm.ArmState) :=
  if L.CondBT κ M F g uses w ∧ Arm.r .ERR (L.pcall M g (L.canon g uses w)) = .None then
    some ((List.range g.sig.returns.length).map fun j =>
        regVal (L.pcall M g (L.canon g uses w)) (.x j),
      L.pcall M g (L.canon g uses w))
  else none

/-- `progXBT` from `worldPR`. -/
noncomputable def progXPRBT (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop)
    (g : Clif.Function) (uses : List CV) (Pn : BitVec 64 → BitVec 8) (Sn : Arm.ArmState)
    (w : Arm.ArmState) : Option (List CV × Arm.ArmState) :=
  L.progXBT κ M F g uses (L.worldPR κ M g Pn Sn w)

open Classical in
/-- **`XPR` with `progXBT`.** -/
noncomputable def XPRBT (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (n : Nat) :
    ExtSem where
  call d uses w := match d with
    | some m => (match L.P.func? m with
      | some h => L.progXPRBT κ M F h uses (P n) (R n) w
      | none => L.Xb.call d uses w)
    | none => (match uses with
      | u :: args => (match symCallee L.Xb L.P (lo64 u) with
        | some h => if L.IndTo g h ∧ args.length = (regLocs h.sig).length then
            L.progXPRBT κ M F h args (P n) (R n) w else none
        | none => L.Xb.call none uses w)
      | [] => L.Xb.call none uses w)
  sym := L.Xb.sym
  tp := L.Xb.tp
  tlsFlags := L.Xb.tlsFlags

/-- **The calls of an activation with both prophecies under `CondBT`.** -/
noncomputable def XPBTI (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) : ExtSemI where
  call n := (L.XPRBT κ M g F P R n).call
  sym := L.Xb.sym
  tp := L.Xb.tp
  tlsFlags := L.Xb.tlsFlags

theorem XPBTI_at (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (n : Nat) :
    (L.XPBTI κ M g F P R).at n = L.XPRBT κ M g F P R n := rfl

/-- **`XPBTI` guarded** (`guardR`) by the contracts of the CLIF invocation of each call: the `XI`
of the induction step of `ThmPRB` (`XPBG` on `CondBT`). -/
noncomputable def XPBTG (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
    (env : Clif.Env) (cs : Clif.State) (c : BitVec 64) : ExtSemI :=
  (L.XPBTI κ M g F P R).guardRI (CallPostN env L.P.bare cs (g.externs.map (·.2)) (indSigs g)
    (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
    L.Xb.sym)

/-- **Stage 2 interface** (`XPBG_eq_of` on `CondBT`). -/
theorem XPBTG_eq_of {M : Nat} {g : Clif.Function}
    {F : BitVec 64 → Prop} {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState}
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64} {n : Nat} {d : Option String}
    {uses : List CV} {w : Arm.ArmState}
    (h : (¬ ∀ r, CallPostN env L.P.bare cs (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym n d uses w r) →
      ∃ x, (L.XPRBT κ M g F P R n).call d uses w = some x ∧
        CallPostN env L.P.bare cs (g.externs.map (·.2)) (indSigs g)
          (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
          L.Xb.sym n d uses w x)
    {r : List CV × Arm.ArmState} (hr : ((L.XPBTG κ M g F P R env cs c).at n).call d uses w = some r) :
    (L.XPRBT κ M g F P R n).call d uses w = some r :=
  ExtSem.guardR_eq_of (X := (L.XPBTI κ M g F P R).at n) h hr

theorem XPRBT_prog {M : Nat} {g : Clif.Function} {m : String} {h : Clif.Function}
    (hpf : L.P.func? m = some h) (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8)
    (R : Nat → Arm.ArmState) (n : Nat) (uses : List CV) (w : Arm.ArmState) :
    (L.XPRBT κ M g F P R n).call (some m) uses w = L.progXPRBT κ M F h uses (P n) (R n) w := by
  simp [XPRBT, hpf]

theorem XPRBT_none {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat} {u : CV} {args : List CV}
    {w : Arm.ArmState} (hn : symCallee L.Xb L.P (lo64 u) = none) :
    (L.XPRBT κ M g F P R n).call none (u :: args) w = L.Xb.call none (u :: args) w := by
  simp [XPRBT, hn]

open Classical in
theorem XPRBT_ind {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat} {u : CV} {args : List CV}
    {w : Arm.ArmState} {h : Clif.Function} (hs : symCallee L.Xb L.P (lo64 u) = some h) :
    (L.XPRBT κ M g F P R n).call none (u :: args) w =
      if L.IndTo g h ∧ args.length = (regLocs h.sig).length
      then L.progXPRBT κ M F h args (P n) (R n) w else none := by
  simp only [XPRBT, hs]

theorem XPRBT_base {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat} {m : String}
    (hn : L.P.func? m = none) (uses : List CV) (w : Arm.ArmState) :
    (L.XPRBT κ M g F P R n).call (some m) uses w = L.Xb.call (some m) uses w := by
  simp [XPRBT, hn]

theorem progXBT_ext {M : Nat} {F : BitVec 64 → Prop} {h : Clif.Function}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hx : L.progXBT κ M F h uses w = some (outs, w')) :
    Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  unfold progXBT at hx
  split at hx
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨-, rfl⟩ := hx
    exact ⟨hc.2, by rw [(L.pcall_pc M h _).1, L.program_canon]⟩
  · cases hx

theorem progXPRBT_ext {M : Nat} {F : BitVec 64 → Prop} {h : Clif.Function}
    {uses : List CV} {Pn : BitVec 64 → BitVec 8} {Sn w : Arm.ArmState} {outs : List CV}
    {w' : Arm.ArmState} (hx : L.progXPRBT κ M F h uses Pn Sn w = some (outs, w')) :
    Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  have := L.progXBT_ext hx
  exact ⟨this.1, this.2.trans (L.program_worldPR h Pn Sn w)⟩

theorem XPRBT_ext (hL : L.Ok) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat} {d : Option String}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hx : (L.XPRBT κ M g F P R n).call d uses w = some (outs, w'))
    (herr : Arm.r .ERR w = .None) : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  cases d with
  | some m =>
    cases hpf : L.P.func? m with
    | none =>
      rw [L.XPRBT_base hpf] at hx
      exact hL.baseExt _ _ _ _ _ (.inr ⟨m, rfl, hpf⟩) hx herr
    | some h =>
      rw [L.XPRBT_prog hpf] at hx
      exact L.progXPRBT_ext hx
  | none =>
    cases uses with
    | nil => exact hL.baseExt _ _ _ _ _ (.inl rfl) hx herr
    | cons u args =>
      cases hs : symCallee L.Xb L.P (lo64 u) with
      | none =>
        rw [L.XPRBT_none hs] at hx
        exact hL.baseExt _ _ _ _ _ (.inl rfl) hx herr
      | some h =>
        rw [L.XPRBT_ind hs] at hx
        split at hx
        · exact L.progXPRBT_ext hx
        · cases hx

end LinkSys

end E2E
