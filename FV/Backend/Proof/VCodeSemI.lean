module

public import FV.Backend.Proof.RegallocCSem

@[expose] public section

/-!
# The VCode world with a call counter (SEM1 step 2, `docs/plans/uninit.md` §5.3)

Under the slot-byte oracle (`Clif.Place.init`, #537) a callee's results depend on stale stack
bytes of the actual machine run, so the per-function theorem's call semantics has to give the
`n`-th call of an activation the actual run's `n`-th callee result (a prophecy fixed by the
machine entry state), not one result for every world. This file is the leaf of that change:

* `VConf.mapW`/`MConf.mapW`, `VStep_mapW`/`MStep_mapW` and `VStep_liftW`/`MStep_liftW`: a world
  map `π : W₂ → W₁` along which an instruction semantics `sem₂` projects to `sem₁`
  (`ISem.ProjW`) carries VCode and allocated-code runs of `sem₂` to runs of `sem₁`, and back
  when every behaviour of `sem₁` lifts (`ISem.LiftsW`). Generic in the value and world types.
* `ExtSemI`: the externals with the calls indexed by the activation's call count;
  `ExtSemI.at X n`: the `ExtSem` of call number `n`; `ExtSemI.const X`: every call `X`'s.
* `csemI`: `csem` on the world `Arm.ArmState × Nat`, the second component counting the calls
  (`MInst.isCallI`: `call`, `try_call`'s call). A call uses `X.at n` and bumps the counter; every
  other instruction is `csem` at any index (`csem_call_congr`: only calls read `ExtSem.call`)
  and keeps it (`csemI_noncall`).
* `csemI_const_projW`/`csemI_const_liftsW`, `vstar_csemI_const`/`vstar_csemI_const_lift`: with
  one `ExtSem` for every call (`ExtSemI.const`) the counted semantics is today's `csem`, runs
  included, so the existing theory is the special case.
-/

namespace Backend.Proof

open Backend

/-! ## World maps -/

section
variable {V W₁ W₂ : Type} (π : W₂ → W₁)

/-- A VCode configuration with its world mapped by `π`. -/
def VConf.mapW : VConf V W₂ → VConf V W₁
  | .run s => .run ⟨s.b, s.k, s.ρ, π s.w⟩
  | .ret vals w => .ret vals (π w)
  | .halt w => .halt (π w)

/-- An allocated-code configuration with its world mapped by `π`. -/
def MConf.mapW : MConf V W₂ → MConf V W₁
  | .run s => .run ⟨s.b, s.its, s.m, π s.w⟩
  | .ret vals m w => .ret vals m (π w)
  | .halt w => .halt (π w)

/-- `sem₂` projects to `sem₁` along `π`: each of its results is one of `sem₁` on the mapped
worlds. -/
def ISem.ProjW (sem₂ : ISem V W₂) (sem₁ : ISem V W₁) : Prop :=
  ∀ i uses w outs w' ctl, sem₂ i uses w = some (outs, w', ctl) →
    sem₁ i uses (π w) = some (outs, π w', ctl)

/-- Every result of `sem₁` on a mapped world `π w` is the map of one of `sem₂` on `w`. -/
def ISem.LiftsW (sem₂ : ISem V W₂) (sem₁ : ISem V W₁) : Prop :=
  ∀ i uses w outs v' ctl, sem₁ i uses (π w) = some (outs, v', ctl) →
    ∃ w', π w' = v' ∧ sem₂ i uses w = some (outs, w', ctl)

variable {π}

theorem VNext_mapW {vc : VCode} {b k n : Nat} {i : MInst} {uses : List V} {ρ : Nat → V}
    {w : W₂} {ctl : Ctl} {c : VConf V W₂} (h : VNext vc b k n i uses ρ w ctl c) :
    VNext vc b k n i uses ρ (π w) ctl (c.mapW π) := by
  cases h with
  | next hk => exact .next hk
  | goto hk hs he => exact .goto hk hs he
  | ret hi => exact .ret hi
  | halt => exact .halt

theorem VNext_liftW {vc : VCode} {b k n : Nat} {i : MInst} {uses : List V} {ρ : Nat → V}
    {w : W₂} {ctl : Ctl} {d : VConf V W₁} (h : VNext vc b k n i uses ρ (π w) ctl d) :
    ∃ c, c.mapW π = d ∧ VNext vc b k n i uses ρ w ctl c := by
  cases h with
  | next hk => exact ⟨.run ⟨b, k + 1, ρ, w⟩, rfl, .next hk⟩
  | goto hk hs he => exact ⟨.run ⟨_, 0, _, w⟩, rfl, .goto hk hs he⟩
  | ret hi => exact ⟨.ret uses w, rfl, .ret hi⟩
  | halt => exact ⟨.halt w, rfl, .halt⟩

/-- **A VCode step of `sem₂` is one of `sem₁` on the mapped configurations.** -/
theorem VStep_mapW {vc : VCode} {sem₂ : ISem V W₂} {sem₁ : ISem V W₁}
    (hp : ISem.ProjW π sem₂ sem₁) {c c' : VConf V W₂} (h : VStep vc sem₂ c c') :
    VStep vc sem₁ (c.mapW π) (c'.mapW π) := by
  cases h with
  | step hb hi ho hs hl hn => exact .step hb hi ho (hp _ _ _ _ _ _ hs) hl (VNext_mapW hn)

/-- **A VCode step of `sem₁` from a mapped configuration lifts to one of `sem₂`.** -/
theorem VStep_liftW {vc : VCode} {sem₂ : ISem V W₂} {sem₁ : ISem V W₁}
    (hl : ISem.LiftsW π sem₂ sem₁) {c : VConf V W₂} {d : VConf V W₁}
    (h : VStep vc sem₁ (c.mapW π) d) : ∃ c', c'.mapW π = d ∧ VStep vc sem₂ c c' := by
  match c, h with
  | .run ⟨b, k, ρ, w⟩, .step hb hi ho hs hlen hn =>
    obtain ⟨w', rfl, hs'⟩ := hl _ _ _ _ _ _ hs
    obtain ⟨c', rfl, hn'⟩ := VNext_liftW hn
    exact ⟨c', rfl, .step hb hi ho hs' hlen hn'⟩

theorem vstar_mapW {vc : VCode} {sem₂ : ISem V W₂} {sem₁ : ISem V W₁}
    (hp : ISem.ProjW π sem₂ sem₁) {c c' : VConf V W₂} (h : Star (VStep vc sem₂) c c') :
    Star (VStep vc sem₁) (c.mapW π) (c'.mapW π) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (VStep_mapW hp h) ih

theorem vstar_liftW {vc : VCode} {sem₂ : ISem V W₂} {sem₁ : ISem V W₁}
    (hl : ISem.LiftsW π sem₂ sem₁) {c : VConf V W₂} {d : VConf V W₁}
    (h : Star (VStep vc sem₁) (c.mapW π) d) : ∃ c', c'.mapW π = d ∧ Star (VStep vc sem₂) c c' := by
  generalize he : c.mapW π = e at h
  induction h generalizing c with
  | refl => exact ⟨c, he, .refl _⟩
  | step h1 _ ih =>
    subst he
    obtain ⟨c1, rfl, h1'⟩ := VStep_liftW hl h1
    obtain ⟨c', hc', h'⟩ := ih rfl
    exact ⟨c', hc', .step h1' h'⟩

theorem MNext_mapW {vc : VCode} {rf : RFunc} {b k n : Nat} {i : MInst} {uses : List V}
    {its : List RItem} {m : Loc → V} {w : W₂} {ctl : Ctl} {c : MConf V W₂}
    (h : MNext vc rf b k n i uses its m w ctl c) :
    MNext vc rf b k n i uses its m (π w) ctl (c.mapW π) := by
  cases h with
  | next hk => exact .next hk
  | goto hk hs hi => exact .goto hk hs hi
  | ret hi => exact .ret hi
  | halt => exact .halt

theorem MNext_liftW {vc : VCode} {rf : RFunc} {b k n : Nat} {i : MInst} {uses : List V}
    {its : List RItem} {m : Loc → V} {w : W₂} {ctl : Ctl} {d : MConf V W₁}
    (h : MNext vc rf b k n i uses its m (π w) ctl d) :
    ∃ c, c.mapW π = d ∧ MNext vc rf b k n i uses its m w ctl c := by
  cases h with
  | next hk => exact ⟨.run ⟨b, its, m, w⟩, rfl, .next hk⟩
  | goto hk hs hi => exact ⟨.run ⟨_, _, m, w⟩, rfl, .goto hk hs hi⟩
  | ret hi => exact ⟨.ret uses m w, rfl, .ret hi⟩
  | halt => exact ⟨.halt w, rfl, .halt⟩

/-- **An allocated-code step of `sem₂` is one of `sem₁` on the mapped configurations.** -/
theorem MStep_mapW {vc : VCode} {sem₂ : ISem V W₂} {sem₁ : ISem V W₁} {keep : Reg → V → V}
    {rf : RFunc} (hp : ISem.ProjW π sem₂ sem₁) {c c' : MConf V W₂}
    (h : MStep vc sem₂ keep rf c c') : MStep vc sem₁ keep rf (c.mapW π) (c'.mapW π) := by
  cases h with
  | move => exact .move
  | op hb hi ho ha hs hl hh hc hn =>
    exact .op hb hi ho ha (hp _ _ _ _ _ _ hs) hl hh hc (MNext_mapW hn)

/-- **An allocated-code step of `sem₁` from a mapped configuration lifts to one of `sem₂`.** -/
theorem MStep_liftW {vc : VCode} {sem₂ : ISem V W₂} {sem₁ : ISem V W₁} {keep : Reg → V → V}
    {rf : RFunc} (hl : ISem.LiftsW π sem₂ sem₁) {c : MConf V W₂} {d : MConf V W₁}
    (h : MStep vc sem₁ keep rf (c.mapW π) d) :
    ∃ c', c'.mapW π = d ∧ MStep vc sem₂ keep rf c c' := by
  match c, h with
  | .run ⟨b, _, m, w⟩, .move => exact ⟨.run ⟨b, _, _, w⟩, rfl, .move⟩
  | .run ⟨b, _, m, w⟩, .op hb hi ho ha hs hlen hh hc hn =>
    obtain ⟨w', rfl, hs'⟩ := hl _ _ _ _ _ _ hs
    obtain ⟨c', rfl, hn'⟩ := MNext_liftW hn
    exact ⟨c', rfl, .op hb hi ho ha hs' hlen hh hc hn'⟩

theorem mstar_mapW {vc : VCode} {sem₂ : ISem V W₂} {sem₁ : ISem V W₁} {keep : Reg → V → V}
    {rf : RFunc} (hp : ISem.ProjW π sem₂ sem₁) {c c' : MConf V W₂}
    (h : Star (MStep vc sem₂ keep rf) c c') :
    Star (MStep vc sem₁ keep rf) (c.mapW π) (c'.mapW π) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (MStep_mapW hp h) ih

theorem mstar_liftW {vc : VCode} {sem₂ : ISem V W₂} {sem₁ : ISem V W₁} {keep : Reg → V → V}
    {rf : RFunc} (hl : ISem.LiftsW π sem₂ sem₁) {c : MConf V W₂} {d : MConf V W₁}
    (h : Star (MStep vc sem₁ keep rf) (c.mapW π) d) :
    ∃ c', c'.mapW π = d ∧ Star (MStep vc sem₂ keep rf) c c' := by
  generalize he : c.mapW π = e at h
  induction h generalizing c with
  | refl => exact ⟨c, he, .refl _⟩
  | step h1 _ ih =>
    subst he
    obtain ⟨c1, rfl, h1'⟩ := MStep_liftW hl h1
    obtain ⟨c', hc', h'⟩ := ih rfl
    exact ⟨c', hc', .step h1' h'⟩

end

/-! ## Calls indexed by the call count -/

/-- The externals of an activation with its calls indexed by their number in the activation's
run (`call n d args w`: the results and the world after call number `n`, counted from `0`; the
other fields as in `ExtSem`). -/
structure ExtSemI where
  call : Nat → Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState)
  sym : String → Int → BitVec 64
  tp : BitVec 64
  tlsFlags : String → Arm.ArmState → Arm.PState

/-- The `ExtSem` of call number `n`. -/
def ExtSemI.at (X : ExtSemI) (n : Nat) : ExtSem :=
  { call := X.call n, sym := X.sym, tp := X.tp, tlsFlags := X.tlsFlags }

/-- The same `ExtSem` for every call. -/
def ExtSemI.const (X : ExtSem) : ExtSemI :=
  { call := fun _ => X.call, sym := X.sym, tp := X.tp, tlsFlags := X.tlsFlags }

@[simp] theorem ExtSemI.const_at (X : ExtSem) (n : Nat) : (ExtSemI.const X).at n = X := rfl

/-- The instructions `csem` gives a callee result (`ExtSem.call`): `call` and a `try_call`'s
call. -/
def _root_.Backend.MInst.isCallI : MInst → Bool
  | .call _ | .tryCall _ _ => true
  | _ => false

/-- **Only calls read `ExtSem.call`.** -/
theorem csem_call_congr (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    {i : MInst} (h : i.isCallI = false) : csem F ctx { X with call := c } i = csem F ctx X i := by
  cases i <;> first | rfl | cases h

/-- `csem` of a non-call is the same at every call index. -/
theorem csem_at_noncall (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) {i : MInst}
    (h : i.isCallI = false) (n n' : Nat) : csem F ctx (X.at n) i = csem F ctx (X.at n') i :=
  csem_call_congr F ctx (X.at n') (X.call n) h

open Classical in
/-- **The counted concrete semantics**: `csem` on the first component of the world, the call of
number `n` (the second component) with `X.at n`, a call bumping the counter. -/
noncomputable def csemI (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) :
    ISem CV (Arm.ArmState × Nat) :=
  fun i uses w => (csem F ctx (X.at w.2) i uses w.1).map
    fun r => (r.1, (r.2.1, if i.isCallI then w.2 + 1 else w.2), r.2.2)

theorem csemI_eq (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) (i : MInst)
    (uses : List CV) (w : Arm.ArmState) (n : Nat) :
    csemI F ctx X i uses (w, n) = (csem F ctx (X.at n) i uses w).map
      fun r => (r.1, (r.2.1, if i.isCallI then n + 1 else n), r.2.2) := rfl

/-- A non-call: `csem` at any index, the counter kept. -/
theorem csemI_noncall (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) {i : MInst}
    (h : i.isCallI = false) (uses : List CV) (w : Arm.ArmState) (n n' : Nat) :
    csemI F ctx X i uses (w, n) = (csem F ctx (X.at n') i uses w).map
      fun r => (r.1, (r.2.1, n), r.2.2) := by
  rw [csemI_eq, csem_at_noncall F ctx X h n n']
  simp only [h, Bool.false_eq_true, ↓reduceIte]

/-- A call: call number `n` with `X.at n`, the counter bumped. -/
theorem csemI_call (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) {i : MInst}
    (h : i.isCallI = true) (uses : List CV) (w : Arm.ArmState) (n : Nat) :
    csemI F ctx X i uses (w, n) = (csem F ctx (X.at n) i uses w).map
      fun r => (r.1, (r.2.1, n + 1), r.2.2) := by
  rw [csemI_eq]; simp only [h, ↓reduceIte]

/-- **One `ExtSem` for every call: `csemI` projects to `csem`** along `Prod.fst`. -/
theorem csemI_const_projW (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    ISem.ProjW Prod.fst (csemI F ctx (ExtSemI.const X)) (csem F ctx X) := by
  intro i uses w outs w' ctl h
  obtain ⟨w, n⟩ := w
  rw [csemI_eq] at h
  cases hc : csem F ctx X i uses w with
  | none => rw [ExtSemI.const_at, hc] at h; cases h
  | some r =>
    rw [ExtSemI.const_at, hc] at h
    obtain ⟨o, v, c⟩ := r
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl

/-- **One `ExtSem` for every call: every `csem` behaviour is one of `csemI`.** -/
theorem csemI_const_liftsW (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    ISem.LiftsW Prod.fst (csemI F ctx (ExtSemI.const X)) (csem F ctx X) := by
  intro i uses w outs v' ctl h
  obtain ⟨w, n⟩ := w
  refine ⟨(v', if i.isCallI then n + 1 else n), rfl, ?_⟩
  rw [csemI_eq, ExtSemI.const_at]
  exact (congrArg (Option.map _) h).trans rfl

/-- **A VCode run of `csemI` with one `ExtSem` for every call is a run of `csem`.** -/
theorem vstar_csemI_const {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {vc : VCode}
    {c c' : VConf CV (Arm.ArmState × Nat)}
    (h : Star (VStep vc (csemI F ctx (ExtSemI.const X))) c c') :
    Star (VStep vc (csem F ctx X)) (c.mapW Prod.fst) (c'.mapW Prod.fst) :=
  vstar_mapW (csemI_const_projW F ctx X) h

/-- **A VCode run of `csem` is one of `csemI` with one `ExtSem` for every call**, from any
counter. -/
theorem vstar_csemI_const_lift {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {vc : VCode}
    {c : VConf CV (Arm.ArmState × Nat)} {d : VConf CV Arm.ArmState}
    (h : Star (VStep vc (csem F ctx X)) (c.mapW Prod.fst) d) :
    ∃ c', c'.mapW Prod.fst = d ∧ Star (VStep vc (csemI F ctx (ExtSemI.const X))) c c' :=
  vstar_liftW (csemI_const_liftsW F ctx X) h

end Backend.Proof
