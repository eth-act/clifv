import FV.E2E.RegLevelDriverSem

/-!
# A call semantics guarded by its callee contract (SEM1 item (b), `docs/plans/uninit.md` §5.9)

With the slot-byte oracle the CLIF callee run of call `n` reads one fixed byte table, while the
canonical callee run of `XPR n` depends on the VCode `(uses, w)` beyond what the CLIF contract
fixes (64-bit argument registers, the world outside the live allocations). So `XCallsOk` cannot
hold for `XPRI` at every related `(uses, w)` (§5.9, "Finding"). `ExtSem.guard X Q` keeps `X`'s
result where it satisfies `Q` and otherwise returns an ε-chosen result satisfying `Q`:

* `ExtSem.guard`, `guard_of` (`X`'s result is kept where it satisfies `Q`), `guard_spec`;
* `CallPost env exts sigs MR sym d uses w r`: `r` is a result `XCallsOk`/`XCallsIndOk` accept for
  the call `(d, uses, w)`, for every CLIF invocation the call can stand for;
* `xCallsOk_guard`, `xCallsIndOk_guard`: the guarded semantics meets both contracts as soon as
  every call has some acceptable result (`∀ d uses w, ∃ r, CallPost … d uses w r`).

So the contract side (stage 1) needs only existence, and the machine side (stage 2) needs the
guarded result to be `X`'s at the calls the machine makes (`guard_of`).
-/

namespace E2E

open Backend Backend.Proof

open Classical in
/-- **`X` guarded by `Q`**: `X`'s result where it satisfies `Q`, otherwise an ε-chosen result
satisfying `Q` (if any), otherwise `X`'s. -/
noncomputable def _root_.Backend.Proof.ExtSem.guard (X : ExtSem)
    (Q : Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop) : ExtSem where
  call d uses w :=
    match X.call d uses w with
    | some r => if Q d uses w r then some r
      else if h : ∃ r', Q d uses w r' then some (Classical.choose h) else some r
    | none => if h : ∃ r', Q d uses w r' then some (Classical.choose h) else none
  sym := X.sym
  tp := X.tp
  tlsFlags := X.tlsFlags

@[simp] theorem _root_.Backend.Proof.ExtSem.guard_sym (X : ExtSem)
    (Q : Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop) :
    (X.guard Q).sym = X.sym := rfl

@[simp] theorem _root_.Backend.Proof.ExtSem.guard_tp (X : ExtSem)
    (Q : Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop) :
    (X.guard Q).tp = X.tp := rfl

@[simp] theorem _root_.Backend.Proof.ExtSem.guard_tlsFlags (X : ExtSem)
    (Q : Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop) :
    (X.guard Q).tlsFlags = X.tlsFlags := rfl

/-- **Where `X`'s result satisfies `Q`, the guarded semantics returns it.** -/
theorem _root_.Backend.Proof.ExtSem.guard_of {X : ExtSem}
    {Q : Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop}
    {d : Option String} {uses : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState}
    (hx : X.call d uses w = some r) (hq : Q d uses w r) : (X.guard Q).call d uses w = some r := by
  simp only [ExtSem.guard, hx, hq, ↓reduceIte]

/-- **Where some result satisfies `Q`, the guarded semantics returns one.** -/
theorem _root_.Backend.Proof.ExtSem.guard_spec {X : ExtSem}
    {Q : Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop}
    {d : Option String} {uses : List CV} {w : Arm.ArmState} (h : ∃ r, Q d uses w r) :
    ∃ r, (X.guard Q).call d uses w = some r ∧ Q d uses w r := by
  simp only [ExtSem.guard]
  cases hx : X.call d uses w with
  | some r =>
    by_cases hq : Q d uses w r
    · exact ⟨r, by simp [hq], hq⟩
    · exact ⟨Classical.choose h, by simp [hq, h], Classical.choose_spec h⟩
  | none => exact ⟨Classical.choose h, by simp [h], Classical.choose_spec h⟩

/-- **The results the callee contracts accept for a call** `(d, uses, w)`: for every CLIF
invocation of an extern of `exts` (`XCallsOk`) or, through an indirect call of a signature of
`sigs`, of any extern (`XCallsIndOk`) that the call can stand for, `r` has one value per declared
return (#587: an `sret` callee's struct pointer is not a call result), the first ones related to
the CLIF results, and a world related to the CLIF memory after the call. -/
def CallPost (env : Clif.Env) (exts : List Clif.ExtFunc) (sigs : List Clif.Signature)
    (MR : MemRelT) (sym : String → Int → BitVec 64) (d : Option String) (uses : List CV)
    (w : Arm.ArmState) (r : List CV × Arm.ArmState) : Prop :=
  (∀ ext ∈ exts, ∀ g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (args : List CV)
    (vals rvals : List Clif.Val) (cm' : Clif.Mem),
    env.extern ext.name = some g →
    (d = some ext.name ∧ uses = args ∨
      d = none ∧ ext.colocated = false ∧ uses = ofX (sym ext.name 0) :: args) →
    ArgsAt ext.sig vals args w → MR sl cm w →
    g vals cm = .returned rvals cm' → rvals.length = ext.sig.returns.length →
    r.1.length = ext.sig.returns.length ∧ PrefixHold rvals r.1 ∧ MR sl cm' r.2) ∧
  (∀ sig ∈ sigs, ∀ (n : String) g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (u : CV)
    (args : List CV) (vals rvals : List Clif.Val) (cm' : Clif.Mem),
    d = none → uses = u :: args →
    env.extern n = some g → (∀ s, env.sigOf n = some s → sig.abiMatch s = true) →
    lo64 u = sym n 0 →
    vals.length ≤ 8 → AllHold vals args → MR sl cm w →
    g vals cm = .returned rvals cm' → rvals.length = sig.returns.length →
    vals.map (·.ty) = Clif.AbiParam.tys sig.params →
    r.1.length = sig.returns.length ∧ PrefixHold rvals r.1 ∧ MR sl cm' r.2)

/-- **The guarded semantics meets the extern contract** when every call has an accepted
result. -/
theorem xCallsOk_guard {env : Clif.Env} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
    {MR : MemRelT} (X : ExtSem)
    (hex : ∀ d uses w, ∃ r, CallPost env exts sigs MR X.sym d uses w r) :
    XCallsOk env exts MR (X.guard (CallPost env exts sigs MR X.sym)) := by
  intro ext hext g sl cm w d uses args vals rvals cm' hg hd hargs hmr hret hlen
  obtain ⟨⟨outs, w'⟩, hc, hq⟩ := ExtSem.guard_spec (X := X) (hex d uses w)
  obtain ⟨h1, h2, h3⟩ := hq.1 ext hext g sl cm args vals rvals cm' hg hd hargs hmr hret hlen
  exact ⟨outs, w', hc, h1, h2, h3⟩

/-- **The guarded semantics meets the indirect-call contract** when every call has an accepted
result. -/
theorem xCallsIndOk_guard {env : Clif.Env} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
    {MR : MemRelT} (X : ExtSem)
    (hex : ∀ d uses w, ∃ r, CallPost env exts sigs MR X.sym d uses w r) :
    XCallsIndOk env sigs MR (X.guard (CallPost env exts sigs MR X.sym)) := by
  intro sig hsig n g sl cm w u args vals rvals cm' hg hs hu h8 hall hmr hret hlen hty
  obtain ⟨⟨outs, w'⟩, hc, hq⟩ := ExtSem.guard_spec (X := X) (hex none (u :: args) w)
  obtain ⟨h1, h2, h3⟩ :=
    hq.2 sig hsig n g sl cm u args vals rvals cm' rfl rfl hg hs hu h8 hall hmr hret hlen hty
  exact ⟨outs, w', hc, h1, h2, h3⟩

end E2E
