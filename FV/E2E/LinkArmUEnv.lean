import FV.E2E.LinkArmU
import FV.Clif.LinkClifXN

/-!
# Linking at the Arm level with unwinding: the external semantics and the statement (S10f, #233)

`FV/E2E/LinkArm.lean`'s §Cond/progX/X/envR/envOf and `Thm`, for the linked machine with unwinding
(`LinkSysU`, `FV/E2E/LinkArmU.lean`) and the CLIF runs with unwinding (`Clif.runLoopX`).

* `pcallU`/`praiseU`: the linked machine's call of a program function at depth `M`: the state at
  its first return (`returnedCall`; an error state when it left by unwinding), and its raise
  (`raisedCall`: the exception object in x0 and that state, when it left by unwinding).
* `CondU`/`CondR`: `LinkSys.Cond` with the callee run with unwinding (`crunX M`) returning,
  resp. ending `unwound`.
* `progXU`/`progXR`, `XU`/`XRU`: an activation's external semantics (`ExtSem`, normal results)
  and raising callees (`XRaise`) at depth `M`: a program callee is the linked machine's call from
  the canonical state when `CondU` (resp. `CondR`) holds and the call returns (resp. raises); the
  rest is the base's (`Xb`, `XRb`).
* `envRX`/`envOfX`: the CLIF environment with unwinding of an activation (`Clif.linkEnvRX` with the
  callee runs `crunX M`, without the functions it may not reach).
* `CrunOkX`: the callee runs with unwinding are whole-program runs with unwinding (`LinkSys.CrunOk`'s
  counterpart, from `Clif.runLoopX_linkN`/`_linkD`: `crunOkX_std`, `crunOkX_peak`).
* `ThmU κ M`: `LinkSys.Thm` on the machine with unwinding, with the exceptional end: a run of the
  program without functions under `envRX M g` that ends `unwound` is realised by every machine-side
  activation leaving its frame by unwinding (`ActUnw`, `UnwExit` at the last step).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-! ## The linked call with unwinding -/

/-- The linked call returns at its first return: the return address, no error, the caller's
program and `sp`. -/
theorem linkedCall_retOf {M : Arm.ArmState → Arm.ArmState} {a : Art} {s : Arm.ArmState}
    (h : ∃ n, RetOf a s (runX M n (enterAt a s))) :
    Arm.r .PC (linkedCall M a s) = Arm.r .PC s + 4 ∧ Arm.r .ERR (linkedCall M a s) = .None ∧
      (linkedCall M a s).program = s.program ∧ spv (linkedCall M a s) = spv s := by
  have hr := (firstNat_spec _ h).1
  simp only [linkedCall, h, ↓reduceDIte]
  refine ⟨by rw [r_set_program]; exact hr.1, by rw [r_set_program]; exact hr.2.1, rfl, ?_⟩
  simp only [spv]
  rw [r_set_program]
  exact hr.2.2.2

theorem junkAt_pc (s : Arm.ArmState) :
    (junkAt s).program = s.program ∧ Arm.r .PC (junkAt s) = Arm.r .PC s + 4 := by
  simp only [junkAt, Arm.w_program, true_and]
  rw [Arm.r_of_w_different (by simp), Arm.r_of_w_same]

theorem linkedCall_pc (M : Arm.ArmState → Arm.ArmState) (a : Art) (s : Arm.ArmState) :
    (linkedCall M a s).program = s.program ∧ Arm.r .PC (linkedCall M a s) = Arm.r .PC s + 4 := by
  by_cases h : ∃ n, RetOf a s (runX M n (enterAt a s))
  · obtain ⟨h1, -, h3, -⟩ := linkedCall_retOf h
    exact ⟨h3, h1⟩
  · simp only [linkedCall, h, ↓reduceDIte]
    exact junkAt_pc s

theorem returnedCall_pc (M : Arm.ArmState → Arm.ArmState) (U : Unw.UnwHooks) (T : Unw.FnTables)
    (a : Art) (s : Arm.ArmState) :
    (returnedCall M U T a s).program = s.program ∧
      Arm.r .PC (returnedCall M U T a s) = Arm.r .PC s + 4 := by
  unfold returnedCall
  split
  · exact junkAt_pc s
  · exact linkedCall_pc M a s

theorem junkAt_err (s : Arm.ArmState) : Arm.r .ERR (junkAt s) ≠ .None := by
  simp only [junkAt]
  rw [Arm.r_of_w_same]
  simp

/-- A call that returns normally (no error) did not leave the callee's frame by unwinding. -/
theorem returnedCall_ok {M : Arm.ArmState → Arm.ArmState} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {a : Art} {s : Arm.ArmState} (h : Arm.r .ERR (returnedCall M U T a s) = .None) :
    ¬ ExitU M U T a s ∧ returnedCall M U T a s = linkedCall M a s := by
  unfold returnedCall at h ⊢
  split at h
  · exact absurd h (junkAt_err s)
  · rename_i hx
    simp only [hx, ↓reduceIte, not_false_eq_true, and_self]

/-- **A raising call is at the callee's first return**: the exception object is x0 there, at the
return address, without error, with the caller's program and `sp`. -/
theorem raisedCall_some {M : Arm.ArmState → Arm.ArmState} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {a : Art} {s : Arm.ArmState} {obj : BitVec 64} {t : Arm.ArmState}
    (h : raisedCall M U T a s = some (obj, t)) :
    ExitU M U T a s ∧ t = linkedCall M a s ∧ obj = xreg 0 t ∧ Arm.r .PC t = Arm.r .PC s + 4 ∧
      Arm.r .ERR t = .None ∧ t.program = s.program ∧ spv t = spv s := by
  unfold raisedCall at h
  split at h
  · rename_i hx
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hr, -⟩ := id hx
    exact ⟨hx, rfl, rfl, linkedCall_retOf hr⟩
  · cases h

theorem raisedCall_none_of_returned {M : Arm.ArmState → Arm.ArmState} {U : Unw.UnwHooks}
    {T : Unw.FnTables} {a : Art} {s : Arm.ArmState}
    (h : Arm.r .ERR (returnedCall M U T a s) = .None) : raisedCall M U T a s = none := by
  simp only [raisedCall, (returnedCall_ok h).1, ↓reduceIte]

namespace LinkSysU

variable (L : LinkSysU)
variable {κ : Nat → Clif.Function → Nat}

/-- The linked machine's call of the function `g` of `P` at depth `M` (normal return). -/
noncomputable def pcallU : Nat → Clif.Function → Arm.ArmState → Arm.ArmState
  | 0, _, s => junkAt s
  | M + 1, g, s => returnedCall (L.machU M g) (L.UU M) (L.A g).tables (L.A g) s

/-- The linked machine's raise of a call of the function `g` of `P` at depth `M`. -/
noncomputable def praiseU : Nat → Clif.Function → Arm.ArmState → Option (BitVec 64 × Arm.ArmState)
  | 0, _, _ => none
  | M + 1, g, s => raisedCall (L.machU M g) (L.UU M) (L.A g).tables (L.A g) s

theorem hooksU_call (M : Nat) :
    (L.hooksU M).call = LinkSys.callHook L.Hb L.Xb L.P (L.pcallU M) := by
  cases M <;> rfl

theorem UU_raise (M : Nat) : (L.UU M).raise = raiseHook L.Ub L.Xb L.P (L.praiseU M) := by
  cases M <;> rfl

theorem hooksU_tls (M : Nat) : (L.hooksU M).tls = L.Hb.tls := by cases M <;> rfl

theorem hooksU_base {M : Nat} {d : Option String} (h : L.BaseDest d) (u : Arm.ArmState)
    (hn : d = none → (blrTarget u).bind (symCallee L.Xb L.P) = none) :
    (L.hooksU M).call d u = L.Hb.call d u := by
  rw [hooksU_call]
  rcases h with rfl | ⟨n, rfl, hpf⟩
  · simp only [LinkSys.callHook, hn rfl]
  · simp only [LinkSys.callHook, hpf]

theorem hooksU_some {M : Nat} {n : String} {h : Clif.Function} (hpf : L.P.func? n = some h)
    (u : Arm.ArmState) : (L.hooksU M).call (some n) u = L.pcallU M h u := by
  rw [hooksU_call]; simp only [LinkSys.callHook, hpf]

theorem hooksU_none {M : Nat} {h : Clif.Function} {u : Arm.ArmState}
    (hb : (blrTarget u).bind (symCallee L.Xb L.P) = some h) :
    (L.hooksU M).call none u = L.pcallU M h u := by
  rw [hooksU_call]; simp only [LinkSys.callHook, hb]

theorem UU_base {M : Nat} {d : Option String} (h : L.BaseDest d) (u : Arm.ArmState)
    (hn : d = none → (blrTarget u).bind (symCallee L.Xb L.P) = none) :
    (L.UU M).raise d u = L.Ub.raise d u := by
  rw [UU_raise]
  rcases h with rfl | ⟨n, rfl, hpf⟩
  · simp only [raiseHook, hn rfl]
  · simp only [raiseHook, hpf]

theorem UU_some {M : Nat} {n : String} {h : Clif.Function} (hpf : L.P.func? n = some h)
    (u : Arm.ArmState) : (L.UU M).raise (some n) u = L.praiseU M h u := by
  rw [UU_raise]; simp only [raiseHook, hpf]

theorem UU_none {M : Nat} {h : Clif.Function} {u : Arm.ArmState}
    (hb : (blrTarget u).bind (symCallee L.Xb L.P) = some h) :
    (L.UU M).raise none u = L.praiseU M h u := by
  rw [UU_raise]; simp only [raiseHook, hb]

theorem pcallU_pc (M : Nat) (h : Clif.Function) (u : Arm.ArmState) :
    (L.pcallU M h u).program = u.program ∧ Arm.r .PC (L.pcallU M h u) = Arm.r .PC u + 4 := by
  cases M with
  | zero => exact junkAt_pc u
  | succ M => exact returnedCall_pc _ _ _ _ u

/-- A raise of the linked machine's call of `h` is at `h`'s first return, left by unwinding. -/
theorem praiseU_some {M : Nat} {h : Clif.Function} {u : Arm.ArmState} {obj : BitVec 64}
    {t : Arm.ArmState} (hr : L.praiseU M h u = some (obj, t)) :
    0 < M ∧ ExitU (L.machU (M - 1) h) (L.UU (M - 1)) (L.A h).tables (L.A h) u ∧
      t = linkedCall (L.machU (M - 1) h) (L.A h) u ∧ obj = xreg 0 t ∧
      Arm.r .PC t = Arm.r .PC u + 4 ∧ Arm.r .ERR t = .None ∧ t.program = u.program ∧
      spv t = spv u := by
  cases M with
  | zero => cases hr
  | succ M => exact ⟨Nat.succ_pos M, raisedCall_some hr⟩

/-- **Exclusivity on the machine**: a call of `h` that returns without error does not raise. -/
theorem praiseU_none_of_pcallU {M : Nat} {h : Clif.Function} {u : Arm.ArmState}
    (he : Arm.r .ERR (L.pcallU M h u) = .None) : L.praiseU M h u = none := by
  cases M with
  | zero => rfl
  | succ M => exact raisedCall_none_of_returned he

/-! ## The external semantics of an activation with unwinding -/

/-- The common part of `LinkSys.Cond`: the callee's stack fits below `sp` outside the world and
the code, no error, and the call's arguments and the world are related to CLIF arguments and
memory from which `g`'s callee run with unwinding at depth `M` ends with an outcome `o` with
`Q o`. -/
def CondQ (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop) (g : Clif.Function)
    (uses : List CV) (w : Arm.ArmState) (Q : Clif.XOutcome → Prop) : Prop :=
  0 < M ∧ Arm.r .ERR w = .None ∧ (spv w).toNat % 16 = 0 ∧
  frameDrop (L.A g).af + κ (M - 1) g ≤ (spv w).toNat ∧
  (∀ a, StackBelow (frameDrop (L.A g).af + κ (M - 1) g) (spv w) a → F a ∧ ¬ L.Img a) ∧
  ∃ vals cm cs, MemRel F L.syms cm w ∧ ArgsAt g.sig vals uses w ∧
    StackArgsAvoid F g.sig vals w ∧ (L.NeedSlots → L.PlaceAt cm (spv w)) ∧
    Clif.initState L.P g.name vals cm = .ok cs ∧ Q (L.crunX M cs)

/-- `LinkSys.Cond` for the runs with unwinding: the callee run returns. -/
def CondU (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop) (g : Clif.Function)
    (uses : List CV) (w : Arm.ArmState) : Prop :=
  L.CondQ κ M F g uses w fun o => ∃ rvals cm', o = .returned rvals cm'

/-- The callee run ends `unwound`. -/
def CondR (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop) (g : Clif.Function)
    (uses : List CV) (w : Arm.ArmState) : Prop :=
  L.CondQ κ M F g uses w fun o => ∃ e cm', o = .unwound e cm'

open Classical in
/-- A call of the function `g` of `P` at depth `M` that returns: the results (x0.., one per
declared return; an `sret` function's struct pointer, returned in x8 as in Cranelift, #587, is
not a call result) and world of the linked machine's call of `g` from the canonical state, when
`CondU` holds and that call returned. -/
noncomputable def progXU (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop)
    (g : Clif.Function) (uses : List CV) (w : Arm.ArmState) : Option (List CV × Arm.ArmState) :=
  if L.CondU κ M F g uses w ∧ Arm.r .ERR (L.pcallU M g (L.canon g uses w)) = .None then
    some ((List.range g.sig.returns.length).map fun j =>
        regVal (L.pcallU M g (L.canon g uses w)) (.x j),
      L.pcallU M g (L.canon g uses w))
  else none

open Classical in
/-- A call of the function `g` of `P` at depth `M` that raises: the exception object and world of
the linked machine's raise of `g` from the canonical state, when `CondR` holds. -/
noncomputable def progXR (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop)
    (g : Clif.Function) (uses : List CV) (w : Arm.ArmState) : Option (BitVec 64 × Arm.ArmState) :=
  if L.CondR κ M F g uses w then L.praiseU M g (L.canon g uses w) else none

open Classical in
/-- **The external semantics of an activation of `g` at depth `M`, with unwinding** (`LinkSys.X`
with `progXU`). -/
noncomputable def XU (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) : ExtSem where
  call d uses w := match d with
    | some n => (match L.P.func? n with
      | some h => L.progXU κ M F h uses w
      | none => L.Xb.call d uses w)
    | none => (match uses with
      | u :: args => (match symCallee L.Xb L.P (lo64 u) with
        | some h => if L.IndTo g h ∧ args.length = (regLocs h.sig).length then
            L.progXU κ M F h args w else none
        | none => L.Xb.call none uses w)
      | [] => L.Xb.call none uses w)
  sym := L.Xb.sym
  tp := L.Xb.tp
  tlsFlags := L.Xb.tlsFlags

open Classical in
/-- **The raising callees of an activation of `g` at depth `M`**: a call (`bl`, or `blr` of an
address `g` may enter, `IndTo`) of a function of `P` raises as `progXR`; the rest is the base's
(`XRb`). -/
noncomputable def XRU (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) : XRaise where
  raise d uses w := match d with
    | some n => (match L.P.func? n with
      | some h => L.progXR κ M F h uses w
      | none => L.XRb.raise d uses w)
    | none => (match uses with
      | u :: args => (match symCallee L.Xb L.P (lo64 u) with
        | some h => if L.IndTo g h ∧ args.length = (regLocs h.sig).length then
            L.progXR κ M F h args w else none
        | none => L.XRb.raise none uses w)
      | [] => L.XRb.raise none uses w)

open Classical in
/-- **The per-function environment with unwinding of `g` at depth `M`** (`LinkSys.envR`): the
linked environment with the callee runs `crunX M` (`Clif.linkEnvRX`), without the functions of `P`
that `g` may not reach (`MayCall`). -/
noncomputable def envRX (M : Nat) (g : Clif.Function) : Clif.XEnv where
  extern n := if (L.P.func? n).isSome ∧ ¬ L.MayCall g n then none
    else (Clif.linkEnvRX L.P L.envX (L.crunX M)).extern n
  names := (Clif.linkEnvRX L.P L.envX (L.crunX M)).names
  sigOf := (Clif.linkEnvRX L.P L.envX (L.crunX M)).sigOf

open Classical in
/-- **The CLIF environment with unwinding of an activation of `g` at depth `M`** with stack
pointer `c` (`LinkSys.envOf`): `envRX`, the functions of `P` called only from a memory whose
slot-placement oracle has `c` (when program callees have slots). -/
noncomputable def envOfX (M : Nat) (g : Clif.Function) (c : BitVec 64) : Clif.XEnv where
  extern n := if (L.P.func? n).isSome ∧ ¬ L.MayCall g n then none
    else if (L.P.func? n).isSome then ((Clif.linkEnvRX L.P L.envX (L.crunX M)).extern n).map
      fun G vals cm => if L.NeedSlots → L.PlaceAt cm c then G vals cm else .stuck "slot placement"
    else (Clif.linkEnvRX L.P L.envX (L.crunX M)).extern n
  names := (Clif.linkEnvRX L.P L.envX (L.crunX M)).names
  sigOf := (Clif.linkEnvRX L.P L.envX (L.crunX M)).sigOf

/-- **The callee runs with unwinding of the linked system are whole-program runs with unwinding**
(`LinkSys.CrunOk`'s counterpart): a returning, trapping or unwinding one is a whole-program run of
some fuel (`runs`), none returns or unwinds at depth `0` (`zero`), and a complete one at a
positive depth is a complete run of the program without functions whose program calls are the
callee runs one level down (`link`, as `Clif.runLoopX_linkR`). -/
class CrunOkX : Prop where
  runs : ∀ M s o, L.crunX M s = o → ((∃ vals mem, o = .returned vals mem) ∨ (∃ c, o = .trapped c) ∨
    ∃ e mem, o = .unwound e mem) → ∃ N, Clif.runLoopX L.envX L.P N s.toX = o
  zero : ∀ s, (∀ vals cm, L.crunX 0 s ≠ .returned vals cm) ∧ ∀ e cm, L.crunX 0 s ≠ .unwound e cm
  link : ∀ M, 0 < M → ∀ f ∈ L.P.funcs, ∀ s : Clif.State, Clif.LInv L.P s →
    Clif.LInv (L.P.only f) s → (¬ Clif.IndFree f → s.mem.symbols = L.syms) → ∀ (E : Clif.XEnv),
    E.names = (Clif.linkEnvRX L.P L.envX (L.crunX (M - 1))).names →
    E.sigOf = (Clif.linkEnvRX L.P L.envX (L.crunX (M - 1))).sigOf →
    (∀ n, L.P.func? n = none → E.extern n = (Clif.linkEnvRX L.P L.envX (L.crunX (M - 1))).extern n) →
    (∀ h ∈ L.P.funcs, (h.name ∈ f.externs.map (·.2.name) ∨
      (L.syms h.name ≠ none ∧ ∃ d, Clif.IndSig f d ∧ d.abiMatch h.sig = true)) →
      E.extern h.name = (Clif.linkEnvRX L.P L.envX (L.crunX (M - 1))).extern h.name) →
    (∀ msg, L.crunX M s ≠ .stuck msg) → L.crunX M s ≠ .outOfFuel →
    ∃ m, Clif.runLoopX E L.P.bare m s.toX = L.crunX M s

/-! ## The per-state facts of the linked machine's runs with unwinding -/

/-- The activation of `a` entered at `c` has returned in `t` (`LinkSys.RetL`). -/
def RetU (a : Art) (c t : Arm.ArmState) : Prop :=
  Arm.r .PC t = xreg 30 c ∧ Arm.r .ERR t = .None ∧ t.program = a.fb.program a.base ∧ spv t = spv c

/-- The machine calls the function `h` of `P` at `s` from `g`'s code (`LinkSys.CallsAtL`). -/
def CallsAtU (g : Clif.Function) (s : Arm.ArmState) (h : Clif.Function) : Prop :=
  (∃ n, insnAt (L.A g).fa (progBase s) (Arm.r .PC s) = some (.bl n) ∧ L.P.func? n = some h) ∨
  ((∃ x, insnAt (L.A g).fa (progBase s) (Arm.r .PC s) = some (.blr x)) ∧
    (blrTarget s).bind (symCallee L.Xb L.P) = some h)

/-- **The states of the activation of `g` at depth `M` entered at `c` of the linked machine with
unwinding** before its return, and of the activations nested through its calls (returning or
raising) whose step ends without error (`LinkSys.ReachL` on `machU`; the last three indices: the
state's own activation's depth, function and entry, and the state). -/
inductive ReachLU (L : LinkSysU) :
    Nat → Clif.Function → Arm.ArmState → Nat → Clif.Function → Arm.ArmState → Arm.ArmState → Prop
  | act {M g c k} : (∀ j ≤ k, ¬ RetU (L.A g) c (runX (L.machU M g) j c)) →
      L.ReachLU M g c M g c (runX (L.machU M g) k c)
  | nest {M g c k h M' g' c' t} :
      (∀ j ≤ k, ¬ RetU (L.A g) c (runX (L.machU (M + 1) g) j c)) →
      L.CallsAtU g (runX (L.machU (M + 1) g) k c) h →
      Arm.r .ERR (runX (L.machU (M + 1) g) (k + 1) c) = .None →
      L.ReachLU M h (enterAt (L.A h) (runX (L.machU (M + 1) g) k c)) M' g' c' t →
      L.ReachLU (M + 1) g c M' g' c' t

/-- At a `blr` of `g` at `t` whose target is the function `h` of `P`, the call is one through a
register `tv` of `g`'s VCode by which `g` may enter `h` (`LinkSys.BlrAt`). -/
def BlrAtU (g : Clif.Function) (t : Arm.ArmState) : Prop :=
  ∀ x h, insnAt (L.A g).fa (L.A g).base (Arm.r .PC t) = some (.blr x) →
    (blrTarget t).bind (symCallee L.Xb L.P) = some h →
    ∃ info tv, (L.A g).vcp.CallSite info ∧ info.dest = .reg (.vreg tv .int) ∧ L.BlrTo g tv h

/-- **The per-state facts at a state `t` of the activation of `g` at depth `M` entered at `c`**
(`LinkSys.GoodAt` with unwinding): the register-level facts with unwinding (`actGoodXU`) of an
activation on `machU M g`, the code image among the kept addresses `G` and holding `imgMem` at
the entry and outside the activation's frame, and the callee of a `blr` one `g` may enter. -/
def GoodAtU (M : Nat) (g : Clif.Function) (c t : Arm.ArmState) : Prop :=
  ∃ X XR K G gv, Unw.ArmStepU X (L.hooksU M) (L.UU M) (L.A g).tables (L.A g).fa = L.machU M g ∧
    actGoodXU (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (L.A g).base c X
      (L.hooksU M) XR (L.UU M) (L.A g).tables K G gv t ∧
    (∀ a, L.Img a → G a) ∧ (∀ a, L.Img a → c.mem a = L.imgMem a) ∧
    (∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A g).af) (spv c) a) ∧ L.BlrAtU g t

/-- **Every state of the run with unwinding whose step ends without error has the per-state
facts** (`LinkSys.RunGoodL` on `machU`). -/
def RunGoodLU (M : Nat) (f : Clif.Function) (c : Arm.ArmState) : Prop :=
  ∀ M' g c' t, L.ReachLU M f c M' g c' t → Arm.r .ERR (L.machU M' g t) = .None →
    L.GoodAtU M' g c' t

/-! ## The linking statement with unwinding -/

/-- **The linking statement with unwinding at depth `M`** (`LinkSys.Thm` on the machine with
unwinding): for every function `g` of `P` and every world-side activation whose run with unwinding
of the program without functions (under `envRX M g`) returns, `Thm`'s conclusion on `machU M g`,
the step into the return not leaving the frame by unwinding (`¬ UnwExit`: an unwinding step also
lands at the return address); when it traps (and the run's traps are explicit,
`TrapsExplicitX`), every machine-side activation reaches the trap (`TrapAt`); and when it ends
`unwound` with exception `e` and memory `cm'`, an exception object related to `e` and a world
related to `cm'` that every machine-side activation at depth `M` realises by leaving its frame by
unwinding (`ActUnw`, the last step an `UnwExit`), and (`NeedNI`) every machine-side activation
entered with a related body-entry world agreeing outside `F ∪ D` up to `F ∪ D`. -/
def ThmU (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat), L.WorldEntry κ M g F vals cs w₀ →
    (∀ (rvals : List Clif.Val) (cm' : Clif.Mem),
      Clif.runLoopX (L.envRX M g) L.P.bare fuel cs.toX = .returned rvals cm' →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
        RetPins rvals us ∧ us.length = outs.length ∧
        PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A g).vc.RetsSite us ∧
        (∀ G ra s, L.MachEntry κ M g F G ra s w₀ →
          ∃ n, ActRet ra F G us outs wf s (runX (L.machU M g) n s) ∧
            PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.machU M g) s n ∧
            ¬ UnwExit (L.UU M) (L.A g).tables (L.A g).fa (runX (L.machU M g) (n - 1) s)) ∧
        (L.NeedNI → ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
            g (spv w₀) cs.frame.slots cs.mem w₀' →
          SameWorld (fun a => F a ∨ D a) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip vals → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip vals → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ G ra s, L.MachEntry κ M g F G ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.machU M g) n s) ∧
              PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.machU M g) s n ∧
              ¬ UnwExit (L.UU M) (L.A g).tables (L.A g).fa (runX (L.machU M g) (n - 1) s))) ∧
    (TrapsExplicitX (L.envRX M g) L.P.bare cs → ∀ c : Clif.TrapCode,
      Clif.runLoopX (L.envRX M g) L.P.bare fuel cs.toX = .trapped c →
      ∀ G ra s, L.MachEntry κ M g F G ra s w₀ →
        ∃ n, TrapAt (L.A g).fb (L.A g).base c (runX (L.machU M g) n s)) ∧
    (∀ (e : Clif.Exn) (cm' : Clif.Mem),
      Clif.runLoopX (L.envRX M g) L.P.bare fuel cs.toX = .unwound e cm' →
      ∃ (obj : BitVec 64) (wf : Arm.ArmState), ExnRel e obj ∧ MemRel F L.syms cm' wf ∧
        (∀ G ra s, L.MachEntry κ M g F G ra s w₀ →
          ∃ n, ActUnw ra F G obj wf s (runX (L.machU M g) n s) ∧
            PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.machU M g) s n ∧ 0 < n ∧
            UnwExit (L.UU M) (L.A g).tables (L.A g).fa (runX (L.machU M g) (n - 1) s)) ∧
        (L.NeedNI → ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
            g (spv w₀) cs.frame.slots cs.mem w₀' →
          SameWorld (fun a => F a ∨ D a) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip vals → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip vals → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ G ra s, L.MachEntry κ M g F G ra s w₀' →
            ∃ n, ActUnw ra (fun a => F a ∨ D a) G obj wf s (runX (L.machU M g) n s) ∧
              PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.machU M g) s n ∧ 0 < n ∧
              UnwExit (L.UU M) (L.A g).tables (L.A g).fa (runX (L.machU M g) (n - 1) s)))

/-- **`ThmU` with a fact `Q M g s` of every machine-side activation** (entered in `s`) that
realises the outcome: `ThmGU` with `Q` the per-state facts `RunGoodLU`; `ThmU` is `ThmUQ` without
`Q` (`ThmUQ.toThmU`, `thmUQ_true`). -/
def ThmUQ (Q : Nat → Clif.Function → Arm.ArmState → Prop) (κ : Nat → Clif.Function → Nat)
    (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat), L.WorldEntry κ M g F vals cs w₀ →
    (∀ (rvals : List Clif.Val) (cm' : Clif.Mem),
      Clif.runLoopX (L.envRX M g) L.P.bare fuel cs.toX = .returned rvals cm' →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
        RetPins rvals us ∧ us.length = outs.length ∧
        PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A g).vc.RetsSite us ∧
        (∀ G ra s, L.MachEntry κ M g F G ra s w₀ →
          ∃ n, ActRet ra F G us outs wf s (runX (L.machU M g) n s) ∧
            PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.machU M g) s n ∧
            ¬ UnwExit (L.UU M) (L.A g).tables (L.A g).fa (runX (L.machU M g) (n - 1) s) ∧
            Q M g s) ∧
        (L.NeedNI → ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
            g (spv w₀) cs.frame.slots cs.mem w₀' →
          SameWorld (fun a => F a ∨ D a) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip vals → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip vals → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ G ra s, L.MachEntry κ M g F G ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.machU M g) n s) ∧
              PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.machU M g) s n ∧
              ¬ UnwExit (L.UU M) (L.A g).tables (L.A g).fa (runX (L.machU M g) (n - 1) s) ∧
              Q M g s)) ∧
    (TrapsExplicitX (L.envRX M g) L.P.bare cs → ∀ c : Clif.TrapCode,
      Clif.runLoopX (L.envRX M g) L.P.bare fuel cs.toX = .trapped c →
      ∀ G ra s, L.MachEntry κ M g F G ra s w₀ →
        ∃ n, TrapAt (L.A g).fb (L.A g).base c (runX (L.machU M g) n s) ∧ Q M g s) ∧
    (∀ (e : Clif.Exn) (cm' : Clif.Mem),
      Clif.runLoopX (L.envRX M g) L.P.bare fuel cs.toX = .unwound e cm' →
      ∃ (obj : BitVec 64) (wf : Arm.ArmState), ExnRel e obj ∧ MemRel F L.syms cm' wf ∧
        (∀ G ra s, L.MachEntry κ M g F G ra s w₀ →
          ∃ n, ActUnw ra F G obj wf s (runX (L.machU M g) n s) ∧
            PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.machU M g) s n ∧ 0 < n ∧
            UnwExit (L.UU M) (L.A g).tables (L.A g).fa (runX (L.machU M g) (n - 1) s) ∧
            Q M g s) ∧
        (L.NeedNI → ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
            g (spv w₀) cs.frame.slots cs.mem w₀' →
          SameWorld (fun a => F a ∨ D a) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip vals → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip vals → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ G ra s, L.MachEntry κ M g F G ra s w₀' →
            ∃ n, ActUnw ra (fun a => F a ∨ D a) G obj wf s (runX (L.machU M g) n s) ∧
              PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.machU M g) s n ∧ 0 < n ∧
              UnwExit (L.UU M) (L.A g).tables (L.A g).fa (runX (L.machU M g) (n - 1) s) ∧
              Q M g s))

/-- **The linking statement with unwinding at depth `M`, with the per-state facts of every
realising activation's run** (`RunGoodLU`). -/
def ThmGU (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  L.ThmUQ (fun M g s => L.RunGoodLU M g s) κ M

theorem ThmUQ.toThmU {Q : Nat → Clif.Function → Arm.ArmState → Prop}
    {κ : Nat → Clif.Function → Nat} {M : Nat} (h : L.ThmUQ Q κ M) : L.ThmU κ M := by
  intro g hg F vals cs w₀ fuel hWE
  obtain ⟨h1, h2, h3⟩ := h g hg F vals cs w₀ fuel hWE
  refine ⟨fun rvals cm' hr => ?_, fun htr c hc G ra s hME => (h2 htr c hc G ra s hME).imp
    fun _ h => h.1, fun e cm' hr => ?_⟩
  · obtain ⟨us, outs, wf, a1, a2, a3, a4, a5, a6, a7⟩ := h1 rvals cm' hr
    exact ⟨us, outs, wf, a1, a2, a3, a4, a5,
      fun G ra s hME => (a6 G ra s hME).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩,
      fun hN D w₀' x1 x2 x3 x4 G ra s hME =>
        (a7 hN D w₀' x1 x2 x3 x4 G ra s hME).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩⟩
  · obtain ⟨obj, wf, a1, a2, a3, a4⟩ := h3 e cm' hr
    exact ⟨obj, wf, a1, a2,
      fun G ra s hME => (a3 G ra s hME).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩,
      fun hN D w₀' x1 x2 x3 x4 G ra s hME =>
        (a4 hN D w₀' x1 x2 x3 x4 G ra s hME).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩⟩

theorem thmUQ_true {κ : Nat → Clif.Function → Nat} {M : Nat} (h : L.ThmU κ M) :
    L.ThmUQ (fun _ _ _ => True) κ M := by
  intro g hg F vals cs w₀ fuel hWE
  obtain ⟨h1, h2, h3⟩ := h g hg F vals cs w₀ fuel hWE
  refine ⟨fun rvals cm' hr => ?_, fun htr c hc G ra s hME => (h2 htr c hc G ra s hME).imp
    fun _ h => ⟨h, trivial⟩, fun e cm' hr => ?_⟩
  · obtain ⟨us, outs, wf, a1, a2, a3, a4, a5, a6, a7⟩ := h1 rvals cm' hr
    exact ⟨us, outs, wf, a1, a2, a3, a4, a5,
      fun G ra s hME => (a6 G ra s hME).imp fun _ h => ⟨h.1, h.2.1, h.2.2, trivial⟩,
      fun hN D w₀' x1 x2 x3 x4 G ra s hME =>
        (a7 hN D w₀' x1 x2 x3 x4 G ra s hME).imp fun _ h => ⟨h.1, h.2.1, h.2.2, trivial⟩⟩
  · obtain ⟨obj, wf, a1, a2, a3, a4⟩ := h3 e cm' hr
    exact ⟨obj, wf, a1, a2,
      fun G ra s hME => (a3 G ra s hME).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, trivial⟩,
      fun hN D w₀' x1 x2 x3 x4 G ra s hME =>
        (a4 hN D w₀' x1 x2 x3 x4 G ra s hME).imp
          fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, trivial⟩⟩

/-! ## The external semantics: unfolding, results, exclusivity -/

theorem XU_base {M : Nat} {g : Clif.Function} {n : String} (hn : L.P.func? n = none)
    (uses : List CV) (w : Arm.ArmState) (F : BitVec 64 → Prop) :
    (L.XU κ M g F).call (some n) uses w = L.Xb.call (some n) uses w := by
  simp [XU, hn]

theorem XU_prog {M : Nat} {g : Clif.Function} {n : String} {h : Clif.Function}
    (hpf : L.P.func? n = some h) (uses : List CV) (w : Arm.ArmState) (F : BitVec 64 → Prop) :
    (L.XU κ M g F).call (some n) uses w = L.progXU κ M F h uses w := by
  simp [XU, hpf]

theorem XU_none {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} {u : CV} {args : List CV}
    {w : Arm.ArmState} (hn : symCallee L.Xb L.P (lo64 u) = none) :
    (L.XU κ M g F).call none (u :: args) w = L.Xb.call none (u :: args) w := by
  simp [XU, hn]

open Classical in
theorem XU_ind {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} {u : CV} {args : List CV}
    {w : Arm.ArmState} {h : Clif.Function} (hs : symCallee L.Xb L.P (lo64 u) = some h) :
    (L.XU κ M g F).call none (u :: args) w = if L.IndTo g h ∧ args.length = (regLocs h.sig).length
      then L.progXU κ M F h args w else none := by
  simp only [XU, hs]

theorem XRU_base {M : Nat} {g : Clif.Function} {n : String} (hn : L.P.func? n = none)
    (uses : List CV) (w : Arm.ArmState) (F : BitVec 64 → Prop) :
    (L.XRU κ M g F).raise (some n) uses w = L.XRb.raise (some n) uses w := by
  simp [XRU, hn]

theorem XRU_prog {M : Nat} {g : Clif.Function} {n : String} {h : Clif.Function}
    (hpf : L.P.func? n = some h) (uses : List CV) (w : Arm.ArmState) (F : BitVec 64 → Prop) :
    (L.XRU κ M g F).raise (some n) uses w = L.progXR κ M F h uses w := by
  simp [XRU, hpf]

theorem XRU_none {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} {u : CV} {args : List CV}
    {w : Arm.ArmState} (hn : symCallee L.Xb L.P (lo64 u) = none) :
    (L.XRU κ M g F).raise none (u :: args) w = L.XRb.raise none (u :: args) w := by
  simp [XRU, hn]

open Classical in
theorem XRU_ind {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} {u : CV} {args : List CV}
    {w : Arm.ArmState} {h : Clif.Function} (hs : symCallee L.Xb L.P (lo64 u) = some h) :
    (L.XRU κ M g F).raise none (u :: args) w = if L.IndTo g h ∧ args.length = (regLocs h.sig).length
      then L.progXR κ M F h args w else none := by
  simp only [XRU, hs]

theorem progXU_ext {M : Nat} {F : BitVec 64 → Prop} {h : Clif.Function}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hx : L.progXU κ M F h uses w = some (outs, w')) :
    Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  unfold progXU at hx
  split at hx
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨-, rfl⟩ := hx
    exact ⟨hc.2, by rw [(L.pcallU_pc M h _).1, L.program_canon]⟩
  · cases hx

/-- A raise of a program callee is at its first return from the canonical state: the exception
object in x0, no error, the caller's program, the return address after the canonical pc. -/
theorem progXR_ext {M : Nat} {F : BitVec 64 → Prop} {h : Clif.Function}
    {uses : List CV} {w : Arm.ArmState} {obj : BitVec 64} {w' : Arm.ArmState}
    (hx : L.progXR κ M F h uses w = some (obj, w')) :
    L.CondR κ M F h uses w ∧ L.praiseU M h (L.canon h uses w) = some (obj, w') ∧
      obj = xreg 0 w' ∧ Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  unfold progXR at hx
  split at hx
  · rename_i hc
    obtain ⟨-, -, -, -, -, h5, h6, -⟩ := L.praiseU_some hx
    exact ⟨hc, hx, (L.praiseU_some hx).2.2.2.1, h5, by rw [h6, L.program_canon]⟩
  · cases hx

theorem XU_ext (hL : L.Ok) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {d : Option String} {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hx : (L.XU κ M g F).call d uses w = some (outs, w'))
    (herr : Arm.r .ERR w = .None) : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  cases d with
  | some n =>
    cases hpf : L.P.func? n with
    | none =>
      rw [L.XU_base hpf _ _ F] at hx
      exact hL.baseExt _ _ _ _ _ (.inr ⟨n, rfl, hpf⟩) hx herr
    | some h =>
      rw [L.XU_prog hpf _ _ F] at hx
      exact L.progXU_ext hx
  | none =>
    cases uses with
    | nil => exact hL.baseExt _ _ _ _ _ (.inl rfl) hx herr
    | cons u args =>
      cases hs : symCallee L.Xb L.P (lo64 u) with
      | none =>
        rw [L.XU_none hs] at hx
        exact hL.baseExt _ _ _ _ _ (.inl rfl) hx herr
      | some h =>
        rw [L.XU_ind hs] at hx
        split at hx
        · exact L.progXU_ext hx
        · cases hx

/-- A raise of a program callee or (by `hb`) of a base callee keeps the program and gives no
error. -/
theorem XRU_ext {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    (hb : ∀ d uses w obj w', L.BaseDest d → L.XRb.raise d uses w = some (obj, w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program)
    {d : Option String} {uses : List CV} {w : Arm.ArmState} {obj : BitVec 64} {w' : Arm.ArmState}
    (hx : (L.XRU κ M g F).raise d uses w = some (obj, w'))
    (herr : Arm.r .ERR w = .None) : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  cases d with
  | some n =>
    cases hpf : L.P.func? n with
    | none =>
      rw [L.XRU_base hpf _ _ F] at hx
      exact hb _ _ _ _ _ (.inr ⟨n, rfl, hpf⟩) hx herr
    | some h =>
      rw [L.XRU_prog hpf _ _ F] at hx
      exact (L.progXR_ext hx).2.2.2
  | none =>
    cases uses with
    | nil => exact hb _ _ _ _ _ (.inl rfl) hx herr
    | cons u args =>
      cases hs : symCallee L.Xb L.P (lo64 u) with
      | none =>
        rw [L.XRU_none hs] at hx
        exact hb _ _ _ _ _ (.inl rfl) hx herr
      | some h =>
        rw [L.XRU_ind hs] at hx
        split at hx
        · exact (L.progXR_ext hx).2.2.2
        · cases hx

/-- **Exclusivity of the external semantics**: a program call that returns normally
(`progXU`) does not raise (`progXR`): the linked machine's call returned without error, so its
callee did not leave by unwinding. -/
theorem progXR_none_of_progXU {M : Nat} {F : BitVec 64 → Prop} {h : Clif.Function}
    {uses : List CV} {w : Arm.ArmState} (hx : L.progXU κ M F h uses w ≠ none) :
    L.progXR κ M F h uses w = none := by
  unfold progXU at hx
  split at hx
  · rename_i hc
    unfold progXR
    split
    · exact L.praiseU_none_of_pcallU hc.2
    · rfl
  · exact absurd rfl hx

/-- **Exclusivity of an activation's callees** (`CalleeUnwOkG.excl`), from the base's. -/
theorem XU_excl {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    (hb : ∀ d uses w, L.BaseDest d → L.Xb.call d uses w ≠ none → L.XRb.raise d uses w = none)
    (d : Option String) (uses : List CV) (w : Arm.ArmState)
    (hx : (L.XU κ M g F).call d uses w ≠ none) : (L.XRU κ M g F).raise d uses w = none := by
  cases d with
  | some n =>
    cases hpf : L.P.func? n with
    | none =>
      rw [L.XU_base hpf _ _ F] at hx
      rw [L.XRU_base hpf _ _ F]
      exact hb _ _ _ (.inr ⟨n, rfl, hpf⟩) hx
    | some h =>
      rw [L.XU_prog hpf _ _ F] at hx
      rw [L.XRU_prog hpf _ _ F]
      exact L.progXR_none_of_progXU hx
  | none =>
    cases uses with
    | nil => exact hb _ _ _ (.inl rfl) hx
    | cons u args =>
      cases hs : symCallee L.Xb L.P (lo64 u) with
      | none =>
        rw [L.XU_none hs] at hx
        rw [L.XRU_none hs]
        exact hb _ _ _ (.inl rfl) hx
      | some h =>
        rw [L.XU_ind hs] at hx
        rw [L.XRU_ind hs]
        split at hx
        · split <;> first | rfl | exact L.progXR_none_of_progXU hx
        · exact absurd rfl hx

/-! ## The environment of an activation -/

/-- A reachable extern of `envRX` is the linked environment's. -/
theorem envRX_of {M : Nat} {g : Clif.Function} {n : String}
    (h : L.P.func? n = none ∨ L.MayCall g n) :
    (L.envRX M g).extern n = (Clif.linkEnvRX L.P L.envX (L.crunX M)).extern n := by
  simp only [envRX]
  split
  · rename_i hc
    obtain ⟨h1, h2⟩ := hc
    rcases h with h | h
    · simp [h] at h1
    · exact absurd h h2
  · rfl

/-- An extern of `envRX` is none or the linked environment's. -/
theorem envRX_restricts {M : Nat} {g : Clif.Function} (n : String) :
    (L.envRX M g).extern n = none ∨
      (L.envRX M g).extern n = (Clif.linkEnvRX L.P L.envX (L.crunX M)).extern n := by
  simp only [envRX]
  split
  · exact .inl rfl
  · exact .inr rfl

/-- **The whole-program run with unwinding of `g` is a run of `P.bare` under `envRX`**
(`Clif.runLoopX_linkR`'s premise on the program functions). -/
theorem envRX_link {M : Nat} {g : Clif.Function} (hnd : (L.P.funcs.map (·.name)).Nodup) :
    ∀ h ∈ L.P.funcs, (h.name ∈ g.externs.map (·.2.name) ∨
      (L.syms h.name ≠ none ∧ ∃ d, Clif.IndSig g d ∧ d.abiMatch h.sig = true)) →
      (L.envRX M g).extern h.name = (Clif.linkEnvRX L.P L.envX (L.crunX M)).extern h.name := by
  intro h hh hc
  refine L.envRX_of (.inr ?_)
  rcases hc with hd | ⟨hsy, d, hdS, hm⟩
  · exact .inl hd
  · refine .inr ⟨hdS.not_indFree, hsy, fun h' hpf => ?_⟩
    obtain ⟨hh', hn'⟩ := Clif.Program.func?_some hpf
    rw [Clif.name_inj hnd hh' hh hn']
    exact ⟨d, indSig_mem hdS, hm⟩

/-- An extern of `envOfX` called from a memory whose oracle has `c` is `envRX`'s. -/
theorem envOfX_envRX {M : Nat} {g : Clif.Function} {c : BitVec 64} {n : String}
    (vals : List Clif.Val) {cm : Clif.Mem} (hpl : L.NeedSlots → L.PlaceAt cm c) :
    ((L.envOfX M g c).extern n).map (· vals cm) = ((L.envRX M g).extern n).map (· vals cm) := by
  simp only [envOfX, envRX]
  split
  · rfl
  · split
    · cases (Clif.linkEnvRX L.P L.envX (L.crunX M)).extern n with
      | none => rfl
      | some G0 =>
        simp only [Option.map_some, Option.some.injEq]
        split
        · rfl
        · exact absurd hpl ‹_›
    · rfl

/-- **Without unwinding, `envRX` is `LinkSys.envR`**: when the base CLIF environment is the
base with unwinding's and the callee runs are those with unwinding read as `Clif.run`'s. -/
theorem envRX_toEnv (hb : L.envX.toEnv = L.base)
    (hc : ∀ M s, L.crun M s = (L.crunX M s).toOutcome) (M : Nat) (g : Clif.Function) :
    (L.envRX M g).toEnv = L.envR M g := by
  have h1 : (fun s => (L.crunX M s).toOutcome) = L.crun M := funext fun s => (hc M s).symm
  have h2 := Clif.linkEnvRX_toEnv (P := L.P) (env := L.envX) (R := L.crunX M)
  rw [hb, h1] at h2
  simp only [Clif.XEnv.toEnv, envRX, LinkSys.envR]
  congr 1
  · funext n
    split
    · rfl
    · exact congrArg (fun E : Clif.Env => E.extern n) h2
  all_goals first
    | exact congrArg Clif.Env.names h2
    | exact congrArg Clif.Env.sigOf h2

/-! ## The callee runs with unwinding -/

/-- `L` with the callee runs with unwinding `c` (the machine side is `L`'s). -/
def withCrunX (c : Nat → Clif.State → Clif.XOutcome) : LinkSysU := { L with crunX := c }

theorem layer_withCrunX (c : Nat → Clif.State → Clif.XOutcome) :
    ∀ M, (L.withCrunX c).layer M = L.layer M
  | 0 => rfl
  | M + 1 => by simp only [layer, layer_withCrunX c M]; rfl

theorem machU_withCrunX (c : Nat → Clif.State → Clif.XOutcome) (M : Nat) (g : Clif.Function) :
    (L.withCrunX c).machU M g = L.machU M g := by
  simp only [machU, hooksU, UU, layer_withCrunX]; rfl

/-- The callee runs with unwinding of at most `M` steps at depth `M` (`Clif.linkEnvNX`). -/
def stdX : LinkSysU := L.withCrunX fun M s => Clif.runLoopX L.envX L.P M s.toX

/-- The callee runs with unwinding of fuel `F` with at most `M` nested levels at depth `M`
(`Clif.runDX`, `Clif.linkEnvDX`). -/
noncomputable def peakX (F : Nat) : LinkSysU := L.withCrunX fun M => Clif.runDX L.envX L.P F M

theorem Ok.withCrunX {L : LinkSysU} (hL : L.Ok) (c : Nat → Clif.State → Clif.XOutcome) :
    (L.withCrunX c).Ok := hL

theorem xinv_toX {P : Clif.Program} {s : Clif.State} (h : Clif.LInv P s) : Clif.XInv P s.toX :=
  ⟨h, by simp [Clif.XState.Aligned, Clif.State.toX]⟩

/-- **The default callee runs with unwinding** (`Clif.runLoopX_linkN`), when the indirect calls'
scope holds with unwinding (`Clif.IndScopeX`). -/
theorem crunOkX_std (hL : L.Ok)
    (hS : ∀ g ∈ L.P.funcs, ¬ Clif.IndFree g → Clif.IndScopeX L.P L.envX L.syms) :
    L.stdX.CrunOkX where
  runs M _ _ h _ := ⟨M, h⟩
  zero _ := ⟨fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩
  link M hM _ hf s hI hIf hsy _ hEn hEs hEb hEp hst hof :=
    Clif.runLoopX_linkN (env := L.envX) (syms := L.syms) (M - 1) hL.names hf hL.free
      (hS _ hf) hEn hEs hEb hEp M s.toX (by omega) (xinv_toX hI) hIf hsy hst hof

/-- **The callee runs with unwinding of fuel `F` and bounded depth** (`Clif.runDX`,
`Clif.runLoopX_linkD`). -/
theorem crunOkX_peak (hL : L.Ok)
    (hS : ∀ g ∈ L.P.funcs, ¬ Clif.IndFree g → Clif.IndScopeX L.P L.envX L.syms) (F : Nat) :
    (L.peakX F).CrunOkX where
  runs M s o h _ := by
    simp only [peakX, withCrunX, Clif.runDX] at h
    split at h
    · exact ⟨F, h⟩
    · subst h; rename_i ho; rcases ho with ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
  zero _ := by
    simp only [peakX, withCrunX, Clif.runDX, Nat.lt_irrefl, false_and, ↓reduceIte]
    exact ⟨fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩
  link M _ _ hf s hI hIf hsy _ hEn hEs hEb hEp hst hof := by
    have hd : 0 < M ∧ Clif.DepthLeX L.envX L.P (M - 1) s.toX := by
      refine Classical.byContradiction fun hc => hof ?_
      show Clif.runDX L.envX L.P F M s = _
      simp only [Clif.runDX, hc, ↓reduceIte]
    have he : Clif.runDX L.envX L.P F M s = Clif.runLoopX L.envX L.P F s.toX := by
      simp only [Clif.runDX, hd, and_self, ↓reduceIte]
    obtain ⟨m, hm⟩ := Clif.runLoopX_linkD (env := L.envX) (syms := L.syms) F (M - 1) hL.names hf
      hL.free (hS _ hf) hEn hEs hEb hEp F s.toX (by omega) hd.2 (xinv_toX hI) hIf hsy
      (by rw [← he]; exact hst) (by rw [← he]; exact hof)
    exact ⟨m, hm.trans he.symm⟩

/-- **A complete callee run at depth `M + 1` is a run of `P.bare` under `envRX M f`**
(`CrunOkX.link` with the activation's environment; for `stdX`, `crunX (M + 1) cs` is the
whole-program run with unwinding of `M + 1` steps). -/
theorem envRX_crun [hR : L.CrunOkX] (hnd : (L.P.funcs.map (·.name)).Nodup) (M : Nat)
    {f : Clif.Function} (hf : f ∈ L.P.funcs) {cs : Clif.State} (hI : Clif.LInv L.P cs)
    (hIf : Clif.LInv (L.P.only f) cs) (hsy : ¬ Clif.IndFree f → cs.mem.symbols = L.syms)
    (hst : ∀ msg, L.crunX (M + 1) cs ≠ .stuck msg) (hof : L.crunX (M + 1) cs ≠ .outOfFuel) :
    ∃ m, Clif.runLoopX (L.envRX M f) L.P.bare m cs.toX = L.crunX (M + 1) cs :=
  hR.link (M + 1) (Nat.succ_pos M) f hf cs hI hIf hsy (L.envRX M f) rfl rfl
    (fun _ hn => L.envRX_of (.inl hn)) (L.envRX_link hnd) hst hof

end LinkSysU

/-! ## Environments that agree on the calls from one memory -/

/-- The externs of `E₁` and `E₂` give the same outcomes on the calls from memory `mem`. -/
def XAgreeAt (E₁ E₂ : Clif.XEnv) (mem : Clif.Mem) : Prop :=
  ∀ n vals, (E₁.extern n).map (· vals mem) = (E₂.extern n).map (· vals mem)

theorem XAgreeAt.toEnv {E₁ E₂ : Clif.XEnv} {mem : Clif.Mem} (h : XAgreeAt E₁ E₂ mem) (n : String)
    (vals : List Clif.Val) :
    (E₁.toEnv.extern n).map (· vals mem) = (E₂.toEnv.extern n).map (· vals mem) := by
  have e := h n vals
  simp only [Clif.XEnv.toEnv]
  cases h1 : E₁.extern n <;> cases h2 : E₂.extern n <;>
    simp only [h1, h2, Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at e ⊢
  rw [e]

theorem extRaise_agree {E₁ E₂ : Clif.XEnv} {mem : Clif.Mem} (h : XAgreeAt E₁ E₂ mem)
    (p : Clif.Program) (ext : Clif.ExtFunc) (vals : List Clif.Val) :
    Clif.extRaise E₁ p mem ext vals = Clif.extRaise E₂ p mem ext vals := by
  have e := h ext.name vals
  unfold Clif.extRaise
  cases p.func? ext.name with
  | some _ => rfl
  | none =>
    dsimp only
    cases h1 : E₁.extern ext.name <;> cases h2 : E₂.extern ext.name <;>
      simp only [h1, h2, Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at e ⊢
    rw [e]

theorem externAtRaise_agree {E₁ E₂ : Clif.XEnv} {mem : Clif.Mem} (hn : E₁.names = E₂.names)
    (hs : E₁.sigOf = E₂.sigOf) (h : XAgreeAt E₁ E₂ mem) (p : Clif.Program) (d : Clif.Signature)
    (a : Nat) (vals : List Clif.Val) :
    Clif.externAtRaise E₁ p mem d a vals = Clif.externAtRaise E₂ p mem d a vals := by
  unfold Clif.externAtRaise
  rw [hn, hs]
  cases (E₂.names ++ p.externNames).find? (fun n => mem.symbols n == some a) with
  | none => rfl
  | some n =>
    have e := h n vals
    dsimp only
    cases h1 : E₁.extern n <;> cases h2 : E₂.extern n <;>
      simp only [h1, h2, Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at e ⊢
    rw [e]

theorem callRaise_agree {E₁ E₂ : Clif.XEnv} {mem : Clif.Mem} (h : XAgreeAt E₁ E₂ mem)
    (p : Clif.Program) (fr : Clif.Frame) (fn : Clif.FnRef) (args : List Clif.ValueId) :
    Clif.callRaise E₁ p mem fr fn args = Clif.callRaise E₂ p mem fr fn args := by
  rw [Clif.callRaise_eq, Clif.callRaise_eq]
  cases Opt.callArgs fr fn args with
  | ok q => exact extRaise_agree h p q.1 q.2
  | trap => rfl
  | stuck => rfl

theorem callIndRaise_agree {E₁ E₂ : Clif.XEnv} {mem : Clif.Mem} (hn : E₁.names = E₂.names)
    (hs : E₁.sigOf = E₂.sigOf) (h : XAgreeAt E₁ E₂ mem) (p : Clif.Program) (fr : Clif.Frame)
    (sig : Nat) (callee : Clif.ValueId) (args : List Clif.ValueId) :
    Clif.callIndRaise E₁ p mem fr sig callee args = Clif.callIndRaise E₂ p mem fr sig callee args := by
  rw [Clif.callIndRaise_eq, Clif.callIndRaise_eq]
  cases Clif.indPre fr sig callee args with
  | ok q =>
    obtain ⟨d, a, v⟩ := q
    dsimp only
    cases p.funcs.find? fun g => (mem.symbols g.name) == some a with
    | some _ => rfl
    | none => exact externAtRaise_agree hn hs h p d a v
  | trap => rfl
  | stuck => rfl

/-- **A raise from a frame of `g` (no `return_call`) depends on the environment only through the
calls from the state's memory**. -/
theorem raiseAt_agree {E₁ E₂ : Clif.XEnv} {P p : Clif.Program} {g : Clif.Function}
    (hP : Clif.LinkFree g) {s : Clif.State} (hI : Clif.LFrame (P.only g) s.frame)
    (hn : E₁.names = E₂.names) (hs : E₁.sigOf = E₂.sigOf) (h : XAgreeAt E₁ E₂ s.mem) :
    Clif.raiseAt? E₁ p s = Clif.raiseAt? E₂ p s := by
  have hff : s.frame.func = g := by simpa [Clif.Program.only] using hI.1
  unfold Clif.raiseAt?
  cases s.frame.body with
  | cons st rest =>
    dsimp only
    cases st.inst with
    | call fn args => exact callRaise_agree h p _ fn args
    | callIndirect sig callee args => exact callIndRaise_agree hn hs h p _ sig callee args
    | _ => rfl
  | nil =>
    dsimp only
    cases ht : s.frame.term with
    | returnCall fn args =>
      obtain ⟨B, hB, -, hbt⟩ | ⟨-, bc, hbt⟩ := hI.2
      · rw [hff] at hB
        exact absurd (hbt.symm.trans ht) (hP B hB fn args)
      · rw [hbt] at ht; cases ht
    | tryCall fn args et =>
      dsimp only
      rw [Clif.tryCallRaise_eq, Clif.tryCallRaise_eq]
      cases Clif.tryPre s.frame fn et with
      | ok _ => exact callRaise_agree h p _ fn args
      | trap => rfl
      | stuck => rfl
    | tryCallIndirect callee args et =>
      dsimp only
      rw [Clif.tryCallIndRaise_eq, Clif.tryCallIndRaise_eq]
      cases Clif.tryIndPre s.frame et with
      | ok _ => exact callIndRaise_agree hn hs h p _ et.sig callee args
      | trap => rfl
      | stuck => rfl
    | _ => rfl

/-- **A step from a frame of `g` depends on the environment only through the calls from the
state's memory** (`LinkSys.step_envOf`'s argument, for any two environments). -/
theorem step_agree {E₁ E₂ : Clif.Env} {P p : Clif.Program} {g : Clif.Function}
    (hP : Clif.LinkFree g) {s : Clif.State} (hI : Clif.LFrame (P.only g) s.frame)
    (hn : E₁.names = E₂.names) (hs : E₁.sigOf = E₂.sigOf)
    (h : ∀ n vals, (E₁.extern n).map (· vals s.mem) = (E₂.extern n).map (· vals s.mem)) :
    Clif.step E₁ p s = Clif.step E₂ p s := by
  have hPf : ∀ f ∈ (P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hP
  have hcall : ∀ (t : Clif.State) ext vals rest rs, t.mem = s.mem →
      Opt.callCont E₁ p t rest rs ext vals = Opt.callCont E₂ p t rest rs ext vals :=
    fun t ext vals rest rs htm => callCont_envEq fun _ => htm ▸ h ext.name vals
  have hind : ∀ (t : Clif.State) rest rs sig d a v, t.mem = s.mem →
      Clif.indCont E₁ p t rest rs sig d a v = Clif.indCont E₂ p t rest rs sig d a v :=
    fun t rest rs sig d a v htm => indCont_envEq hn hs fun _ n _ _ => htm ▸ h n v
  rcases Clif.step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [Clif.step_try _ _ s hb ht, Clif.step_try _ _ s hb ht]
    exact ofRes_congr fun ⟨n, b, bc⟩ _ => ofRes_congr fun ⟨ext, vals⟩ _ =>
      hcall _ ext vals _ _ rfl
  · rw [Clif.step_tryInd _ _ s hb ht, Clif.step_tryInd _ _ s hb ht]
    exact ofRes_congr fun ⟨n, b, bc⟩ _ => ofRes_congr fun ⟨d, a, v⟩ _ => hind _ _ _ _ d a v rfl
  · rw [Clif.step_ind _ _ s hb hi, Clif.step_ind _ _ s hb hi]
    exact ofRes_congr fun ⟨d, a, v⟩ _ => hind _ _ _ _ d a v rfl
  · rw [Opt.step_eq_lift _ _ s hci, Opt.step_eq_lift _ _ s hci]
    cases hl : Opt.lstep s.frame s.mem with
    | call ext vals rs rest => exact hcall s ext vals rest rs rfl
    | tail ext vals => exact absurd hl (Clif.lstep_ne_tail hPf hI)
    | _ => rfl

/-- **A step with unwinding from a frame of `g` depends on the environment only through the
calls from the state's memory.** -/
theorem stepX_agree {E₁ E₂ : Clif.XEnv} {P p : Clif.Program} {g : Clif.Function}
    (hP : Clif.LinkFree g) {xs : Clif.XState} (hI : Clif.LFrame (P.only g) xs.s.frame)
    (hn : E₁.names = E₂.names) (hs : E₁.sigOf = E₂.sigOf) (h : XAgreeAt E₁ E₂ xs.s.mem) :
    Clif.stepX E₁ p xs = Clif.stepX E₂ p xs := by
  unfold Clif.stepX
  rw [raiseAt_agree hP hI hn hs h, step_agree hP hI hn hs h.toEnv]

namespace LinkSysU

variable (L : LinkSysU)

/-- **The run with unwinding of `P.bare` from `g`'s activation calls from a memory whose oracle
has `c`**: its steps under `envOfX` and under `envRX` are the same. -/
theorem stepX_envOfX {M : Nat} {g : Clif.Function} {c : BitVec 64} {xs : Clif.XState}
    (hP : Clif.LinkFree g) (hI : Clif.LFrame (L.P.only g) xs.s.frame)
    (hpl : L.NeedSlots → L.PlaceAt xs.s.mem c) :
    Clif.stepX (L.envOfX M g c) L.P.bare xs = Clif.stepX (L.envRX M g) L.P.bare xs :=
  stepX_agree hP hI rfl rfl fun _ vals => L.envOfX_envRX vals hpl

end LinkSysU

/-- The scope of indirect calls of a base environment without unwinding (`Clif.Env.toX`). -/
theorem _root_.Clif.IndScope.toX {P : Clif.Program} {base : Clif.Env} {syms : String → Option Nat}
    (h : Clif.IndScope P base syms) : Clif.IndScopeX P base.toX syms where
  keep := by rw [Clif.Env.toX_toEnv]; exact h.keep
  keepU := fun n g hg vals m e m' hu => absurd hu (Clif.Env.toX_noUnwind base n g hg vals m e m')
  inj := h.inj
  alias := fun a ha b hb x h1 h2 h3 h4 => by
    simp only [Clif.Env.toX]
    rw [h.alias a ha b hb x h1 h2 h3 h4]

end E2E
