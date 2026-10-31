import FV.E2E.LinkGood
import FV.E2E.DeadCleanupTrapCall

/-! # Callee traps in the linked program: the trap observable and its premises (S9c, #376)

`backend_correct_program` (`FV/E2E/LinkArm.lean`) takes `TrapsExplicit`: a trap of the entry
activation must be an explicitly trapping instruction of the entry function, so a run whose
trap happens inside a callee is outside it. This file sets up the trap counterpart of the
linking induction (`FV/E2E/LinkTrapCallInd.lean`):

* **`LinkSys.TrapIn L M g s c`**, the trap observable of the linked machine of depth `M` run from
  an activation of `g` entered in `s`: the run stops (`LinkSys.Stop`: the run errs for ever
  after a state without error at the activation's body `sp`, no return into its own code before)
  at a trap site of `g` with code `c` (`site`), or at a call of `g` whose callee outside `P`
  traps with `c` in its CLIF semantics (`base`, `BaseTrapCall`), or at a call of `g` of a
  function `h` of `P` whose own activation, entered from that call state one level down, has the
  observable (`prog`).
* **No return** (`noRet_of_stop`, `pcall_junk`): once the observable holds, the callee's machine
  never returns to its caller, so the linked call of a trapping program callee is `junkAt`
  (an error state).
* `LinkSys.mach_err`: under the outside code's error contract an error state of the linked machine
  stays an error state.
* **`BaseTrapsOk L`**, the outside code's trap contract (next to `BaseOk`): where the CLIF
  semantics of an extern outside `P` traps on a call's arguments and memory, its machine semantics
  `Xb` gives no normal return (`XTrapsOk`) and its hook errs; an error state stays an error state.
* **`LinkSys.TrapsD L M g cs`**, the run premise (`TrapsExplicitC`'s linked counterpart): the
  activation's run has no memory-access trap (`TrapsExplicitC` under the linked environment) and
  every trap of a program callee its run hits is one of an activation that satisfies the premise
  one level down (the run is unchanged when the callee traps outside the premise are made stuck,
  `cutEnv`).
* `cutEnv`, `EnvRestrictsS`: an environment some of whose extern outcomes are made stuck, and the
  steps of such a restriction.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-! ## Environments with stuck extern outcomes -/

/-- **`E₁` is `E₂` with some extern outcomes made stuck** (or some externs removed): the same
names and signatures; an extern of `E₁` is one of `E₂` whose outcomes are `E₂`'s or stuck. -/
def EnvRestrictsS (E₁ E₂ : Clif.Env) : Prop :=
  E₁.names = E₂.names ∧ E₁.sigOf = E₂.sigOf ∧ ∀ n, E₁.extern n = none ∨
    ∃ G₁ G₂, E₁.extern n = some G₁ ∧ E₂.extern n = some G₂ ∧
      ∀ vals m, G₁ vals m = G₂ vals m ∨ ∃ msg, G₁ vals m = .stuck msg

theorem callCont_restrictS {E₁ E₂ : Clif.Env} (hE : EnvRestrictsS E₁ E₂) {p : Clif.Program}
    {t : Clif.State} {rest : List Clif.Stmt} {rs : List Clif.ValueId} {ext : Clif.ExtFunc}
    {vals : List Clif.Val} :
    Opt.callCont E₁ p t rest rs ext vals = Opt.callCont E₂ p t rest rs ext vals ∨
      ∃ m, Opt.callCont E₁ p t rest rs ext vals = .stuck m := by
  cases hp : p.func? ext.name with
  | some _ => left; simp only [Opt.callCont, hp]
  | none =>
    rcases hE.2.2 ext.name with h | ⟨G₁, G₂, h1, h2, hG⟩
    · right
      exact ⟨s!"unknown callee %{ext.name}", by simp only [Opt.callCont, hp, h]⟩
    · rcases hG vals t.mem with e | ⟨msg, e⟩
      · left; simp only [Opt.callCont, hp, h1, h2, e]
      · right; exact ⟨msg, by simp only [Opt.callCont, hp, h1, e]⟩

theorem callExternAt_restrictS {E₁ E₂ : Clif.Env} (hE : EnvRestrictsS E₁ E₂) {p : Clif.Program}
    {mem : Clif.Mem} {d : Clif.Signature} {a : Nat} {vals : List Clif.Val} :
    Clif.callExternAt E₁ p mem d a vals = Clif.callExternAt E₂ p mem d a vals ∨
      ∃ m, Clif.callExternAt E₁ p mem d a vals = .stuck m := by
  unfold Clif.callExternAt
  rw [hE.1, hE.2.1]
  cases (E₂.names ++ p.externNames).find? (fun n => mem.symbols n == some a) with
  | none => exact .inl rfl
  | some n =>
    simp only [Clif.Res.ofOption_some, Clif.Res.ok_bind]
    rcases hE.2.2 n with h | ⟨G₁, G₂, h1, h2, hG⟩
    · rw [h]; exact .inr ⟨_, rfl⟩
    · rw [h1, h2]
      simp only [Clif.Res.ofOption_some, Clif.Res.ok_bind]
      cases Clif.Res.check ((E₂.sigOf n).all d.abiMatch) _ with
      | ok _ =>
        simp only [Clif.Res.ok_bind]
        cases Clif.checkTys _ vals (Clif.AbiParam.tys d.params) with
        | ok _ =>
          simp only [Clif.Res.ok_bind]
          rcases hG vals mem with e | ⟨msg, e⟩
          · rw [e]; exact .inl rfl
          · rw [e]; exact .inr ⟨msg, rfl⟩
        | trap c => exact .inl rfl
        | stuck m => exact .inl rfl
      | trap c => exact .inl rfl
      | stuck m => exact .inl rfl

theorem indCont_restrictS {E₁ E₂ : Clif.Env} (hE : EnvRestrictsS E₁ E₂) {p : Clif.Program}
    {t : Clif.State} {rest : List Clif.Stmt} {rs : List Clif.ValueId} {sig : Nat}
    {d : Clif.Signature} {a : Nat} {v : List Clif.Val} :
    Clif.indCont E₁ p t rest rs sig d a v = Clif.indCont E₂ p t rest rs sig d a v ∨
      ∃ m, Clif.indCont E₁ p t rest rs sig d a v = .stuck m := by
  unfold Clif.indCont
  cases hf : p.funcs.find? (fun f => t.mem.symbols f.name == some a) with
  | some _ => exact .inl rfl
  | none =>
    rcases callExternAt_restrictS (p := p) (mem := t.mem) (d := d) (a := a) (vals := v) hE with
      h | ⟨m, h⟩
    · left; simp only [h]
    · right; exact ⟨m, by simp only [h, Clif.StepResult.ofRes_stuck]⟩

/-- A step under `E₁` (`E₂` with some extern outcomes stuck) is `E₂`'s step or stuck (from a
frame of a function of `P`, any program `p`). -/
theorem step_restrictS {E₁ E₂ : Clif.Env} (hE : EnvRestrictsS E₁ E₂) {p P : Clif.Program}
    (hP : ∀ f ∈ P.funcs, Clif.LinkFree f) {s : Clif.State} (hI : Clif.LFrame P s.frame) :
    Clif.step E₁ p s = Clif.step E₂ p s ∨ ∃ m, Clif.step E₁ p s = .stuck m := by
  rcases Clif.step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [Clif.step_try _ _ s hb ht, Clif.step_try _ _ s hb ht]
    exact ofRes_restrict fun ⟨n, b, bc⟩ _ => ofRes_restrict fun ⟨ext, vals⟩ _ => callCont_restrictS hE
  · rw [Clif.step_tryInd _ _ s hb ht, Clif.step_tryInd _ _ s hb ht]
    exact ofRes_restrict fun ⟨n, b, bc⟩ _ => ofRes_restrict fun ⟨d, a, v⟩ _ => indCont_restrictS hE
  · rw [Clif.step_ind _ _ s hb hi, Clif.step_ind _ _ s hb hi]
    exact ofRes_restrict fun ⟨d, a, v⟩ _ => indCont_restrictS hE
  · rw [Opt.step_eq_lift _ _ s hci, Opt.step_eq_lift _ _ s hci]
    cases hl : Opt.lstep s.frame s.mem with
    | call ext vals rs rest => exact callCont_restrictS hE
    | tail ext vals => exact absurd hl (Clif.lstep_ne_tail hP hI)
    | _ => exact .inl rfl

/-- A step under `E₁` (`E₂` with some extern outcomes stuck) that is not stuck is `E₂`'s. -/
theorem step_of_restrictS {E₁ E₂ : Clif.Env} (hE : EnvRestrictsS E₁ E₂) {p P : Clif.Program}
    (hP : ∀ f ∈ P.funcs, Clif.LinkFree f) {s : Clif.State} (hI : Clif.LFrame P s.frame)
    {r : Clif.StepResult} (hs : Clif.step E₁ p s = r) (hr : ∀ m, r ≠ .stuck m) :
    Clif.step E₂ p s = r := by
  rcases step_restrictS (p := p) hE hP hI with h | ⟨m, h⟩
  · rw [← h, hs]
  · exact absurd (hs.symm.trans h) (hr m)

/-- **Two environments with the same names, signatures and extern outcomes at the memories of a
step give the same step** (`LinkSys.step_envOf`'s argument for any two environments). -/
theorem step_congrE {E₁ E₂ : Clif.Env} (hn : E₁.names = E₂.names) (hsg : E₁.sigOf = E₂.sigOf)
    {p P : Clif.Program} (hP : ∀ f ∈ P.funcs, Clif.LinkFree f) {s : Clif.State}
    (hI : Clif.LFrame P s.frame)
    (hx : ∀ (t : Clif.State) n vals, t.mem = s.mem →
      (E₁.extern n).map (· vals t.mem) = (E₂.extern n).map (· vals t.mem)) :
    Clif.step E₁ p s = Clif.step E₂ p s := by
  have hcall : ∀ (t : Clif.State) ext vals rest rs, t.mem = s.mem →
      Opt.callCont E₁ p t rest rs ext vals = Opt.callCont E₂ p t rest rs ext vals :=
    fun t ext vals rest rs htm => callCont_envEq fun _ => hx t ext.name vals htm
  have hind : ∀ (t : Clif.State) rest rs sig d a v, t.mem = s.mem →
      Clif.indCont E₁ p t rest rs sig d a v = Clif.indCont E₂ p t rest rs sig d a v :=
    fun t rest rs sig d a v htm => indCont_envEq hn hsg fun _ n _ _ => hx t n v htm
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
    | tail ext vals => exact absurd hl (Clif.lstep_ne_tail hP hI)
    | _ => rfl

open Classical in
/-- The outcome `o` of a call of the extern `n` on `vals`, `cm`, made stuck when it is a trap
outside `Q`. -/
noncomputable def cutO (Q : String → List Clif.Val → Clif.Mem → Prop) (n : String)
    (vals : List Clif.Val) (cm : Clif.Mem) (o : Clif.Outcome) : Clif.Outcome :=
  if (∃ c, o = .trapped c) ∧ ¬ Q n vals cm then .stuck "uncovered callee trap" else o

/-- **`E` with the extern traps outside `Q` made stuck.** -/
noncomputable def cutEnv (E : Clif.Env) (Q : String → List Clif.Val → Clif.Mem → Prop) :
    Clif.Env where
  extern n := (E.extern n).map fun G vals cm => cutO Q n vals cm (G vals cm)
  names := E.names
  sigOf := E.sigOf

theorem cutO_eq (Q : String → List Clif.Val → Clif.Mem → Prop) (n : String)
    (vals : List Clif.Val) (cm : Clif.Mem) (o : Clif.Outcome) :
    cutO Q n vals cm o = o ∨ ∃ msg, cutO Q n vals cm o = .stuck msg := by
  unfold cutO
  split
  · exact .inr ⟨_, rfl⟩
  · exact .inl rfl

theorem cutO_returned {Q : String → List Clif.Val → Clif.Mem → Prop} {n : String}
    {vals : List Clif.Val} {cm : Clif.Mem} {o : Clif.Outcome} {rv : List Clif.Val} {m : Clif.Mem}
    (h : cutO Q n vals cm o = .returned rv m) : o = .returned rv m := by
  unfold cutO at h
  split at h
  · cases h
  · exact h

theorem cutO_trapped {Q : String → List Clif.Val → Clif.Mem → Prop} {n : String}
    {vals : List Clif.Val} {cm : Clif.Mem} {o : Clif.Outcome} {c : Clif.TrapCode}
    (h : cutO Q n vals cm o = .trapped c) : o = .trapped c ∧ Q n vals cm := by
  unfold cutO at h
  split at h
  · cases h
  · rename_i hn
    subst h
    exact ⟨rfl, Classical.byContradiction fun hq => hn ⟨⟨c, rfl⟩, hq⟩⟩

theorem cutEnv_restrictsS (E : Clif.Env) (Q : String → List Clif.Val → Clif.Mem → Prop) :
    EnvRestrictsS (cutEnv E Q) E := by
  refine ⟨rfl, rfl, fun n => ?_⟩
  cases h : E.extern n with
  | none => left; simp [cutEnv, h]
  | some G =>
    right
    exact ⟨_, G, by simp [cutEnv, h], rfl, fun vals m => cutO_eq Q n vals m (G vals m)⟩

theorem cutEnv_extern {E : Clif.Env} {Q : String → List Clif.Val → Clif.Mem → Prop} {n : String}
    {G' : List Clif.Val → Clif.Mem → Clif.Outcome} (h : (cutEnv E Q).extern n = some G') :
    ∃ G, E.extern n = some G ∧ G' = fun vals cm => cutO Q n vals cm (G vals cm) := by
  simp only [cutEnv, Option.map_eq_some_iff] at h
  obtain ⟨G, hG, rfl⟩ := h
  exact ⟨G, hG, rfl⟩

theorem cutEnv_map (E : Clif.Env) (Q : String → List Clif.Val → Clif.Mem → Prop) (n : String)
    (vals : List Clif.Val) (cm : Clif.Mem) :
    ((cutEnv E Q).extern n).map (· vals cm) = ((E.extern n).map (· vals cm)).map (cutO Q n vals cm) := by
  simp only [cutEnv]
  cases E.extern n <;> rfl

/-- The callee contract of an environment holds for it with some extern traps made stuck. -/
theorem xCallsOk_cut {E : Clif.Env} {Q : String → List Clif.Val → Clif.Mem → Prop}
    {exts : List Clif.ExtFunc} {MR : MemRelT} {X : ExtSem} (h : XCallsOk E exts MR X) :
    XCallsOk (cutEnv E Q) exts MR X := by
  intro ext hext g' sl cm w d uses args vals rvals cm' hg hd hargs hmr hret hrl
  obtain ⟨g, hg0, rfl⟩ := cutEnv_extern hg
  exact h ext hext g sl cm w d uses args vals rvals cm' hg0 hd hargs hmr (cutO_returned hret) hrl

theorem xCallsIndOk_cut {E : Clif.Env} {Q : String → List Clif.Val → Clif.Mem → Prop}
    {sigs : List Clif.Signature} {MR : MemRelT} {X : ExtSem} (h : XCallsIndOk E sigs MR X) :
    XCallsIndOk (cutEnv E Q) sigs MR X := by
  intro sig hsig n g' sl cm w u args vals rvals cm' hg hs hu hargs hmr hret hrl hty
  obtain ⟨g, hg0, rfl⟩ := cutEnv_extern hg
  exact h sig hsig n g sl cm w u args vals rvals cm' hg0 hs hu hargs hmr (cutO_returned hret) hrl hty

/-! ## The linked machine's error states -/

theorem junkAt_err (s : Arm.ArmState) : Arm.r .ERR (junkAt s) ≠ .None := by
  simp [junkAt, Arm.r_of_w_same]

theorem enterAt_err (a : Art) (s : Arm.ArmState) : Arm.r .ERR (enterAt a s) = Arm.r .ERR s :=
  r_enterAt a s (by simp) (by simp)

/-- **A machine step keeps an error state** when its hooks do. -/
theorem armStepX_err {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {s : Arm.ArmState}
    (hH : ∀ d s, Arm.r .ERR s ≠ .None → Arm.r .ERR (H.call d s) ≠ .None)
    (hT : ∀ n r s, Arm.r .ERR s ≠ .None → Arm.r .ERR (H.tls n r s) ≠ .None)
    (h : Arm.r .ERR s ≠ .None) : Arm.r .ERR (ArmStepX X H fa s) ≠ .None := by
  dsimp only [ArmStepX]
  split
  · exact hH _ _ h
  · exact hH _ _ h
  · rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]; exact h
  · rw [Arm.r_of_w_different (by simp)]; exact h
  · rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]; exact h
  · rw [Arm.r_of_w_different (by simp)]; exact h
  · rw [Arm.r_of_w_different (by simp)]; exact h
  · exact hT _ _ _ h
  · rw [stepi_err h]; exact h

theorem runX_err {f : Arm.ArmState → Arm.ArmState}
    (hf : ∀ s, Arm.r .ERR s ≠ .None → Arm.r .ERR (f s) ≠ .None) :
    ∀ n s, Arm.r .ERR s ≠ .None → Arm.r .ERR (runX f n s) ≠ .None
  | 0, _, h => h
  | n + 1, s, h => runX_err hf n (f s) (hf s h)

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- The hooks of the linked machine send the call `info` at `u` outside `P`: a call of an extern
outside `P`, or a `blr` whose target is no function of `P`. -/
def GoesBase (info : CallInfo) (u : Arm.ArmState) : Prop :=
  L.BaseDest (destOf info) ∧ (destOf info = none → (blrTarget u).bind (symCallee L.Xb L.P) = none)

/-- **A call of `g` at `u` whose callee outside `P` traps with `tc`**: the pc at the call `info`
of `g`'s code (no error), sent outside `P` by the hooks, the callee's CLIF semantics trapping with
`tc` on the call's arguments and a memory related to a world of `u` (`TrapCallSem` of the base
environment, signatures erased as in `BaseOk.baseXI`, under `g`'s memory relation `RelW`). -/
def BaseTrapCallI (g : Clif.Function) (tc : Clif.TrapCode) (info : CallInfo) (u : Arm.ArmState) :
    Prop :=
  (L.A g).vcp.CallSite info ∧ L.GoesBase info u ∧ Arm.r .ERR u = .None ∧
  ∃ (ops : Array Operand) (regs : Array Reg) (i' : MInst) (w : Arm.ArmState)
    (F : BitVec 64 → Prop) (slotOff out : Nat) (c : BitVec 64),
    (MInst.call info).operands = .ok ops ∧ (MInst.call info).assign regs = .ok i' ∧
    CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) i' ∧ SameWorld F u w ∧
    TrapCallSem { L.base with sigOf := fun _ => none }
      ((g.externs.map (·.2)).filter fun e => (L.P.func? e.name).isNone) (indSigs g)
      (RelW ⟨F, L.syms, slotOff, out⟩ g c) L.Xb tc (callDest info) (useVals ops regs u) w

/-- `BaseTrapCallI` for some call. -/
def BaseTrapCall (g : Clif.Function) (tc : Clif.TrapCode) (u : Arm.ArmState) : Prop :=
  ∃ info, L.BaseTrapCallI g tc info u

/-- **A call of `g` at `u` of the function `h` of `P`**: the pc at a call of `g`'s code (no
error) that the hooks send to `h` (`bl h`, or `blr` of `h`'s address). -/
def ProgCallAt (g h : Clif.Function) (u : Arm.ArmState) : Prop :=
  ∃ (info : CallInfo) (regs : Array Reg) (i' : MInst), (L.A g).vcp.CallSite info ∧
    (MInst.call info).assign regs = .ok i' ∧ CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) i' ∧
    Arm.r .ERR u = .None ∧
    (destOf info = some h.name ∨
      (destOf info = none ∧ (blrTarget u).bind (symCallee L.Xb L.P) = some h))

/-- **The facts at a call state `u` of `g` calling the function `h` of `P`** that the executable
machine's call step needs (S9d): `h` is a function of `P`, the code image holds its bytes, and a
`blr` at `u` is through a register other than `xzr` by which `g` may enter its target (`BlrAt`). -/
structure ProgCallOk (g h : Clif.Function) (u : Arm.ArmState) : Prop where
  mem : h ∈ L.P.funcs
  code : ∀ a, L.Img a → u.mem a = L.imgMem a
  xzr : ∀ x, insnAt (L.A g).fa (L.A g).base (Arm.r .PC u) = some (.blr x) → x ≠ .xzr
  blrAt : L.BlrAt g u

/-- **The run of the linked machine of depth `M` from an activation of `g` entered in `s` stops
at step `n`**: the state there has no error, the activation's program and body `sp`, no earlier
state returns into `g`'s own code with another `sp` (`PostTrace`), every later state errs, and
every state of the run (and of the returning activations nested in it) whose step ends without
error has the per-state facts (`RunGoodL`, what the executable machine's simulation needs). -/
structure Stop (M : Nat) (g : Clif.Function) (s : Arm.ArmState) (n : Nat) : Prop where
  room : frameDrop (L.A g).af ≤ (spv s).toNat
  trace : PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n
  err : Arm.r .ERR (runX (L.mach M g) n s) = .None
  prog : (runX (L.mach M g) n s).program = (L.A g).fb.program (L.A g).base
  sp : spv (runX (L.mach M g) n s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)
  halt : ∀ m, Arm.r .ERR (runX (L.mach M g) (n + m + 1) s) ≠ .None
  good : L.RunGoodL M g s

/-- **The outside code's trap contract** (next to `BaseOk`; vacuous where no extern outside `P`
traps): where the CLIF semantics of an extern outside `P` traps on a call's arguments and a
memory related to the world (direct, or indirect with the signatures erased as in
`BaseOk.baseXI`), its machine semantics `Xb` gives no normal return (`xt`: `XTrapsOk`) and its
hook errs (`stop`: the outside code does not return there); the base hooks keep an error state
(`err`, `tlsErr`: the machine does not run from a faulted state). -/
structure BaseTrapsOk : Prop where
  xt : ∀ g ∈ L.P.funcs, ∀ F slotOff out c, XTrapsOk { L.base with sigOf := fun _ => none }
    ((g.externs.map (·.2)).filter fun e => (L.P.func? e.name).isNone) (indSigs g)
    (RelW ⟨F, L.syms, slotOff, out⟩ g c) L.Xb
  stop : ∀ g ∈ L.P.funcs, ∀ tc info u, L.BaseTrapCallI g tc info u →
    Arm.r .ERR (L.Hb.call (destOf info) u) ≠ .None
  err : ∀ d s, Arm.r .ERR s ≠ .None → Arm.r .ERR (L.Hb.call d s) ≠ .None
  tlsErr : ∀ n r s, Arm.r .ERR s ≠ .None → Arm.r .ERR (L.Hb.tls n r s) ≠ .None

/-- The program callee traps covered by the premise `D` of the callees' activations: a call of
the function `h` of `P` named `n` on `vals`, `cm` whose activation satisfies `D`. -/
def covQ (D : Clif.Function → Clif.State → Prop) (n : String) (vals : List Clif.Val)
    (cm : Clif.Mem) : Prop :=
  ∀ h cs, L.P.func? n = some h → Clif.initState L.P n vals cm = .ok cs → D h cs

/-- **The run premise of an activation of `g` at depth `M`**, given the premise `D` of the
program callees' activations: no memory-access trap (`TrapsExplicitC` under the linked
environment), and the run under `envR` traps as it does with the program callee traps outside
`D` made stuck (`cutEnv`): every callee trap the run hits is one of an activation satisfying
`D`. -/
def TrapsAt (M : Nat) (D : Clif.Function → Clif.State → Prop) (g : Clif.Function)
    (cs : Clif.State) : Prop :=
  TrapsExplicitC (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs ∧
  ∀ fuel tc, Clif.runLoop (L.envR M g) L.P.bare fuel cs = .trapped tc →
    Clif.runLoop (cutEnv (L.envR M g) (L.covQ D)) L.P.bare fuel cs = .trapped tc

end LinkSys

/-- **The run premise of the linked program with callee traps** (`TrapsExplicitC`'s linked
counterpart), by depth: an activation at depth `M` satisfies `TrapsAt` with its program callees'
activations satisfying the premise at depth `M - 1` (at depth `0` no program callee trap). -/
def LinkSys.TrapsD (L : LinkSys) : Nat → Clif.Function → Clif.State → Prop
  | 0 => L.TrapsAt 0 fun _ _ => False
  | M + 1 => L.TrapsAt (M + 1) (LinkSys.TrapsD L M)

/-- The premise of the program callees' activations of an activation at depth `M`. -/
def LinkSys.TrapsDn (L : LinkSys) : Nat → Clif.Function → Clif.State → Prop
  | 0 => fun _ _ => False
  | M + 1 => L.TrapsD M

theorem LinkSys.trapsD_eq (L : LinkSys) (M : Nat) (g : Clif.Function) (cs : Clif.State) :
    L.TrapsD M g cs = L.TrapsAt M (L.TrapsDn M) g cs := by
  cases M <;> rfl

/-- **The trap observable of the linked machine** of depth `M` from an activation of `g` entered
in `s`, trap code `c`: the run stops (`Stop`) at a trap site of `g` with `c` (`site`), at a call
of `g` whose callee outside `P` traps with `c` (`base`), or at a call of `g` of a function `h`
of `P` (from a return address allowed for `h`, `RaOk`, with the call state's facts `ProgCallOk`)
whose activation entered from that call state has the observable one level down (`prog`). -/
inductive LinkSys.TrapIn (L : LinkSys) : Nat → Clif.Function → Arm.ArmState → Clif.TrapCode →
    Prop
  | site {M : Nat} {g : Clif.Function} {s : Arm.ArmState} {c : Clif.TrapCode} {n : Nat} :
      L.Stop M g s n → TrapAt (L.A g).fb (L.A g).base c (runX (L.mach M g) n s) → L.TrapIn M g s c
  | base {M : Nat} {g : Clif.Function} {s : Arm.ArmState} {c : Clif.TrapCode} {n : Nat} :
      L.Stop M g s n → L.BaseTrapCall g c (runX (L.mach M g) n s) → L.TrapIn M g s c
  | prog {M : Nat} {g h : Clif.Function} {s : Arm.ArmState} {c : Clif.TrapCode} {n : Nat} :
      L.Stop (M + 1) g s n → L.ProgCallAt g h (runX (L.mach (M + 1) g) n s) →
      L.ProgCallOk g h (runX (L.mach (M + 1) g) n s) →
      RaOk (L.A h) (Arm.r .PC (runX (L.mach (M + 1) g) n s)) →
      L.TrapIn M h (enterAt (L.A h) (runX (L.mach (M + 1) g) n s)) c → L.TrapIn (M + 1) g s c

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem TrapIn.stop {L : LinkSys} {M : Nat} {g : Clif.Function} {s : Arm.ArmState}
    {c : Clif.TrapCode} (h : L.TrapIn M g s c) : ∃ n, L.Stop M g s n := by
  cases h with
  | site h _ => exact ⟨_, h⟩
  | base h _ => exact ⟨_, h⟩
  | prog h _ _ _ _ => exact ⟨_, h⟩

/-! ## No return -/

/-- **A stopping run never returns**: from the entry of `h` for a call at `t` (return address
allowed for `h`, `RaOk`), no state of a stopping run is a return to `t` (`RetOf`). -/
theorem noRet_of_stop (hL : L.Ok) {M : Nat} {h : Clif.Function} (hh : h ∈ L.P.funcs)
    {t : Arm.ArmState} {n : Nat} (hst : L.Stop M h (enterAt (L.A h) t) n)
    (hra : RaOk (L.A h) (Arm.r .PC t)) :
    ∀ k, ¬ RetOf (L.A h) t (runX (L.mach M h) k (enterAt (L.A h) t)) := by
  intro k hk
  have hc := hL.compiled h hh
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have hfd : 0 < frameDrop (L.A h).af := by rw [L.frameDrop_eq hL hh]; omega
  have hroom := hst.room
  rw [spv_enterAt] at hroom
  have hlt := (spv t).isLt
  have hne_sp : spv t - BitVec.ofNat 64 (frameDrop (L.A h).af) ≠ spv t := by
    intro e
    have e' := congrArg BitVec.toNat e
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : frameDrop (L.A h).af < 2 ^ 64)] at e'
    omega
  rcases Nat.lt_trichotomy k n with hkn | rfl | hkn
  · rcases hra with hra | ⟨hcp, hne⟩
    · have := retStuck (X := L.Xb) (H := L.hooks M) hc.layout hlm hk.2.2.1
        (by rw [hk.1]; exact hra) (n - k - 1)
      change Arm.r .ERR (runX (L.mach M h) (n - k - 1 + 1) (runX (L.mach M h) k _)) ≠ _ at this
      rw [← runX_add, show k + (n - k - 1 + 1) = n by omega] at this
      exact this hst.err
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · apply hne
        rw [← hk.1]
        simp [runX, enterAt, Arm.r_of_w_same]
      · have hsp := hst.trace k hk0 hkn ⟨_, hcp, hk.1⟩
        rw [hk.2.2.2, spv_enterAt] at hsp
        exact hne_sp hsp.symm
  · have := hst.sp
    rw [hk.2.2.2, spv_enterAt] at this
    exact hne_sp this.symm
  · have := hst.halt (k - n - 1)
    rw [show n + (k - n - 1) + 1 = k by omega] at this
    exact this hk.2.1

/-- **The linked call of a trapping program callee is an error state** (`junkAt`). -/
theorem pcall_junk (hL : L.Ok) {M : Nat} {h : Clif.Function} {c : Clif.TrapCode}
    {t : Arm.ArmState} (hh : h ∈ L.P.funcs) (hT : L.TrapIn M h (enterAt (L.A h) t) c)
    (hra : RaOk (L.A h) (Arm.r .PC t)) : L.pcall (M + 1) h t = junkAt t := by
  obtain ⟨n, hst⟩ := hT.stop
  show linkedCall _ _ _ = _
  unfold linkedCall
  exact dite_eq_right_of_eq_false (eq_false fun ⟨k, hk⟩ => L.noRet_of_stop hL hh hst hra k hk)

/-! ## Error states of the linked machine -/

theorem callHook_err (hB : L.BaseTrapsOk) {pc : Clif.Function → Arm.ArmState → Arm.ArmState}
    (hpc : ∀ g s, Arm.r .ERR s ≠ .None → Arm.r .ERR (pc g s) ≠ .None) (d : Option String)
    (s : Arm.ArmState) (h : Arm.r .ERR s ≠ .None) :
    Arm.r .ERR (callHook L.Hb L.Xb L.P pc d s) ≠ .None := by
  unfold callHook
  split
  · split
    · exact hpc _ _ h
    · exact hB.err _ _ h
  · split
    · exact hpc _ _ h
    · exact hB.err _ _ h

/-- **The linked machine keeps an error state** (under the outside code's error contract). -/
theorem hooks_err (hB : L.BaseTrapsOk) :
    ∀ M d s, Arm.r .ERR s ≠ .None → Arm.r .ERR ((L.hooks M).call d s) ≠ .None
  | 0, d, s, h => L.callHook_err hB (fun _ s _ => junkAt_err s) d s h
  | M + 1, d, s, h => by
    refine L.callHook_err hB (fun g s hs => ?_) d s h
    show Arm.r .ERR (linkedCall _ _ _) ≠ .None
    unfold linkedCall
    split
    · rename_i hex
      exfalso
      obtain ⟨k, hk⟩ := hex
      refine runX_err (fun u hu => armStepX_err (hooks_err hB M) ?_ hu) k _ ?_ hk.2.1
      · rw [hooks_tls]; exact hB.tlsErr
      · rw [enterAt_err]; exact hs
    · exact junkAt_err s

theorem mach_err (hB : L.BaseTrapsOk) (M : Nat) (g : Clif.Function) (s : Arm.ArmState)
    (h : Arm.r .ERR s ≠ .None) : Arm.r .ERR (L.mach M g s) ≠ .None :=
  armStepX_err (L.hooks_err hB M) (by rw [hooks_tls]; exact hB.tlsErr) h

theorem runX_mach_err (hB : L.BaseTrapsOk) (M : Nat) (g : Clif.Function) :
    ∀ n s, Arm.r .ERR s ≠ .None → Arm.r .ERR (runX (L.mach M g) n s) ≠ .None :=
  runX_err (L.mach_err hB M g)

/-! ## The induction statement and the program callees' traps -/

/-- **The trap counterpart of the linking statement at depth `M`** (`LinkSys.Thm`): for every
function `g` of `P` and every world-side activation whose run of `P.bare` under `envR M g` traps
with `tc` under the run premise `TrapsD`, every machine-side activation at depth `M` has the trap
observable. -/
def ThmT (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat) (tc : Clif.TrapCode), L.WorldEntry κ M g F vals cs w₀ →
    L.TrapsD M g cs → Clif.runLoop (L.envR M g) L.P.bare fuel cs = .trapped tc →
    ∀ G ra s, L.MachEntry κ M g F G ra s w₀ → L.TrapIn M g s tc

/-- `ThmT` for any run premise `D` of the activations (`ThmT κ M` is `ThmTG L.TrapsD κ M`;
`FV/E2E/LinkTrapCallT.lean` instantiates it with the premise allowing `try_call` callee traps). -/
def ThmTG (D : Nat → Clif.Function → Clif.State → Prop) (κ : Nat → Clif.Function → Nat)
    (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat) (tc : Clif.TrapCode), L.WorldEntry κ M g F vals cs w₀ →
    D M g cs → Clif.runLoop (L.envR M g) L.P.bare fuel cs = .trapped tc →
    ∀ G ra s, L.MachEntry κ M g F G ra s w₀ → L.TrapIn M g s tc

/-- **A trapping call of a function `h` of `P`** at depth `M` (its callee run at depth `M`
traps, its activation satisfies the run premise `D` one level down) from a world `w` with room for
the callee's stack: from every caller state compatible with `w` (`CallerOk`), the callee's
activation has the trap observable one level down (the trap counterpart of `progCall`; each
caller state is entered with its own body-entry world, no non-interference needed). -/
theorem progCallTG (hL : L.Ok) [hR : L.CrunOk] {D : Nat → Clif.Function → Clif.State → Prop}
    {M : Nat} (hM : 0 < M) (ih : L.ThmTG D κ (M - 1))
    {n : String} {h : Clif.Function} (hpf : L.P.func? n = some h)
    (hcal : ∃ g ∈ L.P.funcs, L.Callee g h) {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (L.A h).af + κ (M - 1) h ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a → F a ∧ ¬ L.Img a)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {tc : Clif.TrapCode}
    (hmr : MemRel F L.syms cm w) (hargs : ArgsAt h.sig vals uses w)
    (hsav : StackArgsAvoid F h.sig vals w) (hpl : L.NeedSlots → L.PlaceAt cm (spv w))
    (hinit : Clif.initState L.P n vals cm = .ok cs) (hrun : L.crun M cs = .trapped tc)
    (hTD : D (M - 1) h cs) :
    ∀ t, L.CallerOk F h uses w t → L.TrapIn (M - 1) h (enterAt (L.A h) t) tc := by
  intro t ht
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  subst hname
  have hc := hL.compiled h hh
  have hfr := lowerRFunc_frame hc.alloc
  have hdrop := L.frameDrop_eq hL hh
  have hfs := L.frameSize_mod hL hh
  obtain ⟨hnd, harg, hwid⟩ := hL.argRegs h hh
  have hsl0 : ¬ L.NeedSlots → h.slots = [] := fun hn => Classical.byContradiction fun hne => by
    obtain ⟨g, hg, hcg⟩ := hcal
    exact hn ⟨g, hg, h, hcg, hne⟩
  have hcase : h.slots = [] ∨ L.PlaceAt cm (spv w) := by
    by_cases hN : L.NeedSlots
    · exact .inr (hpl hN)
    · exact .inl (hsl0 hN)
  obtain ⟨hsl', hsym', hal', hby', hpl'⟩ := L.initState_mem hpf hinit hcase
  have hsz_le := size_le_frameSize hc.alloc
  have hfits : ∀ p ∈ h.slots, ∃ off, (slotLayout h.slots).1.lookup p.1 = some off ∧
      (L.A h).af.slotBase + off + p.2.size ≤ (L.A h).af.frameSize - clobberBytes (L.A h).af.saves := by
    obtain ⟨g, hg, hcg⟩ := hcal
    exact hL.slotFits g hg h hcg
  have hce : ClifEntry h vals cs := clifEntry_initState hpf hinit
  -- the run of the program without functions (program callees: the callee runs one level down)
  obtain ⟨m, hm⟩ := hR.link M hM h hh cs (runInv_entry hh hce)
    (runInv_entry (by simp [Clif.Program.only]) hce) (fun _ => hsym'.trans hmr.symbols)
    (L.envR (M - 1) h) rfl rfl (fun _ hn => L.envR_of (.inl hn)) (L.envR_link hL.names)
    (by rw [hrun]; intro _ e; cases e) (by rw [hrun]; intro e; cases e)
  rw [hrun] at hm
  -- the caller state and its body-entry world
  have hst : spv t = spv w := ht.world.1 _ (by simp [Masked])
  have hslotB : (L.A h).af.slotBase = (RAFrame.compute (L.A h).vcp (L.A h).rf).size :=
    (lowerRFunc_ok hc.alloc).1.2.1
  have herrt : Arm.r .ERR t = .None := by rw [ht.world.1 _ (by simp [Masked])]; exact herr
  let w₀ := bodyOf (L.A h).af (enterAt (L.A h) t)
  have hspw₀ : spv w₀ = spv w - BitVec.ofNat 64 (frameDrop (L.A h).af) := by
    rw [spv_bodyOf, spv_enterAt, hst]
  obtain ⟨-, -, hB⟩ := off_toNat 0 (spv w) (frameDrop (L.A h).af) (by omega)
  -- the callee's outgoing area (in the caller's dead stack) is outside the callee's `F`
  let ib := (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase
  let spb := spv w - BitVec.ofNat 64 (frameDrop (L.A h).af)
  let sz := (RAFrame.compute (L.A h).vcp (L.A h).rf).size
  let Fh : BitVec 64 → Prop := fun a =>
    F a ∧ ¬ OutAt ib spb a ∧ ¬ SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb a
  have hib_le : ib ≤ sz := intBase_le_size _ _
  have hspb : spb.toNat = (spv w).toNat - frameDrop (L.A h).af := hB
  have hlt := (spv w).isLt
  have hout_reg : ∀ a, OutAt ib spb a →
      StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a := by
    intro a ⟨h1, h2⟩
    rw [hspb] at h1 h2
    exact ⟨by omega, by omega⟩
  have hout_F : ∀ a, OutAt ib spb a → F a ∧ ¬ L.Img a := fun a ha => hdead a (hout_reg a ha)
  have hslot_reg : ∀ a, SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb a →
      StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a := by
    intro a ⟨h1, h2⟩
    rw [hspb] at h1 h2
    exact ⟨by omega, by omega⟩
  have hslot_F : ∀ a, SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb a → F a ∧ ¬ L.Img a :=
    fun a ha => hdead a (hslot_reg a ha)
  have hspb_add : ∀ j < ib, OutAt ib spb (spb + BitVec.ofNat 64 j) := by
    intro j hj
    have e : (spb + BitVec.ofNat 64 j).toNat = spb.toNat + j := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), hspb]
      exact Nat.mod_eq_of_lt (by omega)
    exact ⟨by omega, by omega⟩
  have hOut : ∀ (u : Arm.ArmState), spv u = spb →
      (∀ a n, cs.mem.valid a n = true → ∀ k < n, ¬ OutAt ib spb (BitVec.ofNat 64 (a + k))) →
      OutRel Fh ib cs.mem u := by
    intro u hu hv
    refine ⟨by omega, fun j hj hfh => hfh.2.1 (hu ▸ hspb_add j hj), fun a n hva k hk j hj e => ?_⟩
    rw [hu] at e
    exact hv a n hva k hk (e ▸ hspb_add j hj)
  -- the live allocations of the callee's entry: the caller's, and its slots in its slot region
  have hcsv : ∀ a n, cs.mem.valid a n = true → a + n ≤ 2 ^ 64 ∧ ∀ k < n,
      ¬ Fh (BitVec.ofNat 64 (a + k)) ∧ ¬ OutAt ib spb (BitVec.ofNat 64 (a + k)) := by
    intro a n hv
    simp only [Clif.Mem.valid, List.any_eq_true] at hv
    obtain ⟨x, hx, hcx⟩ := hv
    rcases hal' x hx with hx' | ⟨p, hp, rfl⟩
    · have hv' : cm.valid a n = true := List.any_eq_true.mpr ⟨x, hx', hcx⟩
      obtain ⟨h1, h2⟩ := hmr.valid a n hv'
      exact ⟨h1, fun k hk => ⟨fun hf => h2 k hk hf.1, fun ho => h2 k hk (hout_F _ ho).1⟩⟩
    · obtain ⟨off, hoff, hle⟩ := hfits p hp
      simp only [Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq, hoff,
        Option.getD_some] at hcx
      refine ⟨by omega, fun k hk => ?_⟩
      have e : (BitVec.ofNat 64 (a + k)).toNat = a + k := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      refine ⟨fun hf => hf.2.2 ⟨by rw [e]; omega, by rw [e]; omega⟩,
        fun ⟨o1, o2⟩ => by rw [e] at o1 o2; omega⟩
  -- the callee's entry memory is related to a body-entry world agreeing with the caller's
  have hRel : ∀ u, spv u = spb → Arm.r .ERR u = .None →
      (∀ a b, cm.valid a 1 = true → cm.bytes a = some b → Arm.read_mem (BitVec.ofNat 64 a) u = b) →
      RelW ⟨Fh, L.syms, (L.A h).af.slotBase, ib⟩ h (spv w₀) cs.frame.slots cs.mem u := by
    intro u hu herru hbu
    refine ⟨⟨⟨fun a b hv hb => ?_, fun a n hv => ⟨(hcsv a n hv).1,
      fun k hk => ((hcsv a n hv).2 k hk).1⟩, hsym'.trans hmr.symbols⟩, fun id b hl => ?_,
      hOut u hu (fun a n hv k hk => ((hcsv a n hv).2 k hk).2)⟩, by rw [hu, hspw₀], herru⟩
    · obtain ⟨hb', hnot⟩ := hby' a b hb
      refine hbu a b ?_ hb'
      simp only [Clif.Mem.valid, List.any_eq_true] at hv ⊢
      obtain ⟨x, hx, hcx⟩ := hv
      rcases hal' x hx with hx' | ⟨p, hp, rfl⟩
      · exact ⟨x, hx', hcx⟩
      · simp only [Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hcx
        exact absurd ⟨hcx.1, by omega⟩ (hnot p hp)
    · rw [hsl'] at hl
      obtain ⟨p, hp, rfl, rfl⟩ := lookup_map_some hl
      obtain ⟨off, hoff, -⟩ := hfits p hp
      refine ⟨off, hoff, ?_⟩
      simp only [Rel.slotReg, hoff, Option.getD_some, hu]
      omega
  have hx29 : Arm.r (.GPR 29#5) w₀ = spv w - 16#64 := by
    have := x29_bodyOf (L.A h).af (enterAt (L.A h) t)
    rw [if_pos hfr, spv_enterAt, hst] at this
    exact this
  have hWE : L.WorldEntry κ (M - 1) h Fh vals cs w₀ := by
    refine ⟨hce, ?_, ?_, ?_, ?_, ?_, fun a ha => ⟨himgF a ha, fun ho => (hout_F a ho).2 ha,
      fun hs => (hslot_F a hs).2 ha⟩, fun hN => by rw [hspw₀]; exact hpl' (hpl hN)⟩
    · refine hRel w₀ hspw₀ ?_ fun a b hv hb => ?_
      · simp only [w₀]
        rw [r_bodyOf _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp)]
        exact herrt
      · rw [← hmr.bytes a b hv hb]
        simp only [Arm.read_mem, Arm.read_store, w₀, mem_bodyOf, mem_enterAt]
        exact ht.world.2.1 _ (by simpa using (hmr.valid a 1 hv).2 0 (by omega))
    · intro loc v hmem
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
      cases loc with
      | stack off =>
        simp only
        rw [hx29, fp_off_eq]
        refine ⟨fun k hk hf => hsav off v hmem k hk hf.1, ?_⟩
        rw [show Arm.read_mem_bytes v.ty.bytes (spv w + BitVec.ofNat 64 off) w₀ =
            Arm.read_mem_bytes v.ty.bytes (spv w + BitVec.ofNat 64 off) w from
          read_mem_bytes_congr _ _ (fun k hk => by
            simp only [w₀, mem_bodyOf, mem_enterAt]
            exact ht.world.2.1 _ (hsav off v hmem k hk))]
        exact hargs.2.2 off v hmem
      | reg r =>
        obtain ⟨i, hr, hv⟩ := reg_zip _ _ hi
        have hlen := hargs.2.1.1
        obtain ⟨u, hu⟩ : ∃ u, uses[i]? = some u := by
          have hi' : i < uses.length := by
            rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hv).1
          exact ⟨uses[i]'hi', List.getElem?_eq_getElem _⟩
        have hvh := hargs.2.1.2 i v u hv hu
        have hrA : r.isArgReg = true := harg r (List.mem_of_getElem? hr)
        simp only
        rw [show regVal w₀ r = regVal (placeArgs (regLocs h.sig) uses (L.withImg w)) r by
          simp only [w₀]
          rw [regVal_bodyOf _ _ hrA, regVal_enterAt _ _ hrA, ht.regs r (List.mem_of_getElem? hr),
            L.regVal_canon _ _ _ hrA],
          placeArgs_regVal _ _ _ hnd harg hr hu]
        refine vHolds_setVal ?_ hvh
        have hty := hce.sig
        have hvmem : v ∈ vals := List.of_mem_zip hmem |>.2
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hvmem
        have e := congrArg (·[j]?) hty
        simp only [List.getElem?_map, hj, Option.map_some] at e
        cases hp : h.sig.params[j]? with
        | none => rw [hp] at e; cases e
        | some p =>
          rw [hp] at e
          simp only [Option.map_some, Option.some.injEq] at e
          rw [e]; exact hwid p (List.mem_of_getElem? hp)
    · rw [hspw₀, hB]; omega
    · intro a ha
      rw [hspw₀] at ha
      obtain ⟨h1, h2⟩ := ha
      rw [hB] at h1 h2
      have hd := hdead a ⟨by omega, by omega⟩
      exact ⟨⟨hd.1, fun ⟨o1, o2⟩ => by rw [hspb] at o1; omega,
        fun ⟨o1, o2⟩ => by rw [hspb] at o1; omega⟩, hd.2⟩
    · rw [hspw₀, hB, hdrop]; omega
  -- the callee's activation from the caller state `t`
  let G : BitVec 64 → Prop :=
    fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a
  have hcode : ∀ a, CodeAddr (enterAt (L.A h) t) a → L.Img a := fun a ha =>
    hL.imgAddr h hh a (by simpa [CodeAddr] using ha)
  have hspt : spv (enterAt (L.A h) t) = spv w := by rw [spv_enterAt]; exact hst
  have hFrame : frameWG (κ (M - 1) h) ib (RAFrame.compute (L.A h).vcp (L.A h).rf).size
      (L.A h).af G (enterAt (L.A h) t) = Fh := by
    funext a
    apply propext
    rw [frameWG_out hfr (by rw [hspt, ← hdrop]; exact hroom) hib_le (size_le_frameBody hc.alloc), ← hdrop, hspt]
    constructor
    · rintro (⟨hb, hno, hns⟩ | hc | hg)
      · exact ⟨(hdead a hb).1, hno, hns⟩
      · exact ⟨himgF a (hcode a hc), fun ho => (hout_F a ho).2 (hcode a hc),
          fun hs => (hslot_F a hs).2 (hcode a hc)⟩
      · exact ⟨hg.1, fun ho => hg.2 (hout_reg a ho), fun hs => hg.2 (hslot_reg a hs)⟩
    · intro ⟨hF, hno, hns⟩
      by_cases hb : StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a
      · exact .inl ⟨hb, hno, hns⟩
      · exact .inr (.inr ⟨hF, hb⟩)
  have hbw : BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀ :=
    ⟨spv_bodyOf _ _, x29_bodyOf _ _, fun r hr => regVal_bodyOf _ _
      (harg r (hL.entryRegs h hh r hr)), fun f hf h29 h31 => r_bodyOf _ _ h29 h31,
      fun a _ => by simp [w₀], by simp [w₀]⟩
  have hME : L.MachEntry κ (M - 1) h Fh G (Arm.r .PC t + 4) (enterAt (L.A h) t) w₀ := by
    refine ⟨⟨by simp, fun k wd hk => hL.imgCode h hh _ (fun a ha => by
        rw [mem_enterAt]; exact ht.img a ha) k wd hk, by simp, ?_, x30_enterAt _ _, ?_,
        hL.fits h hh⟩, ?_, fun a ha => ?_, hFrame,
      fun a ha => ⟨himgF a ha, fun hb => (hdead a hb).2 ha⟩,
      fun a ha => by rw [mem_enterAt]; exact ht.img a ha, hbw⟩
    · rw [r_enterAt _ _ (by simp) (by simp)]; exact herrt
    · rw [hspt]; exact hal
    · refine stackRoom_of (by rw [hspt, ← hdrop]; exact hroom) fun a ha hb => ?_
      rw [hspt, ← hdrop] at hb
      exact (hdead a hb).2 (hcode a ha)
    · rw [hspt]; exact ha.2
  exact ih h hh Fh vals cs w₀ m tc hWE hTD hm G (Arm.r .PC t + 4) (enterAt (L.A h) t) hME

/-- `progCallTG` for the run premise `TrapsD`. -/
theorem progCallT (hL : L.Ok) [hR : L.CrunOk] {M : Nat} (hM : 0 < M) (ih : L.ThmT κ (M - 1))
    {n : String} {h : Clif.Function} (hpf : L.P.func? n = some h)
    (hcal : ∃ g ∈ L.P.funcs, L.Callee g h) {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (L.A h).af + κ (M - 1) h ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a → F a ∧ ¬ L.Img a)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {tc : Clif.TrapCode}
    (hmr : MemRel F L.syms cm w) (hargs : ArgsAt h.sig vals uses w)
    (hsav : StackArgsAvoid F h.sig vals w) (hpl : L.NeedSlots → L.PlaceAt cm (spv w))
    (hinit : Clif.initState L.P n vals cm = .ok cs) (hrun : L.crun M cs = .trapped tc)
    (hTD : L.TrapsD (M - 1) h cs) :
    ∀ t, L.CallerOk F h uses w t → L.TrapIn (M - 1) h (enterAt (L.A h) t) tc :=
  L.progCallTG (D := L.TrapsD) hL hM ih hpf hcal himgF herr hal hroom hdead hmr hargs hsav hpl
    hinit hrun hTD

theorem linkInitState_ne_trap (P : Clif.Program) (n : String) (vals : List Clif.Val)
    (mem : Clif.Mem) (c : Clif.TrapCode) : Clif.initState P n vals mem ≠ .trap c := by
  simp only [Clif.initState]
  cases P.func? n with
  | none => simp
  | some h =>
    simp only [Clif.Res.ofOption_some, Clif.Res.ok_bind]
    cases he : Clif.enterFunc h vals mem with
    | ok r => simp
    | trap c' => exact absurd he (Opt.enterFunc_not_trap h vals mem c')
    | stuck m => simp

/-- **`progX` of a trapping callee is undefined**: when the callee run at depth `M` from an
entry related to the world `w` traps and its activation satisfies the run premise `D` one level
down, the linked machine's call from the canonical state does not return (`progCallTG`,
`pcall_junk`). -/
theorem progX_noneG (hL : L.Ok) [hR : L.CrunOk] {D : Nat → Clif.Function → Clif.State → Prop}
    {M : Nat} (ih : 0 < M → L.ThmTG D κ (M - 1))
    {h : Clif.Function} (hh : h ∈ L.P.funcs) (hcal : ∃ g ∈ L.P.funcs, L.Callee g h)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {sl : List (Clif.SlotId × Nat)}
    {slotOff out : Nat} {g : Clif.Function} {c : BitVec 64} {cm : Clif.Mem} {w : Arm.ArmState}
    {args : List CV} {vals : List Clif.Val} {cs : Clif.State} {tc : Clif.TrapCode}
    (hargs : ArgsAt h.sig vals args w) (hsav : StackArgsAvoid F h.sig vals w)
    (hmr : RelW ⟨F, L.syms, slotOff, out⟩ g c sl cm w) (hpl : L.NeedSlots → L.PlaceAt cm c)
    (hinit : Clif.initState L.P h.name vals cm = .ok cs) (hret : L.crun M cs = .trapped tc)
    (hTD : 0 < M → D (M - 1) h cs) :
    L.progX κ M F h args w = none := by
  have hpf := func?_of_mem hL.names hh
  unfold progX
  rw [if_neg]
  rintro ⟨⟨hM, herrw, halw, hroom, hdead, -⟩, herr'⟩
  obtain ⟨⟨hmemR0, -, -⟩, hsp, -⟩ := hmr
  have hT := L.progCallTG hL hM (ih hM) hpf hcal himgF herrw halw hroom hdead hmemR0 hargs hsav
    (fun hN => by rw [hsp]; exact hpl hN) hinit hret (hTD hM) _
    (L.callerOk_canon hL hh himgF args w)
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [show L.pcall (M' + 1) h (L.canon h args w) = junkAt (L.canon h args w) from
    L.pcall_junk hL hh hT (L.callerOk_canon hL hh himgF args w).ra] at herr'
  exact junkAt_err _ herr'

/-- `progX_noneG` for the run premise `TrapsD`. -/
theorem progX_none (hL : L.Ok) [hR : L.CrunOk] {M : Nat} (ih : 0 < M → L.ThmT κ (M - 1))
    {h : Clif.Function} (hh : h ∈ L.P.funcs) (hcal : ∃ g ∈ L.P.funcs, L.Callee g h)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {sl : List (Clif.SlotId × Nat)}
    {slotOff out : Nat} {g : Clif.Function} {c : BitVec 64} {cm : Clif.Mem} {w : Arm.ArmState}
    {args : List CV} {vals : List Clif.Val} {cs : Clif.State} {tc : Clif.TrapCode}
    (hargs : ArgsAt h.sig vals args w) (hsav : StackArgsAvoid F h.sig vals w)
    (hmr : RelW ⟨F, L.syms, slotOff, out⟩ g c sl cm w) (hpl : L.NeedSlots → L.PlaceAt cm c)
    (hinit : Clif.initState L.P h.name vals cm = .ok cs) (hret : L.crun M cs = .trapped tc)
    (hTD : 0 < M → L.TrapsD (M - 1) h cs) :
    L.progX κ M F h args w = none :=
  L.progX_noneG (D := L.TrapsD) hL ih hh hcal himgF hargs hsav hmr hpl hinit hret hTD

/-- The stack-passed arguments of a call of a function `h` of `P` that `g` declares are in `g`'s
outgoing area, outside the world (`outFits`). -/
theorem stackArgsAvoid_decl (hL : L.Ok) {g h : Clif.Function} (hg : g ∈ L.P.funcs)
    {ext : Clif.ExtFunc} (hin : ext ∈ g.externs.map (·.2)) (hpf : L.P.func? ext.name = some h)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State}
    (hinit : Clif.initState L.P ext.name vals cm = .ok cs) {F : BitVec 64 → Prop}
    {slotOff : Nat} {c : BitVec 64} {sl : List (Clif.SlotId × Nat)} {w : Arm.ArmState}
    (hmr : RelW ⟨F, L.syms, slotOff, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c sl cm w) :
    StackArgsAvoid F h.sig vals w := by
  obtain ⟨-, hname⟩ := Clif.Program.func?_some hpf
  have hsig := hL.declSig g hg ext hin h hpf
  have hout := hmr.1.2.2
  intro off v hm k hk
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  rw [List.getElem?_zip_eq_some] at hi
  obtain ⟨hli, hvi⟩ := hi
  have hty := (clifEntry_initState (f := h) (by rw [hname]; exact hpf)
    (by rw [hname]; exact hinit)).sig
  obtain ⟨p, hp⟩ : ∃ p, h.sig.params[i]? = some p := by
    have := congrArg (·[i]?) hty
    simp only [List.getElem?_map, hvi, Option.map_some] at this
    cases hp : h.sig.params[i]? with
    | none => rw [hp] at this; cases this
    | some p => exact ⟨p, rfl⟩
  have hvp : v.ty = p.ty := by
    have := congrArg (·[i]?) hty
    simp only [List.getElem?_map, hvi, hp, Option.map_some, Option.some.injEq] at this
    exact this
  have hfit := hL.outFits g hg ext hin (by simp [hpf]) i off p (by rw [hsig]; exact hli)
    (by rw [hsig]; exact hp)
  rw [hvp] at hk
  rw [add_ofNat_add]
  have hav : Avoids F (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase (spv w) := hout.2.1
  exact hav (off + k) (by omega)

/-- An extern of `envOf` that is a function of `P` (`g` may reach it): the linked environment's,
guarded by the slot-placement oracle. -/
theorem envOf_prog {M : Nat} {g : Clif.Function} {c : BitVec 64} {n : String}
    {G : List Clif.Val → Clif.Mem → Clif.Outcome} {h : Clif.Function}
    (hG : (L.envOf M g c).extern n = some G) (hpf : L.P.func? n = some h) :
    L.MayCall g n ∧ ∃ G0, (Clif.linkEnvR L.P L.base (L.crun M)).extern n = some G0 ∧
      ∀ vals cm tc, G vals cm = .trapped tc → (L.NeedSlots → L.PlaceAt cm c) ∧
        G0 vals cm = .trapped tc := by
  simp only [envOf] at hG
  split at hG
  · cases hG
  · rename_i hn
    rw [if_pos (by simp [hpf])] at hG
    refine ⟨Classical.byContradiction fun hd => hn ⟨by simp [hpf], hd⟩, ?_⟩
    cases hG0 : (Clif.linkEnvR L.P L.base (L.crun M)).extern n with
    | none => rw [hG0] at hG; cases hG
    | some G0 =>
      rw [hG0] at hG
      simp only [Option.map_some, Option.some.injEq] at hG
      subst hG
      refine ⟨G0, rfl, fun vals cm tc hr => ?_⟩
      dsimp only at hr
      by_cases hp : L.NeedSlots → L.PlaceAt cm c
      · rw [if_pos hp] at hr; exact ⟨hp, hr⟩
      · rw [if_neg hp] at hr; cases hr

/-- A trap of the linked environment's extern of a function `h` of `P`: the callee run at depth
`M` from `h`'s entry traps. -/
theorem linkEnvR_trap {M : Nat} {h : Clif.Function} {n : String} (hpf : L.P.func? n = some h)
    {G0 : List Clif.Val → Clif.Mem → Clif.Outcome}
    (hG0 : (Clif.linkEnvR L.P L.base (L.crun M)).extern n = some G0) {vals : List Clif.Val}
    {cm : Clif.Mem} {tc : Clif.TrapCode} (ht : G0 vals cm = .trapped tc) :
    ∃ cs, Clif.initState L.P n vals cm = .ok cs ∧ L.crun M cs = .trapped tc := by
  rw [Clif.linkEnvR_some hpf] at hG0
  cases hG0
  simp only at ht
  cases hinit : Clif.initState L.P n vals cm with
  | trap c' => exact absurd hinit (linkInitState_ne_trap _ _ _ _ _)
  | stuck m' => rw [hinit] at ht; cases ht
  | ok cs => rw [hinit] at ht; exact ⟨cs, rfl, ht⟩

/-- **The trapping callees' contract of an activation of `g` at depth `M`** under its
environment with the uncovered callee traps made stuck (those outside `covQ Dn`, `Dn` the run
premise `D` one level down): the base's for the externs outside `P` (`BaseTrapsOk.xt`), and for a
function of `P` the linked machine's call does not return (`progX_noneG`, from the trap
statement one level down). -/
theorem xTrapsOkG (hL : L.Ok) [hR : L.CrunOk] (hB : L.BaseTrapsOk)
    {D : Nat → Clif.Function → Clif.State → Prop} {Dn : Clif.Function → Clif.State → Prop}
    {M : Nat} (hDn : ∀ {h : Clif.Function} {cs : Clif.State}, Dn h cs → 0 < M → D (M - 1) h cs)
    (ih : 0 < M → L.ThmTG D κ (M - 1)) {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {c : BitVec 64} :
    XTrapsOk (cutEnv (L.envOf M g c) (L.covQ Dn)) (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c) (L.X κ M g F) := by
  refine ⟨fun ext hin G' sl cm w d uses args vals tc hG' hd hargs hmr htr => ?_,
    fun sig hsig n G' sl cm w u args vals tc hG' hsg hu hargsS hmr htr hty => ?_⟩
  · obtain ⟨G, hG, rfl⟩ := cutEnv_extern hG'
    obtain ⟨htrG, hQ⟩ := cutO_trapped htr
    cases hpf : L.P.func? ext.name with
    | none =>
      have hb : L.base.extern ext.name = some G := by
        simpa [envOf, hpf, Clif.linkEnvR_none hpf] using hG
      have hx := (hB.xt g hg F (L.A g).af.slotBase
        (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c).1 ext
        (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) G sl cm w d uses args vals tc hb hd hargs hmr htrG
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, -, rfl⟩
      · rw [L.X_base hpf _ _ F]; exact hx
      · rw [L.X_none (by
          show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = none
          rw [lo64_ofX]; exact (L.find_sym hL ext.name).2 hpf)]
        exact hx
    | some h =>
      obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
      have hsig := hL.declSig g hg ext hin h hpf
      obtain ⟨hdecl, G0, hG0, hGt⟩ := L.envOf_prog hG hpf
      obtain ⟨hpl, ht0⟩ := hGt _ _ _ htrG
      obtain ⟨cs, hinit, hret⟩ := L.linkEnvR_trap hpf hG0 ht0
      have hTD : 0 < M → D (M - 1) h cs := fun hM => hDn (hQ h cs hpf hinit) hM
      rw [hsig] at hargs
      have hsav := L.stackArgsAvoid_decl hL hg hin hpf hinit hmr
      rw [← hname] at hinit
      have hnone := L.progX_noneG (κ := κ) hL ih hh ⟨g, hg, .inr (.inl ⟨ext, hin, hpf⟩)⟩ himgF hargs
        hsav hmr hpl hinit hret hTD
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, -, rfl⟩
      · rw [L.X_prog hpf]; exact hnone
      · have hs : symCallee L.Xb L.P (lo64 (ofX ((L.X κ M g F).sym ext.name 0))) = some h := by
          show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = some h
          rw [lo64_ofX]; exact (L.find_sym hL ext.name).1 h hpf
        rw [L.X_ind hs]
        split
        · exact hnone
        · rfl
  · obtain ⟨G, hG, rfl⟩ := cutEnv_extern hG'
    obtain ⟨htrG, hQ⟩ := cutO_trapped htr
    cases hpf : L.P.func? n with
    | none =>
      have hs : symCallee L.Xb L.P (lo64 u) = none := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = none
        rw [hu]; exact (L.find_sym hL n).2 hpf
      have hb : L.base.extern n = some G := by
        simpa [envOf, hpf, Clif.linkEnvR_none hpf] using hG
      have hx := (hB.xt g hg F (L.A g).af.slotBase
        (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c).2 sig hsig n G sl cm w u args vals tc
        hb (fun _ h => nomatch h) hu hargsS hmr htrG hty
      rw [L.X_none hs]; exact hx
    | some h =>
      obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
      subst hname
      obtain ⟨hdecl, G0, hG0, hGt⟩ := L.envOf_prog hG hpf
      obtain ⟨hpl, ht0⟩ := hGt _ _ _ htrG
      obtain ⟨cs, hinit, hret⟩ := L.linkEnvR_trap hpf hG0 ht0
      have hTD : 0 < M → D (M - 1) h cs := fun hM => hDn (hQ h cs hpf hinit) hM
      have hnf : ¬ Clif.IndFree g := fun hif => by
        rw [indSigs_nil_of_indFree hif] at hsig; cases hsig
      have hdeclS := hL.indSig g hg hnf
      have hs : symCallee L.Xb L.P (lo64 u) = some h := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = some h
        rw [hu]; exact (L.find_sym hL h.name).1 h hpf
      have hce := clifEntry_initState (f := h) hpf hinit
      have hvl : vals.length = h.sig.params.length := by
        have := congrArg List.length hce.sig
        simpa using this
      have hm : IndSigMatch sig h :=
        hsg h.sig (by simp only [cutEnv, envOf, Clif.linkEnvR_sigOf, hpf, Option.map_some])
      obtain ⟨⟨bytes, hb, hb8⟩, -⟩ := hdeclS h hh hdecl (.inl ⟨sig, hsig, hm⟩)
      have hall : AllHold vals args :=
        (argsAt_iff_of_regs (hm.paramBytes.trans hb) hb8 hargsS.1).mp hargsS
      have hargs : ArgsAt h.sig vals args w := (argsAt_iff_of_regs hb hb8 hvl).mpr hall
      have hsav : StackArgsAvoid F h.sig vals w := by
        intro off v hm
        obtain ⟨r, hr⟩ := (locsOf_small hb hb8).2 _ (List.of_mem_zip hm).1
        cases hr
      have hnone := L.progX_noneG (κ := κ) hL ih hh ⟨g, hg, .inr (.inr ⟨hh, hdecl⟩)⟩ himgF hargs
        hsav hmr hpl hinit hret hTD
      rw [L.X_ind hs]
      split
      · exact hnone
      · rfl

/-- `xTrapsOkG` for the run premise `TrapsD`. -/
theorem xTrapsOk (hL : L.Ok) [hR : L.CrunOk] (hB : L.BaseTrapsOk) {M : Nat}
    (ih : 0 < M → L.ThmT κ (M - 1)) {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {c : BitVec 64} :
    XTrapsOk (cutEnv (L.envOf M g c) (L.covQ (L.TrapsDn M))) (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c) (L.X κ M g F) :=
  L.xTrapsOkG (D := L.TrapsD) hL hB (fun {h cs} hD hM => by
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    exact hD) ih hg himgF

end LinkSys

namespace LinkSys

variable (L : LinkSys)

/-! ## The activation's environment with the uncovered callee traps made stuck -/

/-- A step of an activation of `g` under `envOf` with some extern outcomes stuck that is not
stuck is its step under `linkEnvR`. -/
theorem step_cut_link (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} {Q : String → List Clif.Val → Clif.Mem → Prop} {s : Clif.State}
    (hJ : L.ActInv g c s) {r : Clif.StepResult}
    (hs : Clif.step (cutEnv (L.envOf M g c) Q) L.P.bare s = r) (hr : ∀ m, r ≠ .stuck m) :
    Clif.step (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare s = r := by
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hL.free f hg
  exact L.step_envOf_link hL hg hJ (step_of_restrictS (cutEnv_restrictsS _ Q) hPf hJ.1.1 hs hr) hr

theorem reach_cut (hL : L.Ok) [L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} {Q : String → List Clif.Val → Clif.Mem → Prop} {cs s : Clif.State}
    (hr : Reach (cutEnv (L.envOf M g c) Q) L.P.bare cs s) (hJ : L.ActInv g c cs) :
    Reach (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs s ∧ L.ActInv g c s := by
  induction hr with
  | refl => exact ⟨.refl _, hJ⟩
  | step hs _ ih =>
    have hs' := L.step_cut_link hL hg hJ hs (fun _ h => nomatch h)
    obtain ⟨h1, h2⟩ := ih (L.actInv_step hL hg hJ hs')
    exact ⟨.step hs' h1, h2⟩

/-- **The run premise of `P.bare` under `linkEnvR` is the one under `envOf` with some extern
outcomes stuck** (`trapsExplicit_envOf` for `TrapsExplicitC`). -/
theorem trapsExplicitC_cut (hL : L.Ok) [L.CrunOk] {M : Nat} {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {c : BitVec 64} {Q : String → List Clif.Val → Clif.Mem → Prop}
    {cs : Clif.State} (hJ : L.ActInv g c cs)
    (h : TrapsExplicitC (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs) :
    TrapsExplicitC (cutEnv (L.envOf M g c) Q) L.P.bare cs where
  stmt := fun s c st rest hr hs hb => by
    obtain ⟨hr', hJs⟩ := L.reach_cut hL hg hr hJ
    exact h.stmt s c st rest hr' (L.step_cut_link hL hg hJs hs (fun _ h => nomatch h)) hb
  tryCall := fun s c fn args et hr hs hb ht => by
    obtain ⟨hr', hJs⟩ := L.reach_cut hL hg hr hJ
    exact h.tryCall s c fn args et hr' (L.step_cut_link hL hg hJs hs (fun _ h => nomatch h)) hb ht
  tryCallInd := fun s c callee args et hr hs hb ht => by
    obtain ⟨hr', hJs⟩ := L.reach_cut hL hg hr hJ
    exact h.tryCallInd s c callee args et hr'
      (L.step_cut_link hL hg hJs hs (fun _ h => nomatch h)) hb ht
  indirect := fun s st rest sig callee args hr hb hi hst =>
    h.indirect s st rest sig callee args (L.reach_cut hL hg hr hJ).1 hb hi hst
  tryIndirect := fun s callee args et hr hb ht hB =>
    h.tryIndirect s callee args et (L.reach_cut hL hg hr hJ).1 hb ht hB

/-- **The run of `g`'s activation under `envOf` with the uncovered callee traps stuck is its run
under `envR` with them stuck** (`runLoop_envOf` with the cut). -/
theorem runLoop_cut (hL : L.Ok) [L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} {Q : String → List Clif.Val → Clif.Mem → Prop} :
    ∀ (n : Nat) (s : Clif.State), L.ActInv g c s →
      Clif.runLoop (cutEnv (L.envOf M g c) Q) L.P.bare n s =
        Clif.runLoop (cutEnv (L.envR M g) Q) L.P.bare n s
  | 0, _, _ => rfl
  | n + 1, s, hJ => by
    have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
      simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; exact hL.free f hg
    have he : Clif.step (cutEnv (L.envOf M g c) Q) L.P.bare s =
        Clif.step (cutEnv (L.envR M g) Q) L.P.bare s :=
      step_congrE (E₁ := cutEnv (L.envOf M g c) Q) (E₂ := cutEnv (L.envR M g) Q) rfl rfl hPf hJ.1.1 fun t nm vals htm => by
        rw [cutEnv_map, cutEnv_map, L.envOf_envR (M := M) (g := g) (n := nm) vals (by rw [htm]; exact hJ.2.2)]
    rw [Clif.runLoop_succ', Clif.runLoop_succ', he]
    cases hs : Clif.step (cutEnv (L.envR M g) Q) L.P.bare s with
    | next s1 =>
      have hs' := step_of_restrictS (cutEnv_restrictsS _ Q) hPf hJ.1.1 hs (fun _ h => nomatch h)
      have hs'' := step_of_restrict L.envR_restricts hPf hJ.1.1 hs' (fun _ h => nomatch h)
      exact runLoop_cut hL hg n s1 (L.actInv_step hL hg hJ hs'')
    | _ => rfl

end LinkSys

end E2E
