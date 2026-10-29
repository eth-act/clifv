module

public import FV.E2E.LinkClif
public import FV.E2E.UnwindStatement

@[expose] public section

/-!
# Traps inside callees, at the CLIF level (S9a, #33)

`TrapsExplicit` (the per-function theorem's run premise) excludes every trap that is not an
explicitly trapping instruction of the entered function: in particular a `call`/`call_indirect`
statement whose callee traps (a trapping `__*ti3` helper, a panic, a callee of the linked
program). This file prepares the per-function theorem that covers them
(`E2E.backend_correct_final_cleanup_trapcall`, `FV/E2E/DeadCleanupTrapCall.lean`):

* `TrapsExplicitC`: `TrapsExplicit` whose statement clause also allows a `call`/`call_indirect`
  statement to trap (its callee trapped); `TrapsExplicit.toC`.
* The **proof device** `trapEnv env c`: the environment with unwinding in which an extern of
  `env` that traps with the code `c` unwinds instead (with `trapExn`). Its run with unwinding
  (`Clif.runLoopX`) ends with an exception exactly where the run of `Clif.run` traps with `c`
  inside a callee, and traps where it traps explicitly (`runLoopX_trapEnv`); its premise
  `TrapsExplicitX` follows from `TrapsExplicitC` (`trapsExplicitX_trapEnv`). The unwinding
  chain of S10 (`IselSimU`, `PrepareCorrectU`) then carries the callee trap to the VCode call
  that ends the activation.
* `TrapRel`: a step of `trapEnv`'s `Clif.run` environment is the step of `env`, except where
  `env`'s step traps with `c` inside a callee (then it is `stuck`): `step_trapRel`;
  `raiseAt_of_trapRel` (that step raises in the run with unwinding).

The statements are for the activation of a function `f` without `try_call`/`try_call_indirect`
terminators and without `return_call`, in a program without functions (`p.funcs = []`, the
per-function theorems' `p.bare`): the calls of `f` are extern calls.
-/

namespace E2E

open Clif Backend.Proof Backend.Proof.Driver

/-! ## The proof device -/

/-- The exception a callee trap becomes in `trapEnv` (`ExnRel trapExn 0`). -/
def trapExn : Exn := ⟨fun _ => true, [⟨.i64, 0⟩, ⟨.i64, 0⟩]⟩

theorem exnRel_trapExn : ExnRel trapExn 0 := ⟨rfl, rfl, rfl⟩

/-- An extern's outcome in `trapEnv`: a trap with code `c` unwinds with `trapExn` (memory as at
the call), every other outcome is unchanged. -/
def trapOut (c : TrapCode) (o : Outcome) (mem : Mem) : XOutcome :=
  match o with
  | .returned v m => .returned v m
  | .trapped c' => if c' = c then .unwound trapExn mem else .trapped c'
  | .stuck m => .stuck m
  | .outOfFuel => .outOfFuel

/-- **The environment with unwinding of the callee traps with code `c`**: the externs of `env`,
a trap with `c` unwinding instead (`trapOut`). -/
def trapEnv (env : Env) (c : TrapCode) : XEnv where
  extern n := (env.extern n).map fun g vals mem => trapOut c (g vals mem) mem
  names := env.names
  sigOf := env.sigOf

section
variable {env : Env} {c : TrapCode} {p : Program}

theorem trapEnv_toEnv_extern (env : Env) (c : TrapCode) (n : String) :
    (trapEnv env c).toEnv.extern n =
      (env.extern n).map fun g vals mem => (trapOut c (g vals mem) mem).toOutcome := by
  simp only [trapEnv, XEnv.toEnv, Option.map_map]
  rfl

theorem trapOut_ne (mem : Mem) {o : Outcome} (h : o ≠ .trapped c) : (trapOut c o mem).toOutcome = o := by
  cases o with
  | trapped c' =>
    have hc : c' ≠ c := fun e => h (by rw [e])
    simp [trapOut, hc, XOutcome.toOutcome]
  | _ => rfl

theorem trapOut_self (mem : Mem) : trapOut c (.trapped c) mem = .unwound trapExn mem := by
  simp [trapOut]

/-- A step of `trapEnv`'s environment is `env`'s (`r₂ = r₁`), or `env`'s traps with `c` where
`trapEnv`'s is `stuck`. -/
def TrapRel (c : TrapCode) (r₂ r₁ : StepResult) : Prop :=
  r₂ = r₁ ∨ (r₁ = .trapped c ∧ ∃ m, r₂ = .stuck m)

/-- `TrapRel` of `Res` results. -/
def ResTrapRel {α : Type} (c : TrapCode) (r₂ r₁ : Res α) : Prop :=
  r₂ = r₁ ∨ (r₁ = .trap c ∧ ∃ m, r₂ = .stuck m)

theorem TrapRel.ofRes {α : Type} (r : Res α) {k₂ k₁ : α → StepResult}
    (h : ∀ a, TrapRel c (k₂ a) (k₁ a)) : TrapRel c (StepResult.ofRes r k₂) (StepResult.ofRes r k₁) := by
  cases r with
  | ok a => exact h a
  | trap _ => exact .inl rfl
  | stuck _ => exact .inl rfl

theorem TrapRel.ofRes' {α : Type} {r₂ r₁ : Res α} (h : ResTrapRel c r₂ r₁) (k : α → StepResult) :
    TrapRel c (StepResult.ofRes r₂ k) (StepResult.ofRes r₁ k) := by
  rcases h with rfl | ⟨rfl, m, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨rfl, m, rfl⟩

theorem func?_nil (hp : p.funcs = []) (n : String) : p.func? n = none := by
  simp [Program.func?, hp]

theorem find?_nil (hp : p.funcs = []) (P : Function → Bool) : p.funcs.find? P = none := by
  simp [hp]

/-! ## One step -/

theorem callCont_trapRel (env : Env) (c : TrapCode) (hp : p.funcs = []) (s : State)
    (rest : List Stmt) (results : List ValueId) (ext : ExtFunc) (vals : List Val) :
    TrapRel c (Opt.callCont (trapEnv env c).toEnv p s rest results ext vals)
      (Opt.callCont env p s rest results ext vals) := by
  simp only [Opt.callCont, func?_nil hp, trapEnv_toEnv_extern]
  cases env.extern ext.name with
  | none => exact .inl rfl
  | some g =>
    simp only [Option.map]
    by_cases hg : g vals s.mem = .trapped c
    · rw [hg, trapOut_self]
      exact .inr ⟨rfl, _, rfl⟩
    · rw [trapOut_ne s.mem hg]
      exact .inl rfl

theorem tailCont_trapRel (env : Env) (c : TrapCode) (hp : p.funcs = []) (s : State)
    (ext : ExtFunc) (vals : List Val) :
    TrapRel c (Opt.tailCont (trapEnv env c).toEnv p s ext vals) (Opt.tailCont env p s ext vals) := by
  simp only [Opt.tailCont, func?_nil hp, trapEnv_toEnv_extern]
  cases env.extern ext.name with
  | none => exact .inl rfl
  | some g =>
    simp only [Option.map]
    by_cases hg : g vals s.mem = .trapped c
    · rw [hg, trapOut_self]
      exact .inr ⟨rfl, _, rfl⟩
    · rw [trapOut_ne s.mem hg]
      exact .inl rfl

theorem callExternAt_trapRel (env : Env) (c : TrapCode) (p : Program) (mem : Mem)
    (declared : Signature) (addr : Nat) (vals : List Val) :
    ResTrapRel c (callExternAt (trapEnv env c).toEnv p mem declared addr vals)
      (callExternAt env p mem declared addr vals) := by
  unfold callExternAt
  simp only [trapEnv_toEnv_extern]
  have hn : (trapEnv env c).toEnv.names = env.names := rfl
  have hs : (trapEnv env c).toEnv.sigOf = env.sigOf := rfl
  rw [hn, hs]
  cases (env.names ++ p.externNames).find? (fun n => mem.symbols n == some addr) with
  | none => exact .inl rfl
  | some name =>
    simp only [Res.ofOption_some, Res.ok_bind]
    cases env.extern name with
    | none => exact .inl rfl
    | some g =>
      simp only [Option.map, Res.ofOption_some, Res.ok_bind]
      cases Res.check ((env.sigOf name).all declared.abiMatch)
          s!"call_indirect: signature does not match %{name}" with
      | trap c' => exact .inl rfl
      | stuck m => exact .inl rfl
      | ok u =>
        simp only [Res.ok_bind]
        cases checkTys s!"arguments of call_indirect to %{name}" vals
            (AbiParam.tys declared.params) with
        | trap c' => exact .inl rfl
        | stuck m => exact .inl rfl
        | ok u' =>
          simp only [Res.ok_bind]
          by_cases hg : g vals mem = .trapped c
          · rw [hg, trapOut_self]
            exact .inr ⟨rfl, _, rfl⟩
          · rw [trapOut_ne mem hg]
            exact .inl rfl

theorem indCont_trapRel (env : Env) (c : TrapCode) (hp : p.funcs = []) (s : State)
    (rest : List Stmt) (results : List ValueId) (sig : Nat) (declared : Signature) (addr : Nat)
    (vals : List Val) :
    TrapRel c (indCont (trapEnv env c).toEnv p s rest results sig declared addr vals)
      (indCont env p s rest results sig declared addr vals) := by
  simp only [indCont, find?_nil hp]
  exact TrapRel.ofRes' (callExternAt_trapRel env c p s.mem declared addr vals) _

/-- **One step of `trapEnv`'s environment** (`TrapRel`). -/
theorem step_trapRel (env : Env) (c : TrapCode) (hp : p.funcs = []) (s : State) :
    TrapRel c (step (trapEnv env c).toEnv p s) (step env p s) := by
  rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [step_try _ _ s hb ht, step_try _ _ s hb ht]
    exact TrapRel.ofRes _ fun ⟨n, b, bc⟩ => TrapRel.ofRes _ fun ⟨ext, vals⟩ =>
      callCont_trapRel env c hp _ _ _ ext vals
  · rw [step_tryInd _ _ s hb ht, step_tryInd _ _ s hb ht]
    exact TrapRel.ofRes _ fun ⟨n, b, bc⟩ => TrapRel.ofRes _ fun ⟨d, a, v⟩ =>
      indCont_trapRel env c hp _ _ _ _ d a v
  · rw [step_ind _ _ s hb hi, step_ind _ _ s hb hi]
    exact TrapRel.ofRes _ fun ⟨d, a, v⟩ => indCont_trapRel env c hp _ _ _ _ d a v
  · rw [Opt.step_eq_lift _ _ s hci, Opt.step_eq_lift _ _ s hci]
    cases Opt.lstep s.frame s.mem with
    | next fr m => exact .inl rfl
    | call ext vals rs rest => exact callCont_trapRel env c hp _ _ _ ext vals
    | ret vals => exact .inl rfl
    | tail ext vals => exact tailCont_trapRel env c hp _ ext vals
    | trap c' => exact .inl rfl
    | stuck m => exact .inl rfl

/-! ## Where `trapEnv`'s step is `stuck`, the step with unwinding raises -/

theorem callCont_trap_inv {env : Env} (hp : p.funcs = []) {s : State} {rest : List Stmt}
    {results : List ValueId} {ext : ExtFunc} {vals : List Val}
    (h : Opt.callCont env p s rest results ext vals = .trapped c) :
    ∃ g, env.extern ext.name = some g ∧ g vals s.mem = .trapped c := by
  simp only [Opt.callCont, func?_nil hp] at h
  cases he : env.extern ext.name with
  | none => rw [he] at h; cases h
  | some g =>
    rw [he] at h
    refine ⟨g, rfl, ?_⟩
    simp only at h
    cases hg : g vals s.mem with
    | returned rv m =>
      rw [hg] at h
      simp only at h
      split at h
      · simp only [continueWith] at h
        split at h <;> cases h
      · cases h
    | trapped c' => rw [hg] at h; cases h; rfl
    | stuck m => rw [hg] at h; cases h
    | outOfFuel => rw [hg] at h; cases h

theorem returnValues_ne_trapped (s : State) (vals : List Val) (mem : Mem) :
    returnValues s vals mem ≠ .trapped c := by
  unfold returnValues
  cases hc : checkTys s!"return values of %{s.frame.func.name}" vals
      (AbiParam.tys s.frame.func.sig.returns) with
  | ok u =>
    simp only [StepResult.ofRes]
    split
    · simp
    · split <;> simp
  | trap c' =>
    simp only [checkTys, Res.check] at hc
    split at hc <;> cases hc
  | stuck m => simp [StepResult.ofRes]

theorem tailCont_trap_inv {env : Env} (hp : p.funcs = []) {s : State} {ext : ExtFunc}
    {vals : List Val} (h : Opt.tailCont env p s ext vals = .trapped c) :
    ∃ g, env.extern ext.name = some g ∧ g vals s.mem = .trapped c := by
  simp only [Opt.tailCont, func?_nil hp] at h
  cases he : env.extern ext.name with
  | none => rw [he] at h; cases h
  | some g =>
    rw [he] at h
    refine ⟨g, rfl, ?_⟩
    simp only at h
    cases hg : g vals s.mem with
    | returned rv m =>
      rw [hg] at h
      exact absurd h (returnValues_ne_trapped s rv m)
    | trapped c' => rw [hg] at h; cases h; rfl
    | stuck m => rw [hg] at h; cases h
    | outOfFuel => rw [hg] at h; cases h

theorem callExternAt_trap_inv {env : Env} {mem : Mem} {declared : Signature} {addr : Nat}
    {vals : List Val} (h : callExternAt env p mem declared addr vals = .trap c) :
    ∃ name g, (env.names ++ p.externNames).find? (fun n => mem.symbols n == some addr) =
        some name ∧ env.extern name = some g ∧ (env.sigOf name).all declared.abiMatch = true ∧
      vals.map (·.ty) = AbiParam.tys declared.params ∧ g vals mem = .trapped c := by
  unfold callExternAt at h
  cases hf : (env.names ++ p.externNames).find? (fun n => mem.symbols n == some addr) with
  | none => rw [hf] at h; cases h
  | some name =>
    rw [hf] at h
    simp only [Res.ofOption_some, Res.ok_bind] at h
    cases he : env.extern name with
    | none => rw [he] at h; cases h
    | some g =>
      rw [he] at h
      simp only [Res.ofOption_some, Res.ok_bind] at h
      cases hs : (env.sigOf name).all declared.abiMatch with
      | false => rw [hs] at h; cases h
      | true =>
        rw [hs] at h
        simp only [Res.check_true, Res.ok_bind, checkTys] at h
        cases ht : (vals.map (·.ty) == AbiParam.tys declared.params) with
        | false => rw [ht] at h; cases h
        | true =>
          rw [ht] at h
          simp only [Res.check_true, Res.ok_bind] at h
          refine ⟨name, g, rfl, he, hs, beq_iff_eq.mp ht, ?_⟩
          cases hg : g vals mem with
          | returned rv m =>
            rw [hg] at h
            simp only at h
            split at h <;> cases h
          | trapped c' => rw [hg] at h; cases h; rfl
          | stuck m => rw [hg] at h; cases h
          | outOfFuel => rw [hg] at h; cases h

theorem indCont_trap_inv {env : Env} (hp : p.funcs = []) {s : State} {rest : List Stmt}
    {results : List ValueId} {sig : Nat} {declared : Signature} {addr : Nat} {vals : List Val}
    (h : indCont env p s rest results sig declared addr vals = .trapped c) :
    callExternAt env p s.mem declared addr vals = .trap c := by
  simp only [indCont, find?_nil hp] at h
  cases he : callExternAt env p s.mem declared addr vals with
  | ok r =>
    rw [he] at h
    simp only [StepResult.ofRes, continueWith] at h
    split at h <;> cases h
  | trap c' => rw [he] at h; cases h; rfl
  | stuck m => rw [he] at h; cases h

theorem externAtRaise_of_trap {env : Env} {mem : Mem} {declared : Signature} {addr : Nat}
    {vals : List Val} (h : callExternAt env p mem declared addr vals = .trap c) :
    externAtRaise (trapEnv env c) p mem declared addr vals = some (trapExn, mem) := by
  obtain ⟨name, g, hf, he, hs, ht, hg⟩ := callExternAt_trap_inv h
  unfold externAtRaise
  have hn : (trapEnv env c).names = env.names := rfl
  rw [hn, hf]
  simp only [trapEnv, he, Option.map, hs, ht, beq_self_eq_true, Bool.and_self, ite_true, hg,
    trapOut_self]

theorem callRaise_of_trap {env : Env} (hp : p.funcs = []) {mem : Mem} {fr : Frame} {fn : FnRef}
    {args : List ValueId} {ext : ExtFunc} {vals : List Val}
    (ha : Opt.callArgs fr fn args = .ok (ext, vals)) {g : List Val → Mem → Outcome}
    (he : env.extern ext.name = some g) (hg : g vals mem = .trapped c) :
    callRaise (trapEnv env c) p mem fr fn args = some (trapExn, mem) := by
  have hpre : (do
      let ext ← Res.ofOption s!"unknown function reference fn{fn}" (fr.func.extern? fn)
      let vals ← fr.getMany args
      checkTys s!"arguments of call to %{ext.name}" vals (AbiParam.tys ext.sig.params)
      pure (ext, vals) : Res (ExtFunc × List Val)) = .ok (ext, vals) := ha
  unfold callRaise
  rw [hpre]
  simp only [func?_nil hp, trapEnv, he, Option.map, hg, trapOut_self]

theorem returnCallRaise_of_trap {env : Env} (hp : p.funcs = []) {mem : Mem} {fr : Frame}
    {fn : FnRef} {args : List ValueId} {ext : ExtFunc} {vals : List Val}
    (ha : Opt.tailArgs fr fn args = .ok (ext, vals)) {g : List Val → Mem → Outcome}
    (he : env.extern ext.name = some g) (hg : g vals mem = .trapped c) :
    returnCallRaise (trapEnv env c) p mem fr fn args = some (trapExn, mem) := by
  have hpre : (do
      let ext ← Res.ofOption s!"unknown function reference fn{fn}" (fr.func.extern? fn)
      let vals ← fr.getMany args
      checkTys s!"arguments of return_call to %{ext.name}" vals (AbiParam.tys ext.sig.params)
      Res.check (AbiParam.tys ext.sig.returns == AbiParam.tys fr.func.sig.returns)
        s!"return_call to %{ext.name}: return types differ from the caller's"
      pure (ext, vals) : Res (ExtFunc × List Val)) = .ok (ext, vals) := ha
  unfold returnCallRaise
  rw [hpre]
  simp only [func?_nil hp, trapEnv, he, Option.map, hg, trapOut_self]

theorem callIndRaise_of_trap {env : Env} (hp : p.funcs = []) {mem : Mem} {fr : Frame} {sig : Nat}
    {callee : ValueId} {args : List ValueId} {declared : Signature} {addr : Nat} {vals : List Val}
    (ha : indPre fr sig callee args = .ok (declared, addr, vals))
    (h : callExternAt env p mem declared addr vals = .trap c) :
    callIndRaise (trapEnv env c) p mem fr sig callee args = some (trapExn, mem) := by
  have hpre : (do
      let declared ← Res.ofOption s!"unknown signature sig{sig}" (fr.func.sigDecls.lookup sig)
      let cv ← fr.get callee
      let cv64 ← Res.ofOption "call_indirect: callee is not i64" (cv.as? .i64)
      let vals ← fr.getMany args
      pure (declared, cv64.toNat, vals) : Res (Signature × Nat × List Val)) =
      .ok (declared, addr, vals) := ha
  unfold callIndRaise
  rw [hpre]
  simp only [find?_nil hp]
  exact externAtRaise_of_trap h

theorem ofRes_trapped_inv {α : Type} {r : Res α} {k : α → StepResult}
    (h : StepResult.ofRes r k = .trapped c) : r = .trap c ∨ ∃ a, r = .ok a ∧ k a = .trapped c := by
  cases r with
  | ok a => exact .inr ⟨a, rfl, h⟩
  | trap c' => cases h; exact .inl rfl
  | stuck m => cases h

theorem ofRes_stuck_inv {α : Type} {r : Res α} {k : α → StepResult} {m : String}
    (h : StepResult.ofRes r k = .stuck m) : (∃ m', r = .stuck m') ∨ ∃ a, r = .ok a ∧ k a = .stuck m := by
  cases r with
  | ok a => exact .inr ⟨a, rfl, h⟩
  | trap c' => cases h
  | stuck m' => exact .inl ⟨m', rfl⟩

/-- **Where `env`'s step traps with `c` and `trapEnv`'s is `stuck`, the step of the run with
unwinding raises** (the statement is a call whose extern traps with `c`), for a state not at a
`try_call`/`try_call_indirect` terminator. -/
theorem raiseAt_of_trapRel (env : Env) (c : TrapCode) (hp : p.funcs = []) {s : State}
    (hnt : s.frame.body = [] → s.frame.term.isTry = false)
    (h1 : step env p s = .trapped c) {m : String} (h2 : step (trapEnv env c).toEnv p s = .stuck m) :
    raiseAt? (trapEnv env c) p s = some (trapExn, s.mem) := by
  rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · have := hnt hb; rw [ht] at this; cases this
  · have := hnt hb; rw [ht] at this; cases this
  · rw [step_ind _ _ s hb hi] at h1 h2
    rcases ofRes_trapped_inv h1 with hpre | ⟨⟨d, a, v⟩, hpre, hk⟩
    · rw [hpre] at h2; cases h2
    · have hx := indCont_trap_inv hp hk
      simp only [raiseAt?, hb, hi]
      exact callIndRaise_of_trap hp hpre hx
  · rw [Opt.step_eq_lift _ _ s hci] at h1 h2
    cases hl : Opt.lstep s.frame s.mem with
    | next fr m' => rw [hl] at h1; cases h1
    | call ext vals rs rest =>
      rw [hl] at h1
      obtain ⟨g, he, hg⟩ := callCont_trap_inv hp h1
      obtain ⟨st, fn, args, hb, hi, -, ha⟩ := Opt.lstep_call_inv hl
      simp only [raiseAt?, hb, hi]
      exact callRaise_of_trap hp ha he hg
    | ret vals =>
      rw [hl] at h1 h2
      simp only [Opt.LRes.lift] at h1 h2
      rw [h1] at h2; cases h2
    | tail ext vals =>
      rw [hl] at h1
      obtain ⟨g, he, hg⟩ := tailCont_trap_inv hp h1
      have hb := Opt.lstep_tail_inv hl
      have hl' := hl
      rw [Opt.lstep_term hb] at hl'
      cases ht : s.frame.term with
      | returnCall fn args =>
        rw [ht] at hl'
        simp only [Opt.LRes.ofRes] at hl'
        cases ha : Opt.tailArgs s.frame fn args with
        | ok r =>
          rw [ha] at hl'
          cases hl'
          simp only [raiseAt?, hb, ht]
          exact returnCallRaise_of_trap hp ha he hg
        | trap c' => rw [ha] at hl'; cases hl'
        | stuck m' => rw [ha] at hl'; cases hl'
      | jump d =>
        rw [ht] at hl'; simp only [Opt.LRes.ofRes] at hl'; split at hl' <;> cases hl'
      | brif x t e =>
        rw [ht] at hl'; simp only [Opt.LRes.ofRes] at hl'
        split at hl' <;> (try cases hl')
        split at hl' <;> cases hl'
      | brTable x d tb =>
        rw [ht] at hl'; simp only [Opt.LRes.ofRes] at hl'
        split at hl' <;> (try cases hl')
        split at hl' <;> cases hl'
      | ret xs => rw [ht] at hl'; simp only [Opt.LRes.ofRes] at hl'; split at hl' <;> cases hl'
      | trap c' => rw [ht] at hl'; cases hl'
      | tryCall _ _ _ => rw [ht] at hl'; cases hl'
      | tryCallIndirect _ _ _ => rw [ht] at hl'; cases hl'
    | trap c' =>
      rw [hl] at h1 h2
      simp only [Opt.LRes.lift] at h1 h2
      rw [h1] at h2; cases h2
    | stuck m' =>
      rw [hl] at h1
      simp only [Opt.LRes.lift] at h1
      cases h1

end

end E2E
