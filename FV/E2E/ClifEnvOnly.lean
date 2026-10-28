import FV.Backend.Proof.LowerContract

/-!
# An environment answering one step's extern invocation only (SEM1, `docs/plans/uninit.md` §5.9)

The CLIF → counted-VCode simulation needs the callee contract of call `n` only for the actual
call of the run (with the slot-byte oracle, the contract of a callee entered with other
arguments or another memory is false). `Clif.step` invokes at most one extern, at the state's
memory, with the name and argument values the state determines. So the environment can be
restricted to that invocation without changing the step:

* `Clif.Env.only env A`: `env` whose externs answer only invocations `A name vals mem` (the same
  names are defined; `stuck` otherwise);
* `Clif.Invoked env p s`: the invocation of a step from `s` (`call`, `call_indirect` through
  `callExternAt`, `try_call`, `try_call_indirect`, `return_call`), at `s.mem`;
* `Clif.step_only`: `step (env.only A) p s = step env p s` when `A` contains `Invoked env p s`.
-/

namespace Clif

open Backend.Proof.Driver

open Classical in
/-- The extern `g` of `n` answering only the invocations `A n vals mem`. -/
noncomputable def onlyFn (A : String → List Val → Mem → Prop) (n : String)
    (g : List Val → Mem → Outcome) (vals : List Val) (m : Mem) : Outcome :=
  if A n vals m then g vals m else .stuck "Env.only"

/-- **`env` answering only the invocations `A name vals mem`** (`stuck` otherwise; the names,
signatures and the defined externs are `env`'s). -/
noncomputable def Env.only (env : Env) (A : String → List Val → Mem → Prop) : Env :=
  { env with extern := fun n => (env.extern n).map (onlyFn A n) }

@[simp] theorem Env.only_names (env : Env) (A : String → List Val → Mem → Prop) :
    (env.only A).names = env.names := rfl

@[simp] theorem Env.only_sigOf (env : Env) (A : String → List Val → Mem → Prop) :
    (env.only A).sigOf = env.sigOf := rfl

theorem Env.only_extern (env : Env) (A : String → List Val → Mem → Prop) (n : String) :
    (env.only A).extern n = (env.extern n).map (onlyFn A n) := rfl

theorem onlyFn_of {A : String → List Val → Mem → Prop} {n : String}
    {g : List Val → Mem → Outcome} {vals : List Val} {m : Mem} (h : A n vals m) :
    onlyFn A n g vals m = g vals m := by
  simp [onlyFn, h]

theorem onlyFn_of_not {A : String → List Val → Mem → Prop} {n : String}
    {g : List Val → Mem → Outcome} {vals : List Val} {m : Mem} (h : ¬ A n vals m) :
    onlyFn A n g vals m = .stuck "Env.only" := by
  simp [onlyFn, h]

/-- **The answered externs of `env.only A` are `env`'s** (for the callee contracts). -/
theorem Env.only_extern_eq {env : Env} {A : String → List Val → Mem → Prop} {n : String}
    {g' : List Val → Mem → Outcome} (h : (env.only A).extern n = some g') :
    ∃ g, env.extern n = some g ∧ g' = onlyFn A n g := by
  rw [Env.only_extern] at h
  cases he : env.extern n with
  | none => rw [he] at h; cases h
  | some g => rw [he] at h; cases h; exact ⟨g, rfl, rfl⟩

theorem Frame.getMany_regs {fr fr' : Frame} (h : fr.regs = fr'.regs) :
    ∀ xs, fr.getMany xs = fr'.getMany xs
  | [] => rfl
  | x :: xs => by simp only [Frame.getMany, Frame.get, h, Frame.getMany_regs h xs]

/-- The extern invocation of a direct call `fn(args)` from `s`. -/
def CallInv (s : State) (fn : FnRef) (args : List ValueId) (n : String) (vals : List Val) : Prop :=
  ∃ e, s.frame.func.extern? fn = some e ∧ e.name = n ∧ s.frame.getMany args = .ok vals

/-- The extern invocation of an indirect call `callee(args)` from `s` (`callExternAt`'s name). -/
def IndInv (env : Env) (p : Program) (s : State) (callee : ValueId) (args : List ValueId)
    (n : String) (vals : List Val) : Prop :=
  ∃ cv, s.frame.get callee = .ok cv ∧ s.frame.getMany args = .ok vals ∧
    (env.names ++ p.externNames).find? (fun m => s.mem.symbols m == some cv.toNat) = some n

/-- **The extern invocation of a step from `s`**: at `s.mem`, with the name and argument values
of the statement or terminator `s` executes. -/
def Invoked (env : Env) (p : Program) (s : State) (n : String) (vals : List Val) (m : Mem) :
    Prop :=
  m = s.mem ∧
  match s.frame.body with
  | st :: _ =>
    match st.inst with
    | .call fn args => CallInv s fn args n vals
    | .callIndirect _ callee args => IndInv env p s callee args n vals
    | _ => False
  | [] =>
    match s.frame.term with
    | .tryCall fn args _ => CallInv s fn args n vals
    | .returnCall fn args => CallInv s fn args n vals
    | .tryCallIndirect callee args _ => IndInv env p s callee args n vals
    | _ => False

theorem stepCall_only {env : Env} {A : String → List Val → Mem → Prop} {p : Program} {s : State}
    {rest : List Stmt} {results : List ValueId} {fn : FnRef} {args : List ValueId}
    (hA : ∀ n vals, CallInv s fn args n vals → A n vals s.mem) :
    stepCall (env.only A) p s rest results fn args = stepCall env p s rest results fn args := by
  simp only [stepCall]
  apply ofRes_congr
  intro ⟨ext, vals⟩ hX
  obtain ⟨e, he, hX⟩ := resBind_ok hX
  obtain ⟨vs, hvs, hX⟩ := resBind_ok hX
  obtain ⟨-, -, hX⟩ := resBind_ok hX
  cases hX
  have he' : s.frame.func.extern? fn = some ext := by
    cases hx : s.frame.func.extern? fn with
    | none => rw [hx] at he; cases he
    | some e' => rw [hx] at he; cases he; rfl
  have hA' := hA ext.name vals ⟨ext, he', rfl, hvs⟩
  simp only
  cases p.func? ext.name with
  | some _ => rfl
  | none =>
    cases hg : env.extern ext.name with
    | none => simp [Env.only_extern, hg]
    | some g => simp [Env.only_extern, hg, onlyFn_of hA']

theorem callExternAt_only {env : Env} {A : String → List Val → Mem → Prop} {p : Program}
    {mem : Mem} {declared : Signature} {addr : Nat} {vals : List Val}
    (hA : ∀ n, (env.names ++ p.externNames).find? (fun m => mem.symbols m == some addr) = some n →
      A n vals mem) :
    callExternAt (env.only A) p mem declared addr vals = callExternAt env p mem declared addr vals := by
  simp only [callExternAt, Env.only_names, Env.only_sigOf]
  cases hf : (env.names ++ p.externNames).find? (fun m => mem.symbols m == some addr) with
  | none => rfl
  | some n =>
    simp only [Res.ofOption_some, Res.ok_bind]
    cases hg : env.extern n with
    | none => simp [Env.only_extern, hg]
    | some g => simp [Env.only_extern, hg, onlyFn_of (hA n hf)]

theorem stepCallIndirect_only {env : Env} {A : String → List Val → Mem → Prop} {p : Program}
    {s : State} {rest : List Stmt} {results : List ValueId} {sig : Nat} {callee : ValueId}
    {args : List ValueId}
    (hA : ∀ n vals, IndInv env p s callee args n vals → A n vals s.mem) :
    stepCallIndirect (env.only A) p s rest results sig callee args =
      stepCallIndirect env p s rest results sig callee args := by
  simp only [stepCallIndirect]
  apply ofRes_congr
  intro ⟨declared, addr, vals⟩ hX
  obtain ⟨d, -, hX⟩ := resBind_ok hX
  obtain ⟨cv, hcv, hX⟩ := resBind_ok hX
  cases hc : cv.as? .i64 with
  | none => simp [hc] at hX
  | some y =>
    have hcy := val_as_i64 hc
    simp only [hc, Res.ofOption_some, Res.ok_bind] at hX
    obtain ⟨vs, hvs, hX⟩ := resBind_ok hX
    cases hX
    simp only
    cases p.funcs.find? fun f => (s.mem.symbols f.name) == some y.toNat with
    | some _ => rfl
    | none =>
      rw [callExternAt_only (A := A) fun n hn => hA n vals ⟨cv, hcv, hvs, by
        rw [hcy]; exact hn⟩]

/-- **Restricting the environment to the step's invocation does not change the step.** -/
theorem step_only {env : Env} {A : String → List Val → Mem → Prop} {p : Program} {s : State}
    (hA : ∀ n vals m, Invoked env p s n vals m → A n vals m) :
    step (env.only A) p s = step env p s := by
  cases hb : s.frame.body with
  | cons st rest =>
    cases hi : st.inst with
    | call fn args =>
      have h1 : ∀ e, step e p s = stepCall e p s rest st.results fn args := fun e => by
        simp [step, hb, hi]
      rw [h1, h1]
      exact stepCall_only fun n vals h => hA n vals s.mem ⟨rfl, by simp only [hb, hi]; exact h⟩
    | callIndirect sig callee args =>
      have h1 : ∀ e, step e p s = stepCallIndirect e p s rest st.results sig callee args :=
        fun e => by simp [step, hb, hi]
      rw [h1, h1]
      exact stepCallIndirect_only fun n vals h =>
        hA n vals s.mem ⟨rfl, by simp only [hb, hi]; exact h⟩
    | _ => simp [step, hb, hi]
  | nil =>
    have h0 : ∀ e, step e p s = stepTerm e p s s.frame.term := fun e => by simp [step, hb]
    rw [h0, h0]
    cases ht : s.frame.term with
    | tryCall fn args et =>
      simp only [stepTerm, stepTryCall]
      apply ofRes_congr
      intro _ _
      exact stepCall_only fun n vals h => hA n vals s.mem ⟨rfl, by
        simp only [hb, ht]; obtain ⟨e, h1, h2, h3⟩ := h
        exact ⟨e, h1, h2, by rw [← h3]; exact Frame.getMany_regs (by rfl) args⟩⟩
    | tryCallIndirect callee args et =>
      simp only [stepTerm, stepTryCallIndirect]
      apply ofRes_congr
      intro _ _
      exact stepCallIndirect_only fun n vals h => hA n vals s.mem ⟨rfl, by
        simp only [hb, ht]; obtain ⟨cv, h1, h2, h3⟩ := h
        exact ⟨cv, h1, by rw [← h2]; exact Frame.getMany_regs (by rfl) args, h3⟩⟩
    | returnCall fn args =>
      simp only [stepTerm, stepReturnCall]
      apply ofRes_congr
      intro ⟨ext, vals⟩ hX
      obtain ⟨e, he, hX⟩ := resBind_ok hX
      obtain ⟨vs, hvs, hX⟩ := resBind_ok hX
      obtain ⟨-, -, hX⟩ := resBind_ok hX
      obtain ⟨-, -, hX⟩ := resBind_ok hX
      cases hX
      have he' : s.frame.func.extern? fn = some ext := by
        cases hx : s.frame.func.extern? fn with
        | none => rw [hx] at he; cases he
        | some e' => rw [hx] at he; cases he; rfl
      have hA' := hA ext.name vals s.mem ⟨rfl, by simp only [hb, ht]; exact ⟨ext, he', rfl, hvs⟩⟩
      simp only
      cases p.func? ext.name with
      | some _ => rfl
      | none =>
        cases hg : env.extern ext.name with
        | none => simp [Env.only_extern, hg]
        | some g => simp [Env.only_extern, hg, onlyFn_of hA']
    | _ => rfl

end Clif
