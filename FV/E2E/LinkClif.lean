import FV.Clif.Run
import FV.Opt.Proof.SemSim

/-!
# Linking at the CLIF level: whole-program runs as per-function runs

`cargo fv` compiles every function of a program `P` as its own CLIF file, in which every other
function is an extern. `Clif.runLoop env P` enters a called function of `P` (pushes a frame);
the per-function view runs `P.only f` (the program with `f` alone) under an environment in
which a call of another function `g` of `P` is atomic and returns what `g`'s whole-program run
returns (`linkEnv P base`; the externs outside `P` are `base`'s).

* `step_below`, `runLoop_below_*`: a run with more callers below the stack is the run without
  them until the bottom frame returns, which then resumes the first extra caller.
* `runLim`: the outcome of a run with unbounded fuel (`outOfFuel` iff no fuel suffices).
* `runLoop_link`: **every complete whole-program run (returned or trapped) is a complete
  per-function run** of the entered function under `linkEnv P base`, for programs without
  `call_indirect`, `try_call_indirect` and `return_call` (`LinkFree`; `call` and `try_call`,
  whose normal return `Clif.run` models, are allowed) and with distinct function names.
-/

namespace Clif

/-! ## More callers below the stack -/

/-- `s` with the callers `M` appended below its stack. -/
def State.below (s : State) (M : List (Frame × List ValueId)) : State :=
  { s with callers := s.callers ++ M }

@[simp] theorem State.below_frame (s : State) (M : List (Frame × List ValueId)) :
    (s.below M).frame = s.frame := rfl

@[simp] theorem State.below_mem (s : State) (M : List (Frame × List ValueId)) :
    (s.below M).mem = s.mem := rfl

@[simp] theorem State.below_callers (s : State) (M : List (Frame × List ValueId)) :
    (s.below M).callers = s.callers ++ M := rfl

/-- A completed activation (results `vals`, memory `mem`) returns to the callers `M`: the first
one resumes with its pending call's results bound, or the run is done. -/
def resumeStep : List (Frame × List ValueId) → List Val → Mem → StepResult
  | [], vals, mem => .done vals mem
  | (caller, results) :: callers, vals, mem =>
    match caller.regs.setMany results vals with
    | some regs => .next { frame := { caller with regs }, callers, mem }
    | none => .stuck "call result arity mismatch"

/-- A step result with the callers `M` below the stack. -/
def StepResult.below (M : List (Frame × List ValueId)) : StepResult → StepResult
  | .next s => .next (s.below M)
  | .done vals mem => resumeStep M vals mem
  | .trapped c => .trapped c
  | .stuck m => .stuck m

theorem StepResult.ofRes_below {α : Type} (X : Res α) (k : α → StepResult)
    (M : List (Frame × List ValueId)) :
    (StepResult.ofRes X k).below M = StepResult.ofRes X fun a => (k a).below M := by
  cases X <;> rfl

theorem continueWith_below (s : State) (rest : List Stmt) (results : List ValueId)
    (vals : List Val) (mem : Mem) (M : List (Frame × List ValueId)) :
    continueWith (s.below M) rest results vals mem =
      (continueWith s rest results vals mem).below M := by
  unfold continueWith
  simp only [State.below_frame]
  split <;> rfl

theorem returnValues_below (s : State) (vals : List Val) (mem : Mem)
    (M : List (Frame × List ValueId)) :
    returnValues (s.below M) vals mem = (returnValues s vals mem).below M := by
  unfold returnValues
  rw [StepResult.ofRes_below]
  simp only [State.below_frame, State.below_callers]
  congr 1
  funext _
  cases s.callers with
  | nil =>
    simp only [List.nil_append]
    cases M with
    | nil => rfl
    | cons c M => obtain ⟨_, _⟩ := c; rfl
  | cons c cs =>
    obtain ⟨caller, results⟩ := c
    simp only [List.cons_append]
    split <;> rfl

theorem stepCall_below (env : Env) (p : Program) (s : State) (rest : List Stmt)
    (results : List ValueId) (fn : FnRef) (args : List ValueId)
    (M : List (Frame × List ValueId)) :
    stepCall env p (s.below M) rest results fn args =
      (stepCall env p s rest results fn args).below M := by
  unfold stepCall
  rw [StepResult.ofRes_below]
  simp only [State.below_frame, State.below_mem]
  congr 1
  funext ⟨ext, vals⟩
  split
  · split
    · rw [StepResult.ofRes_below]
      congr 1
    · rfl
  · split
    · split
      · split
        · exact continueWith_below ..
        · rfl
      · rfl
      · rfl
      · rfl
    · rfl

theorem stepCallIndirect_below (env : Env) (p : Program) (s : State) (rest : List Stmt)
    (results : List ValueId) (sig : Nat) (callee : ValueId) (args : List ValueId)
    (M : List (Frame × List ValueId)) :
    stepCallIndirect env p (s.below M) rest results sig callee args =
      (stepCallIndirect env p s rest results sig callee args).below M := by
  unfold stepCallIndirect
  rw [StepResult.ofRes_below]
  simp only [State.below_frame, State.below_mem]
  congr 1
  funext ⟨declared, addr, vals⟩
  split
  · split
    · rw [StepResult.ofRes_below]
      congr 1
    · rfl
  · rw [StepResult.ofRes_below]
    congr 1
    funext ⟨rvals, mem'⟩
    exact continueWith_below ..

theorem stepReturnCall_below (env : Env) (p : Program) (s : State) (fn : FnRef)
    (args : List ValueId) (M : List (Frame × List ValueId)) :
    stepReturnCall env p (s.below M) fn args = (stepReturnCall env p s fn args).below M := by
  unfold stepReturnCall
  rw [StepResult.ofRes_below]
  simp only [State.below_frame, State.below_mem]
  congr 1
  funext ⟨ext, vals⟩
  split
  · split
    · rw [StepResult.ofRes_below]
      congr 1
    · rfl
  · split
    · split
      · exact returnValues_below ..
      · rfl
      · rfl
      · rfl
    · rfl

theorem State.below_with_frame (s : State) (fr : Frame) (M : List (Frame × List ValueId)) :
    ({ s.below M with frame := fr } : State) = ({ s with frame := fr } : State).below M := rfl

theorem stepTerm_below (env : Env) (p : Program) (s : State) (t : Terminator)
    (M : List (Frame × List ValueId)) :
    stepTerm env p (s.below M) t = (stepTerm env p s t).below M := by
  cases t with
  | jump dest =>
    simp only [stepTerm, StepResult.ofRes_below, State.below_frame]; rfl
  | brif c t e =>
    simp only [stepTerm, StepResult.ofRes_below, State.below_frame]; rfl
  | brTable x d tb =>
    simp only [stepTerm, StepResult.ofRes_below, State.below_frame]; rfl
  | ret xs =>
    simp only [stepTerm, StepResult.ofRes_below, State.below_frame]
    congr 1
    funext vals
    exact returnValues_below ..
  | returnCall fn args => exact stepReturnCall_below ..
  | trap code => rfl
  | tryCall fn args et =>
    simp only [stepTerm, stepTryCall, StepResult.ofRes_below, State.below_frame]
    congr 1
    funext ⟨n, b, bc⟩
    rw [State.below_with_frame]
    exact stepCall_below ..
  | tryCallIndirect callee args et =>
    simp only [stepTerm, stepTryCallIndirect, StepResult.ofRes_below, State.below_frame]
    congr 1
    funext ⟨n, b, bc⟩
    rw [State.below_with_frame]
    exact stepCallIndirect_below ..

/-- **One step with more callers below the stack.** -/
theorem step_below (env : Env) (p : Program) (s : State) (M : List (Frame × List ValueId)) :
    step env p (s.below M) = (step env p s).below M := by
  unfold step
  simp only [State.below_frame]
  split
  · exact stepTerm_below ..
  · split
    · exact stepCall_below ..
    · exact stepCallIndirect_below ..
    · rw [StepResult.ofRes_below]
      congr 1
      funext ⟨vals, mem⟩
      exact continueWith_below ..

/-! ## Runs with more callers below the stack -/

/-- What `runLoop` does after a step, with `fuel` left. -/
def afterStep (env : Env) (p : Program) (fuel : Nat) : StepResult → Outcome
  | .next s' => runLoop env p fuel s'
  | .done vals mem => .returned vals mem
  | .trapped c => .trapped c
  | .stuck m => .stuck m

theorem runLoop_succ' (env : Env) (p : Program) (fuel : Nat) (s : State) :
    runLoop env p (fuel + 1) s = afterStep env p fuel (step env p s) := by
  rw [runLoop_succ]
  cases step env p s <;> rfl

/-- A run that does not return (its bottom frame does not return within the fuel) is the same
run with more callers below the stack. -/
theorem runLoop_below_of_not_returned (env : Env) (p : Program)
    (M : List (Frame × List ValueId)) :
    ∀ (N : Nat) (s : State), (∀ vals mem, runLoop env p N s ≠ .returned vals mem) →
      runLoop env p N (s.below M) = runLoop env p N s
  | 0, _, _ => rfl
  | N + 1, s, h => by
    rw [runLoop_succ', runLoop_succ', step_below]
    have h' := h
    rw [runLoop_succ'] at h'
    cases hs : step env p s with
    | next s' =>
      rw [hs] at h'
      exact runLoop_below_of_not_returned env p M N s' h'
    | done vals mem =>
      rw [hs] at h'
      exact absurd rfl (h' vals mem)
    | trapped c => rfl
    | stuck m => rfl

/-- **The bottom frame returns**: a run that returns `vals`/`mem` within `N` steps does so at
step `j ≤ N`; with callers `M` below the stack the run is then at `resumeStep M vals mem`, with
the remaining fuel. -/
theorem runLoop_below_returned (env : Env) (p : Program) :
    ∀ (N : Nat) (s : State) (vals : List Val) (mem : Mem),
      runLoop env p N s = .returned vals mem →
      ∃ j, 0 < j ∧ j ≤ N ∧ ∀ (M : List (Frame × List ValueId)) (n : Nat),
        runLoop env p (n + j) (s.below M) = afterStep env p n (resumeStep M vals mem)
  | 0, _, _, _, h => by simp at h
  | N + 1, s, vals, mem, h => by
    rw [runLoop_succ'] at h
    cases hs : step env p s with
    | next s' =>
      rw [hs] at h
      obtain ⟨j, hj0, hjN, hr⟩ := runLoop_below_returned env p N s' vals mem h
      refine ⟨j + 1, by omega, by omega, fun M n => ?_⟩
      rw [show n + (j + 1) = (n + j) + 1 by omega, runLoop_succ', step_below, hs]
      exact hr M n
    | done vals' mem' =>
      rw [hs] at h
      simp only [afterStep, Outcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨1, by omega, by omega, fun M n => ?_⟩
      rw [runLoop_succ', step_below, hs]
      rfl
    | trapped c => rw [hs] at h; cases h
    | stuck m => rw [hs] at h; cases h

/-- More fuel does not change a run that ended. -/
theorem runLoop_add (env : Env) (p : Program) :
    ∀ (N : Nat) (s : State), runLoop env p N s ≠ .outOfFuel →
      ∀ k, runLoop env p (N + k) s = runLoop env p N s
  | 0, _, h, _ => absurd rfl h
  | N + 1, s, h, k => by
    rw [show N + 1 + k = (N + k) + 1 by omega, runLoop_succ', runLoop_succ']
    rw [runLoop_succ'] at h
    cases hs : step env p s with
    | next s' =>
      rw [hs] at h
      exact runLoop_add env p N s' h k
    | _ => rfl

/-- The outcome of a run with unbounded fuel: the outcome of any run that ended (they agree,
`runLoop_add`), else `outOfFuel` (the run diverges). -/
noncomputable def runLim (env : Env) (p : Program) (s : State) : Outcome := by
  classical
  exact if h : ∃ n, runLoop env p n s ≠ .outOfFuel then runLoop env p (Classical.choose h) s
    else .outOfFuel

theorem runLim_eq {env : Env} {p : Program} {s : State} {n : Nat}
    (h : runLoop env p n s ≠ .outOfFuel) : runLim env p s = runLoop env p n s := by
  unfold runLim
  split
  · rename_i hex
    have hc := Classical.choose_spec hex
    rw [← runLoop_add env p _ s hc n, Nat.add_comm, runLoop_add env p n s h]
  · rename_i hn
    exact absurd ⟨n, h⟩ hn

/-! ## The linked environment -/

/-- The program with `f` as its only function (the file `cargo fv` compiles for `f`). -/
def Program.only (p : Program) (f : Function) : Program := { p with funcs := [f] }

/-- **The environment of the per-function programs of `P`**: a call of a function `g` of `P`
runs `g`'s whole-program run (`Clif.runWith base P g` with unbounded fuel: `runLim`); every
other extern is `base`'s. -/
noncomputable def linkEnv (P : Program) (base : Env) : Env where
  extern n := match P.func? n with
    | some _ => some fun vals mem =>
      match initState P n vals mem with
      | .ok s => runLim base P s
      | .trap c => .trapped c
      | .stuck m => .stuck m
    | none => base.extern n

theorem linkEnv_none {P : Program} {base : Env} {n : String} (h : P.func? n = none) :
    (linkEnv P base).extern n = base.extern n := by
  simp [linkEnv, h]

theorem linkEnv_some {P : Program} {base : Env} {n : String} {g : Function}
    (h : P.func? n = some g) :
    (linkEnv P base).extern n = some fun vals mem =>
      match initState P n vals mem with
      | .ok s => runLim base P s
      | .trap c => .trapped c
      | .stuck m => .stuck m := by
  simp [linkEnv, h]

theorem Program.func?_some {p : Program} {n : String} {g : Function} (h : p.func? n = some g) :
    g ∈ p.funcs ∧ g.name = n := by
  unfold Program.func? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem Program.func?_none {p : Program} {n : String} (h : p.func? n = none) :
    ∀ g ∈ p.funcs, g.name ≠ n := by
  unfold Program.func? at h
  intro g hg he
  have := List.find?_eq_none.mp h g hg
  simp [he] at this

theorem Program.only_func? (p : Program) (f : Function) (n : String) :
    (p.only f).func? n = if f.name = n then some f else none := by
  simp only [Program.func?, Program.only, List.find?_cons, List.find?_nil]
  by_cases h : f.name = n
  · simp [h]
  · have hb : (f.name == n) = false := by simpa using h
    rw [hb]
    simp [h]

/-! ## The programs: no indirect calls and no `return_call` -/

/-- `g` has no `call_indirect` statement and no `try_call_indirect` or `return_call`
terminator (`call` and `try_call` are allowed). -/
def LinkFree (g : Function) : Prop :=
  ∀ b ∈ g.blocks, (∀ st ∈ b.body, ∀ sig callee args, st.inst ≠ .callIndirect sig callee args) ∧
    (∀ callee args et, b.term ≠ .tryCallIndirect callee args et) ∧
    ∀ fn args, b.term ≠ .returnCall fn args

/-- A frame of a function of `P`, at a program point of one of its blocks, or at the pending
`jump` to the normal-return successor of a `try_call` (`Clif.stepTryCall`). -/
def LFrame (P : Program) (fr : Frame) : Prop :=
  fr.func ∈ P.funcs ∧ ((∃ b ∈ fr.func.blocks, fr.body <:+ b.body ∧ fr.term = b.term) ∨
    (fr.body = [] ∧ ∃ bc, fr.term = .jump bc))

/-- Every frame of `s`, running or suspended, is an `LFrame`. -/
def LInv (P : Program) (s : State) : Prop := LFrame P s.frame ∧ ∀ c ∈ s.callers, LFrame P c.1

theorem LFrame.regs {P : Program} {fr : Frame} (h : LFrame P fr) (regs : Regs) :
    LFrame P { fr with regs } := h

theorem LFrame.rest {P : Program} {fr : Frame} {st : Stmt} {rest : List Stmt} (h : LFrame P fr)
    (hb : fr.body = st :: rest) (regs : Regs) : LFrame P { fr with regs, body := rest } := by
  rcases h with ⟨hf, ⟨b, hbm, hsuf, ht⟩ | ⟨hnil, _⟩⟩
  · exact ⟨hf, .inl ⟨b, hbm, (List.suffix_cons st rest).trans (hb ▸ hsuf), ht⟩⟩
  · rw [hnil] at hb; cases hb

theorem LFrame.jump {P : Program} {fr : Frame} (hf : fr.func ∈ P.funcs) (regs : Regs)
    (bc : BlockCall) : LFrame P { fr with regs, body := [], term := .jump bc } :=
  ⟨hf, .inr ⟨rfl, bc, rfl⟩⟩

theorem LFrame.enterFunc {P : Program} {g : Function} {vals : List Val} {mem : Mem} {fr : Frame}
    {mem' : Mem} (hg : g ∈ P.funcs) (h : enterFunc g vals mem = .ok (fr, mem')) : LFrame P fr := by
  obtain ⟨b, regs, hb, -, -, -, -, he⟩ := Opt.enterFunc_ok h
  rw [he]
  exact ⟨hg, .inl ⟨b, List.mem_of_mem_head? hb, List.suffix_refl _, rfl⟩⟩

/-- The next step of an `LFrame` that is not at a `try_call` is a local step (`Opt.lstep`). -/
theorem LFrame.headNoCI {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {fr : Frame}
    (h : LFrame P fr) (hnt : ∀ fn args et, fr.body = [] → fr.term ≠ .tryCall fn args et) :
    Opt.HeadNoCI fr := by
  rcases h with ⟨hf, ⟨b, hbm, hsuf, ht⟩ | ⟨hnil, bc, ht⟩⟩
  · refine ⟨fun st rest hbd => (hP _ hf b hbm).1 st (hsuf.subset (by rw [hbd]; simp)), fun hb => ?_⟩
    cases hterm : fr.term with
    | tryCall fn args et => exact absurd hterm (hnt fn args et hb)
    | tryCallIndirect c a et => exact absurd (ht.symm.trans hterm) ((hP _ hf b hbm).2.1 c a et)
    | _ => rfl
  · refine ⟨fun st rest hbd => ?_, fun _ => ?_⟩
    · rw [hnil] at hbd; cases hbd
    · rw [ht]; rfl

theorem lstep_next_lframe {P : Program} {fr : Frame} {m : Mem} {fr' : Frame} {m' : Mem}
    (hI : LFrame P fr) (h : Opt.lstep fr m = .next fr' m') : LFrame P fr' := by
  obtain ⟨func, regs, slots, body, term⟩ := fr
  cases body with
  | nil =>
    simp only [Opt.lstep] at h
    cases term <;> simp only [Opt.LRes.ofRes] at h <;> (repeat' split at h) <;>
      (try contradiction) <;>
      (cases h; obtain ⟨b, _, _, hbk, _, _, _, rfl⟩ := Opt.enterBlock_ok ‹_›
       exact ⟨hI.1, .inl ⟨b, List.mem_of_find?_eq_some hbk, List.suffix_refl _, rfl⟩⟩)
  | cons st rest =>
    simp only [Opt.lstep] at h
    split at h
    · simp only [Opt.LRes.ofRes] at h; split at h <;> contradiction
    · simp only [Opt.LRes.ofRes] at h
      split at h <;> try contradiction
      split at h <;> try contradiction
      cases h
      exact hI.rest rfl _

theorem lstep_ne_tail {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {fr : Frame} {m : Mem}
    (hI : LFrame P fr) {ext : ExtFunc} {vals : List Val} : Opt.lstep fr m ≠ .tail ext vals := by
  intro hl
  obtain ⟨fn, args, ht, -⟩ := Opt.lstep_tail_term hl
  rcases hI with ⟨hf, ⟨b, hb, -, hbt⟩ | ⟨-, bc, hbt⟩⟩
  · exact (hP _ hf b hb).2.2 fn args (hbt ▸ ht)
  · rw [hbt] at ht; cases ht

/-! ## Step shapes -/

/-- The function of the bottom frame of `s` (the activation whose return ends the run). -/
def State.bottom (s : State) : Function := (s.callers.getLast?.map (·.1.func)).getD s.frame.func

theorem bottom_push {fr fr0 fr1 : Frame} {rs : List ValueId} {cs : List (Frame × List ValueId)}
    {m m' : Mem} (h : fr0.func = fr.func) :
    State.bottom ⟨fr1, (fr0, rs) :: cs, m⟩ = State.bottom ⟨fr, cs, m'⟩ := by
  cases cs with
  | nil => simp [State.bottom, h]
  | cons c cs =>
    simp only [State.bottom, List.getLast?_cons_cons]
    cases hx : (c :: cs).getLast? with
    | none => simp at hx
    | some x => rfl

theorem bottom_pop {fr fr1 c : Frame} {rs : List ValueId} {cs : List (Frame × List ValueId)}
    {m m' : Mem} (h : fr1.func = c.func) :
    State.bottom ⟨fr1, cs, m⟩ = State.bottom ⟨fr, (c, rs) :: cs, m'⟩ := by
  cases cs with
  | nil => simp [State.bottom, h]
  | cons c cs =>
    simp only [State.bottom, List.getLast?_cons_cons]
    cases hx : (c :: cs).getLast? with
    | none => simp at hx
    | some x => rfl

theorem returnValues_next {s : State} {vals : List Val} {mem : Mem} {s1 : State}
    (h : returnValues s vals mem = .next s1) :
    ∃ c rs cs regs, s.callers = (c, rs) :: cs ∧ s1.callers = cs ∧ s1.frame = { c with regs } := by
  obtain ⟨_, h⟩ := Opt.StepResult.ofRes_eq_next h
  obtain ⟨frame, callers, m⟩ := s
  cases callers with
  | nil => cases h.2
  | cons c cs =>
    obtain ⟨caller, results⟩ := c
    simp only at h
    split at h
    · rename_i regs _
      cases h.2
      exact ⟨caller, results, cs, regs, rfl, rfl, rfl⟩
    · cases h.2

theorem ofRes_eq_done {α : Type} {r : Res α} {k : α → StepResult} {v : List Val} {m : Mem}
    (h : StepResult.ofRes r k = .done v m) : ∃ a, r = .ok a ∧ k a = .done v m := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | trap c => cases h
  | stuck m => cases h

theorem returnValues_done {s : State} {vals : List Val} {mem : Mem} {v : List Val} {m : Mem}
    (h : returnValues s vals mem = .done v m) :
    s.callers = [] ∧ v = vals ∧ vals.map (·.ty) = AbiParam.tys s.frame.func.sig.returns := by
  obtain ⟨u, hu, h⟩ := ofRes_eq_done h
  simp only [checkTys, Opt.Res.check_eq_ok, beq_iff_eq] at hu
  obtain ⟨frame, callers, m'⟩ := s
  cases callers with
  | nil =>
    simp only [StepResult.done.injEq] at h
    exact ⟨rfl, h.1.symm, hu⟩
  | cons c cs =>
    obtain ⟨caller, results⟩ := c
    simp only at h
    revert h
    split <;> intro h <;> cases h

theorem callCont_next {env : Env} {p : Program} {t : State} {rest : List Stmt}
    {rs : List ValueId} {ext : ExtFunc} {vals : List Val} {s1 : State}
    (h : Opt.callCont env p t rest rs ext vals = .next s1) :
    (s1.callers = ({ t.frame with body := rest }, rs) :: t.callers ∧
      ∃ g mem', p.func? ext.name = some g ∧ enterFunc g vals t.mem = .ok (s1.frame, mem')) ∨
    (s1.callers = t.callers ∧ ∃ regs, s1.frame = { t.frame with regs, body := rest }) := by
  unfold Opt.callCont at h
  split at h
  · rename_i g hg
    split at h
    · obtain ⟨⟨fr', mem'⟩, he, h⟩ := Opt.StepResult.ofRes_eq_next h
      cases h
      exact .inl ⟨rfl, g, mem', hg, he⟩
    · cases h
  · split at h
    · split at h
      · split at h
        · unfold continueWith at h
          split at h
          · rename_i regs _
            cases h
            exact .inr ⟨rfl, regs, rfl⟩
          · cases h
        · cases h
      all_goals cases h
    · cases h

theorem callCont_ne_done {env : Env} {p : Program} {s : State} {rest : List Stmt}
    {rs : List ValueId} {ext : ExtFunc} {vals : List Val} {v : List Val} {m : Mem} :
    Opt.callCont env p s rest rs ext vals ≠ .done v m := by
  intro h
  unfold Opt.callCont at h
  split at h
  · split at h
    · cases he : enterFunc _ vals s.mem with
      | ok a => rw [he] at h; cases h
      | trap c => rw [he] at h; cases h
      | stuck m => rw [he] at h; cases h
    · cases h
  · split at h
    · split at h
      · split at h
        · unfold continueWith at h
          split at h <;> cases h
        · cases h
      all_goals cases h
    · cases h

/-- The prelude of `Clif.stepTryCall`. -/
def tryPre (fr : Frame) (fn : FnRef) (et : ExnTable) : Res (Nat × ValueId × BlockCall) := do
  let ext ← Res.ofOption s!"unknown function reference fn{fn}" (fr.func.extern? fn)
  let sig ← Res.ofOption s!"unknown signature sig{et.sig}" (fr.func.sigDecls.lookup et.sig)
  Res.check (AbiParam.tys sig.params == AbiParam.tys ext.sig.params &&
      AbiParam.tys sig.returns == AbiParam.tys ext.sig.returns)
    s!"try_call: sig{et.sig} is not the signature of fn{fn}"
  let base := fr.func.freshValue
  let bc ← tryNormal et base
  pure (ext.sig.returns.length, base, bc)

/-- The state of a `try_call`'s call: the frame waits at the `jump` to the normal return. -/
def tryState (s : State) (bc : BlockCall) : State :=
  { s with frame := { s.frame with body := [], term := .jump bc } }

/-- **A `try_call` step**: its prelude, the call's prelude, then the call (`Opt.callCont`) from
the frame waiting at the normal-return `jump`. -/
theorem step_try (env : Env) (p : Program) (s : State) {fn : FnRef} {args : List ValueId}
    {et : ExnTable} (hb : s.frame.body = []) (ht : s.frame.term = .tryCall fn args et) :
    step env p s = StepResult.ofRes (tryPre s.frame fn et) fun (n, b, bc) =>
      StepResult.ofRes (Opt.callArgs (tryState s bc).frame fn args) fun (ext, vals) =>
        Opt.callCont env p (tryState s bc) [] ((List.range n).map (b + ·)) ext vals := by
  rw [step_term env p s hb, ht]
  rfl

/-- Steps of a whole-program run keep `LInv` and the bottom frame's function. -/
theorem step_next_linv {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env} {s s1 : State}
    (hI : LInv P s) (h : step env P s = .next s1) : LInv P s1 ∧ s1.bottom = s.bottom := by
  -- a call (`callCont`) from `t`, whose frame is `s`'s up to `regs`/`body`/`term`
  have hcall : ∀ (t : State) rest rs ext vals, t.callers = s.callers → t.frame.func = s.frame.func →
      (∀ regs, LFrame P { t.frame with regs, body := rest }) →
      Opt.callCont env P t rest rs ext vals = .next s1 → LInv P s1 ∧ s1.bottom = s.bottom := by
    intro t rest rs ext vals htc htf hfr hc
    rcases callCont_next hc with ⟨hc1, g, mem', hg, he⟩ | ⟨hc1, regs, hf1⟩
    · refine ⟨⟨LFrame.enterFunc (Program.func?_some hg).1 he, ?_⟩, ?_⟩
      · rw [hc1, htc]
        simp only [List.forall_mem_cons]
        exact ⟨hfr t.frame.regs, hI.2⟩
      · obtain ⟨fr1, cs1, m1⟩ := s1
        obtain ⟨fr, cs, m⟩ := s
        simp only at hc1 htc htf
        subst hc1 htc
        exact bottom_push htf
    · refine ⟨⟨hf1 ▸ hfr regs, by rw [hc1, htc]; exact hI.2⟩, ?_⟩
      obtain ⟨fr1, cs1, m1⟩ := s1
      simp only at hc1 hf1
      simp only [State.bottom, hc1, htc, hf1, htf]
  by_cases hT : ∃ fn args et, s.frame.body = [] ∧ s.frame.term = .tryCall fn args et
  · obtain ⟨fn, args, et, hb, ht⟩ := hT
    rw [step_try env P s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    obtain ⟨⟨ext, vals⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    exact hcall (tryState s bc) [] _ ext vals rfl rfl (fun regs => LFrame.jump hI.1.1 regs bc) h
  · have hnt : ∀ fn args et, s.frame.body = [] → s.frame.term ≠ .tryCall fn args et :=
      fun fn args et hb ht => hT ⟨fn, args, et, hb, ht⟩
    rw [Opt.step_eq_lift env P s (hI.1.headNoCI hP hnt)] at h
    cases hl : Opt.lstep s.frame s.mem with
    | next fr1 m1 =>
      rw [hl] at h; cases h
      exact ⟨⟨lstep_next_lframe hI.1 hl, hI.2⟩, by simp [State.bottom, (Opt.lstep_next_frame hl).1]⟩
    | call ext vals rs rest =>
      rw [hl] at h
      obtain ⟨st, fn, args, hb, -, -, -⟩ := Opt.lstep_call_inv hl
      exact hcall s rest rs ext vals rfl rfl (fun regs => hI.1.rest hb regs) h
    | ret vals =>
      rw [hl] at h
      obtain ⟨c, rs, cs, regs, hc, hc1, hf1⟩ := returnValues_next h
      refine ⟨⟨hf1 ▸ (hI.2 (c, rs) (by rw [hc]; simp)).regs regs, ?_⟩, ?_⟩
      · rw [hc1]; exact fun c' hc' => hI.2 c' (by rw [hc]; simp [hc'])
      · obtain ⟨fr1, cs1, m1⟩ := s1
        obtain ⟨fr, cs0, m⟩ := s
        simp only at hc hc1 hf1
        subst hc hc1
        exact bottom_pop (by rw [hf1])
    | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1)
    | trap c => rw [hl] at h; cases h
    | stuck m => rw [hl] at h; cases h

/-- A whole-program step that finishes the run returns from the bottom frame, with values of its
return types. -/
theorem step_done_linv {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env} {s : State}
    {v : List Val} {m : Mem} (hI : LInv P s) (h : step env P s = .done v m) :
    s.callers = [] ∧ v.map (·.ty) = AbiParam.tys s.frame.func.sig.returns := by
  by_cases hT : ∃ fn args et, s.frame.body = [] ∧ s.frame.term = .tryCall fn args et
  · obtain ⟨fn, args, et, hb, ht⟩ := hT
    rw [step_try env P s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := ofRes_eq_done h
    obtain ⟨⟨ext, vals⟩, -, h⟩ := ofRes_eq_done h
    exact absurd h callCont_ne_done
  · have hnt : ∀ fn args et, s.frame.body = [] → s.frame.term ≠ .tryCall fn args et :=
      fun fn args et hb ht => hT ⟨fn, args, et, hb, ht⟩
    rw [Opt.step_eq_lift env P s (hI.1.headNoCI hP hnt)] at h
    cases hl : Opt.lstep s.frame s.mem with
    | ret vals =>
      rw [hl] at h
      obtain ⟨hc, rfl, ht⟩ := returnValues_done h
      exact ⟨hc, ht⟩
    | call ext vals rs rest => rw [hl] at h; exact absurd h callCont_ne_done
    | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1)
    | next fr1 m1 => rw [hl] at h; cases h
    | trap c => rw [hl] at h; cases h
    | stuck m => rw [hl] at h; cases h

/-- **Return types**: a whole-program run that returns gives values of the bottom frame's return
types. -/
theorem runLoop_returned_tys {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env} :
    ∀ (N : Nat) (s : State) (vals : List Val) (mem : Mem), LInv P s →
      runLoop env P N s = .returned vals mem →
      vals.map (·.ty) = AbiParam.tys s.bottom.sig.returns
  | 0, _, _, _, _, h => by simp at h
  | N + 1, s, vals, mem, hI, h => by
    rw [runLoop_succ'] at h
    cases hs : step env P s with
    | next s1 =>
      rw [hs] at h
      have h1 := step_next_linv hP hI hs
      rw [runLoop_returned_tys hP N s1 vals mem h1.1 h, h1.2]
    | done v m =>
      rw [hs] at h
      simp only [afterStep, Outcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hc, ht⟩ := step_done_linv hP hI hs
      rw [ht]
      simp [State.bottom, hc]
    | trapped c => rw [hs] at h; cases h
    | stuck m => rw [hs] at h; cases h

/-! ## The linking theorem (CLIF) -/

theorem afterStep_fuel {env : Env} {p : Program} {r : StepResult} (h : ∀ s1, r ≠ .next s1)
    (n n' : Nat) : afterStep env p n r = afterStep env p n' r := by
  cases r with
  | next s1 => exact absurd rfl (h s1)
  | _ => rfl

theorem name_inj {fs : List Function} (h : (fs.map (·.name)).Nodup) {g g' : Function}
    (hg : g ∈ fs) (hg' : g' ∈ fs) (he : g.name = g'.name) : g = g' := by
  induction fs with
  | nil => cases hg
  | cons a fs ih =>
    rw [List.map_cons, List.nodup_cons] at h
    have hn : ∀ x ∈ fs, x.name ≠ a.name := fun x hx hx' => h.1 (List.mem_map.mpr ⟨x, hx, hx'⟩)
    cases List.mem_cons.mp hg with
    | inl h1 =>
      cases List.mem_cons.mp hg' with
      | inl h2 => rw [h1, h2]
      | inr h2 => exact absurd (he.symm.trans (congrArg Function.name h1)) (hn g' h2)
    | inr h1 =>
      cases List.mem_cons.mp hg' with
      | inl h2 => exact absurd (he.trans (congrArg Function.name h2)) (hn g h1)
      | inr h2 => exact ih h.2 h1 h2

theorem ofRes_cases {α : Type} (X : Res α) (k₁ k₂ : α → StepResult) :
    StepResult.ofRes X k₁ = StepResult.ofRes X k₂ ∨
      ∃ a, StepResult.ofRes X k₁ = k₁ a ∧ StepResult.ofRes X k₂ = k₂ a := by
  cases X with
  | ok a => exact .inr ⟨a, rfl, rfl⟩
  | _ => exact .inl rfl

/-- **Linking at the CLIF level.** For a program `P` with distinct function names whose
functions have no `call_indirect`, `try_call_indirect` or `return_call` (`LinkFree`; `call` and
`try_call` are allowed), a whole-program run (a call of a function of `P` enters it) from a
state whose frames run functions of `P` (`LInv`) that returns or traps within `N` steps is a
per-function run of `P.only f` (only `f` is entered; a call of any other function `g` of `P` is
atomic and returns what `g`'s whole-program run returns, `linkEnv P base`) with the same
outcome. -/
theorem runLoop_link {P : Program} {base : Env} {f : Function}
    (hnd : (P.funcs.map (·.name)).Nodup) (hf : f ∈ P.funcs) (hP : ∀ g ∈ P.funcs, LinkFree g) :
    ∀ (N : Nat) (s : State), LInv P s →
      (∀ msg, runLoop base P N s ≠ .stuck msg) → runLoop base P N s ≠ .outOfFuel →
      ∃ m, runLoop (linkEnv P base) (P.only f) m s = runLoop base P N s := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro s hI hst hof
  cases N with
  | zero => exact absurd rfl hof
  | succ N =>
  -- a per-function step `r` after which the whole-program run continues with `n` steps
  have helper : ∀ (r : StepResult) (n : Nat), n < N + 1 →
      step (linkEnv P base) (P.only f) s = r → runLoop base P (N + 1) s = afterStep base P n r →
      (∀ s1, r = .next s1 → LInv P s1) →
      ∃ m, runLoop (linkEnv P base) (P.only f) m s = runLoop base P (N + 1) s := by
    intro r n hn hr hrun hinv
    cases r with
    | next s1 =>
      rw [hrun] at hst hof ⊢
      obtain ⟨m, hm⟩ := ih n hn s1 (hinv s1 rfl) hst hof
      exact ⟨m + 1, by rw [runLoop_succ', hr]; exact hm⟩
    | _ => exact ⟨0 + 1, by rw [runLoop_succ', hr, hrun]; rfl⟩
  -- the steps that do not call another function of `P` are the same
  have same : step (linkEnv P base) (P.only f) s = step base P s →
      ∃ m, runLoop (linkEnv P base) (P.only f) m s = runLoop base P (N + 1) s := fun h =>
    helper _ N (by omega) h (runLoop_succ' ..) fun s1 hs1 => (step_next_linv hP hI hs1).1
  -- a call (`callCont`) from `t`, whose frame is `s`'s up to `regs`/`body`/`term`
  have call : ∀ (t : State) rest rs ext vals, t.callers = s.callers → t.mem = s.mem →
      (∀ regs, LFrame P { t.frame with regs, body := rest }) →
      step base P s = Opt.callCont base P t rest rs ext vals →
      step (linkEnv P base) (P.only f) s = Opt.callCont (linkEnv P base) (P.only f) t rest rs ext vals →
      ∃ m, runLoop (linkEnv P base) (P.only f) m s = runLoop base P (N + 1) s := by
    intro t rest rs ext vals htc htm hfr e1 e2
    cases hpf : P.func? ext.name with
    | none =>
      have hfn : f.name ≠ ext.name := Program.func?_none hpf f hf
      apply same
      rw [e1, e2]
      simp only [Opt.callCont, hpf, Program.only_func?, hfn, ↓reduceIte, linkEnv_none hpf]
    | some g =>
      obtain ⟨hgP, hgn⟩ := Program.func?_some hpf
      by_cases hgf : g = f
      · subst hgf
        apply same
        rw [e1, e2]
        simp only [Opt.callCont, hpf, Program.only_func?, hgn, ↓reduceIte]
      have hfn : f.name ≠ ext.name := fun h => hgf (name_inj hnd hgP hf (hgn.trans h.symm))
      -- the per-function step: the atomic call of `g`
      have e2' := e2
      simp only [Opt.callCont, Program.only_func?, hfn, ↓reduceIte, linkEnv_some hpf] at e2'
      rw [runLoop_succ', e1] at hst hof
      rw [runLoop_succ', e1]
      simp only [Opt.callCont, hpf] at hst hof ⊢
      cases hsig : (AbiParam.tys g.sig.params == AbiParam.tys ext.sig.params &&
          AbiParam.tys g.sig.returns == AbiParam.tys ext.sig.returns) with
      | false =>
        simp only [hsig, Bool.false_eq_true, ↓reduceIte, afterStep] at hst
        exact absurd rfl (hst _)
      | true =>
        simp only [hsig, ↓reduceIte] at hst hof ⊢
        simp only [Bool.and_eq_true, beq_iff_eq] at hsig
        cases he : enterFunc g vals t.mem with
        | trap c => exact absurd he (Opt.enterFunc_not_trap g vals t.mem c)
        | stuck m =>
          rw [he] at hst; exact absurd rfl (hst m)
        | ok a =>
          obtain ⟨fr', mem'⟩ := a
          rw [he] at hst hof
          simp only [StepResult.ofRes_ok, afterStep] at hst hof ⊢
          have hinit : initState P ext.name vals t.mem = .ok ⟨fr', [], mem'⟩ := by
            simp [initState, hpf, he, Res.ofOption, bind, Res.bind, pure]
          rw [hinit] at e2'
          simp only at e2'
          let K : List (Frame × List ValueId) := ({ t.frame with body := rest }, rs) :: t.callers
          have hK : ({ frame := fr', callers := K, mem := mem' } : State) =
              (⟨fr', [], mem'⟩ : State).below K := rfl
          have hsubI : LInv P ⟨fr', [], mem'⟩ :=
            ⟨LFrame.enterFunc hgP he, fun _ h => by cases h⟩
          have hfr' : fr'.func = g := by
            obtain ⟨_, _, _, _, _, _, _, hfr⟩ := Opt.enterFunc_ok he
            rw [hfr]
          rw [hK] at hst hof ⊢
          cases hsub : runLoop base P N ⟨fr', [], mem'⟩ with
          | returned rvals mem2 =>
            obtain ⟨j, hj0, hjN, hj⟩ := runLoop_below_returned base P N _ rvals mem2 hsub
            have hN : N = (N - j) + j := by omega
            rw [hN, hj] at hst hof ⊢
            have hlim : runLim base P ⟨fr', [], mem'⟩ = .returned rvals mem2 :=
              (runLim_eq (n := N) (by rw [hsub]; exact fun h => by cases h)).trans hsub
            have hty := runLoop_returned_tys hP N _ rvals mem2 hsubI hsub
            simp only [State.bottom, List.getLast?_nil, Option.map_none, Option.getD_none,
              hfr'] at hty
            rw [hlim] at e2'
            simp only [hty, hsig.2, beq_self_eq_true, ↓reduceIte] at e2'
            -- resume the caller
            cases hset : t.frame.regs.setMany rs rvals with
            | none =>
              simp only [resumeStep, K, hset, afterStep] at hst
              exact absurd rfl (hst _)
            | some regs =>
              have hc : continueWith t rest rs rvals mem2 =
                  .next ⟨{ t.frame with regs, body := rest }, t.callers, mem2⟩ := by
                simp only [continueWith, hset]
              rw [hc] at e2'
              have hres : resumeStep K rvals mem2 =
                  .next ⟨{ t.frame with regs, body := rest }, t.callers, mem2⟩ := by
                simp only [resumeStep, K, hset]
              rw [hres] at hst hof ⊢
              simp only [afterStep] at hst hof ⊢
              obtain ⟨m, hm⟩ := ih (N - j) (by omega)
                ⟨{ t.frame with regs, body := rest }, t.callers, mem2⟩
                ⟨hfr regs, by rw [htc]; exact hI.2⟩ hst hof
              exact ⟨m + 1, by rw [runLoop_succ', e2']; exact hm⟩
          | trapped c =>
            have hne : ∀ vals mem, runLoop base P N ⟨fr', [], mem'⟩ ≠ .returned vals mem := by
              rw [hsub]; exact fun _ _ h => by cases h
            rw [runLoop_below_of_not_returned base P K N _ hne, hsub] at hst hof ⊢
            have hlim : runLim base P ⟨fr', [], mem'⟩ = .trapped c :=
              (runLim_eq (n := N) (by rw [hsub]; exact fun h => by cases h)).trans hsub
            rw [hlim] at e2'
            exact ⟨1, by rw [runLoop_succ', e2']; rfl⟩
          | stuck msg =>
            have hne : ∀ vals mem, runLoop base P N ⟨fr', [], mem'⟩ ≠ .returned vals mem := by
              rw [hsub]; exact fun _ _ h => by cases h
            rw [runLoop_below_of_not_returned base P K N _ hne, hsub] at hst
            exact absurd rfl (hst msg)
          | outOfFuel =>
            have hne : ∀ vals mem, runLoop base P N ⟨fr', [], mem'⟩ ≠ .returned vals mem := by
              rw [hsub]; exact fun _ _ h => by cases h
            rw [runLoop_below_of_not_returned base P K N _ hne, hsub] at hof
            exact absurd rfl hof
  by_cases hT : ∃ fn args et, s.frame.body = [] ∧ s.frame.term = .tryCall fn args et
  · -- a `try_call`: its preludes are the same, then the call from the waiting frame
    obtain ⟨fn, args, et, hb, ht⟩ := hT
    have e1 := step_try base P s hb ht
    have e2 := step_try (linkEnv P base) (P.only f) s hb ht
    rcases ofRes_cases (tryPre s.frame fn et) _ _ with h1 | ⟨⟨n, b, bc⟩, h1, h1'⟩
    · exact same (by rw [e1, e2]; exact h1.symm)
    rw [h1] at e1
    rw [h1'] at e2
    dsimp only at e1 e2
    rcases ofRes_cases (Opt.callArgs (tryState s bc).frame fn args) _ _ with h2 | ⟨⟨ext, vals⟩, h2, h2'⟩
    · exact same (by rw [e1, e2]; exact h2.symm)
    rw [h2] at e1
    rw [h2'] at e2
    dsimp only at e1 e2
    exact call (tryState s bc) [] _ ext vals rfl rfl (fun regs => LFrame.jump hI.1.1 regs bc) e1 e2
  have hnt : ∀ fn args et, s.frame.body = [] → s.frame.term ≠ .tryCall fn args et :=
    fun fn args et hb ht => hT ⟨fn, args, et, hb, ht⟩
  have hci := hI.1.headNoCI hP hnt
  have e1 := Opt.step_eq_lift base P s hci
  have e2 := Opt.step_eq_lift (linkEnv P base) (P.only f) s hci
  cases hl : Opt.lstep s.frame s.mem with
  | next fr1 m1 => exact same (by rw [e1, e2, hl]; rfl)
  | ret vals => exact same (by rw [e1, e2, hl]; rfl)
  | trap c => exact same (by rw [e1, e2, hl]; rfl)
  | stuck m => exact same (by rw [e1, e2, hl]; rfl)
  | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1)
  | call ext vals rs rest =>
    rw [hl] at e1 e2
    obtain ⟨st, fn, args, hb, -, -, -⟩ := Opt.lstep_call_inv hl
    exact call s rest rs ext vals rfl rfl (fun regs => hI.1.rest hb regs) e1 e2

end Clif
