import FV.E2E.LinkWorld
import FV.E2E.LinkClifN
import FV.E2E.Link

/-! # Linking at the Arm level: the program's own callees run their compiled code

`backend_correct_linked` (`FV/E2E/Link.lean`) states a function's Arm code against the
whole-program CLIF run with the program callees' contracts as premises. Here the machine runs
the program callees' compiled code, and their contracts are discharged from their own
per-function theorems (`backend_correct_world`), by induction on the whole-program fuel.

* `linkedCall M a s`: a `bl` of a function compiled as `a` from state `s`, run by the machine
  `M`: the callee's ABI entry (`enterAt`: its program, pc at its base, return address in x30),
  then the state at its first return to `pc + 4` without error (with the caller's program
  again); a callee that never returns gives an error state (`junkAt`).
* `LinkSys.hooks M`: the hooks of the linked machine whose program callees run at most `M`
  levels deep (`hooks (M + 1)` runs a callee `g` of `P` by `ArmStepX _ (hooks M) (A g).fa`);
  calls of externs outside `P` and TLS keep the base hooks.
* `LinkSys.X M`: the external semantics of the VCode run of an activation: a call of a function
  of `P` gives what the linked machine computes from a canonical state built from the call's
  arguments and the caller's world (`LinkSys.canon`), defined when the callee's whole-program
  CLIF run returns within `M` steps (`LinkSys.Cond`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-! ## Machine-state helpers -/

theorem r_set_program (f : Arm.StateField) (s : Arm.ArmState) (p : Arm.Program) :
    Arm.r f (Arm.set_program s p) = Arm.r f s := by
  cases f <;> unfold Arm.r <;> rfl

@[simp] theorem mem_set_program (s : Arm.ArmState) (p : Arm.Program) :
    (Arm.set_program s p).mem = s.mem := rfl

@[simp] theorem program_set_program (s : Arm.ArmState) (p : Arm.Program) :
    (Arm.set_program s p).program = p := rfl

/-- `s` with memory `m`. -/
def setMem (s : Arm.ArmState) (m : Arm.Memory) : Arm.ArmState := { s with mem := m }

theorem r_setMem (f : Arm.StateField) (s : Arm.ArmState) (m : Arm.Memory) :
    Arm.r f (setMem s m) = Arm.r f s := by
  cases f <;> unfold Arm.r <;> rfl

@[simp] theorem mem_setMem (s : Arm.ArmState) (m : Arm.Memory) : (setMem s m).mem = m := rfl

@[simp] theorem program_setMem (s : Arm.ArmState) (m : Arm.Memory) :
    (setMem s m).program = s.program := rfl

theorem runX_add (f : Arm.ArmState → Arm.ArmState) :
    ∀ (a b : Nat) (s : Arm.ArmState), runX f (a + b) s = runX f b (runX f a s)
  | 0, b, s => by simp [runX]
  | a + 1, b, s => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [runX]
    exact runX_add f a b (f s)

/-! ## The linked call -/

/-- The compiled image of one function: the pipeline's artifacts and its load address. -/
structure Art where
  k : Nat
  vc : VCode
  vcp : VCode
  rf : RFunc
  af : AFunc
  fa : FnAsm
  fb : FnBin
  base : BitVec 64

/-- The ABI entry state of the callee `a` for a `bl` at `s`: the callee's program, pc at its
base, the return address (the instruction after the `bl`) in x30. -/
def enterAt (a : Art) (s : Arm.ArmState) : Arm.ArmState :=
  Arm.w .PC a.base (Arm.w (.GPR 30#5) (Arm.r .PC s + 4) (Arm.set_program s (a.fb.program a.base)))

/-- The state after a call whose callee does not return: an error, at the next instruction. -/
def junkAt (s : Arm.ArmState) : Arm.ArmState :=
  Arm.w .ERR (.Other "linked callee did not return") (Arm.w .PC (Arm.r .PC s + 4) s)

/-- The callee `a`, called at `s`, has returned in `t`: at the return address, without error,
with its own program. -/
def RetOf (a : Art) (s t : Arm.ArmState) : Prop :=
  Arm.r .PC t = Arm.r .PC s + 4 ∧ Arm.r .ERR t = .None ∧ t.program = a.fb.program a.base

open Classical in
/-- **A `bl` of the function compiled as `a`, run by the machine `M`**: from the callee's entry
state, the state at its return, with the caller's program (the return is unique: past it the
machine stops with an error, `retStuck`). -/
noncomputable def linkedCall (M : Arm.ArmState → Arm.ArmState) (a : Art) (s : Arm.ArmState) :
    Arm.ArmState :=
  if h : ∃ n, RetOf a s (runX M n (enterAt a s)) then
    Arm.set_program (runX M (Classical.choose h) (enterAt a s)) s.program
  else junkAt s

theorem wordsAt_find_none {base a : BitVec 64} :
    ∀ {ws : List (BitVec 32)} {k : Nat},
      (∀ j < ws.length, a ≠ base + BitVec.ofNat 64 (4 * (k + j))) → (wordsAt base k ws).find? a = none
  | [], _, _ => rfl
  | w :: ws, k, h => by
    simp only [wordsAt, Arm.Map.find?]
    rw [if_neg (fun e => h 0 (by simp) (by rw [← e]; simp))]
    exact wordsAt_find_none fun j hj => by
      have := h (j + 1) (by simp; omega)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this

/-- The program of the function `a` has no word at an address outside its code. -/
theorem program_find_none {a : Art} {ra : BitVec 64}
    (hra : ∀ k < a.fb.words.size, ra ≠ a.base + BitVec.ofNat 64 (4 * k)) :
    (a.fb.program a.base).find? ra = none :=
  wordsAt_find_none fun j hj => by simpa using hra j (by simpa using hj)

/-- No instruction of the laid-out function `fa` (laid out as `fb` at `base`) is at an address
outside its code. -/
theorem insnAt_none {fa : FnAsm} {fb : FnBin} {lm : Std.HashMap Lbl Nat} {base pc : BitVec 64}
    (hl : fa.layout = .ok fb) (hm : labelOffsets fa.lines = .ok lm)
    (hra : ∀ k < fb.words.size, pc ≠ base + BitVec.ofNat 64 (4 * k)) :
    insnAt fa base pc = none := by
  unfold insnAt
  rw [dif_neg]
  rintro ⟨j, i, t, hj, he⟩
  obtain ⟨h4, w, -, hw⟩ := FnAsm.layout_word hl hm hj rfl
  have hk := (Array.getElem?_eq_some_iff.mp hw).1
  exact hra _ hk (by rw [← he]; congr 2; omega)

theorem stepi_err {s : Arm.ArmState} (h : Arm.r .ERR s ≠ .None) : Arm.stepi s = s := by
  unfold Arm.stepi
  have h' : Arm.read_err s ≠ .None := h
  revert h'
  cases Arm.read_err s <;> simp

/-- **Past the return address the callee's machine stops with an error**: at a state with the
callee's program, no error and the pc outside the callee's code, the next step of the machine
`ArmStepX X H a.fa` errors, and an error state stays put. -/
theorem retStuck {X : ExtSem} {H : ArmHooks} {a : Art} {lm : Std.HashMap Lbl Nat}
    (hl : a.fa.layout = .ok a.fb) (hm : labelOffsets a.fa.lines = .ok lm)
    {t : Arm.ArmState} (hprog : t.program = a.fb.program a.base)
    (hra : ∀ k < a.fb.words.size, Arm.r .PC t ≠ a.base + BitVec.ofNat 64 (4 * k)) :
    ∀ n, Arm.r .ERR (runX (ArmStepX X H a.fa) (n + 1) t) ≠ .None := by
  have hins : ∀ u : Arm.ArmState, u.program = a.fb.program a.base → Arm.r .PC u = Arm.r .PC t →
      ArmStepX X H a.fa u = Arm.stepi u := by
    intro u hu hpc
    have hnone : insnAt a.fa (progBase u) (Arm.r .PC u) = none := by
      by_cases hw : a.fb.words.toList = []
      · unfold insnAt
        split
        · rename_i h
          obtain ⟨j, i, t', hj, -⟩ := h
          obtain ⟨-, w, -, hw'⟩ := FnAsm.layout_word hl hm hj rfl
          have := (Array.getElem?_eq_some_iff.mp hw').1
          simp only [Array.toList_eq_nil_iff] at hw
          simp [hw] at this
        · rfl
      · rw [progBase_eq (by rw [hu]; rfl) hw, hpc]
        exact insnAt_none hl hm hra
    simp only [ArmStepX, hnone]
  -- one step from an error-free state outside the code: an error
  have h1 : ∀ u : Arm.ArmState, u.program = a.fb.program a.base → Arm.r .PC u = Arm.r .PC t →
      Arm.r .ERR (ArmStepX X H a.fa u) ≠ .None := by
    intro u hu hpc
    rw [hins u hu hpc]
    by_cases he : Arm.r .ERR u = .None
    · unfold Arm.stepi
      simp only [Arm.read_err] at he ⊢
      rw [he]
      simp only
      have hf : Arm.fetch_inst (Arm.read_pc u) u = none := by
        unfold Arm.fetch_inst
        rw [hu]
        simp only [Arm.read_pc] at *
        rw [hpc]
        exact program_find_none hra
      rw [hf]
      simp [Arm.r, Arm.write_err, Arm.read_base_error, Arm.write_base_error]
    · rw [stepi_err he]; exact he
  -- the error state is a fixed point
  have hfix : ∀ u : Arm.ArmState, u.program = a.fb.program a.base → Arm.r .PC u = Arm.r .PC t →
      Arm.r .ERR u ≠ .None → ArmStepX X H a.fa u = u := fun u hu hpc he => by
    rw [hins u hu hpc, stepi_err he]
  have hstep1 : (ArmStepX X H a.fa t).program = a.fb.program a.base ∧
      Arm.r .PC (ArmStepX X H a.fa t) = Arm.r .PC t := by
    rw [hins t hprog rfl]
    by_cases he : Arm.r .ERR t = .None
    · unfold Arm.stepi
      simp only [Arm.read_err] at he ⊢
      rw [he]
      simp only
      have hf : Arm.fetch_inst (Arm.read_pc t) t = none := by
        unfold Arm.fetch_inst
        rw [hprog]
        exact program_find_none hra
      rw [hf]
      simp only [Arm.write_err]
      exact ⟨by rw [Arm.w_program]; exact hprog, Arm.r_of_w_different (by simp)⟩
    · rw [stepi_err he]; exact ⟨hprog, rfl⟩
  have hP : ∀ m, (runX (ArmStepX X H a.fa) (m + 1) t).program = a.fb.program a.base ∧
      Arm.r .PC (runX (ArmStepX X H a.fa) (m + 1) t) = Arm.r .PC t ∧
      Arm.r .ERR (runX (ArmStepX X H a.fa) (m + 1) t) ≠ .None := by
    intro m
    induction m with
    | zero => exact ⟨hstep1.1, hstep1.2, h1 t hprog rfl⟩
    | succ m ih =>
      have e : runX (ArmStepX X H a.fa) (m + 1 + 1) t =
          ArmStepX X H a.fa (runX (ArmStepX X H a.fa) (m + 1) t) := by
        rw [runX_add _ (m + 1) 1]; rfl
      rw [e, hfix _ ih.1 ih.2.1 ih.2.2]
      exact ih
  exact fun n => (hP n).2.2

/-- **The linked call returns where the per-function theorem says**: a return (`RetOf`) of the
callee's machine at step `n`, with the return address outside the callee's code, is the one
`linkedCall` takes. -/
theorem linkedCall_eq {X : ExtSem} {H : ArmHooks} {a : Art} {lm : Std.HashMap Lbl Nat}
    (hl : a.fa.layout = .ok a.fb) (hm : labelOffsets a.fa.lines = .ok lm) {s : Arm.ArmState}
    (hra : ∀ k < a.fb.words.size, Arm.r .PC s + 4 ≠ a.base + BitVec.ofNat 64 (4 * k)) {n : Nat}
    (hret : RetOf a s (runX (ArmStepX X H a.fa) n (enterAt a s))) :
    linkedCall (ArmStepX X H a.fa) a s =
      Arm.set_program (runX (ArmStepX X H a.fa) n (enterAt a s)) s.program := by
  have hex : ∃ n, RetOf a s (runX (ArmStepX X H a.fa) n (enterAt a s)) := ⟨n, hret⟩
  unfold linkedCall
  rw [dif_pos hex]
  have hm' := Classical.choose_spec hex
  generalize Classical.choose hex = m at hm' ⊢
  -- the return is unique: past one, the machine has an error
  have huniq : ∀ i j, RetOf a s (runX (ArmStepX X H a.fa) i (enterAt a s)) →
      RetOf a s (runX (ArmStepX X H a.fa) j (enterAt a s)) → ¬ i < j := by
    intro i j hi hj hlt
    have := retStuck (X := X) (H := H) hl hm hi.2.2 (by rw [hi.1]; exact hra)
      (j - i - 1)
    rw [← runX_add, show i + (j - i - 1 + 1) = j by omega] at this
    exact this hj.2.1
  have : m = n := by
    rcases Nat.lt_trichotomy m n with h | h | h
    · exact absurd h (huniq m n hm' hret)
    · exact h
    · exact absurd h (huniq n m hret hm')
  rw [this]

/-! ## The linked system -/

/-- **A linked program**: the functions `P` with their compiled images `A`; the base
environment (`base`: the CLIF semantics of the externs outside `P`; `Xb`, `Hb`: their machine
semantics and hooks, the link-time symbols and TLS); the link-time symbol addresses `syms`; the
addresses `F` outside the world of every activation (the entry activation's frame and its
callees' stack, the program's code); the code image (addresses `Img` holding `imgMem`); a return
address `raStar` outside all code (for the canonical call state); and the stack `D` one call
level may use. -/
structure LinkSys where
  P : Clif.Program
  A : Clif.Function → Art
  base : Clif.Env
  Xb : ExtSem
  Hb : ArmHooks
  syms : String → Option Nat
  F : BitVec 64 → Prop
  Img : BitVec 64 → Prop
  imgMem : Arm.Memory
  raStar : BitVec 64
  D : Nat

namespace LinkSys

variable (L : LinkSys)

/-- The callees' stack budget of an activation at level `M`. -/
def K (M : Nat) : Nat := L.D * M

/-- The call hook of the linked machine: a `bl` of a function `g` of `P` runs `pc g`; externs
outside `P` and `blr`: the base hook. -/
def callHook (Hb : ArmHooks) (P : Clif.Program) (pc : Clif.Function → Arm.ArmState → Arm.ArmState)
    (d : Option String) (s : Arm.ArmState) : Arm.ArmState :=
  match d with
  | some n => (match P.func? n with
    | some g => pc g s
    | none => Hb.call d s)
  | none => Hb.call none s

/-- **The hooks of the linked machine**, by depth: at depth `M + 1` a `bl` of a function `g` of
`P` runs `g`'s code by the machine with the hooks of depth `M` (`linkedCall`); at depth `0` it
gives an error state. Externs outside `P`, `blr` and TLS: the base hooks. -/
noncomputable def hooks : Nat → ArmHooks
  | 0 => ⟨callHook L.Hb L.P (fun _ s => junkAt s), L.Hb.tls⟩
  | M + 1 => ⟨callHook L.Hb L.P (fun g s => linkedCall (ArmStepX L.Xb (hooks M) (L.A g).fa) (L.A g) s),
      L.Hb.tls⟩

/-- The machine of an activation of `g` at depth `M`. -/
noncomputable def mach (M : Nat) (g : Clif.Function) : Arm.ArmState → Arm.ArmState :=
  ArmStepX L.Xb (L.hooks M) (L.A g).fa

end LinkSys

/-- The registers of the register-passed parameters of a signature, in order. -/
def regLocs (sig : Clif.Signature) : List Reg :=
  (locsOf sig).filterMap fun l => match l with
    | .reg r => some r
    | .stack _ => none

/-- `s` with the values `uses` in the registers `rs`. -/
def placeArgs (rs : List Reg) (uses : List CV) (s : Arm.ArmState) : Arm.ArmState :=
  (rs.zip uses).foldl (fun s p => setReg s p.1 p.2) s

namespace LinkSys

variable (L : LinkSys)

open Classical in
/-- `w` with the code image. -/
noncomputable def withImg (w : Arm.ArmState) : Arm.ArmState :=
  setMem w fun a => if L.Img a then L.imgMem a else w.mem a

/-- **The canonical state of a call** of `g` with arguments `uses` from the world `w`: `w` with
the arguments in `g`'s parameter registers, the code image, and the pc before `raStar`. -/
noncomputable def canon (g : Clif.Function) (uses : List CV) (w : Arm.ArmState) : Arm.ArmState :=
  Arm.w .PC (L.raStar - 4) (placeArgs (regLocs g.sig) uses (L.withImg w))

/-- When the external semantics at depth `M` defines a call of `g` from world `w`: the callee's
stack (its frame and its callees' budget) fits below `sp` outside the world and the code, no
error, and the call's arguments and the world are related to CLIF arguments and memory on which
`g`'s whole-program run returns within `M` steps. -/
def Cond (M : Nat) (g : Clif.Function) (uses : List CV) (w : Arm.ArmState) : Prop :=
  0 < M ∧ Arm.r .ERR w = .None ∧ (spv w).toNat % 16 = 0 ∧
  frameDrop (L.A g).af + L.K (M - 1) ≤ (spv w).toNat ∧
  (∀ a, StackBelow (frameDrop (L.A g).af + L.K (M - 1)) (spv w) a → L.F a ∧ ¬ L.Img a) ∧
  ∃ vals cm cs rvals cm', MemRel L.F L.syms cm w ∧ ArgsAt g.sig vals uses w ∧
    Clif.initState L.P g.name vals cm = .ok cs ∧ Clif.runLoop L.base L.P M cs = .returned rvals cm'

open Classical in
/-- **The external semantics of an activation at depth `M`**: a call of a function `g` of `P`
gives the results (x0.., one per ABI return) and world of the linked machine's call of `g` from
the canonical state, when `Cond` holds and that call returned; the rest is the base's. -/
noncomputable def X (M : Nat) : ExtSem where
  call d uses w := match d with
    | some n => (match L.P.func? n with
      | some g =>
        if L.Cond M g uses w ∧ Arm.r .ERR ((L.hooks M).call (some n) (L.canon g uses w)) = .None then
          some ((List.range (sigRets g.sig).length).map fun j =>
              regVal ((L.hooks M).call (some n) (L.canon g uses w)) (.x j),
            (L.hooks M).call (some n) (L.canon g uses w))
        else none
      | none => L.Xb.call d uses w)
    | none => L.Xb.call none uses w
  sym := L.Xb.sym
  tp := L.Xb.tp
  tlsFlags := L.Xb.tlsFlags

/-- The machine only uses the symbols of the external semantics. -/
theorem armStepX_X (M : Nat) (H : ArmHooks) (fa : FnAsm) :
    ArmStepX (L.X M) H fa = ArmStepX L.Xb H fa := rfl

end LinkSys

/-! ## CLIF helpers -/

/-- A returning run never reaches a trapping step. -/
theorem reach_not_trapped {env : Clif.Env} {p : Clif.Program} :
    ∀ {fuel : Nat} {cs : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem},
      Clif.runLoop env p fuel cs = .returned vals cm → ∀ {s : Clif.State}, Reach env p cs s →
      ∀ c, Clif.step env p s ≠ .trapped c := by
  intro fuel cs vals cm hrun s hr
  induction hr generalizing fuel with
  | refl s =>
    intro c hc
    cases fuel with
    | zero => cases hrun
    | succ n => rw [Clif.runLoop_succ, hc] at hrun; cases hrun
  | step hs _ ih =>
    cases fuel with
    | zero => cases hrun
    | succ n =>
      rw [Clif.runLoop_succ, hs] at hrun
      exact ih hrun

/-- **A returning run satisfies the run premises** (`TrapsExplicit`) when the entered function
has no indirect calls (`LinkFree`). -/
theorem trapsExplicit_of_returned {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    (hfree : Clif.LinkFree cs.frame.func) {fuel : Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned vals cm) : TrapsExplicit env p cs where
  stmt := fun s c _ _ hr hs _ => absurd hs (reach_not_trapped hrun hr c)
  tryCall := fun s c _ _ _ hr hs _ _ => absurd hs (reach_not_trapped hrun hr c)
  tryCallInd := fun s c _ _ _ hr hs _ _ => absurd hs (reach_not_trapped hrun hr c)
  indirect := fun _ st _ sig callee args _ _ hi ⟨B, hB, hst⟩ =>
    absurd hi ((hfree B hB).1 st hst sig callee args)
  tryIndirect := fun _ callee args et _ _ _ ⟨B, hB, e⟩ =>
    absurd e ((hfree B hB).2.1 callee args et)

/-- The entry state of a function without stack slots: no slots, the memory unchanged. -/
theorem initState_noSlots {P : Clif.Program} {h : Clif.Function} {n : String}
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} (hf : P.func? n = some h)
    (hs : h.slots = []) (hi : Clif.initState P n vals cm = .ok cs) :
    cs.frame.slots = [] ∧ cs.mem = cm := by
  simp only [Clif.initState, hf, Clif.Res.ofOption_some, Clif.Res.ok_bind] at hi
  cases he : Clif.enterFunc h vals cm with
  | ok r =>
    rw [he] at hi
    obtain ⟨fr, mem'⟩ := r
    simp only [Clif.Res.ok_bind, Clif.Res.pure_eq, Clif.Res.ok.injEq] at hi
    subst hi
    obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok he
    rw [hs] at hal
    simp only [Opt.allocSlots, List.foldl_nil, Prod.mk.injEq] at hal
    exact ⟨hal.1.symm, hal.2.symm⟩
  | trap => rw [he] at hi; cases hi
  | stuck => rw [he] at hi; cases hi

/-! ## The premises and the induction statement -/

/-- The destination of a call as the hooks see it (`bl name`: `some name`; `blr`: `none`). -/
def destOf (info : CallInfo) : Option String :=
  match info.dest with
  | .sym n => some n
  | .reg _ => none

namespace LinkSys

variable (L : LinkSys)

/-- A call outside `P` (an extern of the base environment, or `blr`). -/
def BaseDest (d : Option String) : Prop := d = none ∨ ∃ n, d = some n ∧ L.P.func? n = none

/-- A call site of `g`'s compiled code calling the function `h` of `P`. -/
def ProgSite (g : Clif.Function) (info : CallInfo) (h : Clif.Function) : Prop :=
  (L.A g).vcp.CallSite info ∧ ∃ n, info.dest = .sym n ∧ L.P.func? n = some h

/-- **The premises of the linked program** (`backend_correct_program`): the program and its
compilation, the scope of this layer, the link layout, and the base environment's contracts. -/
structure Ok : Prop where
  /-- distinct names, no `call_indirect`/`try_call_indirect`/`return_call` -/
  linkable : Linkable L.P
  subset : ∀ g ∈ L.P.funcs, InSubset (L.P.only g) g
  compiled : ∀ g ∈ L.P.funcs, Compiled g (L.A g).k (L.A g).vc (L.A g).vcp (L.A g).rf
    (L.A g).af (L.A g).fa (L.A g).fb
  covered : ∀ g ∈ L.P.funcs, FormsCovered ⟨(L.A g).fa.k, (L.A g).af.slotBase⟩ (L.A g).vcp
  /-- scope: no `try_call` -/
  noTry : ∀ g ∈ L.P.funcs, ∀ B ∈ g.blocks, B.term.isTry = false
  /-- scope: no stack-passed call arguments (no outgoing-argument area) -/
  noOut : ∀ g ∈ L.P.funcs, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase = 0
  /-- scope: parameters in registers (distinct argument registers), no `sret` -/
  regParams : ∀ g ∈ L.P.funcs, ∀ l ∈ locsOf g.sig, ∃ r, l = .reg r
  argRegs : ∀ g ∈ L.P.funcs, (regLocs g.sig).Nodup ∧ ∀ r ∈ regLocs g.sig, r.isArgReg = true
  noSret : ∀ g ∈ L.P.funcs, g.sig.params.any (·.purpose == .sret) = false
  /-- scope: the functions called from `P` have no stack slots (their frame is the allocator's) -/
  calleeSlots : ∀ g ∈ L.P.funcs, ∀ info h, L.ProgSite g info h → h.slots = [] ∧
    (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize
  /-- scope: a call of a function `h` of `P` passes integer arguments in `h`'s parameter
  registers and takes the results from x0.. (checked per call site) -/
  callRegs : ∀ g ∈ L.P.funcs, ∀ info h, L.ProgSite g info h →
    ∃ n Lu Ld, info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧ Lu.map (·.2) = regLocs h.sig ∧
      Ld.map (·.1) = (List.range (sigRets h.sig).length).map Reg.x
  /-- the entry `Args` reads parameter registers -/
  entryRegs : ∀ g ∈ L.P.funcs, ∀ r, (L.A g).vcp.EntryArg r → r ∈ regLocs g.sig
  /-- layout: every function's words fit at its base -/
  fits : ∀ g ∈ L.P.funcs, (L.A g).base.toNat + 4 * (L.A g).fb.words.size ≤ 2 ^ 64
  /-- layout: the code image (`Img`, holding `imgMem`) contains every function's words -/
  imgAddr : ∀ g ∈ L.P.funcs, ∀ a, CodeAddr (Arm.set_program Arm.ArmState.default
    ((L.A g).fb.program (L.A g).base)) a → L.Img a
  imgCode : ∀ g ∈ L.P.funcs, ∀ t : Arm.ArmState, (∀ a, L.Img a → t.mem a = L.imgMem a) →
    ∀ k w, (L.A g).fb.words[k]? = some w →
      Arm.read_mem_bytes 4 ((L.A g).base + BitVec.ofNat 64 (4 * k)) t = w
  /-- the code is outside every activation's world -/
  imgF : ∀ a, L.Img a → L.F a
  /-- layout: the return address of a call is not in the callee's code -/
  raCall : ∀ g ∈ L.P.funcs, ∀ h ∈ L.P.funcs, ∀ pc, CallPc (L.A g).fa (L.A g).base pc →
    ∀ k < (L.A h).fb.words.size, pc + 4 ≠ (L.A h).base + BitVec.ofNat 64 (4 * k)
  raStar : ∀ h ∈ L.P.funcs, ∀ k < (L.A h).fb.words.size,
    L.raStar ≠ (L.A h).base + BitVec.ofNat 64 (4 * k)
  /-- the stack of one call level -/
  depth : ∀ g ∈ L.P.funcs, frameDrop (L.A g).af ≤ L.D
  /-- the base environment: symbols, the contracts of the calls outside `P` (at the program's
  call sites), the CLIF contract of the base externs, TLS -/
  symOk : ∀ n b, L.syms n = some b → L.Xb.sym n 0 = BitVec.ofNat 64 b
  baseOs : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → L.BaseDest (destOf info) →
    ∀ F K G s0 Pc ctx, CallSoundCtlG F K G s0 Pc (callExec L.Hb) (csem F ctx L.Xb) (.call info) .next
  basePc : ∀ d s, L.BaseDest d → Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
    Arm.r .PC (L.Hb.call d s) = Arm.r .PC s + 4
  baseExt : ∀ d uses w outs w', L.BaseDest d → L.Xb.call d uses w = some (outs, w') →
    Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program
  baseX : ∀ g ∈ L.P.funcs, ∀ F slotOff out c, XCallsOk L.base
    ((g.externs.map (·.2)).filter fun e => (L.P.func? e.name).isNone)
    (RelW ⟨F, L.syms, slotOff, out⟩ g c) L.Xb
  baseTls : ∀ g ∈ L.P.funcs, hasTls g = true → ∀ F K, TlsOk F K L.Xb L.Hb

/-- **The machine side of an activation of `g` at depth `M`** entered in `s` with body-entry
world `w₀`: the ABI entry, the stack (frame and the callees' budget `K M`), the addresses `G` it
keeps (outside its stack; containing the code image, which `s` holds), the addresses outside
its world are `F`, and `w₀` agrees with `s`. -/
structure MachEntry (M : Nat) (g : Clif.Function) (G : BitVec 64 → Prop) (ra : BitVec 64)
    (s w₀ : Arm.ArmState) : Prop where
  abi : AbiEntry (L.A g).fb (L.A g).base ra s
  stack : StackAvail (L.K M) (L.A g).af s
  gfree : ∀ a, G a → ¬ StackBelow (frameDrop (L.A g).af + L.K M) (spv s) a
  hF : frameWG (L.K M) (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase
    (RAFrame.compute (L.A g).vcp (L.A g).rf).size (L.A g).af G s = L.F
  imgG : ∀ a, L.Img a → G a
  imgS : ∀ a, L.Img a → s.mem a = L.imgMem a
  body : BodyEntryW L.F (L.A g).vcp.EntryArg (L.A g).af s w₀

/-- **The world side of an activation of `g` at depth `M`**: the CLIF entry state on `vals`
related to the body-entry world `w₀` (`RelW` with the body's `sp`), the arguments where the body
reads them, and the callees' dead stack below the body's `sp` fits and lies outside the world
and the code. -/
structure WorldEntry (M : Nat) (g : Clif.Function) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) : Prop where
  clif : ClifEntry g vals cs
  rel : RelW ⟨L.F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
    g (spv w₀) cs.frame.slots cs.mem w₀
  args : ArgsAtEntry L.F g.sig vals w₀
  room : L.K M ≤ (spv w₀).toNat
  dead : ∀ a, StackBelow (L.K M) (spv w₀) a → L.F a ∧ ¬ L.Img a
  align : (spv w₀).toNat % 16 = 0

/-- **The linking statement at depth `M`**: for every function `g` of `P` and every world-side
activation whose per-function run (program callees running at most `M` steps) returns, one VCode
outcome that every machine-side activation at depth `M` realises. -/
def Thm (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (vals : List Clif.Val) (cs : Clif.State) (w₀ : Arm.ArmState) (fuel : Nat)
    (rvals : List Clif.Val) (cm' : Clif.Mem), L.WorldEntry M g vals cs w₀ →
    Clif.runLoop (Clif.linkEnvN L.P L.base M) (L.P.only g) fuel cs = .returned rvals cm' →
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
      us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel L.F L.syms cm' wf ∧
      ∀ G ra s, L.MachEntry M g G ra s w₀ →
        ∃ n, ActRet ra L.F G us outs wf s (runX (L.mach M g) n s)

end LinkSys

end E2E
