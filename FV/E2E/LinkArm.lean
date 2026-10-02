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

/-! ## Stack and frame arithmetic -/

theorem off_toNat (a sp : BitVec 64) (D : Nat) (hD : D ≤ sp.toNat) :
    ((a - (sp - BitVec.ofNat 64 D)).toNat < D ↔ a.toNat < sp.toNat ∧ sp.toNat ≤ a.toNat + D) ∧
    (a.toNat < (sp - BitVec.ofNat 64 D).toNat ↔ a.toNat < sp.toNat - D) ∧
    (sp - BitVec.ofNat 64 D).toNat = sp.toNat - D := by
  have hsp := sp.isLt
  have ha := a.isLt
  have hB : (sp - BitVec.ofNat 64 D).toNat = sp.toNat - D := by
    rw [BitVec.toNat_sub_of_le] <;> simp only [BitVec.le_def, BitVec.toNat_ofNat] <;>
      rw [Nat.mod_eq_of_lt (by omega)] <;> omega
  refine ⟨?_, by rw [hB], hB⟩
  rw [BitVec.toNat_sub, hB]
  rcases Nat.lt_or_ge a.toNat (sp.toNat - D) with h | h
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - (sp.toNat - D) + a.toNat = (a.toNat - (sp.toNat - D)) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem frameWG_noSlots {K : Nat} {af : AFunc} {G : BitVec 64 → Prop} {u : Arm.ArmState}
    {a : BitVec 64} (hfr : af.frame = true) (hroom : af.frameSize + 16 + K ≤ (spv u).toNat) :
    frameWG K 0 af.frameSize af G u a ↔
      StackBelow (af.frameSize + 16 + K) (spv u) a ∨ CodeAddr u a ∨ G a := by
  have hd : frameDrop af = af.frameSize + 16 := by simp [frameDrop, hfr]
  obtain ⟨h1, h2, h3⟩ := off_toNat a (spv u) (af.frameSize + 16) (by omega)
  simp only [frameWG, frameW, frameF, StackBelow, hd]
  constructor
  · rintro (((⟨-, h⟩ | ⟨-, h⟩ | hc) | ⟨hl, hr⟩) | hg)
    · exact .inl (by have := h1.1 (by omega); omega)
    · exact .inl (by have := h1.1 h; omega)
    · exact .inr (.inl hc)
    · rw [h3] at hr; exact .inl (by have := h2.1 hl; omega)
    · exact .inr (.inr hg)
  · rintro (⟨hl, hr⟩ | hc | hg)
    · by_cases hb : a.toNat < (spv u).toNat - (af.frameSize + 16)
      · exact .inl (.inr ⟨h2.2 hb, by rw [h3]; omega⟩)
      · have := h1.2 ⟨hl, by omega⟩
        by_cases hs : (a - (spv u - BitVec.ofNat 64 (af.frameSize + 16))).toNat < af.frameSize
        · exact .inl (.inl (.inl ⟨Nat.zero_le _, hs⟩))
        · exact .inl (.inl (.inr (.inl ⟨by omega, this⟩)))
    · exact .inl (.inl (.inr (.inr hc)))
    · exact .inr hg

/-- No code in the `n` bytes below `sp` gives the stack room. -/
theorem stackRoom_of {n : Nat} {u : Arm.ArmState} (hn : n ≤ (spv u).toNat)
    (hc : ∀ a, CodeAddr u a → ¬ StackBelow n (spv u) a) : StackRoom n u := by
  refine ⟨hn, fun a ha => ?_⟩
  have := (off_toNat a (spv u) n hn).1
  apply Classical.byContradiction
  intro hlt
  exact hc a ha (this.1 (by omega))

/-! ## Entering a callee, the canonical state -/

theorem r_enterAt (a : Art) (u : Arm.ArmState) {f : Arm.StateField} (h1 : f ≠ .PC)
    (h2 : f ≠ .GPR 30#5) : Arm.r f (enterAt a u) = Arm.r f u := by
  simp only [enterAt]
  rw [Arm.r_of_w_different h1, Arm.r_of_w_different h2, r_set_program]

@[simp] theorem pc_enterAt (a : Art) (u : Arm.ArmState) : Arm.r .PC (enterAt a u) = a.base := by
  simp only [enterAt, Arm.r_of_w_same]

theorem x30_enterAt (a : Art) (u : Arm.ArmState) : xreg 30 (enterAt a u) = Arm.r .PC u + 4 := by
  simp only [enterAt, xreg]
  rw [Arm.r_of_w_different (by simp)]
  exact Arm.r_of_w_same

@[simp] theorem mem_enterAt (a : Art) (u : Arm.ArmState) : (enterAt a u).mem = u.mem := by
  simp only [enterAt]
  exact Arm.mem_w_of_mem_eq (Arm.mem_w_of_mem_eq rfl _ _) _ _

@[simp] theorem program_enterAt (a : Art) (u : Arm.ArmState) :
    (enterAt a u).program = a.fb.program a.base := by
  simp only [enterAt, Arm.w_program, program_set_program]

theorem spv_enterAt (a : Art) (u : Arm.ArmState) : spv (enterAt a u) = spv u :=
  r_enterAt a u (by simp) (by simp)

theorem regVal_enterAt (a : Art) (u : Arm.ArmState) {r : Reg} (hr : r.isArgReg = true) :
    regVal (enterAt a u) r = regVal u r := by
  cases r with
  | x n =>
    simp only [Reg.isArgReg, decide_eq_true_eq] at hr
    simp only [regVal]
    rw [r_enterAt a u (by simp) (fun e => by
      have := congrArg (fun f => match f with | Arm.StateField.GPR i => i.toNat | _ => 0) e
      simp [rnum_toNat (show n < 32 by omega)] at this; omega)]
  | v n => simp only [regVal]; rw [r_enterAt a u (by simp) (by simp)]
  | _ => simp [Reg.isArgReg] at hr

theorem r_withImg (L : LinkSys) (w : Arm.ArmState) (f : Arm.StateField) :
    Arm.r f (L.withImg w) = Arm.r f w := r_setMem f w _

open Classical in
theorem mem_withImg (L : LinkSys) (w : Arm.ArmState) (a : BitVec 64) :
    (L.withImg w).mem a = if L.Img a then L.imgMem a else w.mem a := by
  classical
  simp only [LinkSys.withImg, mem_setMem]

@[simp] theorem program_withImg (L : LinkSys) (w : Arm.ArmState) :
    (L.withImg w).program = w.program := rfl

/-- The value a register holds after `setReg` (an X register keeps 64 bits). -/
def setVal : Reg → CV → CV
  | .x _, v => ofX (lo64 v)
  | _, v => v

theorem regVal_setReg_same {s : Arm.ArmState} {r : Reg} {v : CV} (hr : r.isArgReg = true) :
    regVal (setReg s r v) r = setVal r v := by
  cases r with
  | x n => simp [regVal, setVal, Arm.r_of_w_same, ofX]
  | v n => simp [regVal, setVal, Arm.r_of_w_same]
  | _ => simp [Reg.isArgReg] at hr

theorem regVal_setReg_ne {s : Arm.ArmState} {r r' : Reg} {v : CV} (hr : r.isArgReg = true)
    (hr' : r'.isArgReg = true) (hne : r ≠ r') : regVal (setReg s r' v) r = regVal s r := by
  cases r <;> cases r' <;> simp only [Reg.isArgReg, decide_eq_true_eq] at hr hr' <;>
    (try simp at hr) <;> (try simp at hr')
  · rename_i n m
    simp only [setReg_x, regVal]
    rw [Arm.r_of_w_different]
    intro e
    injection e with e
    exact rnum_ne (by omega) (by omega) (fun h => hne (by rw [h])) e
  · simp only [setReg_v, regVal]; rw [Arm.r_of_w_different (by simp)]
  · simp only [setReg_x, regVal]; rw [Arm.r_of_w_different (by simp)]
  · rename_i n m
    simp only [setReg_v, regVal]
    rw [Arm.r_of_w_different]
    intro e
    injection e with e
    exact rnum_ne (by omega) (by omega) (fun h => hne (by rw [h])) e

theorem r_setReg {s : Arm.ArmState} {r : Reg} {v : CV} (hr : r.isArgReg = true)
    {f : Arm.StateField} (hf : ¬ Masked f) : Arm.r f (setReg s r v) = Arm.r f s := by
  cases r with
  | x n =>
    simp only [Reg.isArgReg, decide_eq_true_eq] at hr
    simp only [setReg_x]
    exact Arm.r_of_w_different (fun e => hf (by subst e; exact Masked_gpr (by omega) (by omega)))
  | v n =>
    simp only [setReg_v]
    exact Arm.r_of_w_different (fun e => hf (by subst e; trivial))
  | _ => rfl

theorem mem_setReg (s : Arm.ArmState) (r : Reg) (v : CV) : (setReg s r v).mem = s.mem := by
  cases r <;> simp only [setReg] <;> first | rfl | exact Arm.mem_w_of_mem_eq rfl _ _

theorem program_setReg (s : Arm.ArmState) (r : Reg) (v : CV) :
    (setReg s r v).program = s.program := by
  cases r <;> simp only [setReg] <;> first | rfl | exact Arm.w_program

theorem placeArgs_cons (r : Reg) (rs : List Reg) (u : CV) (us : List CV) (s : Arm.ArmState) :
    placeArgs (r :: rs) (u :: us) s = placeArgs rs us (setReg s r u) := rfl

theorem placeArgs_nil_left (us : List CV) (s : Arm.ArmState) : placeArgs [] us s = s := rfl

theorem placeArgs_nil_right (rs : List Reg) (s : Arm.ArmState) : placeArgs rs [] s = s := by
  cases rs <;> rfl

theorem placeArgs_r : ∀ (rs : List Reg) (us : List CV) (s : Arm.ArmState),
    (∀ r ∈ rs, r.isArgReg = true) → ∀ f, ¬ Masked f → Arm.r f (placeArgs rs us s) = Arm.r f s
  | [], _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _ => by rw [placeArgs_nil_right]
  | r :: rs, u :: us, s, h, f, hf => by
    rw [placeArgs_cons, placeArgs_r rs us _ (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) f hf,
      r_setReg (h r (List.mem_cons_self ..)) hf]

theorem placeArgs_mem : ∀ (rs : List Reg) (us : List CV) (s : Arm.ArmState),
    (placeArgs rs us s).mem = s.mem
  | [], _, _ => rfl
  | _ :: _, [], _ => by rw [placeArgs_nil_right]
  | r :: rs, u :: us, s => by rw [placeArgs_cons, placeArgs_mem rs us, mem_setReg]

theorem placeArgs_program : ∀ (rs : List Reg) (us : List CV) (s : Arm.ArmState),
    (placeArgs rs us s).program = s.program
  | [], _, _ => rfl
  | _ :: _, [], _ => by rw [placeArgs_nil_right]
  | r :: rs, u :: us, s => by rw [placeArgs_cons, placeArgs_program rs us, program_setReg]

theorem placeArgs_regVal_ne : ∀ (rs : List Reg) (us : List CV) (s : Arm.ArmState) {r : Reg},
    (∀ r' ∈ rs, r'.isArgReg = true) → r.isArgReg = true → r ∉ rs →
      regVal (placeArgs rs us s) r = regVal s r
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _, _ => by rw [placeArgs_nil_right]
  | r0 :: rs, u :: us, s, r, h, hr, hn => by
    rw [placeArgs_cons, placeArgs_regVal_ne rs us _ (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
      hr (fun h' => hn (List.mem_cons_of_mem _ h')),
      regVal_setReg_ne hr (h r0 (List.mem_cons_self ..)) (fun e => hn (e ▸ List.mem_cons_self ..))]

theorem placeArgs_regVal : ∀ (rs : List Reg) (us : List CV) (s : Arm.ArmState) {j : Nat} {r : Reg}
    {u : CV}, rs.Nodup → (∀ r' ∈ rs, r'.isArgReg = true) → rs[j]? = some r → us[j]? = some u →
      regVal (placeArgs rs us s) r = setVal r u
  | [], _, _, _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, _, _, h => by simp at h
  | r0 :: rs, u0 :: us, s, j, r, u, hnd, harg, hr, hu => by
    rw [placeArgs_cons]
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr hu
      subst hr hu
      rw [placeArgs_regVal_ne rs us _ (fun r' hr' => harg r' (List.mem_cons_of_mem _ hr'))
        (harg _ (List.mem_cons_self ..)) (List.nodup_cons.mp hnd).1,
        regVal_setReg_same (harg _ (List.mem_cons_self ..))]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hr hu
      exact placeArgs_regVal rs us _ (List.nodup_cons.mp hnd).2
        (fun r' hr' => harg r' (List.mem_cons_of_mem _ hr')) hr hu

theorem vHolds_setVal {v : Clif.Val} {r : Reg} {u : CV} (hw : v.ty.width ≤ 64) (h : VHolds v u) :
    VHolds v (setVal r u) := by
  cases r with
  | x n =>
    simp only [setVal, VHolds, ofX, lo64] at h ⊢
    rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_setWidth_of_le _ hw]
    exact h
  | _ => exact h

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
  argRegs : ∀ g ∈ L.P.funcs, (regLocs g.sig).Nodup ∧ (∀ r ∈ regLocs g.sig, r.isArgReg = true) ∧
    ∀ p ∈ g.sig.params, p.ty.width ≤ 64
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

/-! ## The callee's body-entry world, the canonical call state -/

/-- The body-entry world of an activation entered in `u` that agrees with `u` (`BodyEntry`):
`sp` lowered by the frame, the frame pointer set. -/
def bodyOf (af : AFunc) (u : Arm.ArmState) : Arm.ArmState :=
  Arm.w (.GPR 29#5) (if af.frame then spv u - 16#64 else xreg 29 u)
    (Arm.w (.GPR 31#5) (spv u - BitVec.ofNat 64 (frameDrop af)) u)

theorem spv_bodyOf (af : AFunc) (u : Arm.ArmState) :
    spv (bodyOf af u) = spv u - BitVec.ofNat 64 (frameDrop af) := by
  simp only [bodyOf, spv]
  rw [Arm.r_of_w_different (by simp), Arm.r_of_w_same]

theorem x29_bodyOf (af : AFunc) (u : Arm.ArmState) :
    xreg 29 (bodyOf af u) = if af.frame then spv u - 16#64 else xreg 29 u := by
  simp only [bodyOf, xreg]
  exact Arm.r_of_w_same

theorem r_bodyOf (af : AFunc) (u : Arm.ArmState) {f : Arm.StateField} (h29 : f ≠ .GPR 29#5)
    (h31 : f ≠ .GPR 31#5) : Arm.r f (bodyOf af u) = Arm.r f u := by
  simp only [bodyOf]
  rw [Arm.r_of_w_different h29, Arm.r_of_w_different h31]

@[simp] theorem mem_bodyOf (af : AFunc) (u : Arm.ArmState) : (bodyOf af u).mem = u.mem :=
  Arm.mem_w_of_mem_eq (Arm.mem_w_of_mem_eq rfl _ _) _ _

@[simp] theorem program_bodyOf (af : AFunc) (u : Arm.ArmState) :
    (bodyOf af u).program = u.program := by
  simp only [bodyOf, Arm.w_program]

theorem argReg_ne29 {r : Reg} (hr : r.isArgReg = true) {f : Arm.StateField} (hf : r.field = some f) :
    f ≠ .GPR 29#5 ∧ f ≠ .GPR 31#5 ∧ f ≠ .GPR 30#5 ∧ f ≠ .PC := by
  cases r with
  | x n =>
    simp only [Reg.isArgReg, decide_eq_true_eq] at hr
    simp only [Reg.field, Option.some.injEq] at hf
    subst hf
    have h : ∀ m, 8 < m → m < 32 → Arm.StateField.GPR (rnum n) ≠ .GPR (BitVec.ofNat 5 m) :=
      fun m h1 h2 e => rnum_ne (a := n) (b := m) (by omega) h2 (by omega) (Arm.StateField.GPR.inj e)
    exact ⟨h 29 (by omega) (by omega), h 31 (by omega) (by omega), h 30 (by omega) (by omega),
      by simp⟩
  | v n =>
    simp only [Reg.field, Option.some.injEq] at hf
    subst hf
    simp
  | _ => simp [Reg.isArgReg] at hr

theorem regVal_eq_of_field {s t : Arm.ArmState} {r : Reg} (hr : r.isArgReg = true)
    (h : ∀ f, r.field = some f → Arm.r f s = Arm.r f t) : regVal s r = regVal t r := by
  cases r with
  | x n => simp only [regVal]; rw [h _ rfl]
  | v n => simp only [regVal]; rw [h _ rfl]
  | _ => simp [Reg.isArgReg] at hr

theorem regVal_bodyOf (af : AFunc) (u : Arm.ArmState) {r : Reg} (hr : r.isArgReg = true) :
    regVal (bodyOf af u) r = regVal u r :=
  regVal_eq_of_field hr fun f hf => r_bodyOf af u (argReg_ne29 hr hf).1 (argReg_ne29 hr hf).2.1

namespace LinkSys

variable (L : LinkSys)

theorem r_canon {g : Clif.Function} (hg : ∀ r ∈ regLocs g.sig, r.isArgReg = true) (uses : List CV)
    (w : Arm.ArmState) {f : Arm.StateField} (hf : ¬ Masked f) :
    Arm.r f (L.canon g uses w) = Arm.r f w := by
  simp only [canon]
  rw [Arm.r_of_w_different (by rintro rfl; exact hf trivial), placeArgs_r _ _ _ hg f hf, r_withImg]

theorem mem_canon (g : Clif.Function) (uses : List CV) (w : Arm.ArmState) :
    (L.canon g uses w).mem = (L.withImg w).mem := by
  simp only [canon]
  exact Arm.mem_w_of_mem_eq (placeArgs_mem _ _ _) _ _

theorem program_canon (g : Clif.Function) (uses : List CV) (w : Arm.ArmState) :
    (L.canon g uses w).program = w.program := by
  simp only [canon, Arm.w_program, placeArgs_program, program_withImg]

theorem regVal_canon (g : Clif.Function) (uses : List CV) (w : Arm.ArmState) {r : Reg}
    (hr : r.isArgReg = true) :
    regVal (L.canon g uses w) r = regVal (placeArgs (regLocs g.sig) uses (L.withImg w)) r :=
  regVal_eq_of_field hr fun f hf => by
    simp only [canon]; rw [Arm.r_of_w_different (argReg_ne29 hr hf).2.2.2]

/-- A state from which a call of `g` (arguments `uses`, caller's world `w`) behaves as from the
canonical one: the same world, the code image, the same parameter registers, a return address
outside `g`'s code. -/
structure CallerOk (g : Clif.Function) (uses : List CV) (w t : Arm.ArmState) : Prop where
  world : SameWorld L.F t w
  img : ∀ a, L.Img a → t.mem a = L.imgMem a
  regs : ∀ r ∈ regLocs g.sig, regVal t r = regVal (L.canon g uses w) r
  ra : ∀ k < (L.A g).fb.words.size, Arm.r .PC t + 4 ≠ (L.A g).base + BitVec.ofNat 64 (4 * k)

theorem callerOk_canon (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs) (uses : List CV)
    (w : Arm.ArmState) : L.CallerOk g uses w (L.canon g uses w) := by
  have harg := (hL.argRegs g hg).2.1
  refine ⟨⟨fun f hf => L.r_canon harg uses w hf, fun a ha => ?_, L.program_canon g uses w⟩,
    fun a ha => ?_, fun _ _ => rfl, fun k hk => ?_⟩
  · rw [L.mem_canon, mem_withImg, if_neg (fun hi => ha (hL.imgF a hi))]
  · rw [L.mem_canon, mem_withImg, if_pos ha]
  · simp only [canon, Arm.r_of_w_same, BitVec.sub_add_cancel]
    exact hL.raStar g hg k hk

end LinkSys

/-! ## A call of a program function -/

theorem allReg_zip : ∀ (ls : List ArgLoc) (vs : List Clif.Val), (∀ l ∈ ls, ∃ r, l = .reg r) →
    ∀ {i : Nat} {r : Reg} {v : Clif.Val}, (ls.zip vs)[i]? = some (.reg r, v) →
      (ls.filterMap fun l => match l with | .reg r => some r | .stack _ => none)[i]? = some r ∧
      ((ls.zip vs).filterMap fun q => match q.1 with | .reg _ => some q.2 | .stack _ => none)[i]? =
        some v
  | [], _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | l :: ls, v0 :: vs, hall, i, r, v, h => by
    obtain ⟨r0, rfl⟩ := hall l (List.mem_cons_self ..)
    cases i with
    | zero =>
      simp only [List.zip_cons_cons, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq,
        ArgLoc.reg.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    | succ i =>
      simp only [List.zip_cons_cons, List.getElem?_cons_succ] at h
      simp only [List.filterMap_cons, List.zip_cons_cons, List.getElem?_cons_succ]
      exact allReg_zip ls vs (fun l hl => hall l (List.mem_cons_of_mem _ hl)) h

namespace LinkSys

variable (L : LinkSys)

/-- The body-entry world of the canonical call agrees with a compatible caller's callee entry. -/
theorem bodyEntryW_compat (hL : L.Ok) {h : Clif.Function} (hh : h ∈ L.P.funcs) {uses : List CV}
    {w t : Arm.ArmState} (ht : L.CallerOk h uses w t) :
    BodyEntryW L.F (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t)
      (bodyOf (L.A h).af (enterAt (L.A h) (L.canon h uses w))) := by
  have harg := (hL.argRegs h hh).2.1
  have hc := L.callerOk_canon hL hh uses w
  have hsp : spv (enterAt (L.A h) (L.canon h uses w)) = spv (enterAt (L.A h) t) := by
    rw [spv_enterAt, spv_enterAt]; simp only [spv]
    rw [hc.world.1 _ (by simp [Masked]), ht.world.1 _ (by simp [Masked])]
  have h29 : xreg 29 (enterAt (L.A h) (L.canon h uses w)) = xreg 29 (enterAt (L.A h) t) := by
    simp only [xreg]
    rw [r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
      hc.world.1 _ (by simp [Masked]), ht.world.1 _ (by simp [Masked])]
  refine ⟨by rw [spv_bodyOf, hsp], by rw [x29_bodyOf, hsp, h29], fun r hr => ?_, fun f hf h29' h31 => ?_,
    fun a ha => ?_, by simp⟩
  · have hra := harg r (hL.entryRegs h hh r hr)
    rw [regVal_bodyOf _ _ hra, regVal_enterAt _ _ hra, regVal_enterAt _ _ hra,
      ht.regs r (hL.entryRegs h hh r hr)]
  · have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
    have h30 : f ≠ .GPR 30#5 := by rintro rfl; exact hf (by simp [Masked])
    rw [r_bodyOf _ _ h29' h31, r_enterAt _ _ hpc h30, r_enterAt _ _ hpc h30,
      hc.world.1 f hf, ht.world.1 f hf]
  · rw [mem_bodyOf, mem_enterAt, mem_enterAt, hc.world.2.1 a ha, ht.world.2.1 a ha]

end LinkSys

namespace LinkSys

variable (L : LinkSys)

theorem frameSize_mod (hL : L.Ok) {h : Clif.Function} (hh : h ∈ L.P.funcs) :
    (L.A h).af.frameSize % 16 = 0 := by
  rw [(lowerRFunc_ok (hL.compiled h hh).alloc).1.1]
  exact alignTo16_mod _

theorem frameDrop_eq (hL : L.Ok) {h : Clif.Function} (hh : h ∈ L.P.funcs) :
    frameDrop (L.A h).af = (L.A h).af.frameSize + 16 := by
  simp [frameDrop, lowerRFunc_frame (hL.compiled h hh).alloc]

/-- **A call of a function `h` of `P`** at depth `M` (its whole-program run returns within `M`
steps) from a world `w` with room for the callee's stack: one VCode outcome of `h`, which the
linked machine's call realises from every caller state compatible with `w` (`CallerOk`), in
particular from the canonical one. -/
theorem progCall (hL : L.Ok) {M : Nat} (hM : 0 < M) (ih : L.Thm (M - 1)) {n : String}
    {h : Clif.Function} (hpf : L.P.func? n = some h) (hsl : h.slots = [])
    (hsz : (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (L.A h).af + L.K (M - 1) ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (L.A h).af + L.K (M - 1)) (spv w) a → L.F a ∧ ¬ L.Img a)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem} (hmr : MemRel L.F L.syms cm w) (hargs : ArgsAt h.sig vals uses w)
    (hinit : Clif.initState L.P n vals cm = .ok cs)
    (hrun : Clif.runLoop L.base L.P M cs = .returned rvals cm') :
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
      us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel L.F L.syms cm' wf ∧
      ∀ t, L.CallerOk h uses w t → ∃ k,
        (L.hooks M).call (some n) t =
          Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program ∧
        ActRet (Arm.r .PC t + 4) L.F
          (fun a => L.F a ∧ ¬ StackBelow (frameDrop (L.A h).af + L.K (M - 1)) (spv w) a)
          us outs wf (enterAt (L.A h) t) (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) := by
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  subst hname
  have hc := hL.compiled h hh
  have hfr := lowerRFunc_frame hc.alloc
  have hdrop := L.frameDrop_eq hL hh
  have hfs := L.frameSize_mod hL hh
  obtain ⟨hnd, harg, hwid⟩ := hL.argRegs h hh
  obtain ⟨hsl', hcm⟩ := initState_noSlots hpf hsl hinit
  have hce : ClifEntry h vals cs := clifEntry_initState hpf hinit
  -- the per-function run (program callees at most `M - 1` steps)
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (M - 1) hL.linkable.names hh
    hL.linkable.free M cs (by omega) (runInv_entry hh hce) (by rw [hrun]; intro _ e; cases e)
    (by rw [hrun]; intro e; cases e)
  rw [hrun] at hm
  -- the canonical state and the shared body-entry world
  let cn := L.canon h uses w
  let w₀ := bodyOf (L.A h).af (enterAt (L.A h) cn)
  have hcOk := L.callerOk_canon hL hh uses w
  have hsp0 : spv cn = spv w := hcOk.world.1 _ (by simp [Masked])
  have hspw₀ : spv w₀ = spv w - BitVec.ofNat 64 (frameDrop (L.A h).af) := by
    rw [spv_bodyOf, spv_enterAt, hsp0]
  obtain ⟨-, -, hB⟩ := off_toNat 0 (spv w) (frameDrop (L.A h).af) (by omega)
  have hWE : L.WorldEntry (M - 1) h vals cs w₀ := by
    refine ⟨hce, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsl', hcm]
      refine ⟨⟨⟨fun a b hv hb => ?_, hmr.valid, hmr.symbols⟩, fun id b hl => by simp at hl, ?_⟩,
        rfl, ?_⟩
      · rw [← hmr.bytes a b hv hb]
        simp only [Arm.read_mem, Arm.read_store, w₀, mem_bodyOf, mem_enterAt]
        rw [L.mem_canon, mem_withImg, if_neg]
        intro hi
        exact (hmr.valid a 1 hv).2 0 (by omega) (by simpa using hL.imgF _ hi)
      · rw [hL.noOut h hh]; exact outRel_zero _ _ _
      · simp only [w₀]
        rw [r_bodyOf _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          hcOk.world.1 _ (by simp [Masked])]
        exact herr
    · intro loc v hmem
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
      cases loc with
      | stack off =>
        obtain ⟨r, e⟩ := hL.regParams h hh _ (List.of_mem_zip hmem).1
        cases e
      | reg r =>
        obtain ⟨hr, hv⟩ := allReg_zip _ _ (hL.regParams h hh) hi
        have hlen := hargs.2.1.1
        obtain ⟨u, hu⟩ : ∃ u, uses[i]? = some u := by
          have hi' : i < uses.length := by
            rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hv).1
          exact ⟨uses[i]'hi', List.getElem?_eq_getElem _⟩
        have hvh := hargs.2.1.2 i v u hv hu
        have hrA : r.isArgReg = true := harg r (List.mem_of_getElem? hr)
        simp only
        rw [show regVal w₀ r = regVal (placeArgs (regLocs h.sig) uses (L.withImg w)) r by
          simp only [w₀]; rw [regVal_bodyOf _ _ hrA, regVal_enterAt _ _ hrA, L.regVal_canon _ _ _ hrA],
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
      apply hdead
      rw [hspw₀] at ha
      obtain ⟨h1, h2⟩ := ha
      rw [hB] at h1 h2
      exact ⟨by omega, by omega⟩
    · rw [hspw₀, hB, hdrop]; omega
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmemR, hall⟩ :=
    ih h hh vals cs w₀ m rvals cm' hWE hm
  refine ⟨us, outs, wf, hus, hlen, hhold, hmemR, fun t ht => ?_⟩
  -- the callee's activation from `t`
  let G : BitVec 64 → Prop :=
    fun a => L.F a ∧ ¬ StackBelow (frameDrop (L.A h).af + L.K (M - 1)) (spv w) a
  have hspt : spv (enterAt (L.A h) t) = spv w := by
    rw [spv_enterAt]; exact ht.world.1 _ (by simp [Masked])
  have hcode : ∀ a, CodeAddr (enterAt (L.A h) t) a → L.Img a := fun a ha =>
    hL.imgAddr h hh a (by simpa [CodeAddr] using ha)
  have hME : L.MachEntry (M - 1) h G (Arm.r .PC t + 4) (enterAt (L.A h) t) w₀ := by
    refine ⟨⟨by simp, fun k wd hk => hL.imgCode h hh _ (fun a ha => by
        rw [mem_enterAt]; exact ht.img a ha) k wd hk, by simp, ?_, x30_enterAt _ _, ht.ra, ?_,
        hL.fits h hh⟩, ?_, fun a ha => ?_, ?_, fun a ha => ⟨hL.imgF a ha, fun hb => (hdead a hb).2 ha⟩,
      fun a ha => by rw [mem_enterAt]; exact ht.img a ha, L.bodyEntryW_compat hL hh ht⟩
    · rw [r_enterAt _ _ (by simp) (by simp), ht.world.1 _ (by simp [Masked])]; exact herr
    · rw [hspt]; exact hal
    · refine stackRoom_of (by rw [hspt, ← hdrop]; exact hroom) fun a ha hb => ?_
      rw [hspt, ← hdrop] at hb
      exact (hdead a hb).2 (hcode a ha)
    · rw [hspt]; exact ha.2
    · funext a
      apply propext
      rw [hL.noOut h hh, hsz, frameWG_noSlots hfr (by rw [hspt, ← hdrop]; exact hroom), ← hdrop, hspt]
      constructor
      · rintro (hb | hc | hg)
        · exact (hdead a hb).1
        · exact hL.imgF a (hcode a hc)
        · exact hg.1
      · intro hF
        by_cases hb : StackBelow (frameDrop (L.A h).af + L.K (M - 1)) (spv w) a
        · exact .inl hb
        · exact .inr (.inr ⟨hF, hb⟩)
  obtain ⟨k, hret⟩ := hall G (Arm.r .PC t + 4) (enterAt (L.A h) t) hME
  refine ⟨k, ?_, hret⟩
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  show callHook L.Hb L.P _ (some h.name) t = _
  simp only [callHook, hpf]
  exact linkedCall_eq hc.layout hlm ht.ra
    ⟨hret.ret.pc, hret.ret.err, hret.prog.trans (program_enterAt _ _)⟩

end LinkSys

end E2E
