import FV.E2E.LinkWorld
import FV.E2E.LinkClifN
import FV.E2E.Link
import FV.E2E.PairDriver

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

/-! ## `blr`: the call target the instruction names -/

/-- The target of the `blr` at the pc of `s`: the register its instruction word (in memory) names,
decoded as the machine decodes it. -/
def blrTarget (s : Arm.ArmState) : Option (BitVec 64) :=
  match Arm.decode_raw_inst (Arm.read_mem_bytes 4 (Arm.r .PC s) s) with
  | some (.BR (.Uncond_branch_reg i)) => some (Arm.r (.GPR i.Rn) s)
  | _ => none

/-- The function of `P` whose link-time address (`Xb.sym`) is `a`. -/
def symCallee (Xb : ExtSem) (P : Clif.Program) (a : BitVec 64) : Option Clif.Function :=
  P.funcs.find? (fun h => Xb.sym h.name 0 == a)

theorem toArmInst_blr (env : Env) {n : Nat} (hn : n ≤ 30) :
    Insn.toArmInst env (.blr (.x n)) = .ok (.BR (.Uncond_branch_reg
      { opc := 1, op2 := 31, op3 := 0, Rn := BitVec.ofNat 5 n, op4 := 0 })) := by
  simp [Insn.toArmInst, Insn.armFields, Reg.encZR, hn, Arm.ArmInst.norm, Functor.map, Except.map,
    bind, Except.bind, pure, Except.pure]

/-- At a `blr xn` line of the laid-out code whose words are in memory, the machine's target is
`xn`. -/
theorem blrTarget_of {fa : FnAsm} {fb : FnBin} {base : BitVec 64} {lm : Std.HashMap Lbl Nat}
    {t : Arm.ArmState} {j : Nat} {tt : Option Clif.TrapCode} {n : Nat}
    (hl : fa.layout = .ok fb) (hm : labelOffsets fa.lines = .ok lm)
    (hj : fa.lines.toList[j]? = some (.ins (.blr (.x n)) tt)) (hn : n < 29)
    (hpc : Arm.r .PC t = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j))
    (hmem : ∀ k w, fb.words[k]? = some w → Arm.read_mem_bytes 4 (base + BitVec.ofNat 64 (4 * k)) t = w) :
    blrTarget t = some (Arm.r (.GPR (rnum n)) t) := by
  obtain ⟨h4, w, henc, hw⟩ := FnAsm.layout_word hl hm hj rfl
  simp only [Line.encodeAt] at henc
  have hdec := Insn.decode_encode_of (toArmInst_blr _ (by omega)) henc
  have hread : Arm.read_mem_bytes 4 (Arm.r .PC t) t = w := by
    rw [hpc]
    have := hmem _ w hw
    rwa [show 4 * (lineOffset fa.lines.toList j / 4) = lineOffset fa.lines.toList j by omega] at this
  unfold blrTarget
  rw [hread, hdec]
  rfl

/-! ## The linked system -/

/-- `n` names a declaration of `g` other than `g` itself: the program functions an activation of
`g` calls (directly, or through a pointer, which the per-function program resolves through the
declarations, `Clif.callExternAt`). -/
def DeclN (g : Clif.Function) (n : String) : Prop := n ∈ g.externs.map (·.2.name) ∧ n ≠ g.name

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

/-- The call hook of the linked machine: a `bl` of a function `g` of `P`, and a `blr` whose
target register holds `g`'s link-time address, run `pc g`; the other calls: the base hook. -/
def callHook (Hb : ArmHooks) (Xb : ExtSem) (P : Clif.Program)
    (pc : Clif.Function → Arm.ArmState → Arm.ArmState) (d : Option String) (s : Arm.ArmState) :
    Arm.ArmState :=
  match d with
  | some n => (match P.func? n with
    | some g => pc g s
    | none => Hb.call d s)
  | none => (match (blrTarget s).bind (symCallee Xb P) with
    | some g => pc g s
    | none => Hb.call none s)

/-- **The hooks of the linked machine**, by depth: at depth `M + 1` a call (`bl`, or `blr` of its
address) of a function `g` of `P` runs `g`'s code by the machine with the hooks of depth `M`
(`linkedCall`); at depth `0` it gives an error state. Other calls and TLS: the base hooks. -/
noncomputable def hooks : Nat → ArmHooks
  | 0 => ⟨callHook L.Hb L.Xb L.P (fun _ s => junkAt s), L.Hb.tls⟩
  | M + 1 => ⟨callHook L.Hb L.Xb L.P
      (fun g s => linkedCall (ArmStepX L.Xb (hooks M) (L.A g).fa) (L.A g) s), L.Hb.tls⟩

/-- The linked machine's call of the function `g` of `P` at depth `M`. -/
noncomputable def pcall : Nat → Clif.Function → Arm.ArmState → Arm.ArmState
  | 0, _, s => junkAt s
  | M + 1, g, s => linkedCall (ArmStepX L.Xb (L.hooks M) (L.A g).fa) (L.A g) s

theorem hooks_call (M : Nat) : (L.hooks M).call = callHook L.Hb L.Xb L.P (L.pcall M) := by
  cases M <;> rfl

/-- The machine of an activation of `g` at depth `M`. -/
noncomputable def mach (M : Nat) (g : Clif.Function) : Arm.ArmState → Arm.ArmState :=
  ArmStepX L.Xb (L.hooks M) (L.A g).fa

end LinkSys

/-- The registers of the register-passed parameters of a signature, in order. -/
def regLocs (sig : Clif.Signature) : List Reg :=
  (locsOf sig).filterMap fun l => match l with
    | .reg r => some r
    | .stack _ => none

theorem argLocs_size : ∀ (bytes : List Nat) (acc : Array ArgLoc) (nx st : Nat),
    (bytes.foldl (fun (p : Array ArgLoc × Nat × Nat) (b : Nat) =>
      if p.2.1 < 8 then (p.1.push (.reg (.x p.2.1)), p.2.1 + 1, p.2.2)
      else (p.1.push (.stack (alignTo p.2.2 (max b 8))), p.2.1, alignTo p.2.2 (max b 8) + max b 8))
      (acc, nx, st)).1.size = acc.size + bytes.length
  | [], _, _, _ => by simp
  | b :: bytes, acc, nx, st => by
    rw [List.foldl_cons]
    split <;> rw [argLocs_size] <;> simp <;> omega

theorem argLocs_fst (bytes : List Nat) : (argLocs bytes).1 =
    (bytes.foldl (fun (p : Array ArgLoc × Nat × Nat) (b : Nat) =>
      if p.2.1 < 8 then (p.1.push (.reg (.x p.2.1)), p.2.1 + 1, p.2.2)
      else (p.1.push (.stack (alignTo p.2.2 (max b 8))), p.2.1, alignTo p.2.2 (max b 8) + max b 8))
      (#[], 0, 0)).1.toList := rfl

theorem argLocs_length (bytes : List Nat) : (argLocs bytes).1.length = bytes.length := by
  rw [argLocs_fst, Array.length_toList, argLocs_size]
  simp

theorem locsOf_length (s : Clif.Signature) : (locsOf s).length = s.params.length ∨ locsOf s = [] := by
  unfold locsOf
  cases h : sigArgLocs s with
  | error e => exact .inr rfl
  | ok r =>
    obtain ⟨locs, n⟩ := r
    left
    simp only
    unfold sigArgLocs at h
    cases hb : sigArgs s with
    | error e => rw [hb] at h; cases h
    | ok bytes =>
      rw [hb] at h
      simp only [bind, Except.bind] at h
      have hl := sigParamBytes_length (s := s) hb
      split at h
      · split at h
        · cases h
        · rename_i hne
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
          simpa using hne
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        rw [← hl, ← argLocs_length bytes, h]

theorem filterMap_zip_length : ∀ (ls : List ArgLoc) (vs : List Clif.Val), ls.length = vs.length →
    ((ls.zip vs).filterMap fun q => match q.1 with | .reg _ => some q.2 | .stack _ => none).length =
      (ls.filterMap fun l => match l with | .reg r => some r | .stack _ => none).length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | l :: ls, v :: vs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    cases l <;> simp [List.filterMap_cons, filterMap_zip_length ls vs h]

/-- The register-passed arguments of a call are as many as the register parameters. -/
theorem argsAt_regLocs {s : Clif.Signature} {vals : List Clif.Val} {args : List CV}
    {w : Arm.ArmState} (h : ArgsAt s vals args w) : args.length = (regLocs s).length := by
  rw [← h.2.1.1]
  unfold regArgVals regLocs
  rcases locsOf_length s with hl | hl
  · exact filterMap_zip_length _ _ (by rw [hl, h.1])
  · rw [hl]; rfl

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
error, and the call's arguments (the stack-passed ones in the world, outside `F`) and the world
are related to CLIF arguments and memory on which `g`'s whole-program run returns within `M`
steps. -/
def Cond (M : Nat) (F : BitVec 64 → Prop) (g : Clif.Function) (uses : List CV)
    (w : Arm.ArmState) : Prop :=
  0 < M ∧ Arm.r .ERR w = .None ∧ (spv w).toNat % 16 = 0 ∧
  frameDrop (L.A g).af + L.K (M - 1) ≤ (spv w).toNat ∧
  (∀ a, StackBelow (frameDrop (L.A g).af + L.K (M - 1)) (spv w) a → F a ∧ ¬ L.Img a) ∧
  ∃ vals cm cs rvals cm', MemRel F L.syms cm w ∧ ArgsAt g.sig vals uses w ∧
    StackArgsAvoid F g.sig vals w ∧
    Clif.initState L.P g.name vals cm = .ok cs ∧ Clif.runLoop L.base L.P M cs = .returned rvals cm'

open Classical in
/-- A call of the function `g` of `P` at depth `M`: the results (x0.., one per ABI
return) and world of the linked machine's call of `g` from the canonical state, when `Cond`
holds and that call returned. -/
noncomputable def progX (M : Nat) (F : BitVec 64 → Prop) (g : Clif.Function) (uses : List CV)
    (w : Arm.ArmState) : Option (List CV × Arm.ArmState) :=
  if L.Cond M F g uses w ∧ Arm.r .ERR (L.pcall M g (L.canon g uses w)) = .None then
    some ((List.range (sigRets g.sig).length).map fun j =>
        regVal (L.pcall M g (L.canon g uses w)) (.x j),
      L.pcall M g (L.canon g uses w))
  else none

open Classical in
/-- **The external semantics of an activation of `g` at depth `M`**: a call (`bl`) of a function
of `P` is `progX`, as is an indirect call (`blr`) whose target is the address of a function of
`P` that `g` declares (`DeclN`; other than `g`) with as many register parameters as the call has
arguments (otherwise undefined); the rest is the base's. -/
noncomputable def X (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop) : ExtSem where
  call d uses w := match d with
    | some n => (match L.P.func? n with
      | some h => L.progX M F h uses w
      | none => L.Xb.call d uses w)
    | none => (match uses with
      | u :: args => (match symCallee L.Xb L.P (lo64 u) with
        | some h => if DeclN g h.name ∧ args.length = (regLocs h.sig).length then
            L.progX M F h args w else none
        | none => L.Xb.call none uses w)
      | [] => L.Xb.call none uses w)
  sym := L.Xb.sym
  tp := L.Xb.tp
  tlsFlags := L.Xb.tlsFlags

open Classical in
/-- **The CLIF environment of an activation of `g` at depth `M`**: `linkEnvN`, without the
functions of `P` that `g` does not declare (and `g` itself). The run of `P.only g` only calls
declared externs (`step_envOf`), so it is the run under `linkEnvN`. -/
noncomputable def envOf (M : Nat) (g : Clif.Function) : Clif.Env where
  extern n := if (L.P.func? n).isSome ∧ ¬ DeclN g n then none
    else (Clif.linkEnvN L.P L.base M).extern n

end LinkSys

/-! ## CLIF helpers -/

/-- The declared returns are the first ABI returns (`sigRets`: an `sret` signature without
returns adds the struct pointer). -/
theorem returns_le_sigRets (s : Clif.Signature) : s.returns.length ≤ (sigRets s).length := by
  unfold sigRets
  split
  · split
    · rename_i h; simp [List.isEmpty_iff.mp h]
    · exact Nat.le_refl _
  · exact Nat.le_refl _

/-! ## CLIF: runs that enter no function with stack slots keep the live allocations -/

/-- The externs of `env` create no allocation: an address valid after a call was valid before. -/
def NoAllocEnv (env : Clif.Env) : Prop :=
  ∀ n g, env.extern n = some g → ∀ vals m rvals m', g vals m = .returned rvals m' →
    ∀ a k, m'.valid a k = true → m.valid a k = true

section ValidKeep
open Clif Opt

theorem store_allocs {w : Nat} {m : Mem} {fl a n} {x : BitVec w} {m'}
    (h : m.store fl a n x = .ok m') : m'.allocs = m.allocs := by
  simp only [Mem.store, Res.bind_eq_ok, Res.pure_eq_ok] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  rfl

theorem evalInst_allocs {fr mem i vals mem'} (h : evalInst fr mem i = .ok (vals, mem')) :
    mem'.allocs = mem.allocs := by
  cases i <;> simp only [evalInst, Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h
  all_goals (repeat' (first | obtain ⟨_, _, h⟩ := h | split at h)) <;>
    (try simp only [Res.pure_eq_ok, Prod.mk.injEq, Res.bind_eq_ok] at h) <;>
    (repeat' (first | obtain ⟨_, _, h⟩ := h | split at h))
  all_goals first | rfl | exact store_allocs ‹_›

theorem lstep_next_allocs {fr m fr' m'} (h : lstep fr m = .next fr' m') : m'.allocs = m.allocs := by
  obtain ⟨func, regs, slots, body, term⟩ := fr
  cases body with
  | nil =>
    simp only [lstep] at h
    cases term <;> simp only [LRes.ofRes] at h <;> (repeat' split at h) <;> (try contradiction) <;>
      (cases h; rfl)
  | cons st rest =>
    simp only [lstep] at h
    split at h
    · simp only [LRes.ofRes] at h; split at h <;> contradiction
    · simp only [LRes.ofRes] at h
      split at h <;> try contradiction
      split at h <;> try contradiction
      cases h
      exact evalInst_allocs ‹_›

theorem valid_free {m : Mem} {bs : List Nat} {a k : Nat} (h : (m.free bs).valid a k = true) :
    m.valid a k = true := by
  simp only [Mem.valid, Mem.free, List.any_eq_true, List.mem_filter] at h ⊢
  obtain ⟨x, ⟨hx, -⟩, hc⟩ := h
  exact ⟨x, hx, hc⟩

theorem valid_of_allocs {m m' : Mem} (h : m'.allocs = m.allocs) {a k : Nat}
    (hv : m'.valid a k = true) : m.valid a k = true := by
  simpa [Mem.valid, h] using hv

theorem enterSlots_nil {g : Function} (hs : g.slots = []) (mem : Mem) :
    ∃ pl, enterSlots g mem = ([], { mem with place := pl }) := by
  unfold enterSlots
  rw [hs]
  split
  · exact ⟨mem.place, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- Entering a function without stack slots changes only the slot-placement oracle. -/
theorem enterFunc_noSlots {g : Function} {vals : List Val} {mem mem' : Mem} {fr : Clif.Frame}
    (hs : g.slots = []) (h : enterFunc g vals mem = .ok (fr, mem')) :
    fr.slots = [] ∧ ∃ pl, mem' = { mem with place := pl } := by
  obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok h
  obtain ⟨pl, hpl⟩ := enterSlots_nil hs mem
  rw [hpl, Prod.mk.injEq] at hal
  exact ⟨hal.1.symm, pl, hal.2.symm⟩

theorem callCont_valid {env : Clif.Env} {p : Program} {t : State} {rest : List Stmt}
    {rs : List ValueId} {ext : ExtFunc} {vals : List Val} {s1 : State} (hna : NoAllocEnv env)
    (hslot : ∀ g, p.func? ext.name = some g → g.slots = [])
    (h : Opt.callCont env p t rest rs ext vals = .next s1) :
    ∀ a k, s1.mem.valid a k = true → t.mem.valid a k = true := by
  intro a k hv
  unfold Opt.callCont at h
  split at h
  · rename_i g hg
    split at h
    · obtain ⟨⟨fr', mem'⟩, he, h⟩ := Opt.StepResult.ofRes_eq_next h
      cases h
      obtain ⟨-, pl, rfl⟩ := enterFunc_noSlots (hslot g hg) he
      exact hv
    · cases h
  · split at h
    · rename_i gsem hgs
      split at h
      · rename_i rvals mem' hr
        split at h
        · unfold continueWith at h
          split at h
          · cases h
            exact hna _ _ hgs _ _ _ _ hr a k hv
          · cases h
        · cases h
      all_goals cases h
    · cases h

/-- **A whole-program step keeps the live allocations** when the functions it enters have no
stack slots (the declared ones; with indirect calls, those with an address) and the externs
create none. -/
theorem step_valid {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Clif.Env} (hna : NoAllocEnv env)
    (hsl : ∀ g ∈ P.funcs, ∀ fn e h, g.extern? fn = some e → P.func? e.name = some h → h.slots = [])
    {s : State} (hI : LInv P s)
    (haddr : (∃ k ∈ P.funcs, ¬ IndFree k) → ∀ h ∈ P.funcs, s.mem.symbols h.name ≠ none → h.slots = []) :
    (∀ s1, step env P s = .next s1 → ∀ a k, s1.mem.valid a k = true → s.mem.valid a k = true) ∧
    (∀ v m, step env P s = .done v m → ∀ a k, m.valid a k = true → s.mem.valid a k = true) := by
  have hcall : ∀ (t : State) rest rs ext vals fn args, t.mem = s.mem → t.frame.func = s.frame.func →
      Opt.callArgs t.frame fn args = .ok (ext, vals) → ∀ s1,
      Opt.callCont env P t rest rs ext vals = .next s1 →
      ∀ a k, s1.mem.valid a k = true → s.mem.valid a k = true := by
    intro t rest rs ext vals fn args htm htf hca s1 hc a k hv
    rw [← htm]
    refine callCont_valid hna (fun g hg => hsl _ hI.1.1 fn ext g ?_ hg) hc a k hv
    rw [← htf]; exact Opt.callArgs_extern hca
  -- an indirect call from a frame of a function with indirect calls
  have hind : ∀ (t : State) rest rs sig d a' v, t.mem = s.mem → ¬ IndFree s.frame.func → ∀ s1,
      indCont env P t rest rs sig d a' v = .next s1 →
      ∀ a k, s1.mem.valid a k = true → s.mem.valid a k = true := by
    intro t rest rs sig d a' v htm hnf s1 hc a k hv
    rw [← htm]
    rcases indCont_next hc with ⟨-, g, mem', hg, he, hm, hsym⟩ | ⟨-, -, n, g, rv, hg, hr⟩
    · obtain ⟨-, pl, hpl⟩ :=
        enterFunc_noSlots (haddr ⟨_, hI.1.1, hnf⟩ g hg (by rw [← htm, hsym]; simp)) he
      rw [hm, hpl] at hv
      exact hv
    · exact hna _ _ hg _ _ _ _ hr a k hv
  have hnfT : ∀ callee args et, s.frame.body = [] → s.frame.term = .tryCallIndirect callee args et →
      ¬ IndFree s.frame.func := fun callee args et hb ht hif => by
    rcases hI.1 with ⟨-, ⟨b0, hb0, -, ht0⟩ | ⟨-, bc0, ht0⟩⟩
    · exact (hif b0 hb0).2 callee args et (ht0.symm.trans ht)
    · rw [ht] at ht0; cases ht0
  have hnfS : ∀ st rest sig callee args, s.frame.body = st :: rest →
      st.inst = .callIndirect sig callee args → ¬ IndFree s.frame.func :=
    fun st rest sig callee args hb hi hif => by
    rcases hI.1 with ⟨-, ⟨b0, hb0, hsuf, -⟩ | ⟨hnil, -⟩⟩
    · exact (hif b0 hb0).1 st (hsuf.subset (by rw [hb]; simp)) sig callee args hi
    · rw [hnil] at hb; cases hb
  rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · refine ⟨fun s1 h => ?_, fun v m h => ?_⟩
    · rw [step_try env P s hb ht] at h
      obtain ⟨⟨n, b, bc⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
      obtain ⟨⟨ext, vals⟩, hca, h⟩ := Opt.StepResult.ofRes_eq_next h
      exact hcall (tryState s bc) [] _ ext vals fn args rfl rfl hca s1 h
    · rw [step_try env P s hb ht] at h
      obtain ⟨⟨n, b, bc⟩, -, h⟩ := ofRes_eq_done h
      obtain ⟨⟨ext, vals⟩, -, h⟩ := ofRes_eq_done h
      exact absurd h callCont_ne_done
  · refine ⟨fun s1 h => ?_, fun v m h => ?_⟩
    · rw [step_tryInd env P s hb ht] at h
      obtain ⟨⟨n, b, bc⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
      obtain ⟨⟨d, a', w⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
      exact hind (tryState s bc) [] _ _ d a' w rfl (hnfT _ _ _ hb ht) s1 h
    · rw [step_tryInd env P s hb ht] at h
      obtain ⟨⟨n, b, bc⟩, -, h⟩ := ofRes_eq_done h
      obtain ⟨⟨d, a', w⟩, -, h⟩ := ofRes_eq_done h
      exact absurd h indCont_ne_done
  · refine ⟨fun s1 h => ?_, fun v m h => ?_⟩
    · rw [step_ind env P s hb hi] at h
      obtain ⟨⟨d, a', w⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
      exact hind s rest st.results sig d a' w rfl (hnfS _ _ _ _ _ hb hi) s1 h
    · rw [step_ind env P s hb hi] at h
      obtain ⟨⟨d, a', w⟩, -, h⟩ := ofRes_eq_done h
      exact absurd h indCont_ne_done
  · rw [Opt.step_eq_lift env P s hci]
    refine ⟨fun s1 h => ?_, fun v m h => ?_⟩
    · cases hl : Opt.lstep s.frame s.mem with
      | next fr1 m1 =>
        rw [hl] at h; cases h
        exact fun a k hv => valid_of_allocs (lstep_next_allocs hl) hv
      | call ext vals rs rest =>
        rw [hl] at h
        obtain ⟨st, fn, args, -, -, -, hca⟩ := Opt.lstep_call_inv hl
        exact hcall s rest rs ext vals fn args rfl rfl hca s1 h
      | ret vals =>
        rw [hl] at h
        rw [returnValues_mem.1 s1 h]
        exact fun a k hv => valid_free (by rwa [Mem.leave_valid] at hv)
      | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1)
      | trap c => rw [hl] at h; cases h
      | stuck m => rw [hl] at h; cases h
    · cases hl : Opt.lstep s.frame s.mem with
      | ret vals =>
        rw [hl] at h
        rw [returnValues_mem.2 v m h]
        exact fun a k hv => valid_free (by rwa [Mem.leave_valid] at hv)
      | call ext vals rs rest => rw [hl] at h; exact absurd h callCont_ne_done
      | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1)
      | next fr1 m1 => rw [hl] at h; cases h
      | trap c => rw [hl] at h; cases h
      | stuck m => rw [hl] at h; cases h

/-- **A returning whole-program run keeps the live allocations** (functions entered without stack
slots: the declared ones, and with indirect calls those with an address; externs that create
none and, with indirect calls, keep the symbols). -/
theorem runLoop_valid {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Clif.Env}
    (hna : NoAllocEnv env)
    (hsl : ∀ g ∈ P.funcs, ∀ fn e h, g.extern? fn = some e → P.func? e.name = some h → h.slots = []) :
    ∀ (N : Nat) (s : State) (vals : List Val) (mem : Mem), LInv P s →
      ((∃ k ∈ P.funcs, ¬ IndFree k) → Opt.EnvKeepsSymbols env ∧
        ∀ h ∈ P.funcs, s.mem.symbols h.name ≠ none → h.slots = []) →
      runLoop env P N s = .returned vals mem → ∀ a k, mem.valid a k = true → s.mem.valid a k = true
  | 0, _, _, _, _, _, h => by simp at h
  | N + 1, s, vals, mem, hI, hind, h => by
    rw [runLoop_succ'] at h
    have hsv := step_valid hP hna hsl hI (fun hk => (hind hk).2)
    cases hs : step env P s with
    | next s1 =>
      rw [hs] at h
      intro a k hv
      have hind1 : (∃ k ∈ P.funcs, ¬ IndFree k) → Opt.EnvKeepsSymbols env ∧
          ∀ h ∈ P.funcs, s1.mem.symbols h.name ≠ none → h.slots = [] := fun hk =>
        ⟨(hind hk).1, fun h hh hs1 => (hind hk).2 h hh (by
          rw [← (step_symbols hP (hind hk).1 hI).1 s1 hs]; exact hs1)⟩
      exact hsv.1 s1 hs a k
        (runLoop_valid hP hna hsl N s1 vals mem (step_next_linv hP hI hs).1 hind1 h a k hv)
    | done v m =>
      rw [hs] at h
      simp only [afterStep, Outcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hsv.2 v m hs
    | trapped c => rw [hs] at h; cases h
    | stuck m => rw [hs] at h; cases h

end ValidKeep

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

/-- **A returning run satisfies the run premises** (`TrapsExplicit`) when the entered function's
indirect calls never reach a function of the program: they have no address on the run. -/
theorem trapsExplicit_of_returned {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    (hind : ¬ Clif.IndFree cs.frame.func → ∀ s, Reach env p cs s → ∀ g ∈ p.funcs,
      s.mem.symbols g.name = none)
    {fuel : Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned vals cm) : TrapsExplicit env p cs where
  stmt := fun s c _ _ hr hs _ => absurd hs (reach_not_trapped hrun hr c)
  tryCall := fun s c _ _ _ hr hs _ _ => absurd hs (reach_not_trapped hrun hr c)
  tryCallInd := fun s c _ _ _ hr hs _ _ => absurd hs (reach_not_trapped hrun hr c)
  indirect := fun s st _ sig callee args hr _ hi ⟨B, hB, hst⟩ cv _ g hg e => by
    have hnf : ¬ Clif.IndFree cs.frame.func := fun hif => (hif B hB).1 st hst sig callee args hi
    rw [hind hnf s hr g hg] at e
    cases e
  tryIndirect := fun s callee args et hr _ _ ⟨B, hB, e⟩ cv _ g hg e' => by
    have hnf : ¬ Clif.IndFree cs.frame.func := fun hif => (hif B hB).2 callee args et e
    rw [hind hnf s hr g hg] at e'
    cases e'

/-- The states a run reaches keep the symbols (when the externs do) and `LInv`. -/
theorem reach_symbols {P : Clif.Program} (hP : ∀ g ∈ P.funcs, Clif.LinkFree g) {env : Clif.Env}
    (hk : Opt.EnvKeepsSymbols env) {cs s : Clif.State} (hr : Reach env P cs s) (hI : Clif.LInv P cs) :
    s.mem.symbols = cs.mem.symbols ∧ Clif.LInv P s := by
  induction hr with
  | refl => exact ⟨rfl, hI⟩
  | step hs _ ih =>
    obtain ⟨h1, h2⟩ := ih (Clif.step_next_linv hP hI hs).1
    exact ⟨h1.trans ((Clif.step_symbols hP hk hI).1 _ hs), h2⟩

/-- The entry state of a function without stack slots: no slots, the memory unchanged but for
the slot-placement oracle. -/
theorem initState_noSlots {P : Clif.Program} {h : Clif.Function} {n : String}
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} (hf : P.func? n = some h)
    (hs : h.slots = []) (hi : Clif.initState P n vals cm = .ok cs) :
    cs.frame.slots = [] ∧ ∃ pl, cs.mem = { cm with place := pl } := by
  simp only [Clif.initState, hf, Clif.Res.ofOption_some, Clif.Res.ok_bind] at hi
  cases he : Clif.enterFunc h vals cm with
  | ok r =>
    rw [he] at hi
    obtain ⟨fr, mem'⟩ := r
    simp only [Clif.Res.ok_bind, Clif.Res.pure_eq, Clif.Res.ok.injEq] at hi
    subst hi
    exact enterFunc_noSlots hs he
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

/-- The `n` bytes from `sp` (no wrap). -/
def OutAt (n : Nat) (sp a : BitVec 64) : Prop := sp.toNat ≤ a.toNat ∧ a.toNat < sp.toNat + n

theorem intBase_le_size (vc : VCode) (rf : RFunc) :
    (RAFrame.compute vc rf).intBase ≤ (RAFrame.compute vc rf).size := by
  obtain ⟨h1, h2, h3, -⟩ := compute_facts vc rf
  by_cases hfs : rf.floatStack = true <;> simp [hfs] at h2 <;> omega

theorem frameWG_out {K lo : Nat} {af : AFunc} {G : BitVec 64 → Prop} {u : Arm.ArmState}
    {a : BitVec 64} (hfr : af.frame = true) (hroom : af.frameSize + 16 + K ≤ (spv u).toNat)
    (hlo : lo ≤ af.frameSize) :
    frameWG K lo af.frameSize af G u a ↔
      (StackBelow (af.frameSize + 16 + K) (spv u) a ∧
        ¬ OutAt lo (spv u - BitVec.ofNat 64 (af.frameSize + 16)) a) ∨ CodeAddr u a ∨ G a := by
  have hd : frameDrop af = af.frameSize + 16 := by simp [frameDrop, hfr]
  obtain ⟨h1, h2, h3⟩ := off_toNat a (spv u) (af.frameSize + 16) (by omega)
  have hsp := (spv u).isLt
  have ha := a.isLt
  have hsub : ∀ (b : BitVec 64), (spv u).toNat - (af.frameSize + 16) ≤ b.toNat →
      (b - (spv u - BitVec.ofNat 64 (af.frameSize + 16))).toNat =
        b.toNat - ((spv u).toNat - (af.frameSize + 16)) := by
    intro b hb
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h3]; exact hb), h3]
  have hbel : a.toNat < (spv u).toNat - (af.frameSize + 16) →
      (a - (spv u - BitVec.ofNat 64 (af.frameSize + 16))).toNat =
        2 ^ 64 - ((spv u).toNat - (af.frameSize + 16)) + a.toNat := by
    intro hb
    rw [BitVec.toNat_sub, h3, Nat.mod_eq_of_lt (by omega)]
  simp only [frameWG, frameW, frameF, StackBelow, hd, OutAt, h3]
  constructor
  · rintro (((⟨hl, h⟩ | ⟨hl, h⟩ | hc) | ⟨hl, hr⟩) | hg)
    · by_cases hb : (spv u).toNat - (af.frameSize + 16) ≤ a.toNat
      · rw [hsub a hb] at hl h; exact .inl ⟨⟨by omega, by omega⟩, by omega⟩
      · rw [hbel (Nat.not_le.mp hb)] at h; omega
    · by_cases hb : (spv u).toNat - (af.frameSize + 16) ≤ a.toNat
      · rw [hsub a hb] at hl h; exact .inl ⟨⟨by omega, by omega⟩, by omega⟩
      · rw [hbel (Nat.not_le.mp hb)] at h; omega
    · exact .inr (.inl hc)
    · exact .inl ⟨⟨by omega, by omega⟩, by omega⟩
    · exact .inr (.inr hg)
  · rintro (⟨⟨hl, hr⟩, hno⟩ | hc | hg)
    · by_cases hb : a.toNat < (spv u).toNat - (af.frameSize + 16)
      · exact .inl (.inr ⟨by omega, by omega⟩)
      · have e := hsub a (Nat.not_lt.mp hb)
        by_cases hs : (a - (spv u - BitVec.ofNat 64 (af.frameSize + 16))).toNat < af.frameSize
        · exact .inl (.inl (.inl ⟨by rw [e]; omega, hs⟩))
        · exact .inl (.inl (.inr (.inl ⟨by omega, by rw [e]; omega⟩)))
    · exact .inl (.inl (.inr (.inr hc)))
    · exact .inr hg

theorem append_inj' {n m : Nat} {x x' : BitVec n} {y y' : BitVec m} (h : x ++ y = x' ++ y') :
    x = x' ∧ y = y' := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun z => z.getLsbD (i + m)) h
    simpa [BitVec.getLsbD_append, show ¬ (i + m < m) by omega] using this
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun z => z.getLsbD i) h
    simpa [BitVec.getLsbD_append, hi] using this

theorem read_mem_bytes_bytes : ∀ (n : Nat) (a : BitVec 64) (s t : Arm.ArmState),
    Arm.read_mem_bytes n a s = Arm.read_mem_bytes n a t →
    ∀ k < n, s.mem (a + BitVec.ofNat 64 k) = t.mem (a + BitVec.ofNat 64 k)
  | 0, _, _, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, a, s, t, h, k, hk => by
    simp only [Arm.read_mem_bytes] at h
    have h' := congrArg (BitVec.cast (by omega : (n + 1) * 8 = n * 8 + 8)) h
    simp only [BitVec.cast_cast, BitVec.cast_eq] at h'
    have hh := append_inj' h'
    cases k with
    | zero =>
      have := hh.2
      simpa [Arm.read_mem, Arm.read_store] using this
    | succ j =>
      have := read_mem_bytes_bytes n (a + 1#64) s t hh.1 j (by omega)
      rwa [BitVec.add_assoc, show (1#64 : BitVec 64) + BitVec.ofNat 64 j = BitVec.ofNat 64 (j + 1) by
        apply BitVec.eq_of_toNat_eq; simp; omega] at this

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

/-! ## The operands of a call -/

theorem zip_fixed : ∀ (os : List Operand) (rs : List Reg) (fr : List Reg),
    os.length = rs.length → os.length = fr.length →
    (∀ (i : Nat) (o : Operand) (r : Reg), os[i]? = some o → fr[i]? = some r → o.con = .fixed r) →
    (∀ p ∈ os.zip (rs.map Loc.reg), ∀ r, p.1.con = .fixed r → p.2 = .reg r) → rs = fr
  | [], [], [], _, _, _, _ => rfl
  | o :: os, r :: rs, f :: fr, h1, h2, hc, hf => by
    have e := hf (o, .reg r) (by simp) f (hc 0 o f rfl rfl)
    simp only [Loc.reg.injEq] at e
    subst e
    congr 1
    exact zip_fixed os rs fr (by simpa using h1) (by simpa using h2)
      (fun i o' r' h h' => hc (i + 1) o' r' h h')
      (fun p hp r' hr' => hf p (by simp only [List.map_cons, List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp) r' hr')
  | [], _ :: _, _, h1, _, _, _ => by simp at h1
  | _ :: _, [], _, h1, _, _, _ => by simp at h1
  | [], [], _ :: _, _, h2, _, _ => by simp at h2
  | _ :: _, _ :: _, [], _, h2, _, _ => by simp at h2

theorem callRegs_eq {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} {regs : Array Reg}
    (hsz : (retOps Lu ++ callDefOps Ld).length = regs.size)
    (hfix : ∀ p ∈ ((retOps Lu ++ callDefOps Ld).toArray.zip (regs.map Loc.reg)).toList, ∀ r,
      p.1.con = .fixed r → p.2 = .reg r) :
    regs.toList = Lu.map (·.2) ++ Ld.map (·.1) := by
  apply zip_fixed (retOps Lu ++ callDefOps Ld) regs.toList _ (by simpa using hsz)
    (by simp [retOps, callDefOps])
  · intro i o r ho hr
    rw [List.getElem?_append] at ho hr
    simp only [retOps, callDefOps, List.length_map] at ho hr
    split at ho
    · rw [if_pos (by assumption)] at hr
      simp only [List.getElem?_map, Option.map_eq_some_iff] at ho hr
      obtain ⟨q, hq, rfl⟩ := ho
      obtain ⟨q', hq', rfl⟩ := hr
      rw [hq] at hq'; cases hq'; rfl
    · rw [if_neg (by assumption)] at hr
      simp only [List.getElem?_map, Option.map_eq_some_iff] at ho hr
      obtain ⟨q, hq, rfl⟩ := ho
      obtain ⟨q', hq', rfl⟩ := hr
      rw [hq] at hq'; cases hq'; rfl
  · intro p hp r hr
    exact hfix p (by simpa using hp) r hr

theorem call_zip {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} {regs : Array Reg}
    (hr : regs.toList = Lu.map (·.2) ++ Ld.map (·.1)) :
    ((retOps Lu ++ callDefOps Ld).toArray.zip regs).toList =
      (retOps Lu).zip (Lu.map (·.2)) ++ (callDefOps Ld).zip (Ld.map (·.1)) := by
  rw [Array.toList_zip, hr, List.toList_toArray, List.zip_append (by simp [retOps])]

theorem map_zip_retOps (s : Arm.ArmState) : ∀ Lu : List (Nat × Reg),
    ((retOps Lu).zip (Lu.map (·.2))).map (fun p => regVal s p.2) = Lu.map (fun q => regVal s q.2)
  | [] => rfl
  | q :: Lu => by
    have := map_zip_retOps s Lu
    simp only [retOps, List.map_cons, List.zip_cons_cons] at this ⊢
    rw [this]

theorem call_useVals {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} {regs : Array Reg}
    (hr : regs.toList = Lu.map (·.2) ++ Ld.map (·.1)) (s : Arm.ArmState) :
    useVals (retOps Lu ++ callDefOps Ld).toArray regs s = Lu.map (fun q => regVal s q.2) := by
  simp only [useVals, call_zip hr, List.filter_append]
  rw [List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr]
  · rw [List.append_nil]; exact map_zip_retOps s Lu
  · intro p hp
    have := (List.of_mem_zip hp).1
    simp only [callDefOps, List.mem_map] at this
    obtain ⟨q, -, e⟩ := this
    rw [← e]; simp [Operand.isUse]
  · intro p hp
    have := (List.of_mem_zip hp).1
    simp only [retOps, List.mem_map] at this
    obtain ⟨q, -, e⟩ := this
    rw [← e]; simp [Operand.isUse]

theorem call_defs {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} {regs : Array Reg}
    (hr : regs.toList = Lu.map (·.2) ++ Ld.map (·.1)) :
    ((retOps Lu ++ callDefOps Ld).toArray.zip regs).toList.filter (·.1.isDef) =
      (callDefOps Ld).zip (Ld.map (·.1)) := by
  rw [call_zip hr, List.filter_append, List.filter_eq_nil_iff.mpr, List.filter_eq_self.mpr]
  · rfl
  · intro p hp
    have := (List.of_mem_zip hp).1
    simp only [callDefOps, List.mem_map] at this
    obtain ⟨q, -, e⟩ := this
    rw [← e]; simp [Operand.isDef]
  · intro p hp
    have := (List.of_mem_zip hp).1
    simp only [retOps, List.mem_map] at this
    obtain ⟨q, -, e⟩ := this
    rw [← e]; simp [Operand.isDef]

theorem assign_call_sym {n : String} {us ds : List (Reg × Reg)} {regs : Array Reg} {i' : MInst}
    (h : (MInst.call ⟨.sym n, us, ds⟩).assign regs = .ok i') :
    ∃ us' ds', i' = .call ⟨.sym n, us', ds'⟩ := by
  unfold MInst.assign at h
  simp only [MInst.visitOperands, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
    StateT.run] at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h
    · simp only [Except.ok.injEq] at h
      subst h
      split at hv
      · cases hv
      · split at hv
        · cases hv
        · simp only [Except.ok.injEq] at hv
          subst hv
          exact ⟨_, _, rfl⟩

theorem assign_call_reg {tv : Nat} {us ds : List (Reg × Reg)} {regs : Array Reg} {i' : MInst}
    (h : (MInst.call ⟨.reg (.vreg tv .int), us, ds⟩).assign regs = .ok i') :
    ∃ r0 us' ds', regs[0]? = some r0 ∧ i' = .call ⟨.reg r0, us', ds'⟩ := by
  unfold MInst.assign at h
  simp only [MInst.visitOperands, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
    StateT.run, get, set, getThe, MonadStateOf.get, StateT.get, MonadStateOf.set, StateT.set] at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h
    · simp only [Except.ok.injEq] at h
      subst h
      cases h0 : regs[0]? with
      | none => rw [h0] at hv; simp [throw, throwThe, MonadExceptOf.throw, StateT.lift] at hv
      | some r0 =>
        rw [h0] at hv
        simp only [StateT.pure, pure, Except.pure] at hv
        split at hv
        · cases hv
        · split at hv
          · cases hv
          · simp only [Except.ok.injEq] at hv
            subst hv
            exact ⟨r0, _, _, rfl, rfl⟩



theorem callRegs_eq_reg {tv : Nat} {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} {regs : Array Reg}
    (hsz : (tgtOp tv :: (retOps Lu ++ callDefOps Ld)).length = regs.size)
    (hfix : ∀ p ∈ ((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray.zip (regs.map Loc.reg)).toList,
      ∀ r, p.1.con = .fixed r → p.2 = .reg r) :
    ∃ r0, regs.toList = r0 :: (Lu.map (·.2) ++ Ld.map (·.1)) := by
  obtain ⟨l⟩ := regs
  cases l with
  | nil => simp at hsz
  | cons r0 rs =>
    refine ⟨r0, ?_⟩
    have := callRegs_eq (regs := rs.toArray) (by simpa using hsz) (fun p hp r hr => hfix p (by
      simp only [Array.toList_zip, List.toList_toArray, Array.toList_map, List.map_cons,
        List.zip_cons_cons, List.mem_cons] at hp ⊢
      exact .inr hp) r hr)
    simpa using this


theorem call_useVals_reg {tv : Nat} {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} {regs : Array Reg}
    {r0 : Reg} (hr : regs.toList = r0 :: (Lu.map (·.2) ++ Ld.map (·.1))) (s : Arm.ArmState) :
    useVals (tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray regs s =
      regVal s r0 :: Lu.map (fun q => regVal s q.2) := by
  have h2 : regs = (r0 :: (Lu.map (·.2) ++ Ld.map (·.1))).toArray := by
    rw [← hr]
  have hrest := call_useVals (Lu := Lu) (Ld := Ld) (regs := (Lu.map (·.2) ++ Ld.map (·.1)).toArray)
    (by simp) s
  rw [h2]
  simp only [useVals, Array.toList_zip, List.toList_toArray, List.zip_cons_cons, List.filter_cons,
    show (tgtOp tv).isUse = true from rfl, ↓reduceIte, List.map_cons] at hrest ⊢
  rw [hrest]


theorem call_defs_reg {tv : Nat} {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} {regs : Array Reg}
    {r0 : Reg} (hr : regs.toList = r0 :: (Lu.map (·.2) ++ Ld.map (·.1))) :
    ((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray.zip regs).toList.filter (·.1.isDef) =
      (callDefOps Ld).zip (Ld.map (·.1)) := by
  have h2 : regs = (r0 :: (Lu.map (·.2) ++ Ld.map (·.1))).toArray := by
    rw [← hr]
  have hrest := call_defs (Lu := Lu) (Ld := Ld) (regs := (Lu.map (·.2) ++ Ld.map (·.1)).toArray)
    (by simp)
  rw [h2]
  simp only [Array.toList_zip, List.toList_toArray, List.zip_cons_cons, List.filter_cons,
    show (tgtOp tv).isDef = false from rfl, Bool.false_eq_true, ↓reduceIte] at hrest ⊢
  exact hrest


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

/-- `h` is a callee of `g`: a call site of `g`'s compiled code calls it, or `g` declares it. -/
def Callee (g h : Clif.Function) : Prop :=
  (∃ info, L.ProgSite g info h) ∨ ∃ e ∈ g.externs.map (·.2), L.P.func? e.name = some h

/-- Some program callee has an outgoing-argument area: its activations from the canonical and
the actual caller state differ there, so the linking needs non-interference. -/
def NeedNI : Prop :=
  ∃ g ∈ L.P.funcs, ∃ h, L.Callee g h ∧ (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase ≠ 0

/-- **The premises of the linked program** (`backend_correct_program`): the program and its
compilation, the scope of this layer, the link layout, and the base environment's contracts. -/
structure Ok : Prop where
  /-- distinct names, no `return_call` -/
  names : (L.P.funcs.map (·.name)).Nodup
  free : ∀ g ∈ L.P.funcs, Clif.LinkFree g
  subset : ∀ g ∈ L.P.funcs, InSubset (L.P.only g) g
  compiled : ∀ g ∈ L.P.funcs, Compiled g (L.A g).k (L.A g).vc (L.A g).vcp (L.A g).rf
    (L.A g).af (L.A g).fa (L.A g).fb
  covered : ∀ g ∈ L.P.funcs, FormsCovered ⟨(L.A g).fa.k, (L.A g).af.slotBase⟩ (L.A g).vcp
  /-- scope: the outgoing-argument area of a function holds the stack-passed arguments of the
  functions of `P` it declares (checked per declaration; vacuous for register-only signatures) -/
  outFits : ∀ g ∈ L.P.funcs, ∀ e ∈ g.externs.map (·.2), (L.P.func? e.name).isSome →
    ∀ (i off : Nat) (p : Clif.AbiParam), (locsOf e.sig)[i]? = some (ArgLoc.stack off) →
      e.sig.params[i]? = some p →
      off + p.ty.bytes ≤ (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase
  /-- the base externs create no allocation (needed only when a function of `P` has an
  outgoing-argument area: the callees' runs keep it free of live CLIF bytes) -/
  baseNoAlloc : (∃ g ∈ L.P.funcs, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase ≠ 0) →
    NoAllocEnv L.base
  argRegs : ∀ g ∈ L.P.funcs, (regLocs g.sig).Nodup ∧ (∀ r ∈ regLocs g.sig, r.isArgReg = true) ∧
    ∀ p ∈ g.sig.params, p.ty.width ≤ 64
  /-- an `sret` function's returns carry its ABI results (the struct pointer: `lowerFunction`
  appends it to every `return`), checked on the compiled code -/
  sretRets : ∀ g ∈ L.P.funcs, g.sig.params.any (·.purpose == .sret) = true → ∀ us,
    (L.A g).vc.RetsSite us → (sigRets g.sig).length ≤ us.length
  /-- scope: the functions called from `P` (at a call site, or declared as an extern) have no
  stack slots (their frame's slot region is empty) -/
  calleeSlots : ∀ g ∈ L.P.funcs, ∀ h, ((∃ info, L.ProgSite g info h) ∨
      ∃ e ∈ g.externs.map (·.2), L.P.func? e.name = some h) →
    h.slots = [] ∧ (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize
  /-- scope: a call of a function `h` of `P` passes integer arguments in `h`'s parameter
  registers and takes the results from x0.. (the defs past the results: a `try_call`'s exception
  payload registers; checked per call site) -/
  callRegs : ∀ g ∈ L.P.funcs, ∀ info h, L.ProgSite g info h →
    ∃ n Lu Ld, info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧ Lu.map (·.2) = regLocs h.sig ∧
      (Ld.map (·.1)).take (sigRets h.sig).length = (List.range (sigRets h.sig).length).map Reg.x
  /-- a `try_call` of a function `h` of `P` takes at most `h`'s results (the compiler's
  `ti.rets` is their number) -/
  tryRets : ∀ g ∈ L.P.funcs, ∀ info ti h, (L.A g).vcp.TrySite info ti → L.ProgSite g info h →
    ti.rets ≤ (sigRets h.sig).length
  /-- scope: a `blr` call site (an indirect call, or a call through the GOT) passes integer
  arguments in the parameter registers of every function of `P` its function declares that has as
  many register parameters, and takes that function's results from x0.. (checked per site;
  vacuous without `blr` sites) -/
  blrRegs : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → (∀ n, info.dest ≠ .sym n) →
    ∃ t Lu Ld, info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      ∀ h ∈ L.P.funcs, DeclN g h.name → (regLocs h.sig).length = Lu.length →
        Lu.map (·.2) = regLocs h.sig ∧
        (Ld.map (·.1)).take (sigRets h.sig).length = (List.range (sigRets h.sig).length).map Reg.x
  /-- a `blr` `try_call` takes at most the results of the declared functions it may call -/
  blrTry : ∀ g ∈ L.P.funcs, ∀ info ti, (L.A g).vcp.TrySite info ti → ∀ t Lu Ld,
    info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ → ∀ h ∈ L.P.funcs, DeclN g h.name →
      (regLocs h.sig).length = Lu.length → ti.rets ≤ (sigRets h.sig).length
  /-- layout: the return address of a `blr` is not in the code of a function of `P` it may call
  (the declared ones other than the caller) -/
  raBlr : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → (∀ n, info.dest ≠ .sym n) →
    ∀ h ∈ L.P.funcs, DeclN g h.name → ∀ pc, CallPc (L.A g).fa (L.A g).base pc →
      ∀ k < (L.A h).fb.words.size, pc + 4 ≠ (L.A h).base + BitVec.ofNat 64 (4 * k)
  /-- scope of the indirect calls (`call_indirect`, `try_call_indirect`) of a function `g`: the
  base externs keep the symbols, distinct names of `P` have distinct addresses, `g` declares every
  name of `P` with an address but its own (`Clif.IndScope`), and `g` has no address (it calls no
  pointer to itself) -/
  indScope : ∀ g ∈ L.P.funcs, ¬ Clif.IndFree g → Clif.IndScope L.P L.base g L.syms
  indNoSym : ∀ g ∈ L.P.funcs, ¬ Clif.IndFree g → L.syms g.name = none
  /-- the indirect calls of `g` and the functions it declares pass their arguments in registers
  and return no `sret` pointer -/
  indSig : ∀ g ∈ L.P.funcs, ¬ Clif.IndFree g →
    (∀ sig ∈ indSigs g, sig.params.any (·.purpose == .sret) = false) ∧
    ∀ h ∈ L.P.funcs, DeclN g h.name → h.sig.params.any (·.purpose == .sret) = false ∧
      ∃ bytes, sigParamBytes h.sig = .ok bytes ∧ bytes.length ≤ 8
  /-- when a function of `P` has an outgoing-argument area and one has indirect calls, the
  functions with an address have no stack slots (an indirect call enters no slotted function) -/
  addrSlots : (∃ g ∈ L.P.funcs, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase ≠ 0) →
    (∃ g ∈ L.P.funcs, ¬ Clif.IndFree g) → ∀ h ∈ L.P.funcs, L.syms h.name ≠ none → h.slots = []
  /-- the link-time address of a function of `P` is no other symbol's -/
  symInj : ∀ h ∈ L.P.funcs, ∀ n, L.Xb.sym h.name 0 = L.Xb.sym n 0 → n = h.name
  /-- the declarations of the program's functions are their definitions' signatures -/
  declSig : ∀ g ∈ L.P.funcs, ∀ e ∈ g.externs.map (·.2), ∀ h, L.P.func? e.name = some h → e.sig = h.sig
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
  /-- layout: the return address of a call is not in the code of a function of `P` that `g`
  calls (stated for the callees of `g`'s call sites, not for every function of `P`: the return
  address is in `g`'s own code, so a function calling itself directly is outside this layer) -/
  raCall : ∀ g ∈ L.P.funcs, ∀ info h, L.ProgSite g info h → ∀ pc, CallPc (L.A g).fa (L.A g).base pc →
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
  /-- the indirect calls of `g` that reach an extern outside `P` (vacuous without indirect
  calls) -/
  baseXI : ∀ g ∈ L.P.funcs, ∀ F slotOff out c, XCallsIndOk L.base (indSigs g)
    (RelW ⟨F, L.syms, slotOff, out⟩ g c) L.Xb
  baseTls : ∀ g ∈ L.P.funcs, hasTls g = true → ∀ F K, TlsOk F K L.Xb L.Hb
  /-- the results of a `try_call` of an extern outside `P` (normal return; vacuous without such
  `try_call`s) -/
  baseTry : ∀ g ∈ L.P.funcs, ∀ F, CalleeTryOk F L.Xb L.Hb
    fun info ti => (L.A g).vcp.TrySite info ti ∧ L.BaseDest (destOf info)
  /-- **non-interference of the base externs** (needed only when a program callee has an
  outgoing-argument area): a returning call of an extern outside `P`, pinned to its CLIF call,
  from two worlds that agree outside `Z ⊇ F`, related to the same CLIF memory and with the same
  argument bytes, gives the same results and worlds that agree outside `Z` -/
  baseNI : L.NeedNI → ∀ g ∈ L.P.funcs, ∀ F, XNI F L.syms (g.externs.map (·.2)) (indSigs g)
    (fun n sig vals cm => L.P.func? n = none ∧
      CallLg L.base (g.externs.map (·.2)) (indSigs g) n sig vals cm) L.Xb
  /-- the TLSDESC flags do not depend on the world outside `F` (needed only when a program
  callee has an outgoing-argument area) -/
  baseTlsNI : L.NeedNI → ∀ F, XTls F L.Xb

/-- **The machine side of an activation of `g` at depth `M`** entered in `s` with body-entry
world `w₀`: the ABI entry, the stack (frame and the callees' budget `K M`), the addresses `G` it
keeps (outside its stack; containing the code image, which `s` holds), the addresses outside
its world are `F`, and `w₀` agrees with `s`. -/
structure MachEntry (M : Nat) (g : Clif.Function) (F G : BitVec 64 → Prop) (ra : BitVec 64)
    (s w₀ : Arm.ArmState) : Prop where
  abi : AbiEntry (L.A g).fb (L.A g).base ra s
  stack : StackAvail (L.K M) (L.A g).af s
  gfree : ∀ a, G a → ¬ StackBelow (frameDrop (L.A g).af + L.K M) (spv s) a
  hF : frameWG (L.K M) (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase
    (RAFrame.compute (L.A g).vcp (L.A g).rf).size (L.A g).af G s = F
  imgG : ∀ a, L.Img a → G a
  imgS : ∀ a, L.Img a → s.mem a = L.imgMem a
  body : BodyEntryW F (L.A g).vcp.EntryArg (L.A g).af s w₀

/-- **The world side of an activation of `g` at depth `M`**: the CLIF entry state on `vals`
related to the body-entry world `w₀` (`RelW` with the body's `sp`), the arguments where the body
reads them, and the callees' dead stack below the body's `sp` fits and lies outside the world
and the code. -/
structure WorldEntry (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop) (vals : List Clif.Val)
    (cs : Clif.State) (w₀ : Arm.ArmState) : Prop where
  clif : ClifEntry g vals cs
  rel : RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
    g (spv w₀) cs.frame.slots cs.mem w₀
  args : ArgsAtEntry F g.sig vals w₀
  room : L.K M ≤ (spv w₀).toNat
  dead : ∀ a, StackBelow (L.K M) (spv w₀) a → F a ∧ ¬ L.Img a
  align : (spv w₀).toNat % 16 = 0
  img : ∀ a, L.Img a → F a

/-- **The linking statement at depth `M`**: for every function `g` of `P` and every world-side
activation (addresses `F` outside its world) whose per-function run (program callees running at
most `M` steps) returns, one VCode outcome that every machine-side activation at depth `M`
realises, and (when the linking needs non-interference, `NeedNI`) that every machine-side
activation entered with a body-entry world related to the same CLIF entry, agreeing outside
`F ∪ D` (with the same argument registers and stack-passed argument bytes), realises up to
`F ∪ D`. -/
def Thm (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat)
    (rvals : List Clif.Val) (cm' : Clif.Mem), L.WorldEntry M g F vals cs w₀ →
    Clif.runLoop (Clif.linkEnvN L.P L.base M) (L.P.only g) fuel cs = .returned rvals cm' →
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
      us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A g).vc.RetsSite us ∧
      (∀ G ra s, L.MachEntry M g F G ra s w₀ →
        ∃ n, ActRet ra F G us outs wf s (runX (L.mach M g) n s)) ∧
      (L.NeedNI → ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
        RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
          g (spv w₀) cs.frame.slots cs.mem w₀' →
        SameWorld (fun a => F a ∨ D a) w₀ w₀' →
        (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip vals → regVal w₀' r = regVal w₀ r) →
        (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip vals → ∀ k < v.ty.bytes,
          w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
            w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
        ∀ G ra s, L.MachEntry M g F G ra s w₀' →
          ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n s))

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
structure CallerOk (F : BitVec 64 → Prop) (g : Clif.Function) (uses : List CV) (w t : Arm.ArmState) :
    Prop where
  world : SameWorld F t w
  img : ∀ a, L.Img a → t.mem a = L.imgMem a
  regs : ∀ r ∈ regLocs g.sig, regVal t r = regVal (L.canon g uses w) r
  ra : ∀ k < (L.A g).fb.words.size, Arm.r .PC t + 4 ≠ (L.A g).base + BitVec.ofNat 64 (4 * k)

theorem callerOk_canon (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) (uses : List CV)
    (w : Arm.ArmState) : L.CallerOk F g uses w (L.canon g uses w) := by
  have harg := (hL.argRegs g hg).2.1
  refine ⟨⟨fun f hf => L.r_canon harg uses w hf, fun a ha => ?_, L.program_canon g uses w⟩,
    fun a ha => ?_, fun _ _ => rfl, fun k hk => ?_⟩
  · rw [L.mem_canon, mem_withImg, if_neg (fun hi => ha (himgF a hi))]
  · rw [L.mem_canon, mem_withImg, if_pos ha]
  · simp only [canon, Arm.r_of_w_same, BitVec.sub_add_cancel]
    exact hL.raStar g hg k hk

end LinkSys

/-! ## A call of a program function -/

/-- A register-located parameter at position `i` of a signature's locations is at some position
`j` of the register locations (`regLocs`) and of the register-passed values (`regArgVals`). -/
theorem reg_zip : ∀ (ls : List ArgLoc) (vs : List Clif.Val) {i : Nat} {r : Reg} {v : Clif.Val},
    (ls.zip vs)[i]? = some (.reg r, v) → ∃ j : Nat,
      (ls.filterMap fun l => match l with | .reg r => some r | .stack _ => none)[j]? = some r ∧
      ((ls.zip vs).filterMap fun q => match q.1 with | .reg _ => some q.2 | .stack _ => none)[j]? =
        some v
  | [], _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | l :: ls, v0 :: vs, i, r, v, h => by
    cases i with
    | zero =>
      simp only [List.zip_cons_cons, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, by simp, by simp⟩
    | succ i =>
      simp only [List.zip_cons_cons, List.getElem?_cons_succ] at h
      obtain ⟨j, h1, h2⟩ := reg_zip ls vs h
      cases l with
      | reg r0 =>
        refine ⟨j + 1, ?_, ?_⟩
        · simpa [List.filterMap_cons] using h1
        · simpa [List.filterMap_cons, List.zip_cons_cons] using h2
      | stack o =>
        refine ⟨j, ?_, ?_⟩
        · simpa [List.filterMap_cons] using h1
        · simpa [List.filterMap_cons, List.zip_cons_cons] using h2

namespace LinkSys

variable (L : LinkSys)

/-- The body-entry world of the canonical call agrees with a compatible caller's callee entry. -/
theorem bodyEntryW_compat (hL : L.Ok) {h : Clif.Function} (hh : h ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {uses : List CV}
    {w t : Arm.ArmState} (ht : L.CallerOk F h uses w t) :
    BodyEntryW F (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t)
      (bodyOf (L.A h).af (enterAt (L.A h) (L.canon h uses w))) := by
  have harg := (hL.argRegs h hh).2.1
  have hc := L.callerOk_canon hL hh himgF uses w
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

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → b ∈ l.map (·.2)
  | [], _, _, h => by simp at h
  | (x, y) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · cases h; simp
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- The functions a function of `P` calls have no stack slots. -/
theorem slotFree (hL : L.Ok) : ∀ g ∈ L.P.funcs, ∀ fn e h, g.extern? fn = some e →
    L.P.func? e.name = some h → h.slots = [] :=
  fun g hg _ e h he hf => (hL.calleeSlots g hg h (.inr ⟨e, mem_of_lookup he, hf⟩)).1

/-- **A call of a function `h` of `P`** at depth `M` (its whole-program run returns within `M`
steps) from a world `w` with room for the callee's stack: one VCode outcome of `h`, which the
linked machine's call realises from every caller state compatible with `w` (`CallerOk`), in
particular from the canonical one. -/
theorem progCall (hL : L.Ok) {M : Nat} (hM : 0 < M) (ih : L.Thm (M - 1)) {n : String}
    {h : Clif.Function} (hpf : L.P.func? n = some h) (hsl : h.slots = [])
    (hsz : (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize)
    (hib : (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0 ∨ L.NeedNI)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (L.A h).af + L.K (M - 1) ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (L.A h).af + L.K (M - 1)) (spv w) a → F a ∧ ¬ L.Img a)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem} (hmr : MemRel F L.syms cm w) (hargs : ArgsAt h.sig vals uses w)
    (hsav : StackArgsAvoid F h.sig vals w)
    (hinit : Clif.initState L.P n vals cm = .ok cs)
    (hrun : Clif.runLoop L.base L.P M cs = .returned rvals cm') :
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
      us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A h).vc.RetsSite us ∧
      (∀ t, L.CallerOk F h uses w t → ∃ k,
        L.pcall M h t =
          Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program ∧
        ActRet (Arm.r .PC t + 4) F
          (fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + L.K (M - 1)) (spv w) a)
          us outs wf (enterAt (L.A h) t) (runX (L.mach (M - 1) h) k (enterAt (L.A h) t))) ∧
      (L.NeedNI → ∀ (Z : BitVec 64 → Prop) (t : Arm.ArmState), (∀ a, F a → Z a) →
        SameWorld Z t w → (∀ a, L.Img a → t.mem a = L.imgMem a) →
        (∀ r ∈ regLocs h.sig, regVal t r = regVal (L.canon h uses w) r) →
        (∀ k < (L.A h).fb.words.size, Arm.r .PC t + 4 ≠ (L.A h).base + BitVec.ofNat 64 (4 * k)) →
        MemRel F L.syms cm t →
        (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf h.sig).zip vals → ∀ k < v.ty.bytes,
          t.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
            w.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k)) → ∃ k,
        L.pcall M h t =
          Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program ∧
        ActRet (Arm.r .PC t + 4) Z
          (fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + L.K (M - 1)) (spv w) a)
          us outs wf (enterAt (L.A h) t) (runX (L.mach (M - 1) h) k (enterAt (L.A h) t))) := by
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  subst hname
  have hc := hL.compiled h hh
  have hfr := lowerRFunc_frame hc.alloc
  have hdrop := L.frameDrop_eq hL hh
  have hfs := L.frameSize_mod hL hh
  obtain ⟨hnd, harg, hwid⟩ := hL.argRegs h hh
  obtain ⟨hsl', pl, hcm⟩ := initState_noSlots hpf hsl hinit
  have hce : ClifEntry h vals cs := clifEntry_initState hpf hinit
  -- the per-function run (program callees at most `M - 1` steps)
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (syms := L.syms) (M - 1) hL.names hh
    hL.free (hL.indScope h hh) M cs (by omega) (runInv_entry hh hce)
    (runInv_entry (by simp [Clif.Program.only]) hce) (fun _ => by rw [hcm]; exact hmr.symbols)
    (by rw [hrun]; intro _ e; cases e) (by rw [hrun]; intro e; cases e)
  rw [hrun] at hm
  -- the canonical state and the shared body-entry world
  let cn := L.canon h uses w
  let w₀ := bodyOf (L.A h).af (enterAt (L.A h) cn)
  have hcOk := L.callerOk_canon hL hh himgF uses w
  have hsp0 : spv cn = spv w := hcOk.world.1 _ (by simp [Masked])
  have hspw₀ : spv w₀ = spv w - BitVec.ofNat 64 (frameDrop (L.A h).af) := by
    rw [spv_bodyOf, spv_enterAt, hsp0]
  obtain ⟨-, -, hB⟩ := off_toNat 0 (spv w) (frameDrop (L.A h).af) (by omega)
  -- the callee's outgoing area (in the caller's dead stack) is outside the callee's `F`
  let ib := (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase
  let spb := spv w - BitVec.ofNat 64 (frameDrop (L.A h).af)
  let Fh : BitVec 64 → Prop := fun a => F a ∧ ¬ OutAt ib spb a
  have hib_le : ib ≤ (L.A h).af.frameSize := hsz ▸ intBase_le_size _ _
  have hspb : spb.toNat = (spv w).toNat - frameDrop (L.A h).af := hB
  have hlt := (spv w).isLt
  have hout_reg : ∀ a, OutAt ib spb a →
      StackBelow (frameDrop (L.A h).af + L.K (M - 1)) (spv w) a := by
    intro a ⟨h1, h2⟩
    rw [hspb] at h1 h2
    exact ⟨by omega, by omega⟩
  have hout_F : ∀ a, OutAt ib spb a → F a ∧ ¬ L.Img a := fun a ha => hdead a (hout_reg a ha)
  have hspb_add : ∀ j < ib, OutAt ib spb (spb + BitVec.ofNat 64 j) := by
    intro j hj
    have e : (spb + BitVec.ofNat 64 j).toNat = spb.toNat + j := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), hspb]
      exact Nat.mod_eq_of_lt (by omega)
    exact ⟨by omega, by omega⟩
  have hOut : ∀ (u : Arm.ArmState), spv u = spb →
      (∀ a n, cm.valid a n = true → ∀ k < n, ¬ F (BitVec.ofNat 64 (a + k))) → OutRel Fh ib cm u := by
    intro u hu hv
    refine ⟨by omega, fun j hj hfh => hfh.2 (hu ▸ hspb_add j hj), fun a n hva k hk j hj e => ?_⟩
    rw [hu] at e
    exact hv a n hva k hk (e ▸ (hout_F _ (hspb_add j hj)).1)
  have hWE : L.WorldEntry (M - 1) h Fh vals cs w₀ := by
    refine ⟨hce, ?_, ?_, ?_, ?_, ?_, fun a ha => ⟨himgF a ha, fun ho => (hout_F a ho).2 ha⟩⟩
    · rw [hsl', hcm]
      refine ⟨⟨⟨fun a b hv hb => ?_, fun a n hv => ⟨(hmr.valid a n hv).1,
        fun k hk hf => (hmr.valid a n hv).2 k hk hf.1⟩, hmr.symbols⟩, fun id b hl => by simp at hl,
        hOut w₀ hspw₀ (fun a n hv => (hmr.valid a n hv).2)⟩, rfl, ?_⟩
      · rw [← hmr.bytes a b hv hb]
        simp only [Arm.read_mem, Arm.read_store, w₀, mem_bodyOf, mem_enterAt]
        rw [L.mem_canon, mem_withImg, if_neg]
        intro hi
        exact (hmr.valid a 1 hv).2 0 (by omega) (by simpa using himgF _ hi)
      · simp only [w₀]
        rw [r_bodyOf _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          hcOk.world.1 _ (by simp [Masked])]
        exact herr
    · intro loc v hmem
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
      cases loc with
      | stack off =>
        simp only
        have hx29 : Arm.r (.GPR 29#5) w₀ = spv w - 16#64 := by
          have := x29_bodyOf (L.A h).af (enterAt (L.A h) cn)
          rw [if_pos hfr, spv_enterAt, hsp0] at this
          exact this
        rw [hx29, fp_off_eq]
        refine ⟨fun k hk hf => hsav off v hmem k hk hf.1, ?_⟩
        rw [show Arm.read_mem_bytes v.ty.bytes (spv w + BitVec.ofNat 64 off) w₀ =
            Arm.read_mem_bytes v.ty.bytes (spv w + BitVec.ofNat 64 off) w from
          read_mem_bytes_congr _ _ (fun k hk => by
            simp only [w₀, mem_bodyOf, mem_enterAt]
            rw [L.mem_canon, mem_withImg, if_neg (fun hi => hsav off v hmem k hk (himgF _ hi))])]
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
      rw [hspw₀] at ha
      obtain ⟨h1, h2⟩ := ha
      rw [hB] at h1 h2
      have hd := hdead a ⟨by omega, by omega⟩
      exact ⟨⟨hd.1, fun ⟨o1, o2⟩ => by rw [hspb] at o1; omega⟩, hd.2⟩
    · rw [hspw₀, hB, hdrop]; omega
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmemR, hrs, hall, hni⟩ :=
    ih h hh Fh vals cs w₀ m rvals cm' hWE hm
  -- the callee's live allocations after the call are outside the caller's `F`
  have hmemF : MemRel F L.syms cm' wf := by
    refine ⟨hmemR.bytes, fun a n hv => ?_, hmemR.symbols⟩
    by_cases hib0 : ib = 0
    · obtain ⟨h1, h2⟩ := hmemR.valid a n hv
      exact ⟨h1, fun k hk hf => h2 k hk ⟨hf, fun ⟨o1, o2⟩ => by omega⟩⟩
    · have hv0 := runLoop_valid hL.free (hL.baseNoAlloc ⟨h, hh, hib0⟩) (L.slotFree hL) M
        cs rvals cm' (runInv_entry hh hce)
        (fun hkk => by
          have ⟨k0, hk0, hnk⟩ := hkk
          refine ⟨(hL.indScope k0 hk0 hnk).keep, fun h' hh' hs' =>
            hL.addrSlots ⟨h, hh, hib0⟩ hkk h' hh' ?_⟩
          rw [hcm] at hs'; rwa [← hmr.symbols]) hrun a n hv
      rw [hcm] at hv0
      exact hmr.valid a n hv0
  -- the callee's activation from a caller state `t`
  let G : BitVec 64 → Prop :=
    fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + L.K (M - 1)) (spv w) a
  have hcode : ∀ t, ∀ a, CodeAddr (enterAt (L.A h) t) a → L.Img a := fun t a ha =>
    hL.imgAddr h hh a (by simpa [CodeAddr] using ha)
  have hME : ∀ t w₀', spv t = spv w → Arm.r .ERR t = .None →
      (∀ a, L.Img a → t.mem a = L.imgMem a) →
      (∀ k < (L.A h).fb.words.size, Arm.r .PC t + 4 ≠ (L.A h).base + BitVec.ofNat 64 (4 * k)) →
      BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀' →
      L.MachEntry (M - 1) h Fh G (Arm.r .PC t + 4) (enterAt (L.A h) t) w₀' := by
    intro t w₀' hst herrt himgt hrat hbw
    have hspt : spv (enterAt (L.A h) t) = spv w := by rw [spv_enterAt]; exact hst
    have hFrame : frameWG (L.K (M - 1)) ib (RAFrame.compute (L.A h).vcp (L.A h).rf).size
        (L.A h).af G (enterAt (L.A h) t) = Fh := by
      funext a
      apply propext
      rw [hsz, frameWG_out hfr (by rw [hspt, ← hdrop]; exact hroom) hib_le, ← hdrop, hspt]
      constructor
      · rintro (⟨hb, hno⟩ | hc | hg)
        · exact ⟨(hdead a hb).1, hno⟩
        · exact ⟨himgF a (hcode t a hc), fun ho => (hout_F a ho).2 (hcode t a hc)⟩
        · exact ⟨hg.1, fun ho => hg.2 (hout_reg a ho)⟩
      · intro ⟨hF, hno⟩
        by_cases hb : StackBelow (frameDrop (L.A h).af + L.K (M - 1)) (spv w) a
        · exact .inl ⟨hb, hno⟩
        · exact .inr (.inr ⟨hF, hb⟩)
    refine ⟨⟨by simp, fun k wd hk => hL.imgCode h hh _ (fun a ha => by
        rw [mem_enterAt]; exact himgt a ha) k wd hk, by simp, ?_, x30_enterAt _ _, hrat, ?_,
        hL.fits h hh⟩, ?_, fun a ha => ?_, hFrame,
      fun a ha => ⟨himgF a ha, fun hb => (hdead a hb).2 ha⟩,
      fun a ha => by rw [mem_enterAt]; exact himgt a ha, hbw⟩
    · rw [r_enterAt _ _ (by simp) (by simp)]; exact herrt
    · rw [hspt]; exact hal
    · refine stackRoom_of (by rw [hspt, ← hdrop]; exact hroom) fun a ha hb => ?_
      rw [hspt, ← hdrop] at hb
      exact (hdead a hb).2 (hcode t a ha)
    · rw [hspt]; exact ha.2
  have hpcall : ∀ t k, (∀ k' < (L.A h).fb.words.size,
      Arm.r .PC t + 4 ≠ (L.A h).base + BitVec.ofNat 64 (4 * k')) →
      ArmRet (Arm.r .PC t + 4) (enterAt (L.A h) t)
        (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) →
      (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)).program = (enterAt (L.A h) t).program →
      L.pcall M h t =
        Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program := by
    intro t k hra hret hprog
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    show linkedCall _ _ _ = _
    exact linkedCall_eq hc.layout hlm hra ⟨hret.pc, hret.err, hprog.trans (program_enterAt _ _)⟩
  have hx29 : Arm.r (.GPR 29#5) w₀ = spv w - 16#64 := by
    have := x29_bodyOf (L.A h).af (enterAt (L.A h) cn)
    rw [if_pos hfr, spv_enterAt, hsp0] at this
    exact this
  -- non-interference: a caller state `t` agreeing with `w` outside `Z ⊇ F`, entered with its
  -- own body-entry world
  have key2 : L.NeedNI → ∀ (Z : BitVec 64 → Prop) (t : Arm.ArmState), (∀ a, F a → Z a) →
      SameWorld Z t w → (∀ a, L.Img a → t.mem a = L.imgMem a) →
      (∀ r ∈ regLocs h.sig, regVal t r = regVal (L.canon h uses w) r) →
      (∀ k < (L.A h).fb.words.size, Arm.r .PC t + 4 ≠ (L.A h).base + BitVec.ofNat 64 (4 * k)) →
      MemRel F L.syms cm t →
      (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf h.sig).zip vals → ∀ k < v.ty.bytes,
        t.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
          w.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k)) → ∃ k,
      L.pcall M h t =
        Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program ∧
      ActRet (Arm.r .PC t + 4) Z G us outs wf (enterAt (L.A h) t)
        (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) := by
    intro hN Z t hFZ hZ himgt hregt hrat hmt hstkt
    have hst : spv t = spv w := hZ.1 _ (by simp [Masked])
    have herrt : Arm.r .ERR t = .None := by rw [hZ.1 _ (by simp [Masked])]; exact herr
    let w₀' := bodyOf (L.A h).af (enterAt (L.A h) t)
    let D : BitVec 64 → Prop := fun a => Z a ∧ ¬ Fh a
    have hspw₀' : spv w₀' = spb := by
      simp only [w₀']; rw [spv_bodyOf, spv_enterAt, hst]
    have hbw : BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀' :=
      ⟨spv_bodyOf _ _, x29_bodyOf _ _, fun r hr => regVal_bodyOf _ _
        (harg r (hL.entryRegs h hh r hr)), fun f hf h29 h31 => r_bodyOf _ _ h29 h31,
        fun a _ => by simp [w₀'], by simp [w₀']⟩
    have hrel' : RelW ⟨Fh, L.syms, (L.A h).af.slotBase, ib⟩ h (spv w₀) cs.frame.slots cs.mem w₀' := by
      rw [hsl', hcm]
      refine ⟨⟨⟨fun a b hv hb => ?_, fun a n hv => ⟨(hmr.valid a n hv).1,
        fun k hk hf => (hmr.valid a n hv).2 k hk hf.1⟩, hmr.symbols⟩, fun id b hl => by simp at hl,
        hOut w₀' hspw₀' (fun a n hv => (hmr.valid a n hv).2)⟩, by rw [hspw₀', hspw₀], ?_⟩
      · have := hmt.bytes a b hv hb
        simp only [Arm.read_mem, Arm.read_store, w₀', mem_bodyOf, mem_enterAt] at this ⊢
        exact this
      · simp only [w₀']
        rw [r_bodyOf _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp)]
        exact herrt
    have hsw : SameWorld (fun a => Fh a ∨ D a) w₀ w₀' := by
      refine ⟨fun f hf => ?_, fun a ha => ?_, by simp [w₀, w₀']⟩
      · by_cases h29 : f = .GPR 29#5
        · subst h29
          have e1 := x29_bodyOf (L.A h).af (enterAt (L.A h) cn)
          have e2 := x29_bodyOf (L.A h).af (enterAt (L.A h) t)
          simp only [xreg] at e1 e2
          rw [e1, e2, spv_enterAt, spv_enterAt, hsp0, hst, if_pos hfr, if_pos hfr]
        by_cases h31 : f = .GPR 31#5
        · subst h31
          show spv w₀ = spv w₀'
          rw [hspw₀, hspw₀']
        have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
        have h30 : f ≠ .GPR 30#5 := by rintro rfl; exact hf (by simp [Masked])
        rw [r_bodyOf _ _ h29 h31, r_bodyOf _ _ h29 h31, r_enterAt _ _ hpc h30, r_enterAt _ _ hpc h30,
          hcOk.world.1 f hf, hZ.1 f hf]
      · have hnZ : ¬ Z a := fun hz => by
          by_cases hf : Fh a
          · exact ha (.inl hf)
          · exact ha (.inr ⟨hz, hf⟩)
        simp only [w₀, w₀', mem_bodyOf, mem_enterAt]
        rw [hcOk.world.2.1 a (fun hf => hnZ (hFZ a hf)), hZ.2.1 a hnZ]
    have hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf h.sig).zip vals →
        regVal w₀' r = regVal w₀ r := by
      intro r v hm
      have hrl : r ∈ regLocs h.sig :=
        List.mem_filterMap.mpr ⟨.reg r, (List.of_mem_zip hm).1, rfl⟩
      have hrA := harg r hrl
      simp only [w₀, w₀']
      rw [regVal_bodyOf _ _ hrA, regVal_bodyOf _ _ hrA, regVal_enterAt _ _ hrA,
        regVal_enterAt _ _ hrA, hregt r hrl]
    have hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf h.sig).zip vals → ∀ k < v.ty.bytes,
        w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
          w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) := by
      intro off v hm k hk
      rw [hx29, fp_off_eq]
      have hnF := hsav off v hm k hk
      simp only [w₀, w₀', mem_bodyOf, mem_enterAt]
      rw [hstkt off v hm k hk, hcOk.world.2.1 _ hnF]
    obtain ⟨k, hret⟩ := hni hN D w₀' hrel' hsw hreg hstk G (Arm.r .PC t + 4) (enterAt (L.A h) t)
      (hME t w₀' hst herrt himgt hrat hbw)
    refine ⟨k, hpcall t k hrat hret.ret hret.prog, ⟨hret.ret, hret.regs, fun a ha => hret.mem a
      (fun h' => ha (h'.elim (fun h1 => hFZ a h1.1) (fun h2 => h2.1))), hret.fields, hret.gkeep,
      hret.prog⟩⟩
  refine ⟨us, outs, wf, hus, hlen, hhold, hmemF, hrs, fun t ht => ?_, key2⟩
  by_cases hN : L.NeedNI
  · refine key2 hN F t (fun _ h => h) ht.world ht.img ht.regs ht.ra ⟨fun a b hv hb => ?_,
      hmr.valid, hmr.symbols⟩ fun off v hm k hk => ht.world.2.1 _ (hsav off v hm k hk)
    rw [← hmr.bytes a b hv hb]
    simp only [Arm.read_mem, Arm.read_store]
    exact ht.world.2.1 _ (by simpa using (hmr.valid a 1 hv).2 0 (by omega))
  · -- no outgoing area: the canonical body-entry world is the actual activation's
    have hib0 : ib = 0 := hib.resolve_right hN
    have hFh : Fh = F := funext fun a => propext ⟨fun h => h.1, fun h => ⟨h, fun ⟨o1, o2⟩ => by
      omega⟩⟩
    have hbw : BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀ := by
      rw [hFh]; exact L.bodyEntryW_compat hL hh himgF ht
    have hst : spv t = spv w := ht.world.1 _ (by simp [Masked])
    have herrt : Arm.r .ERR t = .None := by rw [ht.world.1 _ (by simp [Masked])]; exact herr
    obtain ⟨k, hret⟩ := hall G (Arm.r .PC t + 4) (enterAt (L.A h) t)
      (hME t w₀ hst herrt ht.img ht.ra hbw)
    exact ⟨k, hpcall t k ht.ra hret.ret hret.prog, ⟨hret.ret, hret.regs, fun a ha => hret.mem a
      (fun h' => ha h'.1), hret.fields, hret.gkeep, hret.prog⟩⟩

end LinkSys

theorem func?_of_mem {P : Clif.Program} (hnd : (P.funcs.map (·.name)).Nodup) {h : Clif.Function}
    (hh : h ∈ P.funcs) : P.func? h.name = some h := by
  cases e : P.func? h.name with
  | none => exact absurd rfl (Clif.Program.func?_none e h hh)
  | some g =>
    obtain ⟨hg, hgn⟩ := Clif.Program.func?_some e
    rw [Clif.name_inj hnd hg hh hgn]

/-! ## The hooks and the external semantics of the linked system -/

namespace LinkSys

variable (L : LinkSys)

theorem hooks_base {M : Nat} {d : Option String} (h : L.BaseDest d) (u : Arm.ArmState)
    (hn : d = none → (blrTarget u).bind (symCallee L.Xb L.P) = none) :
    (L.hooks M).call d u = L.Hb.call d u := by
  rw [hooks_call]
  rcases h with rfl | ⟨n, rfl, hpf⟩
  · simp only [callHook, hn rfl]
  · simp only [callHook, hpf]

theorem hooks_tls (M : Nat) : (L.hooks M).tls = L.Hb.tls := by cases M <;> rfl

theorem hooks_some {M : Nat} {n : String} {h : Clif.Function} (hpf : L.P.func? n = some h)
    (u : Arm.ArmState) : (L.hooks M).call (some n) u = L.pcall M h u := by
  rw [hooks_call]; simp only [callHook, hpf]

theorem hooks_none {M : Nat} {h : Clif.Function} {u : Arm.ArmState}
    (hb : (blrTarget u).bind (symCallee L.Xb L.P) = some h) :
    (L.hooks M).call none u = L.pcall M h u := by
  rw [hooks_call]; simp only [callHook, hb]

theorem pcall_pc (M : Nat) (h : Clif.Function) (u : Arm.ArmState) :
    (L.pcall M h u).program = u.program ∧ Arm.r .PC (L.pcall M h u) = Arm.r .PC u + 4 := by
  have hj : (junkAt u).program = u.program ∧ Arm.r .PC (junkAt u) = Arm.r .PC u + 4 := by
    simp only [junkAt, Arm.w_program, true_and]
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_same]
  cases M with
  | zero => exact hj
  | succ M =>
    simp only [pcall, linkedCall]
    split
    · rename_i hex
      have := Classical.choose_spec hex
      exact ⟨rfl, by rw [r_set_program]; exact this.1⟩
    · exact hj

theorem X_base {M : Nat} {g : Clif.Function} {n : String} (hn : L.P.func? n = none)
    (uses : List CV) (w : Arm.ArmState) (F : BitVec 64 → Prop) :
    (L.X M g F).call (some n) uses w = L.Xb.call (some n) uses w := by
  simp [X, hn]

theorem X_prog {M : Nat} {g : Clif.Function} {n : String} {h : Clif.Function}
    (hpf : L.P.func? n = some h) (uses : List CV) (w : Arm.ArmState) (F : BitVec 64 → Prop) :
    (L.X M g F).call (some n) uses w = L.progX M F h uses w := by
  simp [X, hpf]

theorem X_none {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} {u : CV} {args : List CV}
    {w : Arm.ArmState} (hn : symCallee L.Xb L.P (lo64 u) = none) :
    (L.X M g F).call none (u :: args) w = L.Xb.call none (u :: args) w := by
  simp [X, hn]

open Classical in
theorem X_ind {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} {u : CV} {args : List CV}
    {w : Arm.ArmState}
    {h : Clif.Function} (hs : symCallee L.Xb L.P (lo64 u) = some h) :
    (L.X M g F).call none (u :: args) w = if DeclN g h.name ∧ args.length = (regLocs h.sig).length
      then L.progX M F h args w else none := by
  simp only [X, hs]

theorem progX_ext {M : Nat} {F : BitVec 64 → Prop} {h : Clif.Function}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hx : L.progX M F h uses w = some (outs, w')) :
    Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  unfold progX at hx
  split at hx
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨-, rfl⟩ := hx
    exact ⟨hc.2, by rw [(L.pcall_pc M h _).1, L.program_canon]⟩
  · cases hx

theorem X_ext (hL : L.Ok) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} {d : Option String}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hx : (L.X M g F).call d uses w = some (outs, w'))
    (herr : Arm.r .ERR w = .None) : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  cases d with
  | some n =>
    cases hpf : L.P.func? n with
    | none =>
      rw [L.X_base hpf _ _ F] at hx
      exact hL.baseExt _ _ _ _ _ (.inr ⟨n, rfl, hpf⟩) hx herr
    | some h =>
      rw [L.X_prog hpf _ _ F] at hx
      exact L.progX_ext hx
  | none =>
    cases uses with
    | nil => exact hL.baseExt _ _ _ _ _ (.inl rfl) hx herr
    | cons u args =>
      cases hs : symCallee L.Xb L.P (lo64 u) with
      | none =>
        rw [L.X_none hs] at hx
        exact hL.baseExt _ _ _ _ _ (.inl rfl) hx herr
      | some h =>
        rw [L.X_ind hs] at hx
        split at hx
        · exact L.progX_ext hx
        · cases hx

end LinkSys

/-! ## The callee contract of the linked machine -/

theorem setVal_regVal (t : Arm.ArmState) (r : Reg) : setVal r (regVal t r) = regVal t r := by
  cases r with
  | x n =>
    simp only [setVal, regVal, ofX, lo64]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := (Arm.r (.GPR (rnum n)) t).isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  | _ => rfl

theorem stackBelow_mono {m n : Nat} {sp a : BitVec 64} (h : StackBelow m sp a) (hmn : m ≤ n) :
    StackBelow n sp a := ⟨h.1, by have := h.2; omega⟩

theorem regVal_set_program (s : Arm.ArmState) (p : Arm.Program) (r : Reg) :
    regVal (Arm.set_program s p) r = regVal s r := by
  cases r <;> simp only [regVal] <;> first | rfl | rw [r_set_program]

namespace LinkSys

variable (L : LinkSys)

theorem K_succ (M : Nat) (hM : 0 < M) : L.K M = L.K (M - 1) + L.D := by
  simp only [K]
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  simp [Nat.mul_succ]

/-- **The core of the operand-view obligation of a call of the function `h` of `P`** (by `bl`
or `blr`) in the linked machine at depth `M` (from the linking statement at depth `M - 1`): from
a caller state `t` whose arguments are in `h`'s parameter registers (`hLu`), the linked call
gives `progX`'s results (in x0.., `hLd`) and world. -/
theorem progOsCore (hL : L.Ok) {M : Nat} (ih : 0 < M → L.Thm (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : (∃ info, L.ProgSite g info h) ∨
      ∃ e ∈ g.externs.map (·.2), L.P.func? e.name = some h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} (hLu : Lu.map (·.2) = regLocs h.sig)
    (hLd : (Ld.map (·.1)).take (sigRets h.sig).length =
      (List.range (sigRets h.sig).length).map Reg.x)
    {info : CallInfo} (hdefs0 : info.defs = callDefs Ld)
    {ops : Array Operand} {regs : Array Reg}
    (hdefs : ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)))
    {t w w' : Arm.ArmState} {outs : List CV}
    (hK : L.K M ≤ (spOf t).toNat) (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hra : ∀ k < (L.A h).fb.words.size,
      Arm.r .PC t + 4 ≠ (L.A h).base + BitVec.ofNat 64 (4 * k))
    (hsw : SameWorld F t w)
    (hx : L.progX M F h (Lu.map (fun q => regVal t q.2)) w = some (outs, w')) :
    SameWorld F (L.pcall M h t) w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (L.K M) (spOf t) a) t (L.pcall M h t) ∧
      (∀ p ∈ defRegs ops regs outs, regVal (L.pcall M h t) p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ (MInst.call info).clobbers → regVal (L.pcall M h t) r = regVal t r) ∧
      (∀ r ∈ (MInst.call info).clobbers, r ∈ calleeSaved →
        ckeep r (regVal (L.pcall M h t) r) = ckeep r (regVal t r)) := by
  have hpf := func?_of_mem hL.names hh
  obtain ⟨hsl, hsz⟩ := hL.calleeSlots g hg h hcallee
  have hib : (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0 ∨ L.NeedNI := by
    by_cases h0 : (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0
    · exact .inl h0
    · exact .inr ⟨g, hg, h, hcallee, h0⟩
  obtain ⟨hnd, harg, -⟩ := hL.argRegs h hh
  generalize huses : Lu.map (fun q => regVal t q.2) = uses at hx
  unfold progX at hx
  have hcond : L.Cond M F h uses w ∧
      Arm.r .ERR (L.pcall M h (L.canon h uses w)) = .None :=
    Classical.byContradiction fun hc => by rw [if_neg hc] at hx; cases hx
  rw [if_pos hcond] at hx
  obtain ⟨⟨hM, herrw, halw, hroom, hdead, vals, cm, cs, rvals, cm', hmr, hargs, hsav, hinit, hrun⟩,
    -⟩ := hcond
  simp only [Option.some.injEq, Prod.mk.injEq] at hx
  obtain ⟨rfl, rfl⟩ := hx
  obtain ⟨us, outsV, wf, hus, hlen, hhold, hmemR, hrs, hcall, -⟩ :=
    L.progCall hL hM (ih hM) hpf hsl hsz hib himgF herrw halw hroom hdead hmr hargs hsav hinit hrun
  -- the caller state is compatible with the canonical one
  have hcOk : L.CallerOk F h uses w t := by
    refine ⟨hsw, fun a ha => (hG a (himgG a ha)).trans (himgS a ha), fun r hr => ?_,
      hra⟩
    rw [← hLu] at hr
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hrA : r.isArgReg = true := harg r (by rw [← hLu]; exact List.mem_of_getElem? hj)
    have hu : uses[j]? = some (regVal t r) := by
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hj
      obtain ⟨q, hq, rfl⟩ := hj
      simp [← huses, hq]
    rw [L.regVal_canon _ _ _ hrA, placeArgs_regVal _ _ _ hnd harg (by rw [← hLu]; exact hj) hu,
      setVal_regVal]
  obtain ⟨ks, hs_eq, hs_ret⟩ := hcall t hcOk
  obtain ⟨kc, hc_eq, hc_ret⟩ := hcall _ (L.callerOk_canon hL hh himgF uses w)
  -- the allocated call
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the world
    rw [hs_eq, hc_eq]
    refine ⟨fun f hf => ?_, fun a ha => ?_, ?_⟩
    · rw [r_set_program, r_set_program]
      by_cases h29 : f = .GPR 29#5
      · subst h29
        have e1 := hs_ret.ret.savedX 29 (by decide)
        have e2 := hc_ret.ret.savedX 29 (by decide)
        simp only [xreg] at e1 e2
        rw [show (BitVec.ofNat 5 29) = 29#5 from rfl] at e1 e2
        rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          (L.callerOk_canon hL hh himgF uses w).world.1 _ hf, hsw.1 _ hf]
      by_cases h31 : f = .GPR 31#5
      · subst h31
        have e1 := hs_ret.ret.sp
        have e2 := hc_ret.ret.sp
        simp only [spv] at e1 e2
        rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          (L.callerOk_canon hL hh himgF uses w).world.1 _ hf, hsw.1 _ hf]
      · rw [hs_ret.fields f hf h29 h31, hc_ret.fields f hf h29 h31]
    · simp only [mem_set_program]
      rw [hs_ret.mem a ha, hc_ret.mem a ha]
    · simp only [program_set_program]
      rw [hsw.2.2, L.program_canon]
  · -- the frame outside the dead stack
    rw [hs_eq]
    refine ⟨?_, fun a ⟨ha, hb⟩ => ?_⟩
    · show spv (Arm.set_program _ _) = spv t
      simp only [spv]; rw [r_set_program]
      have := hs_ret.ret.sp
      simp only [spv] at this
      rw [this, r_enterAt _ _ (by simp) (by simp)]
    · rw [mem_set_program, hs_ret.gkeep a ⟨ha, fun hb' => hb ?_⟩, mem_enterAt]
      have hd := hL.depth h hh
      have hsp : spv w = spOf t := (hsw.1 (.GPR 31#5) (by simp [Masked])).symm
      rw [hsp] at hb'
      exact stackBelow_mono hb' (by rw [L.K_succ M hM]; omega)
  · -- the results
    intro p hp
    obtain ⟨⟨op, r⟩, x⟩ := p
    rw [defRegs, hdefs] at hp
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hp
    simp only [List.getElem?_zip_eq_some] at hj
    obtain ⟨⟨-, hr⟩, hx⟩ := hj
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hx
    obtain ⟨j2, hj2, rfl⟩ := hx
    have hjr : j < (sigRets h.sig).length := by
      have := (List.getElem?_eq_some_iff.mp hj2).1; simpa using this
    have e : ((Ld.map (·.1)).take (sigRets h.sig).length)[j]? = (Ld.map (·.1))[j]? := by
      rw [List.getElem?_take]; simp [hjr]
    rw [← e, hLd] at hr
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hr
    obtain ⟨j1, hj1, rfl⟩ := hr
    rw [List.getElem?_range hjr, Option.some.injEq] at hj1 hj2
    subst hj1 hj2
    show regVal _ (Reg.x j) = regVal _ (Reg.x j)
    rw [hs_eq, regVal_set_program, hc_eq, regVal_set_program]
    -- the `j`-th result register is a return register of the callee
    have hrt := Clif.runLoop_returned_tys hL.free M cs rvals cm'
      (runInv_entry hh (clifEntry_initState hpf hinit)) hrun
    have hbot : cs.bottom = h := by
      have hce := clifEntry_initState (f := h) hpf hinit
      simp [Clif.State.bottom, hce.callers, hce.func]
    rw [hbot] at hrt
    have hlr : (sigRets h.sig).length ≤ us.length := by
      cases hsr : h.sig.params.any (·.purpose == .sret) with
      | true => exact hL.sretRets h hh hsr us hrs
      | false =>
        rw [sigRets_of_noSret hsr, hlen]
        have := congrArg List.length hrt
        simp only [List.length_map, Clif.AbiParam.tys] at this
        rw [← this]; exact hhold.1
    have hju : j < us.length := by omega
    have hus_j : us[j]? = some ((us[j]'hju).1, Reg.x j) := by
      have := congrArg (·[j]?) hus
      simp only [List.getElem?_map, List.getElem?_range hju, List.getElem?_eq_getElem hju,
        Option.map_some, Option.some.injEq] at this
      rw [List.getElem?_eq_getElem hju, ← this]
    have hoj : outsV[j]? = some (outsV[j]'(by omega)) := List.getElem?_eq_getElem _
    rw [hs_ret.regs j _ _ _ hus_j hoj, hc_ret.regs j _ _ _ hus_j hoj]
  · -- the registers the callee preserves
    intro r hr hnd' hnc
    rw [hs_eq, regVal_set_program]
    have hnotd : r ∉ Ld.map (·.1) := by
      intro hm
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      have hmem : (⟨⟨q.2, .int, .def, .late, .fixed q.1⟩, q.1⟩ : Operand × Reg) ∈
          (ops.zip regs).toList := by
        have h1 : (⟨⟨q.2, .int, .def, .late, .fixed q.1⟩, q.1⟩ : Operand × Reg) ∈
            (callDefOps Ld).zip (Ld.map (·.1)) := List.mem_iff_getElem?.mpr (by
          obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
          exact ⟨i, by simp [callDefOps, List.getElem?_zip_eq_some, hi]⟩)
        rw [← hdefs] at h1
        exact (List.mem_filter.mp h1).1
      exact hnd' _ hmem rfl rfl
    have hnD : r ∉ defaultAapcsClobbers := by
      intro hm
      apply hnc
      simp only [MInst.clobbers, List.mem_filter, hm, true_and, hdefs0, callDefs]
      simp only [List.any_map, Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
      exact fun q hq e => hnotd (List.mem_map.mpr ⟨q, hq, by simpa using e⟩)
    rcases allocatable_cases hr with ⟨m, rfl, hm, h16, h17, h18⟩ | ⟨m, rfl, hm⟩
    · have h19 : 19 ≤ m :=
        Classical.byContradiction fun hc => hnD (by simp [defaultAapcsClobbers]; omega)
      have e := hs_ret.ret.savedX m (by simp [calleeSavedX]; exact ⟨m - 19, by omega, by omega⟩)
      simp only [xreg] at e
      simp only [regVal]
      rw [show rnum m = BitVec.ofNat 5 m from rfl, e, r_enterAt _ _ (by simp) (fun e' => by
        have := congrArg (fun f => match f with | Arm.StateField.GPR i => i.toNat | _ => 0) e'
        simp [rnum_toNat (show m < 32 by omega)] at this; omega)]
    · exact absurd (by simp [defaultAapcsClobbers]; omega) hnD
  · -- the callee-saved registers the call clobbers: the low halves of v8–v15
    intro r hr hcs
    rw [hs_eq, regVal_set_program]
    have hrD : r ∈ defaultAapcsClobbers := (List.mem_filter.mp hr).1
    simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range] at hcs
    rcases hcs with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact absurd hrD (by simp [defaultAapcsClobbers]; omega)
    · have e := hs_ret.ret.savedV (8 + i) (by omega) (by omega)
      simp only [ckeep, regVal]
      rw [show rnum (8 + i) = BitVec.ofNat 5 (8 + i) from rfl, e,
        r_enterAt _ _ (by simp) (by simp)]


/-- **The operand-view obligation of a call (`bl`) of a function of `P`** in the linked machine at
depth `M` (from the linking statement at depth `M - 1`). -/
theorem progOs (hL : L.Ok) {M : Nat} (ih : 0 < M → L.Thm (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} {h : Clif.Function} (hsite : L.ProgSite g info h) (ctx : FnCtx) :
    CallSoundCtlG F (L.K M) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csem F ctx (L.X M g F)) (.call info) .next := by
  have ⟨_, n, hdest, hpf⟩ := hsite
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  subst hname
  obtain ⟨n', Lu, Ld, hinfo, hLu, hLd⟩ := hL.callRegs g hg info h hsite
  subst hinfo
  cases hdest
  intro t hK hD hG c wh ops regs i' w outs w' hops hst hasg hP hsw hal herr hsem
  rw [operands_call_sym] at hops
  cases hops
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
  have hregs := callRegs_eq (regs := regs) (by simpa using hsz')
    (fun p hp r hr => (hloc p hp).2 r hr)
  rw [call_useVals hregs] at hsem
  have hx : L.progX M F h (Lu.map (fun q => regVal t q.2)) w = some (outs, w') := by
    simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    rw [L.X_prog hpf] at hx
    exact hx
  obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
  exact ⟨L.pcall M h t, by simp only [callExec, hal, ↓reduceIte, L.hooks_some hpf],
    L.progOsCore hL ih hg hh (.inl ⟨_, hsite⟩) himgF himgG himgS hLu hLd rfl (call_defs hregs) hK hG
      (hL.raCall g hg _ h hsite _ hP.callPc) hsw hx⟩

/-- **The operand-view obligation of a `blr` call** in the linked machine at depth `M`: the
target register holds the address of a function of `P` that `g` declares (the linked call of it,
`progOsCore`), of another function of `P` (`X` undefined), or of no function of `P` (the
base's). -/
theorem progOsReg (hL : L.Ok) {M : Nat} (ih : 0 < M → L.Thm (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) (hreg : ∀ n, info.dest ≠ .sym n)
    (ctx : FnCtx) :
    CallSoundCtlG F (L.K M) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csem F ctx (L.X M g F)) (.call info) .next := by
  obtain ⟨tv, Lu, Ld, rfl, hregs⟩ := hL.blrRegs g hg info hsite hreg
  intro t hK hD hG c wh ops regs i' w outs w' hops hst hasg hP hsw hal herr hsem
  have hops0 := hops
  rw [operands_call_reg] at hops
  cases hops
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
  obtain ⟨r0, hregs0⟩ := callRegs_eq_reg (regs := regs) (by simpa using hsz')
    (fun p hp r hr => (hloc p hp).2 r hr)
  -- the target register: an allocatable X register
  obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
    have hmem : (tgtOp tv, Loc.reg r0) ∈
        (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
      simp [Array.toList_zip, Array.toList_map, hregs0]
    obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
    exact ⟨n, hn, h29, h16⟩
  have hsem0 := hsem
  rw [call_useVals_reg hregs0] at hsem
  -- the allocated call: `blr x n0`
  obtain ⟨r1, us', ds', hr1, rfl⟩ := assign_call_reg hasg
  have h0 : regs[0]? = some (.x n0) := by
    rw [← Array.getElem?_toList, hregs0]; rfl
  rw [h0] at hr1
  cases hr1
  -- the target the machine reads
  have hc := hL.compiled g hg
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have htgt : blrTarget t = some (lo64 (regVal t (.x n0))) := by
    obtain ⟨j, x, tt, hj, hx, hpc⟩ := hP
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    rw [lo64_regVal_x]
    exact blrTarget_of hc.layout hlm hj hn0 hpc
      (fun k wd hk => hL.imgCode g hg t (fun a ha => (hG a (himgG a ha)).trans (himgS a ha)) k wd hk)
  -- the external semantics' call
  have hx : (L.X M g F).call none (regVal t (.x n0) :: Lu.map (fun q => regVal t q.2)) w =
      some (outs, w') := by
    simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    exact hx
  cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
  | none =>
    -- no function of `P` at the target: the base's contract
    have hb : (blrTarget t).bind (symCallee L.Xb L.P) = none := by rw [htgt]; exact hs
    rw [L.X_none hs] at hx
    have hsem' : csem F ctx L.Xb (.call ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩)
        (useVals (tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray regs t) w =
        some (outs, w', .next) := by
      rw [call_useVals_reg hregs0]; simp [csem, hx]
    obtain ⟨s', hex, rest⟩ := hL.baseOs g hg _ hsite (.inl rfl) F (L.K M) G s0
      (CallAt (L.A g).fa (L.A g).base) ctx t hK hD hG c wh _ regs _ w outs w' hops0 hst hasg hP hsw
      hal herr hsem'
    refine ⟨s', ?_, rest⟩
    simp only [callExec] at hex ⊢
    rw [L.hooks_base (.inl rfl) t (fun _ => hb)]
    exact hex
  | some h =>
    rw [L.X_ind hs] at hx
    split at hx
    · rename_i hdecl
      have hh : h ∈ L.P.funcs := List.mem_of_find?_eq_some hs
      have hpf := func?_of_mem hL.names hh
      obtain ⟨hLu, hLd⟩ := hregs h hh hdecl.1 (by rw [← hdecl.2, List.length_map])
      have hb : (blrTarget t).bind (symCallee L.Xb L.P) = some h := by rw [htgt]; exact hs
      obtain ⟨e, he, hen⟩ : ∃ e ∈ g.externs.map (·.2), e.name = h.name := by
        obtain ⟨e, he, hen⟩ := List.mem_map.mp hdecl.1.1
        exact ⟨e.2, List.mem_map_of_mem he, hen⟩
      exact ⟨L.pcall M h t, by simp only [callExec, hal, ↓reduceIte, L.hooks_none hb],
        L.progOsCore hL ih hg hh (.inr ⟨e, he, by rw [hen]; exact hpf⟩) himgF himgG himgS hLu hLd rfl
          (call_defs_reg hregs0) hK hG
          (hL.raBlr g hg _ hsite hreg h hh hdecl.1 _ hP.callPc) hsw hx⟩
    · cases hx

end LinkSys

namespace LinkSys

variable (L : LinkSys)

/-- **The callee contract of the linked machine at depth `M`** for an activation of `g` (from the
linking statement at depth `M - 1`). -/
theorem MachEntry.imgF {M : Nat} {g : Clif.Function} {F G : BitVec 64 → Prop} {ra : BitVec 64}
    {s w₀ : Arm.ArmState} (he : L.MachEntry M g F G ra s w₀) : ∀ a, L.Img a → F a :=
  fun a ha => he.hF ▸ .inr (he.imgG a ha)

theorem calleeOk (hL : L.Ok) {M : Nat} (ih : 0 < M → L.Thm (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry M g F G ra s w₀) :
    CalleeOkG F (L.K M) G s (CallAt (L.A g).fa (L.A g).base) (L.X M g F) (L.hooks M)
      (L.A g).vcp.CallSite where
  os ctx info hsite := by
    cases hd : info.dest with
    | reg r =>
      exact L.progOsReg hL ih hg he.imgF he.imgG he.imgS hsite (fun n => by rw [hd]; simp) ctx
    | sym n =>
    have hdest := hd
    cases hpf : L.P.func? n with
    | some h => exact L.progOs hL ih hg he.imgF he.imgG he.imgS ⟨hsite, n, hdest, hpf⟩ ctx
    | none =>
      have hb : L.BaseDest (destOf info) := .inr ⟨n, by simp [destOf, hdest], hpf⟩
      have h0 := hL.baseOs g hg info hsite hb F (L.K M) G s (CallAt (L.A g).fa (L.A g).base) ctx
      intro t h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg h4 hsw hal herr hsem
      obtain ⟨d, us, ds⟩ := info
      simp only at hdest
      subst hdest
      have hsem' : csem F ctx L.Xb (.call ⟨.sym n, us, ds⟩) (useVals ops regs t) w =
          some (outs, w', .next) := by
        rw [← hsem]; simp [csem, L.X_base hpf _ _ F]
      obtain ⟨s', hex, rest⟩ :=
        h0 t h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg h4 hsw hal herr hsem'
      refine ⟨s', ?_, rest⟩
      obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
      simp only [callExec] at hex ⊢
      rw [L.hooks_base (.inr ⟨n, rfl, hpf⟩) t (fun h => by cases h)]
      exact hex
  pc d u herr hal := by
    cases d with
    | none =>
      cases hb : (blrTarget u).bind (symCallee L.Xb L.P) with
      | none =>
        rw [L.hooks_base (.inl rfl) u (fun _ => hb)]; exact hL.basePc _ _ (.inl rfl) herr hal
      | some h => rw [L.hooks_none hb]; exact (L.pcall_pc M h u).2
    | some n =>
      cases hpf : L.P.func? n with
      | none =>
        rw [L.hooks_base (.inr ⟨n, rfl, hpf⟩) u (fun h => by cases h)]
        exact hL.basePc _ _ (.inr ⟨n, rfl, hpf⟩) herr hal
      | some h => rw [L.hooks_some hpf]; exact (L.pcall_pc M h u).2
  ext _ _ _ _ _ hx herr := L.X_ext hL hx herr

/-- **The `try_call` contract of the linked machine at depth `M`** for an activation of `g`: at
a `try_call` of a function of `P` (`bl`, or `blr` of the address of a declared one) the plain
call's contract (`calleeOk`) with the results `progX` returns (`tryRets`, `blrTry`); at a
`try_call` of an extern outside `P` the base's. -/
theorem calleeTryOk (hL : L.Ok) {M : Nat} (ih : 0 < M → L.Thm (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry M g F G ra s w₀) :
    CalleeTryOkG F (L.K M) G s (CallAt (L.A g).fa (L.A g).base) (L.X M g F) (L.hooks M)
      (L.A g).vcp.TrySite := by
  intro ctx info ti hsite
  cases hd : info.dest with
  | sym n =>
    have hdest := hd
    cases hpf : L.P.func? n with
    | some h =>
      refine calleeTryOkG_of_call (S := fun i t => i = info ∧ t = ti)
        (fun ctx' i t ⟨e1, _⟩ => e1 ▸ (L.calleeOk hL ih hg he).os ctx' info hsite.callSite)
        (fun _ _ _ h => callAt_tryCall_call h)
        (fun i t ⟨_, e2⟩ => e2 ▸ trySite_clobberAll (hL.compiled g hg).alloc hsite)
        (fun i t ⟨e1, e2⟩ uses w outs w' hx => ?_) ctx info ti ⟨rfl, rfl⟩
      subst e1 e2
      rw [hdest] at hx
      simp only at hx
      rw [L.X_prog hpf] at hx
      have hr := hL.tryRets g hg i t h hsite ⟨hsite.callSite, n, hdest, hpf⟩
      unfold progX at hx
      split at hx
      · simp only [Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, -⟩ := hx
        simpa using hr
      · cases hx
    | none =>
      have hb : L.BaseDest (destOf info) := .inr ⟨n, by simp [destOf, hdest], hpf⟩
      intro c wh ops regs i' t w outs w' s' _ _ _ hops hst hasg _ hsw hal herr hsem hex
      obtain ⟨d, us, ds⟩ := info
      simp only at hdest
      subst hdest
      have hsem' : csem F ctx L.Xb (.tryCall ⟨.sym n, us, ds⟩ ti) (useVals ops regs t) w =
          some (outs, w', .goto ti.handlers.length) := by
        rw [← hsem]; simp [csem, L.X_base hpf _ _ F]
      obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall _ regs).2 ti i' hasg
      obtain ⟨us', ds', hic⟩ := assign_call_sym hasg'
      cases hic
      have hex' : callExec L.Hb (.tryCall ⟨.sym n, us', ds'⟩ ti) t = some s' := by
        simp only [callExec] at hex ⊢
        rw [← L.hooks_base (M := M) (.inr ⟨n, rfl, hpf⟩) t (fun h => by cases h)]
        exact hex
      exact hL.baseTry g hg F ctx _ ti ⟨hsite, hb⟩ c wh ops regs _ t w outs w' s' hops hst hasg
        hsw hal herr hsem' hex'
  | reg r =>
    obtain ⟨tv, Lu, Ld, hinfo, -⟩ :=
      hL.blrRegs g hg info hsite.callSite (fun n => by rw [hd]; simp)
    subst hinfo
    intro c wh ops regs i' t w outs w' s' hK hD hG hops hst hasg hP hsw hal herr hsem hex
    have hcl := trySite_clobberAll (hL.compiled g hg).alloc hsite
    have hopsC : (MInst.call ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩).operands = .ok ops := by
      rw [← operands_tryCall_call _ ti]; exact hops
    have hops1 := hopsC
    rw [operands_call_reg] at hops1
    cases hops1
    obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
    obtain ⟨r0, hregs0⟩ := callRegs_eq_reg (regs := regs)
      (by have := hsz'; simp only [Array.size_map] at this ⊢; simpa using this)
      (fun p hp r hr => (hloc p hp).2 r hr)
    obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
      have hmem : (tgtOp tv, Loc.reg r0) ∈
          (((tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray).zip (regs.map Loc.reg)).toList := by
        simp [Array.toList_zip, Array.toList_map, hregs0]
      obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
      exact ⟨n, hn, h29, h16⟩
    obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall _ regs).2 ti i' hasg
    obtain ⟨r1, us', ds', hr1, hic⟩ := assign_call_reg hasg'
    cases hic
    have h0 : regs[0]? = some (.x n0) := by
      rw [← Array.getElem?_toList, hregs0]; rfl
    rw [h0] at hr1
    cases hr1
    have hc := hL.compiled g hg
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    have htgt : blrTarget t = some (lo64 (regVal t (.x n0))) := by
      obtain ⟨j, x, tt, hj, hx, hpc⟩ := hP
      simp only [MInst.callInsn?, Option.some.injEq] at hx
      subst hx
      rw [lo64_regVal_x]
      exact blrTarget_of hc.layout hlm hj hn0 hpc
        (fun k wd hk => hL.imgCode g hg t (fun a ha => (hG a (he.imgG a ha)).trans (he.imgS a ha)) k wd hk)
    have huv := call_useVals_reg (tv := tv) (s := t) hregs0
    cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
    | none =>
      have hb : (blrTarget t).bind (symCallee L.Xb L.P) = none := by rw [htgt]; exact hs
      have hsem' : csem F ctx L.Xb (.tryCall ⟨.reg (.vreg tv .int), retPairs Lu, callDefs Ld⟩ ti)
          (useVals (tgtOp tv :: (retOps Lu ++ callDefOps Ld)).toArray regs t) w =
          some (outs, w', .goto ti.handlers.length) := by
        rw [← hsem, huv]; simp [csem, L.X_none hs]
      have hex' : callExec L.Hb (.tryCall ⟨.reg (.x n0), us', ds'⟩ ti) t = some s' := by
        simp only [callExec] at hex ⊢
        rw [← L.hooks_base (M := M) (.inl rfl) t (fun _ => hb)]
        exact hex
      exact hL.baseTry g hg F ctx _ ti ⟨hsite, .inl rfl⟩ c wh _ regs _ t w outs w' s' hops hst
        hasg hsw hal herr hsem' hex'
    | some h =>
      refine calleeTry_at ((L.calleeOk hL ih hg he).os ctx _ hsite.callSite)
        (fun _ _ h => callAt_tryCall_call h) hcl hK hD hG hops hst hasg hP hsw hal herr hsem hex
        fun outs0 w0 hx => ?_
      simp only at hx
      rw [huv, L.X_ind hs] at hx
      split at hx
      · rename_i hdecl
        have hh : h ∈ L.P.funcs := List.mem_of_find?_eq_some hs
        have hr := hL.blrTry g hg _ ti hsite tv Lu Ld rfl h hh hdecl.1
          (by rw [← hdecl.2, List.length_map])
        unfold progX at hx
        split at hx
        · simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, -⟩ := hx
          simpa using hr
        · cases hx
      · cases hx

theorem find_sym (hL : L.Ok) (n : String) :
    (∀ h, L.P.func? n = some h → L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == L.Xb.sym n 0) = some h) ∧
    (L.P.func? n = none → L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == L.Xb.sym n 0) = none) := by
  constructor
  · intro h hpf
    cases hf : L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == L.Xb.sym n 0) with
    | none =>
      obtain ⟨hh, rfl⟩ := Clif.Program.func?_some hpf
      have := List.find?_eq_none.mp hf h hh
      simp at this
    | some h' =>
      have hh' := List.mem_of_find?_eq_some hf
      have he := List.find?_some hf
      simp only [beq_iff_eq] at he
      have := hL.symInj h' hh' n he
      subst this
      rw [func?_of_mem hL.names hh'] at hpf
      cases hpf; rfl
  · intro hn
    cases hf : L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == L.Xb.sym n 0) with
    | none => rfl
    | some h' =>
      have hh' := List.mem_of_find?_eq_some hf
      have he := List.find?_some hf
      simp only [beq_iff_eq] at he
      have := hL.symInj h' hh' n he
      subst this
      rw [func?_of_mem hL.names hh'] at hn
      cases hn

theorem lo64_ofX (x : BitVec 64) : lo64 (ofX x) = x := by
  simp only [lo64, ofX]
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]

/-- **A call of a function `h` of `P` that `g` declares, from a world of `g`** (the callee's
whole-program run returning within `M` steps): `progX` is defined and gives the callee's CLIF
results and memory in `g`'s relation. -/
theorem progResult (hL : L.Ok) {M : Nat} (ih : 0 < M → L.Thm (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : ∃ e ∈ g.externs.map (·.2), L.P.func? e.name = some h) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : L.K M ≤ c.toNat) (hdead : ∀ a, StackBelow (L.K M) c a → F a ∧ ¬ L.Img a)
    (halign : c.toNat % 16 = 0)
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : Arm.ArmState} {args : List CV}
    {vals rvals : List Clif.Val} {cm' : Clif.Mem} {cs : Clif.State}
    (hargs : ArgsAt h.sig vals args w) (hsav : StackArgsAvoid F h.sig vals w)
    (hmr : RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
      g c sl cm w)
    (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hret : Clif.runLoop L.base L.P M cs = .returned rvals cm') :
    ∃ outs w', L.progX M F h args w = some (outs, w') ∧ outs.length = (sigRets h.sig).length ∧
      PrefixHold rvals outs ∧
      RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c sl cm' w' := by
  have hpf := func?_of_mem hL.names hh
  have hM : 0 < M := by
    cases M with
    | zero => simp at hret
    | succ M => omega
  obtain ⟨⟨hmemR0, hslot, hout⟩, hsp, herrw⟩ := hmr
  have hd := hL.depth h hh
  have hroom' : frameDrop (L.A h).af + L.K (M - 1) ≤ (spv w).toNat := by
    rw [hsp]; have := L.K_succ M hM; omega
  have hdead' : ∀ a, StackBelow (frameDrop (L.A h).af + L.K (M - 1)) (spv w) a →
      F a ∧ ¬ L.Img a := fun a ha =>
    hdead a (by rw [← hsp]; exact stackBelow_mono ha (by have := L.K_succ M hM; omega))
  obtain ⟨hsl, hsz⟩ := hL.calleeSlots g hg h (.inr hcallee)
  have hib : (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0 ∨ L.NeedNI := by
    by_cases h0 : (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0
    · exact .inl h0
    · exact .inr ⟨g, hg, h, .inr hcallee, h0⟩
  obtain ⟨us, outsV, wf, hus, hlen, hhold, hmemR, -, hcall, -⟩ :=
    L.progCall hL hM (ih hM) hpf hsl hsz hib himgF herrw (by rw [hsp]; exact halign) hroom' hdead'
      hmemR0 hargs hsav hinit hret
  obtain ⟨kc, hc_eq, hc_ret⟩ := hcall _ (L.callerOk_canon hL hh himgF args w)
  have hcond : L.Cond M F h args w ∧ Arm.r .ERR (L.pcall M h (L.canon h args w)) = .None := by
    refine ⟨⟨hM, herrw, by rw [hsp]; exact halign, hroom', hdead', vals, cm, cs, rvals, cm',
      hmemR0, hargs, hsav, hinit, hret⟩, ?_⟩
    rw [hc_eq, r_set_program]; exact hc_ret.ret.err
  have hspT : spv (L.pcall M h (L.canon h args w)) = spv w := by
    rw [hc_eq]
    simp only [spv]
    rw [r_set_program]
    have := hc_ret.ret.sp
    simp only [spv] at this
    rw [this, r_enterAt _ _ (by simp) (by simp)]
    exact (L.callerOk_canon hL hh himgF args w).world.1 _ (by simp [Masked])
  have hce := clifEntry_initState (f := h) hpf hinit
  have hlr : rvals.length ≤ (sigRets h.sig).length := by
    have hrt := Clif.runLoop_returned_tys hL.free M cs rvals cm' (runInv_entry hh hce) hret
    have hbot : cs.bottom = h := by simp [Clif.State.bottom, hce.callers, hce.func]
    rw [hbot] at hrt
    have := congrArg List.length hrt
    simp only [List.length_map, Clif.AbiParam.tys] at this
    rw [this]; exact returns_le_sigRets _
  refine ⟨_, _, by rw [progX, if_pos hcond], ?_, ⟨by simpa using hlr, fun j v x hv hx => ?_⟩,
    ⟨⟨⟨fun a b hv hb => ?_, hmemR.valid, hmemR.symbols⟩, ?_, ?_⟩, ?_, hcond.2⟩⟩
  · rw [List.length_map, List.length_range]
  · -- the results
    have hjr : j < rvals.length := (List.getElem?_eq_some_iff.mp hv).1
    have hju : j < us.length := by have := hhold.1; omega
    simp only [List.getElem?_map, List.getElem?_range (by omega : j < (sigRets h.sig).length),
      Option.map_some, Option.some.injEq] at hx
    subst hx
    have hus_j : us[j]? = some ((us[j]'hju).1, Reg.x j) := by
      have := congrArg (·[j]?) hus
      simp only [List.getElem?_map, List.getElem?_range hju, List.getElem?_eq_getElem hju,
        Option.map_some, Option.some.injEq] at this
      rw [List.getElem?_eq_getElem hju, ← this]
    have hoj : outsV[j]? = some (outsV[j]'(by omega)) := List.getElem?_eq_getElem _
    rw [hc_eq, regVal_set_program, hc_ret.regs j _ _ _ hus_j hoj]
    exact hhold.2 j v _ hv hoj
  · -- the bytes of the live allocations
    rw [← hmemR.bytes a b hv hb]
    simp only [Arm.read_mem, Arm.read_store]
    rw [hc_eq, mem_set_program, hc_ret.mem _ (by simpa using (hmemR.valid a 1 hv).2 0 (by omega))]
  · simpa [Rel.slotReg, hspT] using hslot
  · -- the caller's outgoing area: the callee's run creates no allocation there
    by_cases hib0 : (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase = 0
    · rw [hib0]; exact outRel_zero _ _ _
    · refine ⟨hout.1, by rw [hspT]; exact hout.2.1, fun a n hv k hk j hj => ?_⟩
      rw [hspT]
      obtain ⟨-, pl, hcs⟩ := initState_noSlots hpf hsl hinit
      have hv0 := runLoop_valid hL.free (hL.baseNoAlloc ⟨g, hg, hib0⟩) (L.slotFree hL) M
        cs rvals cm' (runInv_entry hh hce)
        (fun hkk => by
          have ⟨k0, hk0, hnk⟩ := hkk
          refine ⟨(hL.indScope k0 hk0 hnk).keep, fun h' hh' hs' => hL.addrSlots ⟨g, hg, hib0⟩ hkk h' hh' ?_⟩
          rw [hcs] at hs'; simpa [hmemR0.symbols] using hs') hret a n hv
      rw [hcs] at hv0
      exact hout.2.2 a n hv0 k hk j hj
  · rw [hspT, hsp]

theorem envOf_some {M : Nat} {g : Clif.Function} {n : String} {G : List Clif.Val → Clif.Mem → Clif.Outcome}
    (h : (L.envOf M g).extern n = some G) :
    (L.P.func? n = none ∧ L.base.extern n = some G) ∨
    (∃ h', L.P.func? n = some h' ∧ DeclN g n ∧ (Clif.linkEnvN L.P L.base M).extern n = some G) := by
  simp only [envOf] at h
  split at h
  · cases h
  · rename_i hn
    cases hpf : L.P.func? n with
    | none => rw [Clif.linkEnvN_none hpf] at h; exact .inl ⟨rfl, h⟩
    | some h' =>
      refine .inr ⟨h', rfl, Classical.byContradiction fun hd => hn ⟨by simp [hpf], hd⟩, h⟩

theorem envOf_eq {M : Nat} {g : Clif.Function} {n : String} (h : L.P.func? n = none ∨ DeclN g n) :
    (L.envOf M g).extern n = (Clif.linkEnvN L.P L.base M).extern n := by
  simp only [envOf]
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rcases h with h | h
  · simp [h] at h1
  · exact h2 h

theorem envOf_keeps (hL : L.Ok) {M : Nat} {g : Clif.Function} (hk : Opt.EnvKeepsSymbols L.base) :
    Opt.EnvKeepsSymbols (L.envOf M g) := by
  intro n G hG vals m rvals m' hr
  have hl : (Clif.linkEnvN L.P L.base M).extern n = some G := by
    rcases L.envOf_some hG with ⟨hpf, hb⟩ | ⟨_, _, _, h⟩
    · rw [Clif.linkEnvN_none hpf]; exact hb
    · exact h
  exact Clif.linkEnvN_keeps hL.free hk n G hl vals m rvals m' hr

/-- **The external contract of an activation of `g` at depth `M`** under its environment
(`envOf`: the linked environment, program callees running at most `M` steps): the base
environment's for the externs outside `P`, and for a function of `P` the linked machine's call
from the canonical state (from the linking statement at depth `M - 1`). -/
theorem xCallsOk (hL : L.Ok) {M : Nat} (ih : 0 < M → L.Thm (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : L.K M ≤ c.toNat)
    (hdead : ∀ a, StackBelow (L.K M) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0) :
    XCallsOk (L.envOf M g) (g.externs.map (·.2))
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c) (L.X M g F) := by
  intro ext hin gsem sl cm w d uses args vals rvals cm' hgs hd hargs hmr hret hrl
  rcases L.envOf_some hgs with ⟨hpf, hgs⟩ | ⟨h, hpf, hdecl, hgs⟩
  · obtain ⟨outs, w', hx, h1, h2, h3⟩ := hL.baseX g hg F (L.A g).af.slotBase
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c ext
      (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) gsem sl cm w d uses args vals rvals cm' hgs hd
      hargs hmr hret hrl
    refine ⟨outs, w', ?_, h1, h2, h3⟩
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [L.X_base hpf _ _ F]; exact hx
    · rw [L.X_none (by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = none
        rw [lo64_ofX]; exact (L.find_sym hL ext.name).2 hpf)]
      exact hx
  · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    have hsig := hL.declSig g hg ext hin h hpf
    rw [Clif.linkEnvN_some hpf] at hgs
    cases hgs
    -- the callee's whole-program run
    simp only at hret
    cases hinit : Clif.initState L.P ext.name vals cm with
    | trap c' => rw [hinit] at hret; cases hret
    | stuck m' => rw [hinit] at hret; cases hret
    | ok cs =>
    rw [hinit] at hret
    simp only at hret
    rw [hsig] at hargs
    have hout := hmr.1.2.2
    have hsp := hmr.2.1
    -- the stack-passed arguments are in the caller's outgoing area, outside `F`
    have hsav : StackArgsAvoid F h.sig vals w := by
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
    rw [← hname] at hinit
    obtain ⟨outs, w', hx, hol, hho, hmr'⟩ :=
      L.progResult hL ih hg hh ⟨ext, hin, hpf⟩ himgF hroom hdead halign hargs hsav hmr hinit hret
    refine ⟨outs, w', ?_, by rw [hol, hsig], hho, hmr'⟩
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [L.X_prog hpf]; exact hx
    · have hs : symCallee L.Xb L.P (lo64 (ofX ((L.X M g F).sym ext.name 0))) = some h := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = some h
        rw [lo64_ofX]; exact (L.find_sym hL ext.name).1 h hpf
      rw [L.X_ind hs, if_pos ⟨by rw [hname]; exact hdecl, argsAt_regLocs hargs⟩]
      exact hx

/-- **The indirect-call contract of an activation of `g` at depth `M`** under its environment: an
indirect call reaching an extern outside `P` is the base's; one reaching a function of `P` that
`g` declares is the linked machine's call from the canonical state (its parameters are in
registers, `indSig`). -/
theorem xCallsIndOk (hL : L.Ok) {M : Nat} (ih : 0 < M → L.Thm (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : L.K M ≤ c.toNat)
    (hdead : ∀ a, StackBelow (L.K M) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0) :
    XCallsIndOk (L.envOf M g) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c) (L.X M g F) := by
  intro sig hsig n gsem sl cm w u args vals rvals cm' hgs hu hl8 hall hmr hret hrl
  rcases L.envOf_some hgs with ⟨hpf, hgs⟩ | ⟨h, hpf, hdecl, hgs⟩
  · have hs : symCallee L.Xb L.P (lo64 u) = none := by
      show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = none
      rw [hu]; exact (L.find_sym hL n).2 hpf
    obtain ⟨outs, w', hx, h1, h2, h3⟩ := hL.baseXI g hg F (L.A g).af.slotBase
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c sig hsig n gsem sl cm w u args vals rvals
      cm' hgs hu hl8 hall hmr hret hrl
    exact ⟨outs, w', by rw [L.X_none hs]; exact hx, h1, h2, h3⟩
  · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    subst hname
    have hnf : ¬ Clif.IndFree g := fun hif => by
      rw [indSigs_nil_of_indFree hif] at hsig; cases hsig
    obtain ⟨hsigNS, hdeclS⟩ := hL.indSig g hg hnf
    obtain ⟨hnsr, bytes, hb, hb8⟩ := hdeclS h hh hdecl
    have hs : symCallee L.Xb L.P (lo64 u) = some h := by
      show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = some h
      rw [hu]; exact (L.find_sym hL h.name).1 h hpf
    rw [Clif.linkEnvN_some hpf] at hgs
    cases hgs
    simp only at hret
    cases hinit : Clif.initState L.P h.name vals cm with
    | trap c' => rw [hinit] at hret; cases hret
    | stuck m' => rw [hinit] at hret; cases hret
    | ok cs =>
    rw [hinit] at hret
    simp only at hret
    have hce := clifEntry_initState (f := h) hpf hinit
    have hvl : vals.length = h.sig.params.length := by
      have := congrArg List.length hce.sig
      simpa using this
    have hargs : ArgsAt h.sig vals args w := (argsAt_iff_of_regs hb hb8 hvl).mpr hall
    have hsav : StackArgsAvoid F h.sig vals w := by
      intro off v hm
      rw [locsOf_of_regs hb hb8] at hm
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
      simp [List.getElem?_zip_eq_some] at hi
    obtain ⟨e, he, hen⟩ : ∃ e ∈ g.externs.map (·.2), e.name = h.name := by
      obtain ⟨e, he, hen⟩ := List.mem_map.mp hdecl.1
      exact ⟨e.2, List.mem_map_of_mem he, hen⟩
    obtain ⟨outs, w', hx, hol, hho, hmr'⟩ :=
      L.progResult hL ih hg hh ⟨e, he, by rw [hen]; exact hpf⟩ himgF hroom hdead halign hargs hsav
        hmr hinit hret
    refine ⟨outs, w', ?_, ?_, hho, hmr'⟩
    · rw [L.X_ind hs, if_pos ⟨hdecl, argsAt_regLocs hargs⟩]
      exact hx
    · rw [hol, sigRets_of_noSret hnsr, sigRets_of_noSret (hsigNS sig hsig)]
      have hrt := Clif.runLoop_returned_tys hL.free M cs rvals cm' (runInv_entry hh hce) hret
      have hbot : cs.bottom = h := by simp [Clif.State.bottom, hce.callers, hce.func]
      rw [hbot] at hrt
      have := congrArg List.length hrt
      simp only [List.length_map, Clif.AbiParam.tys] at this
      rw [← this, hrl]

/-! ## Non-interference of the linked calls -/

theorem ty_bytes_mul (t : Clif.Ty) : t.bytes * 8 = t.width := by cases t <;> rfl

/-- Two worlds with the same `sp` holding the stack-passed arguments of a call agree on their
bytes. -/
theorem stackArgs_bytes {s : Clif.Signature} {vals : List Clif.Val} {w w' : Arm.ArmState}
    (h : StackArgsAt s vals w) (h' : StackArgsAt s vals w') (hsp : spv w' = spv w) :
    ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf s).zip vals → ∀ k < v.ty.bytes,
      w'.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
        w.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k) := by
  intro off v hm k hk
  have e1 := h off v hm
  have e2 := h' off v hm
  simp only [spOf] at e1 e2
  change (Arm.read_mem_bytes v.ty.bytes (spv w + BitVec.ofNat 64 off) w).setWidth v.ty.width =
    v.bits at e1
  change (Arm.read_mem_bytes v.ty.bytes (spv w' + BitVec.ofNat 64 off) w').setWidth v.ty.width =
    v.bits at e2
  rw [hsp] at e2
  have e := congrArg (BitVec.setWidth (v.ty.bytes * 8)) (e2.trans e1.symm)
  have hle : v.ty.bytes * 8 ≤ v.ty.width := Nat.le_of_eq (ty_bytes_mul v.ty)
  rw [BitVec.setWidth_setWidth_of_le _ hle, BitVec.setWidth_setWidth_of_le _ hle,
    BitVec.setWidth_eq, BitVec.setWidth_eq] at e
  exact read_mem_bytes_bytes _ _ _ _ e k hk

/-- `StackArgsAvoid` depends on the argument values only through their types. -/
theorem stackArgsAvoid_tys {F : BitVec 64 → Prop} {s : Clif.Signature} {vals vals' : List Clif.Val}
    {w : Arm.ArmState} (h : StackArgsAvoid F s vals w) (hty : vals'.map (·.ty) = vals.map (·.ty)) :
    StackArgsAvoid F s vals' w := by
  intro off v hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  rw [List.getElem?_zip_eq_some] at hi
  obtain ⟨hl, hv⟩ := hi
  have e := congrArg (·[i]?) hty
  simp only [List.getElem?_map, hv, Option.map_some] at e
  cases hv1 : vals[i]? with
  | none => rw [hv1] at e; cases e
  | some v1 =>
    rw [hv1] at e
    simp only [Option.map_some, Option.some.injEq] at e
    have := h off v1 (List.mem_iff_getElem?.mpr ⟨i, List.getElem?_zip_eq_some.mpr ⟨hl, hv1⟩⟩)
    rwa [← e] at this

/-- The canonical states of a call from two worlds have the same parameter registers. -/
theorem regVal_canon_eq (hL : L.Ok) {h : Clif.Function} (hh : h ∈ L.P.funcs) {args : List CV}
    (hlen : args.length = (regLocs h.sig).length) (w w' : Arm.ArmState) :
    ∀ r ∈ regLocs h.sig, regVal (L.canon h args w') r = regVal (L.canon h args w) r := by
  intro r hr
  obtain ⟨hnd, harg, -⟩ := hL.argRegs h hh
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
  have hjl : j < args.length := by have := (List.getElem?_eq_some_iff.mp hj).1; omega
  rw [L.regVal_canon _ _ _ (harg r hr), L.regVal_canon _ _ _ (harg r hr),
    placeArgs_regVal _ _ _ hnd harg hj (List.getElem?_eq_getElem hjl),
    placeArgs_regVal _ _ _ hnd harg hj (List.getElem?_eq_getElem hjl)]

/-- The canonical state of a call is related to the caller's CLIF memory. -/
theorem memRel_canon {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {cm : Clif.Mem}
    {w : Arm.ArmState} (hm : MemRel F L.syms cm w) (h : Clif.Function) (args : List CV) :
    MemRel F L.syms cm (L.canon h args w) := by
  refine ⟨fun a b hv hb => ?_, hm.valid, hm.symbols⟩
  rw [← hm.bytes a b hv hb]
  simp only [Arm.read_mem, Arm.read_store]
  rw [L.mem_canon, mem_withImg, if_neg]
  intro hi
  exact (hm.valid a 1 hv).2 0 (by omega) (by simpa using himgF _ hi)

/-- **Non-interference of a call of a function `h` of `P`** that `g` declares (when the linking
needs it): from two worlds that agree outside `Z ⊇ F`, related to the same CLIF memory, with the
arguments where `h`'s ABI puts them in both, on which the callee's whole-program run returns,
the two calls (`progX`) give the same results and worlds that agree outside `Z`. -/
theorem progX_ni (hL : L.Ok) (hN : L.NeedNI) {M : Nat} (ih : 0 < M → L.Thm (M - 1))
    {g h : Clif.Function} (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : ∃ e ∈ g.externs.map (·.2), L.P.func? e.name = some h) {F Z : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) (hFZ : ∀ a, F a → Z a) {w w' : Arm.ArmState}
    (hsw : SameWorld Z w w') {cm : Clif.Mem} {vals : List Clif.Val} {args : List CV}
    (hm : MemRel F L.syms cm w) (hm' : MemRel F L.syms cm w') (ha : ArgsAt h.sig vals args w)
    (ha' : ArgsAt h.sig vals args w') {cs : Clif.State} {rvals : List Clif.Val} {cm' : Clif.Mem}
    (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hrun : Clif.runLoop L.base L.P M cs = .returned rvals cm') {o o' : List CV}
    {x x' : Arm.ArmState} (hx : L.progX M F h args w = some (o, x))
    (hx' : L.progX M F h args w' = some (o', x')) : o = o' ∧ SameWorld Z x x' := by
  have hpf := func?_of_mem hL.names hh
  unfold progX at hx hx'
  split at hx
  case isFalse => cases hx
  rename_i hc
  split at hx'
  case isFalse => cases hx'
  simp only [Option.some.injEq, Prod.mk.injEq] at hx hx'
  obtain ⟨rfl, rfl⟩ := hx
  obtain ⟨rfl, rfl⟩ := hx'
  obtain ⟨⟨hM, herr, hal, hroom, hdead, vals1, cm1, cs1, rvals1, cm1', -, -, hsav1, hinit1, -⟩, -⟩ :=
    hc
  have hty : vals.map (·.ty) = vals1.map (·.ty) := by
    rw [(clifEntry_initState hpf hinit).sig, (clifEntry_initState hpf hinit1).sig]
  have hsav := stackArgsAvoid_tys hsav1 hty
  obtain ⟨hsl, hsz⟩ := hL.calleeSlots g hg h (.inr hcallee)
  obtain ⟨us, outs, wf, hus, hlen, hhold, -, hrs, hall, hni⟩ :=
    L.progCall hL hM (ih hM) hpf hsl hsz (.inr hN) himgF herr hal hroom hdead hm ha hsav hinit hrun
  have hc0 := L.callerOk_canon hL hh himgF args w
  have hc1 := L.callerOk_canon hL hh himgF args w'
  have hsp' : spv w' = spv w := (hsw.1 _ (by simp [Masked])).symm
  obtain ⟨k, heq, hret⟩ := hall _ hc0
  obtain ⟨k', heq', hret'⟩ := hni hN Z (L.canon h args w') hFZ
    ((SameWorld.mono hFZ hc1.world).trans hsw.symm) hc1.img
    (L.regVal_canon_eq hL hh (argsAt_regLocs ha) w w') hc1.ra (L.memRel_canon himgF hm' h args)
    (fun off v hmz j hj => by
      rw [L.mem_canon, mem_withImg, if_neg (fun hi => hsav off v hmz j hj (himgF _ hi))]
      exact stackArgs_bytes ha.2.2 ha'.2.2 hsp' off v hmz j hj)
  -- the callee's ABI results are among the defs of its return site
  have hsr : (sigRets h.sig).length ≤ us.length := by
    cases hs : h.sig.params.any (·.purpose == .sret)
    · have hce := clifEntry_initState hpf hinit
      have hrt := Clif.runLoop_returned_tys hL.free M cs rvals cm' (runInv_entry hh hce) hrun
      have hbot : cs.bottom = h := by simp [Clif.State.bottom, hce.callers, hce.func]
      rw [hbot] at hrt
      have e := congrArg List.length hrt
      simp only [List.length_map, Clif.AbiParam.tys] at e
      rw [sigRets_of_noSret hs, ← e]
      have := hhold.1
      omega
    · exact hL.sretRets h hh hs us hrs
  have hres : ∀ (u : Arm.ArmState) (kk : Nat) (Y : BitVec 64 → Prop) (G : BitVec 64 → Prop),
      ActRet (Arm.r .PC u + 4) Y G us outs wf (enterAt (L.A h) u)
        (runX (L.mach (M - 1) h) kk (enterAt (L.A h) u)) →
      ∀ j (hj : j < (sigRets h.sig).length),
        regVal (Arm.set_program (runX (L.mach (M - 1) h) kk (enterAt (L.A h) u)) u.program)
          (.x j) = outs[j]'(by omega) := by
    intro u kk Y G hr j hj
    have hju : j < us.length := by omega
    have hus_j : us[j]? = some ((us[j]'hju).1, Reg.x j) := by
      have := congrArg (·[j]?) hus
      simp only [List.getElem?_map, List.getElem?_range hju, List.getElem?_eq_getElem hju,
        Option.map_some, Option.some.injEq] at this
      rw [List.getElem?_eq_getElem hju, ← this]
    rw [regVal_set_program, hr.regs j _ _ _ hus_j (List.getElem?_eq_getElem _)]
  refine ⟨?_, ?_⟩
  · apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at h1
    rw [heq, heq', hres _ k _ _ hret j h1, hres _ k' _ _ hret' j h1]
  · rw [heq, heq']
    refine ⟨fun f hf => ?_, fun a ha => ?_, ?_⟩
    · rw [r_set_program, r_set_program]
      by_cases h29 : f = .GPR 29#5
      · subst h29
        have e1 := hret.ret.savedX 29 (by unfold calleeSavedX; decide)
        have e2 := hret'.ret.savedX 29 (by unfold calleeSavedX; decide)
        simp only [xreg] at e1 e2
        rw [show (BitVec.ofNat 5 29) = 29#5 from rfl] at e1 e2
        rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          hc0.world.1 _ hf, hc1.world.1 _ hf, hsw.1 _ hf]
      by_cases h31 : f = .GPR 31#5
      · subst h31
        have e1 := hret.ret.sp
        have e2 := hret'.ret.sp
        simp only [spv] at e1 e2
        rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          hc0.world.1 _ hf, hc1.world.1 _ hf, hsw.1 _ hf]
      rw [hret.fields f hf h29 h31, hret'.fields f hf h29 h31]
    · rw [mem_set_program, mem_set_program, hret.mem a (fun hf => ha (hFZ a hf)), hret'.mem a ha]
    · rw [program_set_program, program_set_program, L.program_canon, L.program_canon]
      exact hsw.2.2

/-- **Non-interference of the external semantics of an activation of `g`** at its calls (when
the linking needs it): the base externs' (`baseNI`), and for a function of `P` that `g` declares
`progX_ni` (a direct call has the arguments in the callee's ABI, its declaration having the
callee's signature, `declSig`; an indirect call's callee takes register arguments, `indSig`). -/
theorem xni (hL : L.Ok) (hN : L.NeedNI) {M : Nat} (ih : 0 < M → L.Thm (M - 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) :
    XNI F L.syms (g.externs.map (·.2)) (indSigs g)
      (CallLg (L.envOf M g) (g.externs.map (·.2)) (indSigs g)) (L.X M g F) := by
  intro n sig vals cm args d uses Z w w' o x o' x' hlg hd hFZ hsw hm hm' hA hx hx'
  obtain ⟨hkind, G, rv, cm'', hG, hGo⟩ := hlg
  rcases L.envOf_some hG with ⟨hpf, hb⟩ | ⟨h, hpf, hdecl, hGl⟩
  · have hbase := hL.baseNI hN g hg F n sig vals cm args d uses Z w w' o x o' x'
      ⟨hpf, hkind, G, rv, cm'', hb, hGo⟩ hd hFZ hsw hm hm' hA
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, u, rfl, hu⟩
    · rw [L.X_base hpf] at hx hx'
      exact hbase hx hx'
    · have hs : symCallee L.Xb L.P (lo64 u) = none := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = none
        rw [hu]; exact (L.find_sym hL n).2 hpf
      rw [L.X_none hs] at hx hx'
      exact hbase hx hx'
  · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    subst hname
    rw [Clif.linkEnvN_some hpf] at hGl
    cases hGl
    simp only at hGo
    cases hinit : Clif.initState L.P h.name vals cm with
    | trap c' => rw [hinit] at hGo; cases hGo
    | stuck m' => rw [hinit] at hGo; cases hGo
    | ok cs =>
    rw [hinit] at hGo
    simp only at hGo
    have hce := clifEntry_initState (f := h) hpf hinit
    have hvl : vals.length = h.sig.params.length := by
      have := congrArg List.length hce.sig
      simpa using this
    obtain ⟨e, he, hen⟩ : ∃ e ∈ g.externs.map (·.2), e.name = h.name := by
      obtain ⟨e, he, hen⟩ := List.mem_map.mp hdecl.1
      exact ⟨e.2, List.mem_map_of_mem he, hen⟩
    have hcallee : ∃ e ∈ g.externs.map (·.2), L.P.func? e.name = some h :=
      ⟨e, he, by rw [hen]; exact hpf⟩
    have hAA : ArgsAt h.sig vals args w ∧ ArgsAt h.sig vals args w' := by
      rcases hA with ⟨⟨e', he', hen', hes⟩, h1, h2⟩ | ⟨hsig, h8, hall⟩
      · have := hL.declSig g hg e' he' h (by rw [hen']; exact hpf)
        rw [← hes, this] at h1 h2
        exact ⟨h1, h2⟩
      · have hnf : ¬ Clif.IndFree g := fun hif => by
          rw [indSigs_nil_of_indFree hif] at hsig; cases hsig
        obtain ⟨-, hdeclS⟩ := hL.indSig g hg hnf
        obtain ⟨-, bytes, hb, hb8⟩ := hdeclS h hh hdecl
        exact ⟨(argsAt_iff_of_regs hb hb8 hvl).mpr hall, (argsAt_iff_of_regs hb hb8 hvl).mpr hall⟩
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, u, rfl, hu⟩
    · rw [L.X_prog hpf] at hx hx'
      exact L.progX_ni hL hN ih hg hh hcallee himgF hFZ hsw hm hm' hAA.1 hAA.2 hinit hGo hx hx'
    · have hs : symCallee L.Xb L.P (lo64 u) = some h := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = some h
        rw [hu]; exact (L.find_sym hL h.name).1 h hpf
      rw [L.X_ind hs] at hx hx'
      split at hx
      · rename_i hif
        rw [if_pos hif] at hx'
        exact L.progX_ni hL hN ih hg hh hcallee himgF hFZ hsw hm hm' hAA.1 hAA.2 hinit hGo hx hx'
      · cases hx

/-- The TLSDESC flags of an activation's external semantics are the base's. -/
theorem xTls (hL : L.Ok) (hN : L.NeedNI) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} :
    XTls F (L.X M g F) :=
  fun Z n w w' hFZ hsw => hL.baseTlsNI hN F Z n w w' hFZ hsw

end LinkSys

/-! ## The environment of an activation -/

theorem ofRes_congr {α : Type} {r : Clif.Res α} {k₁ k₂ : α → Clif.StepResult}
    (h : ∀ a, r = .ok a → k₁ a = k₂ a) : Clif.StepResult.ofRes r k₁ = Clif.StepResult.ofRes r k₂ := by
  cases r with
  | ok a => exact h a rfl
  | _ => rfl

theorem callCont_envEq {E₁ E₂ : Clif.Env} {p : Clif.Program} {t : Clif.State} {rest : List Clif.Stmt}
    {rs : List Clif.ValueId} {ext : Clif.ExtFunc} {vals : List Clif.Val}
    (h : p.func? ext.name = none → E₁.extern ext.name = E₂.extern ext.name) :
    Opt.callCont E₁ p t rest rs ext vals = Opt.callCont E₂ p t rest rs ext vals := by
  unfold Opt.callCont
  cases hp : p.func? ext.name with
  | some _ => rfl
  | none => simp only [h hp]

theorem indCont_envEq {E₁ E₂ : Clif.Env} {p : Clif.Program} {t : Clif.State}
    {rest : List Clif.Stmt} {rs : List Clif.ValueId} {sig : Nat} {d : Clif.Signature} {a : Nat}
    {v : List Clif.Val}
    (h : p.funcs.find? (fun f => t.mem.symbols f.name == some a) = none → ∀ n ∈ p.externNames,
      t.mem.symbols n = some a → E₁.extern n = E₂.extern n) :
    Clif.indCont E₁ p t rest rs sig d a v = Clif.indCont E₂ p t rest rs sig d a v := by
  unfold Clif.indCont
  cases hf : p.funcs.find? (fun f => t.mem.symbols f.name == some a) with
  | some _ => rfl
  | none =>
    simp only
    congr 1
    unfold Clif.callExternAt
    cases hn : p.externNames.find? (fun n => t.mem.symbols n == some a) with
    | none => rfl
    | some n =>
      have hq : t.mem.symbols n = some a := by simpa using List.find?_some hn
      simp only [Clif.Res.ofOption_some, Clif.Res.ok_bind,
        h hf n (List.mem_of_find?_eq_some hn) hq]

namespace LinkSys

variable (L : LinkSys)

theorem extern_mem {g : Clif.Function} {fn : Clif.FnRef} {e : Clif.ExtFunc}
    (h : g.extern? fn = some e) : e ∈ g.externs.map (·.2) :=
  mem_of_lookup h

/-- **The run of `P.only g` only calls declared externs**: its steps under `envOf` and under
`linkEnvN` are the same. -/
theorem step_envOf {M : Nat} {g : Clif.Function} {s : Clif.State}
    (hP : Clif.LinkFree g) (hI : Clif.LFrame (L.P.only g) s.frame) :
    Clif.step (L.envOf M g) (L.P.only g) s = Clif.step (Clif.linkEnvN L.P L.base M) (L.P.only g) s := by
  have hfg : s.frame.func = g := by
    have := hI.1; simpa [Clif.Program.only] using this
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hP
  -- a direct call of a declaration of `g`
  have hcall : ∀ (t : Clif.State) fn args ext vals rest rs, t.frame.func = g →
      Opt.callArgs t.frame fn args = .ok (ext, vals) →
      Opt.callCont (L.envOf M g) (L.P.only g) t rest rs ext vals =
        Opt.callCont (Clif.linkEnvN L.P L.base M) (L.P.only g) t rest rs ext vals := by
    intro t fn args ext vals rest rs htf hca
    refine callCont_envEq fun hn => L.envOf_eq (.inr ⟨?_, fun e => ?_⟩)
    · have := Opt.callArgs_extern hca
      rw [htf] at this
      have h' := LinkSys.extern_mem this
      simp only [List.mem_map] at h' ⊢
      obtain ⟨x, hx, rfl⟩ := h'
      exact ⟨x, hx, rfl⟩
    · rw [Clif.Program.only_func?, if_pos e.symm] at hn; cases hn
  -- an indirect call: `callExternAt` searches `g`'s declarations
  have hind : ∀ (t : Clif.State) rest rs sig d a v,
      Clif.indCont (L.envOf M g) (L.P.only g) t rest rs sig d a v =
        Clif.indCont (Clif.linkEnvN L.P L.base M) (L.P.only g) t rest rs sig d a v := by
    intro t rest rs sig d a v
    refine indCont_envEq fun hf n hn hq => L.envOf_eq (.inr ⟨?_, fun e => ?_⟩)
    · rw [Clif.only_externNames] at hn; exact hn
    · subst e
      have := List.find?_eq_none.mp hf g (by simp [Clif.Program.only])
      simp [hq] at this
  rcases Clif.step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [Clif.step_try _ _ s hb ht, Clif.step_try _ _ s hb ht]
    refine ofRes_congr fun ⟨n, b, bc⟩ _ => ofRes_congr fun ⟨ext, vals⟩ hca => ?_
    exact hcall _ fn args ext vals _ _ hfg hca
  · rw [Clif.step_tryInd _ _ s hb ht, Clif.step_tryInd _ _ s hb ht]
    refine ofRes_congr fun ⟨n, b, bc⟩ _ => ofRes_congr fun ⟨d, a, v⟩ _ => ?_
    exact hind _ _ _ _ d a v
  · rw [Clif.step_ind _ _ s hb hi, Clif.step_ind _ _ s hb hi]
    exact ofRes_congr fun ⟨d, a, v⟩ _ => hind _ _ _ _ d a v
  · rw [Opt.step_eq_lift _ _ s hci, Opt.step_eq_lift _ _ s hci]
    cases hl : Opt.lstep s.frame s.mem with
    | call ext vals rs rest =>
      obtain ⟨st, fn, args, -, -, -, hca⟩ := Opt.lstep_call_inv hl
      exact hcall s fn args ext vals rest rs hfg hca
    | tail ext vals => exact absurd hl (Clif.lstep_ne_tail hPf hI)
    | _ => rfl

theorem runLoop_envOf {M : Nat} {g : Clif.Function} (hP : Clif.LinkFree g) :
    ∀ (n : Nat) (s : Clif.State), Clif.LInv (L.P.only g) s →
      Clif.runLoop (L.envOf M g) (L.P.only g) n s =
        Clif.runLoop (Clif.linkEnvN L.P L.base M) (L.P.only g) n s
  | 0, _, _ => rfl
  | n + 1, s, hI => by
    have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
      simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; exact hP
    rw [Clif.runLoop_succ', Clif.runLoop_succ', L.step_envOf hP hI.1]
    cases hs : Clif.step (Clif.linkEnvN L.P L.base M) (L.P.only g) s with
    | next s1 =>
      exact runLoop_envOf hP n s1 (Clif.step_next_linv hPf hI hs).1
    | _ => rfl

theorem reach_envOf {M : Nat} {g : Clif.Function} (hP : Clif.LinkFree g) {cs s : Clif.State}
    (hr : Reach (L.envOf M g) (L.P.only g) cs s) (hI : Clif.LInv (L.P.only g) cs) :
    Reach (Clif.linkEnvN L.P L.base M) (L.P.only g) cs s ∧ Clif.LInv (L.P.only g) s := by
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hP
  induction hr with
  | refl => exact ⟨.refl _, hI⟩
  | step hs _ ih =>
    rw [L.step_envOf hP hI.1] at hs
    obtain ⟨h1, h2⟩ := ih (Clif.step_next_linv hPf hI hs).1
    exact ⟨.step hs h1, h2⟩

/-- The run premises of `P.only g` under `linkEnvN` are those under `envOf`. -/
theorem trapsExplicit_envOf {M : Nat} {g : Clif.Function} (hP : Clif.LinkFree g)
    {cs : Clif.State} (hI : Clif.LInv (L.P.only g) cs)
    (h : TrapsExplicit (Clif.linkEnvN L.P L.base M) (L.P.only g) cs) :
    TrapsExplicit (L.envOf M g) (L.P.only g) cs where
  stmt := fun s c st rest hr hs hb => by
    obtain ⟨hr', hIs⟩ := L.reach_envOf hP hr hI
    rw [L.step_envOf hP hIs.1] at hs
    exact h.stmt s c st rest hr' hs hb
  tryCall := fun s c fn args et hr hs hb ht => by
    obtain ⟨hr', hIs⟩ := L.reach_envOf hP hr hI
    rw [L.step_envOf hP hIs.1] at hs
    exact h.tryCall s c fn args et hr' hs hb ht
  tryCallInd := fun s c callee args et hr hs hb ht => by
    obtain ⟨hr', hIs⟩ := L.reach_envOf hP hr hI
    rw [L.step_envOf hP hIs.1] at hs
    exact h.tryCallInd s c callee args et hr' hs hb ht
  indirect := fun s st rest sig callee args hr hb hi hst =>
    h.indirect s st rest sig callee args (L.reach_envOf hP hr hI).1 hb hi hst
  tryIndirect := fun s callee args et hr hb ht hB =>
    h.tryIndirect s callee args et (L.reach_envOf hP hr hI).1 hb ht hB

end LinkSys

/-! ## The induction -/

namespace LinkSys

variable (L : LinkSys)

theorem tlsOk_hooks {F F' : BitVec 64 → Prop} {K M : Nat} {g : Clif.Function}
    (h : TlsOk F K L.Xb L.Hb) : TlsOk F K (L.X M g F') (L.hooks M) := by
  cases M <;> exact ⟨h.pc, h.seq, h.flags⟩

/-- **The induction step**: the linking statement at depth `M` from the one at depth `M - 1`. -/
theorem thm_of (hL : L.Ok) {M : Nat} (ih : 0 < M → L.Thm (M - 1)) : L.Thm M := by
  intro g hg F vals cs w₀ fuel rvals cm' hWE hrun
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hrun' : Clif.runLoop (L.envOf M g) (L.P.only g) fuel cs = .returned rvals cm' := by
    rw [L.runLoop_envOf (hL.free g hg) fuel cs hI]; exact hrun
  -- the indirect calls of `g` reach no function of the program: `g` has no address
  have htr : TrapsExplicit (L.envOf M g) (L.P.only g) cs := by
    refine trapsExplicit_of_returned (fun hnf s hr g' hg' => ?_) hrun'
    rw [hWE.clif.func] at hnf
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hg'
    subst hg'
    have hk := L.envOf_keeps hL (M := M) (g := g') (hL.indScope g' hg hnf).keep
    have hPf : ∀ f ∈ (L.P.only g').funcs, Clif.LinkFree f := fun f hf => by
      simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; exact hL.free f hg
    rw [(reach_symbols hPf hk hr hI).1, hWE.rel.1.1.symbols]
    exact hL.indNoSym g' hg hnf
  have h := backend_correct_world_ni (hL.subset g hg) hc (X := L.X M g F) (syms := L.syms)
    (env := L.envOf M g) (K := L.K M) (F := F) (c := spv w₀) (hL.covered g hg)
    (L.xCallsOk hL ih hg hWE.img hWE.room hWE.dead hWE.align)
    (L.xCallsIndOk hL ih hg hWE.img hWE.room hWE.dead hWE.align)
    (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel hWE.args htr fuel
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, hni⟩ := h rvals cm' hrun'
  have hAE : ∀ G ra s w₀', L.MachEntry M g F G ra s w₀' →
      ActEntry (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (L.K M) F G (L.X M g F)
        (L.hooks M) (L.A g).base ra s w₀' := fun G ra s w₀' hME =>
    ⟨hME.abi, hME.stack, hME.gfree, hME.hF, L.calleeOk hL ih hg hME,
      fun _ => L.calleeTryOk hL ih hg hME,
      fun ht => L.tlsOk_hooks (hL.baseTls g hg (hasTls_of_vcode hc ht) F (L.K M)), hME.body⟩
  refine ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, fun G ra s hME => hall (L.hooks M) G
    (L.A g).base ra s (hAE G ra s w₀ hME), fun hN D w₀' hrel' hsw hreg hstk G ra s hME => ?_⟩
  exact hni (L.xni hL hN ih hg hWE.img) (L.xTls hL hN) D w₀' hrel' hsw hreg hstk (L.hooks M) G
    (L.A g).base ra s (hAE G ra s w₀' hME)

/-- **The linking statement at every depth.** -/
theorem thm (hL : L.Ok) : ∀ M, L.Thm M
  | 0 => L.thm_of hL fun h => absurd h (Nat.lt_irrefl 0)
  | M + 1 => L.thm_of hL fun _ => thm hL M

end LinkSys

/-! ## The whole-program theorem -/

/-- **The backend's end-to-end theorem for a linked program** (`docs/contracts/e2e.md`,
"Linking at the Arm level"): for a function `f` of a program `P` whose functions are compiled
and laid out as `L` describes (`L.Ok`), the Arm machine whose calls of the program's functions
run their compiled code (`L.mach M f`: the linked hooks of depth `M`, `LinkSys.hooks`) refines
the **whole-program** CLIF run of at most `M + 1` steps, from an ABI entry state with the code
image loaded and stack for `M` call levels. The addresses outside the world `L.F` are the entry
activation's frame, its callees' stack and the code (`hF`). The program callees' contracts are
discharged (by induction on the depth, `LinkSys.thm`); the premises left are the base
environment's contracts, the scope and the link layout (`LinkSys.Ok`), and the entry. -/
theorem backend_correct_program (L : LinkSys) (hL : L.Ok) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (L.K M) (L.A f).af s)
    (hF : L.F = frameWG (L.K M) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + L.K M) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) (L.P.only f) cs) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) := by
  have hc := hL.compiled f hf
  have hfr := lowerRFunc_frame hc.alloc
  have hst := hres
  obtain ⟨hB, hK⟩ := spBody_toNat hres
  have hd : frameDrop (L.A f).af = (L.A f).af.frameSize + 16 := by simp [frameDrop, hfr]
  -- the world side
  have hWE : L.WorldEntry M f L.F args cs w₀ := by
    refine ⟨hcs, ⟨hrel, rfl, ?_⟩, ?_, ?_, ?_, ?_, hL.imgF⟩
    · rw [hbe.other .ERR (by simp [Masked]) (by simp) (by simp)]; exact hent.err
    · refine argsAtEntry_body hfr (entryRegs_of_check hc.lowerOk) hbe hargs fun off v hm k hk hk' => ?_
      rw [hF] at hk'
      rcases hk' with hw | hi
      · exact stackArgsAvoid_frameW hc hres hent hargs off v hm k hk hw
      · exact hsav off v hm k hk hi
    · rw [hbe.sp, hB]; omega
    · intro a ha
      rw [hbe.sp] at ha
      refine ⟨by rw [hF]; exact .inl (.inr ha), fun hi => hgfree a hi ?_⟩
      obtain ⟨h1, h2⟩ := ha
      rw [hB] at h1 h2
      exact ⟨by omega, by omega⟩
    · rw [hbe.sp, hB, hd]
      have := hent.spAligned
      have := L.frameSize_mod hL hf
      omega
  -- the machine side
  have hME : L.MachEntry M f L.F L.Img ra s w₀ :=
    ⟨hent, hres, hgfree, hF.symm, fun _ h => h, himg,
      hbe.w L.F fun r ⟨_, _, hvb, hi, _, hv⟩ =>
        ((ctlCheck_args (lowerRFunc_ok hc.alloc).2.2.2 hvb hi).2.2 _ hv).2⟩
  -- the whole-program run is a per-function run
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  have hlink := Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf) (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols)
  cases ho : Clif.runLoop L.base L.P (M + 1) cs with
  | stuck m => trivial
  | outOfFuel => trivial
  | returned vals cm =>
    obtain ⟨m, hm⟩ := hlink (by rw [ho]; exact fun _ h => nomatch h) (by rw [ho]; exact fun h => nomatch h)
    rw [ho] at hm
    obtain ⟨us, outs, wf, hus, hlen, hhold, hmemR, -, hall, -⟩ :=
      L.thm hL M f hf L.F args cs w₀ m vals cm hWE hm
    obtain ⟨n, hret⟩ := hall L.Img ra s hME
    exact armRefines_of_actRet hus hlen hhold hmemR hret
  | trapped c =>
    obtain ⟨m, hm⟩ := hlink (by rw [ho]; exact fun _ h => nomatch h) (by rw [ho]; exact fun h => nomatch h)
    rw [ho] at hm
    have ih : 0 < M → L.Thm (M - 1) := fun _ => L.thm hL (M - 1)
    have hm' : Clif.runLoop (L.envOf M f) (L.P.only f) m cs = .trapped c := by
      rw [L.runLoop_envOf (hL.free f hf) m cs hIf]; exact hm
    have h := backend_correct_world (hL.subset f hf) hc (X := L.X M f L.F) (syms := L.syms)
      (env := L.envOf M f) (K := L.K M) (F := L.F) (c := spv w₀) (hL.covered f hf)
      (L.xCallsOk hL ih hf hL.imgF hWE.room hWE.dead hWE.align)
      (L.xCallsIndOk hL ih hf hL.imgF hWE.room hWE.dead hWE.align)
      (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel hWE.args
      (L.trapsExplicit_envOf (hL.free f hf) hIf htr) m
    exact h.2 c hm' (L.hooks M) L.Img (L.A f).base ra s ⟨hME.abi, hME.stack, hME.gfree, hME.hF,
      L.calleeOk hL ih hf hME,
      fun _ => L.calleeTryOk hL ih hf hME,
      fun ht => L.tlsOk_hooks (hL.baseTls f hf (hasTls_of_vcode hc ht) L.F (L.K M)), hME.body⟩

/-- **The returning runs**: `backend_correct_program` without the run premise `TrapsExplicit`
(a returning run satisfies it, `trapsExplicit_of_returned`). -/
theorem backend_correct_program_returned (L : LinkSys) (hL : L.Ok) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (L.K M) (L.A f).af s)
    (hF : L.F = frameWG (L.K M) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + L.K M) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.returned vals cm) := by
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf) (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  rw [← hrun]
  refine backend_correct_program L hL hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel
    (trapsExplicit_of_returned (fun hnf s hr g' hg' => ?_) hm)
  rw [hcs.func] at hnf
  simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hg'
  subst hg'
  have hPf : ∀ g ∈ (L.P.only g').funcs, Clif.LinkFree g := fun g hg => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg; exact hL.free g hf
  rw [(reach_symbols hPf (Clif.linkEnvN_keeps hL.free (hL.indScope g' hf hnf).keep) hr hIf).1,
    hrel.1.symbols]
  exact hL.indNoSym g' hf hnf

end E2E
