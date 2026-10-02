import FV.E2E.Final
import FV.E2E.LinkClif

/-! # Linking: the end-to-end theorem against the whole-program CLIF semantics

`cargo fv` compiles every function `f` of a program `P` as its own CLIF file `P.only f`, in
which every other function of `P` is an extern. `backend_correct_final` is per function: the
Arm code of `f` refines `Clif.runLoop env (P.only f)`, assuming its callees meet the contracts
`CalleeOk` (the machine's call hook) and `XCallsOk env` (the external semantics).

* `Clif.runLoop_link` (`FV/E2E/LinkClif.lean`): a whole-program run `Clif.runLoop base P`
  (`call`s and `try_call`s of functions of `P` enter them) that returns or traps is a per-function run of
  `P.only f` under `Clif.linkEnv P base` (a call of another function `g` of `P` is atomic and
  returns what `g`'s whole-program run returns).
* `armRefines_link`: per-function refinement for every fuel ⇒ whole-program refinement.
* **`backend_correct_linked`**: the Arm code of `f` refines the **whole-program** run
  `Clif.runLoop base P fuel cs`, from the premises of `backend_correct_final` at
  `env := Clif.linkEnv P base`, `p := P.only f`. `xCallsOk_link` splits the external contract into
  the base environment's (externs outside `P`) and the program functions' (`linkEnv`).
* `calleeOk_mem_world`, `calleeOk_saves_lr_false`: **why the program functions' contracts are not
  discharged from their own theorems** (docs/contracts/e2e.md, "Linking"): `CalleeOk` forces the
  memory a callee leaves outside the caller's frame to be a function of the caller's *world*
  (`SameWorld`), so a callee whose code stores its return address (or any callee-saved
  register) below `sp` — the prologue of every function with a frame, ours included — cannot
  meet it together with an `X.call` that returns.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-! ## The program conditions -/

/-- The programs the linking theorem covers: distinct function names, and no `call_indirect`,
`try_call_indirect` or `return_call` in any function (`Clif.LinkFree`; `call` and `try_call`
are allowed). -/
structure Linkable (P : Clif.Program) : Prop where
  names : (P.funcs.map (·.name)).Nodup
  free : ∀ g ∈ P.funcs, Clif.LinkFree g

/-- An entry state of a function of `P` satisfies the run invariant of `Clif.runLoop_link`. -/
theorem runInv_entry {P : Clif.Program} {f : Clif.Function} {args : List Clif.Val}
    {cs : Clif.State} (hf : f ∈ P.funcs) (hcs : ClifEntry f args cs) :
    Clif.LInv P cs := by
  obtain ⟨b, hb, hbody, hterm, -, -⟩ := hcs.entry
  refine ⟨⟨by rw [hcs.func]; exact hf, .inl ⟨b, ?_, ?_, hterm⟩⟩, ?_⟩
  · rw [hcs.func]; exact List.mem_of_mem_head? hb
  · rw [hbody]; exact List.suffix_refl _
  · rw [hcs.callers]; exact fun _ h => nomatch h

/-- **Whole-program refinement from per-function refinement**: if the Arm run refines every
per-function run of `f` under the linked environment, it refines the whole-program run. -/
theorem armRefines_link {P : Clif.Program} {baseEnv : Clif.Env} {f : Clif.Function}
    (hP : Linkable P) (hf : f ∈ P.funcs) {cs : Clif.State} (hinv : Clif.LInv P cs)
    {fb : FnBin} {base ra : BitVec 64} {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState}
    (h : ∀ m, ArmRefines fb base ra astep s (Clif.runLoop (Clif.linkEnv P baseEnv) (P.only f) m cs))
    (fuel : Nat) : ArmRefines fb base ra astep s (Clif.runLoop baseEnv P fuel cs) := by
  have hlink := Clif.runLoop_link (base := baseEnv) hP.names hf hP.free fuel cs hinv
  cases ho : Clif.runLoop baseEnv P fuel cs with
  | stuck m => trivial
  | outOfFuel => trivial
  | returned vals mem =>
    obtain ⟨m, hm⟩ := hlink (by rw [ho]; exact fun _ h => nomatch h) (by rw [ho]; exact fun h => nomatch h)
    have := h m
    rwa [hm, ho] at this
  | trapped c =>
    obtain ⟨m, hm⟩ := hlink (by rw [ho]; exact fun _ h => nomatch h) (by rw [ho]; exact fun h => nomatch h)
    have := h m
    rwa [hm, ho] at this

/-! ## The external contract of a linked function -/

/-- The external contract of the linked environment splits into the base environment's for the
externs that are not functions of `P` and the linked one for the program functions. -/
theorem xCallsOk_link {P : Clif.Program} {baseEnv : Clif.Env} {exts : List Clif.ExtFunc}
    {MR : MemRelT} {X : ExtSem}
    (hbase : XCallsOk baseEnv (exts.filter fun e => (P.func? e.name).isNone) MR X)
    (hprog : XCallsOk (Clif.linkEnv P baseEnv) (exts.filter fun e => (P.func? e.name).isSome) MR X) :
    XCallsOk (Clif.linkEnv P baseEnv) exts MR X := by
  intro ext hin g sl cm w d uses args vals rvals cm' hg
  cases hpf : P.func? ext.name with
  | none =>
    rw [Clif.linkEnv_none hpf] at hg
    exact hbase ext (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) g sl cm w d uses args vals rvals cm' hg
  | some _ =>
    exact hprog ext (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) g sl cm w d uses args vals rvals cm' hg

/-- A function without `call_indirect`/`try_call_indirect` has no indirect-call signatures. -/
theorem indSigs_nil_of_linkFree {f : Clif.Function} (h : Clif.LinkFree f) : indSigs f = [] :=
  indSigs_eq_nil (fun B hB st hst sig callee args => (h B hB).1 st hst sig callee args)
    (fun B hB callee args et => (h B hB).2.1 callee args et)

/-! ## The linked theorem -/

/-- **The backend's end-to-end theorem against the whole program** (`docs/contracts/e2e.md`,
"Linking"): for a function `f` of a program `P` (`Linkable`: distinct names, no indirect calls
or `return_call`) compiled from its own file `P.only f`, the Arm run refines the
**whole-program** CLIF run `Clif.runLoop base P` (calls and `try_call`s of functions of `P`
enter them). The premises are `backend_correct_final`'s at `env := Clif.linkEnv P base`,
`p := P.only f`: in particular the external contract `hX` for a call of a function `g` of `P` is
the CLIF semantics of `g`'s whole-program run (`xCallsOk_link` separates it from the base
environment's). The indirect-call contract is vacuous (`Linkable`). -/
theorem backend_correct_linked {P : Clif.Program} {baseEnv : Clif.Env} {f : Clif.Function}
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hP : Linkable P) (hf : f ∈ P.funcs)
    (hsub : InSubset (P.only f) f) (hc : Compiled f k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H)
    (hX : ∀ s, XCallsOk (Clif.linkEnv P baseEnv) (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameF (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit (Clif.linkEnv P baseEnv) (P.only f) cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop baseEnv P fuel cs) := by
  refine armRefines_link hP hf (runInv_entry hf hcs) (fun m => ?_) fuel
  exact backend_correct_final hsub hc hcov hC hCT hTls hX
    (fun _ => by rw [indSigs_nil_of_linkFree (hP.free f hf)]; exact xCallsIndOk_nil _ _ _) hsym
    hslot hent hres hbe hargs hcs hrel htr m

/-! ## Why the program functions' contracts stay premises -/

/-- **`CalleeOk` fixes the callee's memory effect by the world**: for a direct call with no
argument and no result whose external semantics returns (`X.call (some n) [] w = some …`), the
hooked callee leaves the same memory outside the caller's frame addresses `F` from every state
with the world `w` — states that differ in the pc, the allocatable registers or the frame. -/
theorem calleeOk_mem_world {F : BitVec 64 → Prop} {X : ExtSem} {H : ArmHooks}
    (hC : CalleeOk F X H) {n : String} {w w' : Arm.ArmState} {outs : List CV}
    (hx : X.call (some n) [] w = some (outs, w')) {s₁ s₂ : Arm.ArmState}
    (h₁ : SameWorld F s₁ w) (h₂ : SameWorld F s₂ w)
    (ha₁ : Arm.CheckSPAlignment s₁) (ha₂ : Arm.CheckSPAlignment s₂)
    (he₁ : Arm.r .ERR s₁ = .None) (he₂ : Arm.r .ERR s₂ = .None) :
    ∀ a, ¬ F a → (H.call (some n) s₁).mem a = (H.call (some n) s₂).mem a := by
  let info : CallInfo := ⟨.sym n, [], []⟩
  let c : CheckCtx := ⟨default, default, default, default⟩
  have hops : (MInst.call info).operands = .ok #[] := rfl
  have hasg : (MInst.call info).assign #[] = .ok (MInst.call info) := rfl
  have hst : c.checkStatic "" #[] ((#[] : Array Reg).map Loc.reg) (MInst.call info).clobbers =
      Except.ok () := by
    simp [CheckCtx.checkStatic, ensure, forM, List.forM, pure, Except.pure, bind, Except.bind]
  have hsem : ∀ s, csem F ⟨0, 0⟩ X (.call info) (useVals #[] #[] s) w = some (outs, w', .next) := by
    intro s
    simp [csem, info, useVals, hx]
  have key : ∀ s, SameWorld F s w → Arm.CheckSPAlignment s → Arm.r .ERR s = .None →
      ∀ a, ¬ F a → (H.call (some n) s).mem a = w'.mem a := by
    intro s hs ha he a hFa
    obtain ⟨s', hex, hw, -⟩ := hC.os ⟨0, 0⟩ info c "" #[] #[] (.call info) s w outs w' hops hst
      hasg hs ha he (hsem s)
    simp only [callExec, info, Option.some.injEq] at hex
    subst hex
    exact hw.2.1 a hFa
  intro a hFa
  rw [key s₁ h₁ ha₁ he₁ a hFa, key s₂ h₂ ha₂ he₂ a hFa]

/-- **A callee that saves its return address below `sp` does not meet `CalleeOk`** (with an
`X.call` that returns): the saved word `pc + 4` depends on the pc of the call, which is outside
the world. Our own functions' prologues (`stp x29, x30, [sp, #-16]!`) do exactly this, so the
program functions' contracts `hC`/`hX` of `backend_correct_linked` cannot be met by the hook that
runs their code; see docs/contracts/e2e.md, "Linking". -/
theorem calleeOk_saves_lr_false {F : BitVec 64 → Prop} {X : ExtSem} {H : ArmHooks}
    (hC : CalleeOk F X H) {n : String} {w w' : Arm.ArmState} {outs : List CV}
    (hx : X.call (some n) [] w = some (outs, w'))
    (ha : Arm.CheckSPAlignment w) (he : Arm.r .ERR w = .None)
    (hsave : ∀ s, Arm.read_mem_bytes 8 (spv s - 8#64) (H.call (some n) s) = Arm.r .PC s + 4#64)
    (hF : ∀ j < 8, ¬ F (spv w - 8#64 + BitVec.ofNat 64 j)) : False := by
  let s₂ := Arm.w .PC (Arm.r .PC w + 4#64) w
  have h₂ : SameWorld F s₂ w := SameWorld.w_left (by simp [Masked]) (SameWorld.refl F w)
  have hsp : spv s₂ = spv w := by
    simp only [s₂, spv]
    exact Arm.r_of_w_different (by simp)
  have ha₂ : Arm.CheckSPAlignment s₂ := by
    simp only [Arm.CheckSPAlignment, Arm.read_gpr] at ha ⊢
    rw [show Arm.r (.GPR 31#5) s₂ = Arm.r (.GPR 31#5) w from Arm.r_of_w_different (by simp)]
    exact ha
  have he₂ : Arm.r .ERR s₂ = .None := by
    simp only [s₂]; rw [Arm.r_of_w_different (by simp)]; exact he
  have hm := calleeOk_mem_world hC hx (SameWorld.refl F w) h₂ ha ha₂ he he₂
  have hr := read_mem_bytes_congr (s := H.call (some n) w) (t := H.call (some n) s₂) 8
    (spv w - 8#64) fun j hj => hm _ (hF j hj)
  rw [hsave w, ← hsp, hsave s₂] at hr
  have hpc : Arm.r .PC s₂ = Arm.r .PC w + 4#64 := by simp [s₂]
  rw [hpc] at hr
  generalize Arm.r .PC w = x at hr
  bv_omega

end E2E
