import FV.E2E.LinkArmStage2Z

/-!
# Stage 2 at the call sites' own operands (SEM1 #537, #680 (3), `docs/plans/uninit.md` §5.9)

`Stage2Z` (#697) asks for an answer at **every** call instruction `i` that assigns to the machine
call at the state's pc, with its operand values. The machine contracts (`CalleeOkGP.os`,
`CalleeTryOkGP`) are only ever applied to the call sites of the compiled code
(`VCode.CallSite`/`TrySite`), under the GOT guard of `csemV` (`gotGuard`). Only at a call site
does the scope fix the argument registers (`Ok.callRegs`, `Ok.blrRegs`), which the slot-byte
oracle of the program callee needs. Decision (new names; `Stage2Z` and its theorems kept):

* `csemV_of_call_subAtG`: `csemV_of_call_subAt` whose comparison may use the GOT guard;
* **`CalleeOkGP.ofCallSubS`**, **`CalleeTryOkGP.ofCallSubS`**: `ofCallSubU` with the answers
  compared only at call sites, under the guard;
* **`Stage2ZS`**: `Stage2Z` at the call sites of `g`'s code, under the guard;
* `Stage2Z.toZS`, `XPBTGY_subZS`, **`calleeOkXPBTGZS`**, **`calleeTryOkXPBTGZS`**;
* **`Stage2PRBZS`**, `Stage2PRBZ.toZS`, `stage2PRBZS_zero`, **`thmPRBRL_ofZS`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **Fewer answers at one guarded call, the same call result.** -/
theorem csemV_of_call_subAtG {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {X : ExtSem} (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    {i : MInst} {info : CallInfo} (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti)
    {uses : List CV} {w : Arm.ArmState}
    (hc : gotGuard gv X info uses →
      ∀ r, c (callDest info) uses w = some r → X.call (callDest info) uses w = some r)
    {r : List CV × Arm.ArmState × Ctl}
    (h : csemV gv F ctx { X with call := c } i uses w = some r) : csemV gv F ctx X i uses w = some r := by
  rcases hi with rfl | ⟨ti, rfl⟩
  · simp only [csemV] at h ⊢
    split at h
    · rename_i hg1
      have hg2 : gotGuard gv X info uses := hg1
      simp only [csem, Option.map_eq_some_iff] at h
      simp only [hg2, ↓reduceIte, csem, Option.map_eq_some_iff]
      obtain ⟨r', hr', e⟩ := h
      exact ⟨r', hc hg2 _ hr', e⟩
    · cases h
  · simp only [csemV] at h ⊢
    split at h
    · rename_i hg1
      have hg2 : gotGuard gv X info uses := hg1
      simp only [csem, Option.map_eq_some_iff, Option.filter_eq_some_iff] at h
      simp only [hg2, ↓reduceIte, csem, Option.map_eq_some_iff, Option.filter_eq_some_iff]
      obtain ⟨r', ⟨hr', hf⟩, e⟩ := h
      exact ⟨r', ⟨hc hg2 _ hr', hf⟩, e⟩
    · cases h

/-- **`CalleeOkGP.ofCallSub` at the call sites' operands of the states `P`**, under the guard. -/
theorem _root_.Backend.Proof.CalleeOkGP.ofCallSubS {P : Arm.ArmState → Prop}
    {F : BitVec 64 → Prop} {K : Nat} {G : BitVec 64 → Prop} {s0 : Arm.ArmState}
    {Pc : BitVec 64 → MInst → Prop} {X : ExtSem} {H : ArmHooks} {S : CallInfo → Prop}
    {gv : Nat → String → Prop} (h : CalleeOkGP P F K G s0 Pc X H S gv)
    (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    (hc : ∀ s w, P s → SameWorld F s w → ∀ (i : MInst) (info : CallInfo),
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) → S info → ∀ (ops : Array Operand)
      (regs : Array Reg) (i' : MInst), i.operands = .ok ops → ∀ (cc : CheckCtx) (wh : String),
      cc.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () → i.assign regs = .ok i' →
      Pc (Arm.r .PC s) i' → Arm.CheckSPAlignment s → Arm.r .ERR s = .None →
      gotGuard gv X info (useVals ops regs s) →
      ∀ r, c (callDest info) (useVals ops regs s) w = some r →
        X.call (callDest info) (useVals ops regs s) w = some r)
    (hext : ∀ d uses w outs w', c d uses w = some (outs, w') → Arm.r .ERR w = .None →
      Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    CalleeOkGP P F K G s0 Pc { X with call := c } H S gv :=
  ⟨fun ctx info hS s hP hK hF hG cc wh ops regs i' w outs w' hops hst hasg hpi hsw hal herr hsem =>
    h.os ctx info hS s hP hK hF hG cc wh ops regs i' w outs w' hops hst hasg hpi hsw hal herr
      (csemV_of_call_subAtG c (.inl rfl)
        (hc s w hP hsw _ info (.inl rfl) hS ops regs i' hops cc wh hst hasg hpi hal herr) hsem),
    h.pc, hext⟩

/-- **`CalleeTryOkGP.ofCallSub` at the call sites' operands of the states `P`**, under the
guard (`S'` the call sites of the try sites `S`). -/
theorem _root_.Backend.Proof.CalleeTryOkGP.ofCallSubS {P : Arm.ArmState → Prop}
    {F : BitVec 64 → Prop} {K : Nat} {G : BitVec 64 → Prop} {s0 : Arm.ArmState}
    {Pc : BitVec 64 → MInst → Prop} {X : ExtSem} {H : ArmHooks} {S : CallInfo → TryInfo → Prop}
    {S' : CallInfo → Prop} (hS' : ∀ info ti, S info ti → S' info)
    {gv : Nat → String → Prop} (h : CalleeTryOkGP P F K G s0 Pc X H S gv)
    (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    (hc : ∀ s w, P s → SameWorld F s w → ∀ (i : MInst) (info : CallInfo),
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) → S' info → ∀ (ops : Array Operand)
      (regs : Array Reg) (i' : MInst), i.operands = .ok ops → ∀ (cc : CheckCtx) (wh : String),
      cc.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () → i.assign regs = .ok i' →
      Pc (Arm.r .PC s) i' → Arm.CheckSPAlignment s → Arm.r .ERR s = .None →
      gotGuard gv X info (useVals ops regs s) →
      ∀ r, c (callDest info) (useVals ops regs s) w = some r →
        X.call (callDest info) (useVals ops regs s) w = some r) :
    CalleeTryOkGP P F K G s0 Pc { X with call := c } H S gv :=
  fun ctx info ti hS cc wh ops regs i' s w outs w' s' hP hK hF hG hops hst hasg hpi hsw hal herr
    hsem hex => h ctx info ti hS cc wh ops regs i' s w outs w' s' hP hK hF hG hops hst hasg hpi hsw
      hal herr (csemV_of_call_subAtG c (.inr ⟨ti, rfl⟩)
        (hc s w hP hsw _ info (.inr ⟨ti, rfl⟩) (hS' info ti hS) ops regs i' hops cc wh hst hasg hpi
          hal herr) hsem)
      hex

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **Stage 2 of call `n` at the call sites' operands of the states `Q`**: `Stage2Z` for the call
sites of `g`'s compiled code (`VCode.CallSite`), under the GOT guard of the call. -/
def Stage2ZS (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (env : Clif.Env) (cs : Clif.State)
    (c : BitVec 64) (Q : Arm.ArmState → Prop) (n : Nat) : Prop :=
  ∀ u w, Q u → SameWorld F u w → ∀ (i : MInst) (info : CallInfo),
    (i = .call info ∨ ∃ ti, i = .tryCall info ti) → (L.A g).vcp.CallSite info →
    ∀ (ops : Array Operand) (regs : Array Reg)
    (i' : MInst), i.operands = .ok ops → ∀ (cc : CheckCtx) (wh : String),
    cc.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () → i.assign regs = .ok i' →
    CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) i' → Arm.CheckSPAlignment u →
    Arm.r .ERR u = .None → gotGuard (GotV (L.A g).vcp) L.Xb info (useVals ops regs u) →
    (¬ ∀ r, CallPost (env.only (InvokedN env L.P.bare cs n)) (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym (callDest info) (useVals ops regs u) w r) →
    ∃ x, (L.XPRBT κ M g F P R n).call (callDest info) (useVals ops regs u) w = some x ∧
      CallPost (env.only (InvokedN env L.P.bare cs n)) (g.externs.map (·.2)) (indSigs g)
        (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
        L.Xb.sym (callDest info) (useVals ops regs u) w x

theorem Stage2Z.toZS {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {env : Clif.Env} {cs : Clif.State}
    {c : BitVec 64} {Q : Arm.ArmState → Prop} {n : Nat} (h : L.Stage2Z κ M g F P R env cs c Q n) :
    L.Stage2ZS κ M g F P R env cs c Q n :=
  fun u w hu hsw i info hi _ ops regs i' hops cc wh hst hasg hpi hal herr _ =>
    h u w hu hsw i info hi ops regs i' hops cc wh hst hasg hpi hal herr

/-- **`Stage2ZS` gives the answers at the call sites' operands**, under the guard. -/
theorem XPBTGY_subZS (hL : L.Ok) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {env : Clif.Env} {cs : Clif.State}
    {c : BitVec 64} {Q : Arm.ArmState → Prop} {n : Nat} (h2 : L.Stage2ZS κ M g F P R env cs c Q n) :
    ∀ s w, Q s → SameWorld F s w → ∀ (i : MInst) (info : CallInfo),
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) → (L.A g).vcp.CallSite info →
      ∀ (ops : Array Operand) (regs : Array Reg)
      (i' : MInst), i.operands = .ok ops → ∀ (cc : CheckCtx) (wh : String),
      cc.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () → i.assign regs = .ok i' →
      CallAt (L.A g).fa (L.A g).base (Arm.r .PC s) i' → Arm.CheckSPAlignment s →
      Arm.r .ERR s = .None →
      gotGuard (GotV (L.A g).vcp) (L.XPRBT κ M g F P R n) info (useVals ops regs s) →
      ∀ r, ((L.XPBTGY κ M g F P R env cs c).at n).call (callDest info) (useVals ops regs s) w =
          some r →
        (L.XPRBT κ M g F P R n).call (callDest info) (useVals ops regs s) w = some r :=
  fun s w hs hsw i info hi hS ops regs i' hops cc wh hst hasg hpi hal herr hgd _ hr =>
    guardRXR_sub (X := (L.XPBTI κ M g F P R).at n)
      (fun _ _ hx herr => L.XPRBT_ext hL hx herr)
      (h2 s w hs hsw i info hi hS ops regs i' hops cc wh hst hasg hpi hal herr hgd) hr

/-- **The call contract of `XPBTGY … n`** at the states `Q` where `Stage2ZS` holds. -/
theorem calleeOkXPBTGZS (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64}
    (h2 : L.Stage2ZS κ M g F P R env cs c Q n) :
    CalleeOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F P R env cs c).at n) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) :=
  (L.calleeOkPRBRL hL hκ ih hdet hg he hQ).ofCallSubS _ (L.XPBTGY_subZS hL h2)
    (L.XPBTGY_ext hL n)

/-- **The try-call contract of `XPBTGY … n`** at the states `Q` where `Stage2ZS` holds. -/
theorem calleeTryOkXPBTGZS (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRB κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64}
    (h2 : L.Stage2ZS κ M g F P R env cs c Q n) :
    CalleeTryOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F P R env cs c).at n) (L.hooks M)
      (L.A g).vcp.TrySite (GotV (L.A g).vcp) :=
  (L.calleeTryOkPRBRL hL hκ ih hdet hg he hQ).ofCallSubS (fun _ _ h => h.callSite) _
    (L.XPBTGY_subZS hL h2)

/-- **`calleeOkXPBTGZS` with the determinism premise `DetPRBR`** (#719). -/
theorem calleeOkXPBTGZSR (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBR κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64}
    (h2 : L.Stage2ZS κ M g F P R env cs c Q n) :
    CalleeOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F P R env cs c).at n) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) :=
  (L.calleeOkPRBRLR hL hκ ih hdet hg he hQ).ofCallSubS _ (L.XPBTGY_subZS hL h2)
    (L.XPBTGY_ext hL n)

/-- **`calleeTryOkXPBTGZS` with the determinism premise `DetPRBR`** (#719). -/
theorem calleeTryOkXPBTGZSR (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1))
    (hdet : 0 < M → L.DetPRBR κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀)
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {n : Nat}
    {Q : Arm.ArmState → Prop}
    (hQ : ∀ t, Q t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = P n a)
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64}
    (h2 : L.Stage2ZS κ M g F P R env cs c Q n) :
    CalleeTryOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F P R env cs c).at n) (L.hooks M)
      (L.A g).vcp.TrySite (GotV (L.A g).vcp) :=
  (L.calleeTryOkPRBRLR hL hκ ih hdet hg he hQ).ofCallSubS (fun _ _ h => h.callSite) _
    (L.XPBTGY_subZS hL h2)

/-- **Stage 2 at the call sites' operands of activations whose CLIF run returns.** -/
def Stage2PRBZS (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat) (rvals : List Clif.Val) (cm' : Clif.Mem)
    (ini : Clif.SlotInit) (G : BitVec 64 → Prop) (ra : BitVec 64) (s : Arm.ArmState),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G ra s w₀ (L.BP M g s) (L.RP M g s) →
    RaOk (L.A g) (ra - 4) → L.TableOf M g s ini →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    ∀ n, L.Stage2ZS κ M g F (L.BP M g s) (L.RP M g s) (L.envOfB M g (spv w₀)) cs (spv w₀)
      (L.CallStPRB κ M g s w₀ n) n

theorem Stage2PRBZ.toZS {M : Nat} (h : L.Stage2PRBZ κ M) : L.Stage2PRBZS κ M :=
  fun g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun n =>
    Stage2Z.toZS L (h g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun n)

theorem stage2PRBZS_zero (hL : L.Ok) [L.CrunOk] : L.Stage2PRBZS κ 0 :=
  (L.stage2PRBZ_zero hL).toZS

/-- **`thmPRBRL_ofZ` with stage 2 at the call sites** (`thmPRBRL_ofZ`'s proof with
`calleeOkXPBTGZS`). -/
theorem thmPRBRL_ofZS (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRB κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRBZS κ M) (hcnt : L.CountPRB κ M) :
    L.ThmPRBRL κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInvB g (spv w₀) cs := ⟨hI, hWE.clif.callers, fun hN => ⟨ini, hWE.place hN⟩⟩
  have hrun' : Clif.runLoop (L.envOfB M g (spv w₀)) L.P.bare fuel cs = .returned rvals cm' := by
    rw [L.runLoop_envOfB hL hg fuel cs hJ]; exact hrun
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hL.free f hg
  have hnrc : NoRetCall (L.envOfB M g (spv w₀)) L.P.bare cs :=
    noRetCall_of_linv hPf (fun _ h => by simp at h) hI
  have h := backend_correct_world_pipelinePRGY (hL.subset g hg) hc
    (XI := L.XPBTI κ M g F (L.BP M g s) (L.RP M g s)) (syms := L.syms)
    (env := L.envOfB M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
    hnrc (hret g hg F vals cs w₀ ini hWE) (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel
    hWE.args (trapsExplicit_of_returned hrun') fuel
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall⟩ := h.1 rvals cm' hrun'
  have he := hME.entryP.entry
  have hQ := L.callStPRB_q (κ := κ) (M := M) he.body.sp
  have hAE : ActEntryPR (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G
      (L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) (L.envOfB M g (spv w₀)) cs (spv w₀))
      (L.hooks M) (L.A g).base ra (κ M g) (spv w₀) (L.BP M g s) (L.RP M g s) s w₀ :=
    ⟨he.abi, he.stack, he.gfree, he.hF, hME.entryP.proph, hME.reg,
      fun n => L.calleeOkXPBTGZS hL hκ ih hdet hg he (hQ n)
        (h2 g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun n),
      fun _ n => L.calleeTryOkXPBTGZS hL hκ ih hdet hg he (hQ n)
        (h2 g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun n),
      fun ht _ => by
        have h0 := hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)
        cases M <;> exact ⟨h0.pc, h0.seq, h0.flags⟩,
      he.body⟩
  obtain ⟨n, hret', htr⟩ := hall (L.hooks M) G (L.A g).base ra (κ M g) (spv w₀) (L.BP M g s)
    (L.RP M g s) s hAE
  have hnr := L.noRetAt_of hL hg he hra htr hret'.ret.err
  obtain ⟨e, hte⟩ := htab n hnr
  exact ⟨us, outs, wf, n, e, hus, hlen, hhold, hmem, hrs, hret', htr, hte,
    hcnt g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun us outs wf n e hret' htr
      hte⟩

end LinkSys

end E2E
