import FV.E2E.LinkArmStage2R

/-!
# Stage 2 at the call's own operands (SEM1 #537, #680 (3), `docs/plans/uninit.md` §5.9)

Finding: `Stage2Y` asks `XPRBT … n` to answer **every** `uses` that the CLIF invocation of count
`n` accepts (`CallPost` not vacuous). `ArgsAt`/`AllHold` fix only the bits of the CLIF values
(`VHolds`), so `uses` may differ from the call's operand registers in the upper bits of a narrow
argument. `XPRBT` answers a program call from `canon h uses (worldPR …)`, whose callee run may
differ from the actual one in those bits; under `NeedSlots` its slot-byte table then need not be
the CLIF oracle's (`CondBT`'s `TableOf` clause; `DetTabPRB` transfers a table only between
states equal on the masked registers), e.g. when the callee spills an argument register and a
later callee's unwritten slot overlaps the spill. The machine contracts (`CalleeOkGP.os`,
`CalleeTryOkGP`) only ever call the semantics with the operand values of the call state,
`useVals ops regs u`. Decision (new names, `Stage2Y`/`Stage2PRB(R)` kept):

* `csemV_of_call_subAt`: `csemV_of_call_subW` with the answers compared at one call only;
* **`CalleeOkGP.ofCallSubU`**, **`CalleeTryOkGP.ofCallSubU`**: `ofCallSubW` with the answers
  compared only at the call operands of the states `P`;
* **`Stage2Z`**: stage 2 of call `n` at the states `Q`, at a call instruction of `g`'s code
  (`CallAt`), for the call's own operand values;
* `Stage2Y.toZ`, `XPBTGY_subZ`, **`calleeOkXPBTGZ`**, **`calleeTryOkXPBTGZ`**;
* **`Stage2PRBZ`** (as `Stage2PRBR`, with `Stage2Z`), `Stage2PRBR.toZ`, `stage2PRBZ_zero`,
  **`thmPRBRL_ofZ`** (`thmPRBRL_ofR` with `Stage2PRBZ`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **Fewer answers at one call, the same call result**: `csemV_of_call_subW` at the call
`(callDest info, uses, w)` only. -/
theorem csemV_of_call_subAt {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {X : ExtSem} (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    {i : MInst} {info : CallInfo} (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti)
    {uses : List CV} {w : Arm.ArmState}
    (hc : ∀ r, c (callDest info) uses w = some r → X.call (callDest info) uses w = some r)
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
      exact ⟨r', hc _ hr', e⟩
    · cases h
  · simp only [csemV] at h ⊢
    split at h
    · rename_i hg1
      have hg2 : gotGuard gv X info uses := hg1
      simp only [csem, Option.map_eq_some_iff, Option.filter_eq_some_iff] at h
      simp only [hg2, ↓reduceIte, csem, Option.map_eq_some_iff, Option.filter_eq_some_iff]
      obtain ⟨r', ⟨hr', hf⟩, e⟩ := h
      exact ⟨r', ⟨hc _ hr', hf⟩, e⟩
    · cases h

/-- **`CalleeOkGP.ofCallSub` at the call operands of the states `P`** (`ext` given). -/
theorem _root_.Backend.Proof.CalleeOkGP.ofCallSubU {P : Arm.ArmState → Prop}
    {F : BitVec 64 → Prop} {K : Nat} {G : BitVec 64 → Prop} {s0 : Arm.ArmState}
    {Pc : BitVec 64 → MInst → Prop} {X : ExtSem} {H : ArmHooks} {S : CallInfo → Prop}
    {gv : Nat → String → Prop} (h : CalleeOkGP P F K G s0 Pc X H S gv)
    (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    (hc : ∀ s w, P s → SameWorld F s w → ∀ (i : MInst) (info : CallInfo),
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) → ∀ (ops : Array Operand) (regs : Array Reg)
      (i' : MInst), i.operands = .ok ops → ∀ (cc : CheckCtx) (wh : String),
      cc.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () → i.assign regs = .ok i' →
      Pc (Arm.r .PC s) i' → Arm.CheckSPAlignment s → Arm.r .ERR s = .None →
      ∀ r, c (callDest info) (useVals ops regs s) w = some r →
        X.call (callDest info) (useVals ops regs s) w = some r)
    (hext : ∀ d uses w outs w', c d uses w = some (outs, w') → Arm.r .ERR w = .None →
      Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    CalleeOkGP P F K G s0 Pc { X with call := c } H S gv :=
  ⟨fun ctx info hS s hP hK hF hG cc wh ops regs i' w outs w' hops hst hasg hpi hsw hal herr hsem =>
    h.os ctx info hS s hP hK hF hG cc wh ops regs i' w outs w' hops hst hasg hpi hsw hal herr
      (csemV_of_call_subAt c (.inl rfl)
        (hc s w hP hsw _ info (.inl rfl) ops regs i' hops cc wh hst hasg hpi hal herr) hsem),
    h.pc, hext⟩

/-- **`CalleeTryOkGP.ofCallSub` at the call operands of the states `P`.** -/
theorem _root_.Backend.Proof.CalleeTryOkGP.ofCallSubU {P : Arm.ArmState → Prop}
    {F : BitVec 64 → Prop} {K : Nat} {G : BitVec 64 → Prop} {s0 : Arm.ArmState}
    {Pc : BitVec 64 → MInst → Prop} {X : ExtSem} {H : ArmHooks} {S : CallInfo → TryInfo → Prop}
    {gv : Nat → String → Prop} (h : CalleeTryOkGP P F K G s0 Pc X H S gv)
    (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    (hc : ∀ s w, P s → SameWorld F s w → ∀ (i : MInst) (info : CallInfo),
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) → ∀ (ops : Array Operand) (regs : Array Reg)
      (i' : MInst), i.operands = .ok ops → ∀ (cc : CheckCtx) (wh : String),
      cc.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () → i.assign regs = .ok i' →
      Pc (Arm.r .PC s) i' → Arm.CheckSPAlignment s → Arm.r .ERR s = .None →
      ∀ r, c (callDest info) (useVals ops regs s) w = some r →
        X.call (callDest info) (useVals ops regs s) w = some r) :
    CalleeTryOkGP P F K G s0 Pc { X with call := c } H S gv :=
  fun ctx info ti hS cc wh ops regs i' s w outs w' s' hP hK hF hG hops hst hasg hpi hsw hal herr
    hsem hex => h ctx info ti hS cc wh ops regs i' s w outs w' s' hP hK hF hG hops hst hasg hpi hsw
      hal herr (csemV_of_call_subAt c (.inr ⟨ti, rfl⟩)
        (hc s w hP hsw _ info (.inr ⟨ti, rfl⟩) ops regs i' hops cc wh hst hasg hpi hal herr) hsem)
      hex

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **Stage 2 of call `n` at the call operands of the states `Q`**: at a call instruction of
`g`'s code at a state `Q u`, for the call's own operand values `useVals ops regs u` in a world
`w` of `u`, where `CallPost` of the CLIF invocation of count `n` is not vacuous, `XPRBT … n`
answers a `CallPost`-result. -/
def Stage2Z (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (env : Clif.Env) (cs : Clif.State)
    (c : BitVec 64) (Q : Arm.ArmState → Prop) (n : Nat) : Prop :=
  ∀ u w, Q u → SameWorld F u w → ∀ (i : MInst) (info : CallInfo),
    (i = .call info ∨ ∃ ti, i = .tryCall info ti) → ∀ (ops : Array Operand) (regs : Array Reg)
    (i' : MInst), i.operands = .ok ops → ∀ (cc : CheckCtx) (wh : String),
    cc.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () → i.assign regs = .ok i' →
    CallAt (L.A g).fa (L.A g).base (Arm.r .PC u) i' → Arm.CheckSPAlignment u →
    Arm.r .ERR u = .None →
    (¬ ∀ r, CallPost (env.only (InvokedN env L.P.bare cs n)) (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym (callDest info) (useVals ops regs u) w r) →
    ∃ x, (L.XPRBT κ M g F P R n).call (callDest info) (useVals ops regs u) w = some x ∧
      CallPost (env.only (InvokedN env L.P.bare cs n)) (g.externs.map (·.2)) (indSigs g)
        (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
        L.Xb.sym (callDest info) (useVals ops regs u) w x

theorem Stage2Y.toZ {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {env : Clif.Env} {cs : Clif.State}
    {c : BitVec 64} {Q : Arm.ArmState → Prop} {n : Nat} (h : L.Stage2Y κ M g F P R env cs c Q n) :
    L.Stage2Z κ M g F P R env cs c Q n :=
  fun u w hu hsw _ info _ ops regs _ _ _ _ _ _ _ _ _ => h u w hu hsw (callDest info) (useVals ops regs u)

/-- **`Stage2Z` gives the answers at the call operands.** -/
theorem XPBTGY_subZ (hL : L.Ok) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {env : Clif.Env} {cs : Clif.State}
    {c : BitVec 64} {Q : Arm.ArmState → Prop} {n : Nat} (h2 : L.Stage2Z κ M g F P R env cs c Q n) :
    ∀ s w, Q s → SameWorld F s w → ∀ (i : MInst) (info : CallInfo),
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) → ∀ (ops : Array Operand) (regs : Array Reg)
      (i' : MInst), i.operands = .ok ops → ∀ (cc : CheckCtx) (wh : String),
      cc.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () → i.assign regs = .ok i' →
      CallAt (L.A g).fa (L.A g).base (Arm.r .PC s) i' → Arm.CheckSPAlignment s →
      Arm.r .ERR s = .None →
      ∀ r, ((L.XPBTGY κ M g F P R env cs c).at n).call (callDest info) (useVals ops regs s) w =
          some r →
        (L.XPRBT κ M g F P R n).call (callDest info) (useVals ops regs s) w = some r :=
  fun s w hs hsw i info hi ops regs i' hops cc wh hst hasg hpi hal herr _ hr =>
    guardRXR_sub (X := (L.XPBTI κ M g F P R).at n)
      (fun _ _ hx herr => L.XPRBT_ext hL hx herr)
      (h2 s w hs hsw i info hi ops regs i' hops cc wh hst hasg hpi hal herr) hr

/-- **The call contract of `XPBTGY … n`** at the states `Q` where `Stage2Z` holds. -/
theorem calleeOkXPBTGZ (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
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
    (h2 : L.Stage2Z κ M g F P R env cs c Q n) :
    CalleeOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F P R env cs c).at n) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) :=
  (L.calleeOkPRBRL hL hκ ih hdet hg he hQ).ofCallSubU _ (L.XPBTGY_subZ hL h2)
    (L.XPBTGY_ext hL n)

/-- **The try-call contract of `XPBTGY … n`** at the states `Q` where `Stage2Z` holds. -/
theorem calleeTryOkXPBTGZ (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
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
    (h2 : L.Stage2Z κ M g F P R env cs c Q n) :
    CalleeTryOkGP Q F (κ M g) G s (CallAt (L.A g).fa (L.A g).base)
      ((L.XPBTGY κ M g F P R env cs c).at n) (L.hooks M)
      (L.A g).vcp.TrySite (GotV (L.A g).vcp) :=
  (L.calleeTryOkPRBRL hL hκ ih hdet hg he hQ).ofCallSubU _ (L.XPBTGY_subZ hL h2)

/-- **Stage 2 at the call operands of activations whose CLIF run returns.** -/
def Stage2PRBZ (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat) (rvals : List Clif.Val) (cm' : Clif.Mem)
    (ini : Clif.SlotInit) (G : BitVec 64 → Prop) (ra : BitVec 64) (s : Arm.ArmState),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G ra s w₀ (L.BP M g s) (L.RP M g s) →
    RaOk (L.A g) (ra - 4) → L.TableOf M g s ini →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    ∀ n, L.Stage2Z κ M g F (L.BP M g s) (L.RP M g s) (L.envOfB M g (spv w₀)) cs (spv w₀)
      (L.CallStPRB κ M g s w₀ n) n

theorem Stage2PRBR.toZ {M : Nat} (h : L.Stage2PRBR κ M) : L.Stage2PRBZ κ M :=
  fun g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun n =>
    Stage2Y.toZ L (h g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun n)

theorem stage2PRBZ_zero (hL : L.Ok) [L.CrunOk] : L.Stage2PRBZ κ 0 :=
  (L.stage2PRBR_zero hL).toZ

/-- **`thmPRBRL_of` with stage 2 at the call operands** (`thmPRBRL_ofR`'s proof with
`calleeOkXPBTGZ`). -/
theorem thmPRBRL_ofZ (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRB κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRBZ κ M) (hcnt : L.CountPRB κ M) :
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
      fun n => L.calleeOkXPBTGZ hL hκ ih hdet hg he (hQ n)
        (h2 g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun n),
      fun _ n => L.calleeTryOkXPBTGZ hL hκ ih hdet hg he (hQ n)
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
