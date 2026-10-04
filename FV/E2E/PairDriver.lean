import FV.E2E.Pair
import FV.E2E.LinkWorld

/-! # Non-interference of a compiled function (agent/link-widen, stage 2)

Two body-entry worlds of a function that agree outside `F ∪ D` — `D` the bytes the two
activations of a callee may disagree on: its slots and outgoing area in the caller's dead stack,
bytes its CLIF memory has not initialised — with the same argument registers and stack-passed
argument bytes, give **one** VCode outcome: the same `rets`, the same values, final worlds
that agree outside `F ∪ D` (`vcode_ni`). The world-generic driver runs on the pair of worlds
(`pairSem`, memory relation `MRP`: `RelW` on both and agreement outside `Zof F D cm`, the bytes of
`F` and the bytes of `D` that the current CLIF memory `cm` has not initialised). Its per-step
facts come from the rule contracts instantiated, per CLIF step, with the guarded semantics
`csemG` (reads guarded by `¬ Zof F D cm`, the calls pinned to the step's CLIF call) on each world,
paired by `seqRun_pair` and `csemG_lockstep2`. The calls need the external semantics to keep the
agreement (`XNI`); the TLSDESC flags not to depend on bytes outside `F` (`XTls`).
`backend_correct_world_ni` composes it with M6 (`regLevelCorrect_world`): the outcome of `w₀` is
realised by every activation entered with a body-entry world `w₀'` related to `w₀`, outside
`F ∪ D`. -/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver

/-! ## The two worlds' agreement -/

/-- An initialised byte of a live CLIF allocation (at an Arm address). -/
def Init (cm : Clif.Mem) (b : BitVec 64) : Prop :=
  cm.valid b.toNat 1 = true ∧ (cm.bytes b.toNat).isSome = true

/-- The bytes where two worlds may differ when the CLIF memory is `cm`: the frame `F`, and the
bytes of `D` that `cm` has not initialised. -/
def Zof (F D : BitVec 64 → Prop) (cm : Clif.Mem) (b : BitVec 64) : Prop :=
  F b ∨ (D b ∧ ¬ Init cm b)

/-- **The memory relation on two worlds.** -/
def MRP (Γ : Rel) (f : Clif.Function) (c : BitVec 64) (D : BitVec 64 → Prop) : MemRelTW W2 :=
  fun sl cm p => RelW Γ f c sl cm p.1 ∧ RelW Γ f c sl cm p.2 ∧ SameWorld (Zof Γ.F D cm) p.1 p.2

theorem mem_of_init {F : BitVec 64 → Prop} {syms : String → Option Nat} {cm : Clif.Mem}
    {w w' : Arm.ArmState} (h : MemRel F syms cm w) (h' : MemRel F syms cm w') {b : BitVec 64}
    (hb : Init cm b) : w.mem b = w'.mem b := by
  obtain ⟨hv, hs⟩ := hb
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
  have e1 := h.bytes _ _ hv hy
  have e2 := h'.bytes _ _ hv hy
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at e1 e2
  simp only [Arm.read_mem, Arm.read_store] at e1 e2
  rw [e1, e2]

/-- Agreement outside `Zof F D cm` from agreement outside a set `Y`, for worlds both related to
`cm`, when every byte of `Y` is in `F` or `D`, or lies outside `Zof … cm₀` for an earlier memory
`cm₀` (`hY`). -/
theorem sameWorld_zof {F D Y : BitVec 64 → Prop} {syms : String → Option Nat} {cm : Clif.Mem}
    {w w' : Arm.ArmState} (h : MemRel F syms cm w) (h' : MemRel F syms cm w')
    (hsw : SameWorld Y w w') (hY : ∀ b, Y b → F b ∨ D b) : SameWorld (Zof F D cm) w w' := by
  refine ⟨hsw.1, fun b hb => ?_, hsw.2.2⟩
  simp only [Zof, not_or, not_and, Classical.not_not] at hb
  by_cases hy : Y b
  · rcases hY b hy with hf | hd
    · exact absurd hf hb.1
    · exact mem_of_init h h' (hb.2 hd)
  · exact hsw.2.1 b hy

theorem initIn_zof {Γ : Rel} {f : Clif.Function} {c : BitVec 64} {sl : List (Clif.SlotId × Nat)}
    {cm : Clif.Mem} {w : Arm.ArmState} (h : RelW Γ f c sl cm w) (D : BitVec 64 → Prop) :
    InitIn (fun b => ¬ Zof Γ.F D cm b) cm := by
  intro a hv hs hz
  have hlt := (h.1.1.valid a 1 hv).1
  have hnf := (h.1.1.valid a 1 hv).2 0 (by omega)
  have ht : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rcases hz with hf | ⟨-, hn⟩
  · exact hnf (by simpa using hf)
  · exact hn ⟨by rw [ht]; exact hv, by rw [ht]; exact hs⟩

/-! ## The premises on the external semantics -/

/-- A call of a function, as its CLIF call pins it: a declared extern (`exts`) or an indirect
call (signature in `sigs`) of `n`, whose CLIF semantics in `env` returns on `vals` from `cm`. -/
def CallLg (env : Clif.Env) (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) (n : String)
    (sig : Clif.Signature) (vals : List Clif.Val) (cm : Clif.Mem) : Prop :=
  ((∃ e ∈ exts, e.name = n ∧ e.sig = sig) ∨ sig ∈ sigs) ∧
    ∃ g rv cm', env.extern n = some g ∧ g vals cm = .returned rv cm'

/-- **Non-interference of the external semantics** at the calls `Lg` admits (extern `n`,
signature `sig`, argument values `vals`, CLIF memory `cm`): two worlds that agree outside `Z ⊇ F`,
both related to `cm` with stack pointer `sp0`, with the arguments as the call's kind puts them — a declared extern (in
`exts`) with its arguments where the ABI puts them in both, or an indirect call (signature in
`sigs`) with at most 8 register arguments — give, when the call returns on both, the same values
and worlds that agree outside `Z`. -/
def XNI (F : BitVec 64 → Prop) (syms : String → Option Nat) (exts : List Clif.ExtFunc)
    (sigs : List Clif.Signature) (sp0 : BitVec 64)
    (Lg : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (X : ExtSem) : Prop :=
  ∀ (n : String) (sig : Clif.Signature) (vals : List Clif.Val) (cm : Clif.Mem) (args : List CV)
    (d : Option String) (uses : List CV) (Z : BitVec 64 → Prop) (w w' : Arm.ArmState)
    (o : List CV) (x : Arm.ArmState) (o' : List CV) (x' : Arm.ArmState),
    Lg n sig vals cm →
    (d = some n ∧ uses = args ∨ d = none ∧ ∃ u, uses = u :: args ∧ lo64 u = X.sym n 0) →
    (∀ a, F a → Z a) → SameWorld Z w w' → MemRel F syms cm w → MemRel F syms cm w' →
    spv w = sp0 → spv w' = sp0 →
    ((∃ e ∈ exts, e.name = n ∧ e.sig = sig) ∧ ArgsAt sig vals args w ∧ ArgsAt sig vals args w' ∨
      sig ∈ sigs ∧ vals.length ≤ 8 ∧ AllHold vals args) →
    X.call d uses w = some (o, x) → X.call d uses w' = some (o', x') → o = o' ∧ SameWorld Z x x'

/-- The TLSDESC resolver's flags do not depend on the world outside `F`. -/
def XTls (F : BitVec 64 → Prop) (X : ExtSem) : Prop :=
  ∀ (Z : BitVec 64 → Prop) (n : String) (w w' : Arm.ArmState), (∀ a, F a → Z a) →
    SameWorld Z w w' → X.tlsFlags n w = X.tlsFlags n w'

/-! ## The pinned CLIF call of a step -/

/-- The CLIF call of the instruction `inst` at frame `fr`: its signature and argument values. -/
def StepCall (inst : Clif.Inst) (fr : Clif.Frame) (sig : Clif.Signature) (vals : List Clif.Val) :
    Prop :=
  (∃ fn args e, inst = .call fn args ∧ fr.func.extern? fn = some e ∧ sig = e.sig ∧
    fr.getMany args = .ok vals) ∨
  (∃ sg callee args, inst = .callIndirect sg callee args ∧ fr.func.sigDecls.lookup sg = some sig ∧
    fr.getMany args = .ok vals)

theorem stepCall_unique {inst : Clif.Inst} {fr : Clif.Frame} {sig sig' : Clif.Signature}
    {vals vals' : List Clif.Val} (h : StepCall inst fr sig vals) (h' : StepCall inst fr sig' vals') :
    sig = sig' ∧ vals = vals' := by
  rcases h with ⟨fn, args, e, rfl, he, rfl, hv⟩ | ⟨sg, callee, args, rfl, hs, hv⟩ <;>
    rcases h' with ⟨fn', args', e', he0, he', rfl, hv'⟩ | ⟨sg', callee', args', he0, hs', hv'⟩
  · cases he0
    rw [he] at he'; cases he'
    rw [hv] at hv'; cases hv'
    exact ⟨rfl, rfl⟩
  · cases he0
  · cases he0
  · cases he0
    rw [hs] at hs'; cases hs'
    rw [hv] at hv'; cases hv'
    exact ⟨rfl, rfl⟩

/-- **The pin of a step**: the step's CLIF memory, a legitimate call (`CallLg`), the step's
CLIF call. -/
def StepPin (env : Clif.Env) (exts : List Clif.ExtFunc) (sigs : List Clif.Signature)
    (inst : Clif.Inst) (fr : Clif.Frame) (cm : Clif.Mem) :
    String → Clif.Signature → List Clif.Val → Clif.Mem → Prop :=
  fun n sig vals c => c = cm ∧ CallLg env exts sigs n sig vals c ∧ StepCall inst fr sig vals

theorem callPin_stepPin {env : Clif.Env} {f : Clif.Function} {inst : Clif.Inst} {fr : Clif.Frame}
    {cm : Clif.Mem} (hf : fr.func = f) (hsig : IndSigOk f (indSigs f) inst) :
    CallPin (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm) env inst fr cm := by
  refine ⟨fun fn args e vals g rvals cm' hi he hv hg hgo => ?_,
    fun sg callee args s x vals n g rvals cm' hi hs hc hv hsym hg hgo => ?_⟩
  · refine ⟨rfl, ⟨.inl ⟨e, externsIn_self f fn e (hf ▸ he), rfl, rfl⟩, g, rvals, cm', hg, hgo⟩,
      .inl ⟨fn, args, e, hi, he, rfl, hv⟩⟩
  · refine ⟨rfl, ⟨.inr (hsig sg callee args s hi (hf ▸ hs)).1, g, rvals, cm', hg, hgo⟩,
      .inr ⟨sg, callee, args, hi, hs, hv⟩⟩

/-- **The callee lockstep of a pinned step**, from `XNI`: two pinned calls (`CallG`) of the
same instruction on two worlds that agree outside `Z ⊇ F` are the same call. -/
theorem callLockstep {F : BitVec 64 → Prop} {syms : String → Option Nat} {X : ExtSem}
    {env : Clif.Env} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {inst : Clif.Inst}
    {fr : Clif.Frame} {cm : Clif.Mem} {sp0 : BitVec 64} (hNI : XNI F syms exts sigs sp0 (CallLg env exts sigs) X)
    {Z : BitVec 64 → Prop} (hFZ : ∀ a, F a → Z a) {us : List CV} {w w' : Arm.ArmState}
    (hw : SameWorld Z w w') :
    ∀ dest, CallG F syms X exts sigs sp0 (StepPin env exts sigs inst fr cm) dest us w →
      CallG F syms X exts sigs sp0 (StepPin env exts sigs inst fr cm) dest us w' →
      ∀ o x o' x', X.call (destName dest) us w = some (o, x) →
        X.call (destName dest) us w' = some (o', x') → o = o' ∧ SameWorld Z x x' := by
  intro dest h1 h2 o x o' x' hc hc'
  obtain ⟨n1, sig1, vals1, cm1, args1, ⟨hcm1, hlg1, hsc1⟩, ⟨hm1, hc1⟩, ha1, hd1⟩ := h1
  obtain ⟨n2, sig2, vals2, cm2, args2, ⟨hcm2, -, hsc2⟩, ⟨hm2, hc2⟩, ha2, hd2⟩ := h2
  rw [hcm2, ← hcm1] at hm2
  obtain ⟨rfl, rfl⟩ := stepCall_unique hsc1 hsc2
  have hargs : args1 = args2 := by
    rcases hd1 with ⟨rfl, rfl⟩ | ⟨⟨r, rfl⟩, u, rfl, -⟩ <;>
      rcases hd2 with ⟨he, rfl⟩ | ⟨⟨r', he⟩, u', hu', -⟩
    · rfl
    · cases he
    · cases he
    · exact (List.cons.inj hu').2
  subst hargs
  have hd : destName dest = some n1 ∧ us = args1 ∨
      destName dest = none ∧ ∃ u, us = u :: args1 ∧ lo64 u = X.sym n1 0 := by
    rcases hd1 with ⟨rfl, rfl⟩ | ⟨⟨r, rfl⟩, hu⟩
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨rfl, hu⟩
  have hA : (∃ e ∈ exts, e.name = n1 ∧ e.sig = sig1) ∧ ArgsAt sig1 vals1 args1 w ∧
      ArgsAt sig1 vals1 args1 w' ∨ sig1 ∈ sigs ∧ vals1.length ≤ 8 ∧ AllHold vals1 args1 := by
    rcases ha1 with ⟨hk, ha1⟩ | ha1
    · rcases ha2 with ⟨-, ha2⟩ | ha2
      · exact .inl ⟨hk, ha1, ha2⟩
      · exact .inr ha2
    · exact .inr ha1
  exact hNI n1 sig1 vals1 cm1 args1 (destName dest) us Z w w' o x o' x' hlg1 hd hFZ hw hm1 hm2 hc1
    hc2 hA hc hc'

/-! ## Pairing straight-line ends -/

section
variable {sem semA : Sem} {R : Arm.ArmState → Arm.ArmState → Prop}

theorem pair_fall (hsub : ∀ i us w r, semA i us w = some r → sem i us w = some r)
    {ms : List MInst}
    (hstep : ∀ i ∈ ms, ∀ us w w' o w₁ c o' w₁' c', R w w' → semA i us w = some (o, w₁, c) →
      semA i us w' = some (o', w₁', c') → o = o' ∧ c = c' ∧ R w₁ w₁')
    {ρ : Nat → CV} {w w' : Arm.ArmState} {ρ₁ : Nat → CV} {w₁ : Arm.ArmState}
    {e' : SeqEnd CV Arm.ArmState} (hR : R w w')
    (h1 : seqRun semA ms ρ w = some (.fall ρ₁ w₁)) (h2 : seqRun semA ms ρ w' = some e') :
    ∃ w₁', e' = .fall ρ₁ w₁' ∧ seqRun (pairSem sem) ms ρ (w, w') = some (.fall ρ₁ (w₁, w₁')) ∧
      R w₁ w₁' := by
  obtain ⟨ep, hp, hp1, hp2, hpr⟩ := seqRun_pair hsub ms hstep ρ w w' _ _ hR h1 h2
  cases ep with
  | fall ρ' q =>
    simp only [SeqEnd.mapW, SeqEnd.fall.injEq] at hp1 hp2
    obtain ⟨rfl, rfl⟩ := hp1
    exact ⟨q.2, hp2.symm, hp, hpr⟩
  | stop => simp [SeqEnd.mapW] at hp1

theorem pair_stop (hsub : ∀ i us w r, semA i us w = some r → sem i us w = some r)
    {ms : List MInst}
    (hstep : ∀ i ∈ ms, ∀ us w w' o w₁ c o' w₁' c', R w w' → semA i us w = some (o, w₁, c) →
      semA i us w' = some (o', w₁', c') → o = o' ∧ c = c' ∧ R w₁ w₁')
    {ρ : Nat → CV} {w w' : Arm.ArmState} {k : Nat} {i : MInst} {ops : Array Operand}
    {ρ₁ : Nat → CV} {w₁ : Arm.ArmState} {outs : List CV} {w₂ : Arm.ArmState} {ctl : Ctl}
    {e' : SeqEnd CV Arm.ArmState} (hR : R w w')
    (h1 : seqRun semA ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ ctl))
    (h2 : seqRun semA ms ρ w' = some e') :
    ∃ w₁' w₂', e' = .stop k i ops ρ₁ w₁' outs w₂' ctl ∧
      seqRun (pairSem sem) ms ρ (w, w') = some (.stop k i ops ρ₁ (w₁, w₁') outs (w₂, w₂') ctl) ∧
      R w₁ w₁' ∧ R w₂ w₂' := by
  obtain ⟨ep, hp, hp1, hp2, hpr⟩ := seqRun_pair hsub ms hstep ρ w w' _ _ hR h1 h2
  cases ep with
  | fall => simp [SeqEnd.mapW] at hp1
  | stop k' i' ops' ρ' q outs' q' ctl' =>
    simp only [SeqEnd.mapW, SeqEnd.stop.injEq] at hp1 hp2
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp1
    exact ⟨q.2, q'.2, hp2.symm, hp, hpr⟩

end

/-! ## The paired contracts -/

/-- The paired semantics satisfies the driver's world-independent facts. -/
theorem driverSemG_pair (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    DriverSemG (pairSem (csem F ctx X)) where
  jump := fun l q => pairSem_eq (sem := csem F ctx X) rfl rfl
  rename := by
    intro g gn hg i
    funext us q
    simp only [pairSem]
    rw [(driverSem_csem F ctx X).rename g gn hg i]
  retarget := by
    intro i ls i' h
    funext us q
    simp only [pairSem]
    rw [(driverSem_csem F ctx X).retarget i ls i' h]

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64} {D : BitVec 64 → Prop}

/-- The paired lockstep of the guarded runs of one step (memory `cm`, pin `Pc`). -/
theorem guardedStep
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X)
    (hTls : XTls F X) (ctx : FnCtx) (inst : Clif.Inst) (fr : Clif.Frame) (cm : Clif.Mem)
    (ms : List MInst) :
    ∀ i ∈ ms, ∀ us w w' o w₁ ct o' w₁' ct', SameWorld (Zof F D cm) w w' →
      csemG F ctx X (fun b => ¬ Zof F D cm b) syms (f.externs.map (·.2)) (indSigs f) c
        (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm) i us w = some (o, w₁, ct) →
      csemG F ctx X (fun b => ¬ Zof F D cm b) syms (f.externs.map (·.2)) (indSigs f) c
        (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm) i us w' = some (o', w₁', ct') →
      o = o' ∧ ct = ct' ∧ SameWorld (Zof F D cm) w₁ w₁' := by
  intro i _ us w w' o w₁ ct o' w₁' ct' hw h h'
  have hFZ : ∀ a, F a → Zof F D cm a := fun a h => .inl h
  exact csemG_lockstep2 hFZ hw (callLockstep hNI hFZ hw) (fun n => hTls _ n w w' hFZ hw) h h'

/-- The paired lockstep of guarded runs without calls (the pin `False`). -/
theorem guardedStep0 (hTls : XTls F X) (ctx : FnCtx) (cm : Clif.Mem) (ms : List MInst)
    (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) :
    ∀ i ∈ ms, ∀ us w w' o w₁ c o' w₁' c', SameWorld (Zof F D cm) w w' →
      csemG F ctx X (fun b => ¬ Zof F D cm b) syms exts sigs 0 (fun _ _ _ _ => False) i us w =
        some (o, w₁, c) →
      csemG F ctx X (fun b => ¬ Zof F D cm b) syms exts sigs 0 (fun _ _ _ _ => False) i us w' =
        some (o', w₁', c') →
      o = o' ∧ c = c' ∧ SameWorld (Zof F D cm) w₁ w₁' := by
  intro i _ us w w' o w₁ c o' w₁' c' hw h h'
  have hFZ : ∀ a, F a → Zof F D cm a := fun a h => .inl h
  refine csemG_lockstep2 hFZ hw (fun dest h1 => ?_) (fun n => hTls _ n w w' hFZ hw) h h'
  obtain ⟨_, _, _, _, _, hf, _⟩ := h1
  exact hf.elim

theorem csemG_sub' {ctx : FnCtx} {Rd : BitVec 64 → Prop} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {sp0 : BitVec 64}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} :
    ∀ i us w r, csemG F ctx X Rd syms exts sigs sp0 Pc i us w = some r → csem F ctx X i us w = some r :=
  fun _ _ _ _ h => (csemG_sub h).2.2

theorem zof_sub (cm : Clif.Mem) : ∀ b, Zof F D cm b → F b ∨ D b := by
  intro b h
  rcases h with h | ⟨h, -⟩
  · exact .inl h
  · exact .inr h

/-- **The statement calls on pairs of worlds** (`InstCalls` of `pairSem`): from the rule contracts
on each world (guarded semantics, per CLIF step), paired. -/
theorem instCalls_pair (hc : Compiled f k vc vcp rf af fa fb)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X) :
    InstCalls f (pairSem (csem F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p := by
  intro ctx ii info inst st rss st' tr hctx hmem hE hi hcl hsig hemp hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hstk := callsStack_mono (callsStack_of_check hc.lowerOk) (outgoing_le_intBase hc)
  have key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerInstOkP Rd Pc
        (csemG F ⟨fa.k, af.slotBase⟩ X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc) (RelW Γ f c)
        env p ctx inst
        info.results st rss st' st'.emitted.toList := by
    intro Rd Pc
    obtain ⟨B, hB, stm, hstm, hst⟩ := hmem
    obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkP_runTerm lowerRulesCorrect_program
      excludedUnmatchable callRulesCorrectP indRulesCorrectP memRulesCorrectR_program
      refines_csemG (mrStable_relW Γ f c) (callsRefineP_csemG hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
      (indCallsRefineP_csemG hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1)) (memRefinesR_csemG (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym)
      hctx (outArgsOk_relW Γ f c) (externsIn_self f) hE (memRelOk_relW Γ f c) hi hcl hsig
      (fun fn args e hc' he => hstk B hB stm hstm fn args e (hst ▸ hc') he) hvb hrun
    cases hov
    rw [hemp, Array.empty_append] at hem
    rw [hem, List.toList_toArray]; exact hok
  have k0 := key (fun _ => True) (fun _ _ _ _ => True)
  refine ⟨k0.mono, k0.defs, fun fr cm ρ q hfr hvh hdfg hmr => ?_⟩
  obtain ⟨hm1, hm2, hsw⟩ := hmr
  have hff : fr.func = f := hfr.trans hctx.func
  have L := key (fun b => ¬ Zof F D cm b)
    (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm)
  have hII : InitIn (fun b => ¬ Zof F D cm b) cm := initIn_zof (Γ := Γ) hm1 D
  have hpin := callPin_stepPin (env := env) (cm := cm) hff hsig
  have r1 := L.run fr cm ρ q.1 hfr hvh hdfg hm1 hII hpin
  have r2 := L.run fr cm ρ q.2 hfr hvh hdfg hm2 hII hpin
  have hstep := guardedStep (D := D) hNI hTls ⟨fa.k, af.slotBase⟩ inst fr cm
    st'.emitted.toList
  revert r1 r2
  rcases ho : instOutcome env p fr cm inst with ⟨vals, cm'⟩ | c0 | m <;> intro r1 r2
  · obtain ⟨hU, ρ1, w1, hs1, hres, hmr1⟩ := r1
    obtain ⟨-, ρ2, w2, hs2, -, hmr2⟩ := r2
    obtain ⟨w1', he, hp, hR⟩ := pair_fall (sem := csem F ⟨fa.k, af.slotBase⟩ X) csemG_sub' hstep
      (w := q.1) (w' := q.2) hsw hs1 hs2
    have hw : w2 = w1' := by injection he
    rw [← hw] at hp hR
    exact ⟨hU, ρ1, (w1, w2), hp, hres, hmr1, hmr2,
      sameWorld_zof hmr1.1.1 hmr2.1.1 hR (zof_sub cm)⟩
  · intro hex
    obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, htc⟩ := r1 hex
    obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -⟩ := r2 hex
    obtain ⟨w1', w2', he, hp, -, -⟩ := pair_stop (sem := csem F ⟨fa.k, af.slotBase⟩ X)
      csemG_sub' hstep (w := q.1) (w' := q.2) hsw hs1 hs2
    exact ⟨hU, k1, i1, ops1, ρ1, (wa, w1'), outs1, (wb, w2'), hp, htc⟩
  · trivial

/-- **The terminator calls on pairs of worlds** (`TermCalls` of `pairSem`). -/
theorem termCalls_pair {f₀ : Clif.Function} (Γ : Rel) (hΓ : Γ.F = F) (hTls : XTls F X)
    (ctx' : FnCtx) : TermCalls (pairSem (csem F ctx' X)) (MRP Γ f₀ c D) := by
  intro f ctx ti t data targets out st st' tr hctx hbt htl hph hvb hd hemp hrun
  have key : ∀ (Rd : BitVec 64 → Prop), LowerTermOk
      (csemG F ctx' X Rd Γ.syms [] [] 0 (fun _ _ _ _ => False))
      (RelW Γ f₀ c) (termCtx ctx ti data) t targets st st' st'.emitted.toList := fun Rd =>
    termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable refines_csemG (hΓ ▸ mrStable_relW Γ f₀ c) f ctx ti t data
      targets out st st' tr hctx hbt htl hph hvb hd hemp hrun
  have k0 := key (fun _ => True)
  refine ⟨k0.mono, k0.defs, fun fr cm ρ q hfr hvh hdfg hmr => ?_⟩
  obtain ⟨hm1, hm2, hsw⟩ := hmr
  have L := key (fun b => ¬ Zof Γ.F D cm b)
  have r1 := L.run fr cm ρ q.1 hfr hvh hdfg hm1
  have r2 := L.run fr cm ρ q.2 hfr hvh hdfg hm2
  subst hΓ
  have hstep := guardedStep0 (D := D) (syms := Γ.syms) hTls ctx' cm st'.emitted.toList [] []
  revert r1 r2
  cases t
  all_goals intro r1 r2
  all_goals dsimp only at r1 r2 ⊢
  all_goals first
    | (intro vals hv
       obtain ⟨hU, k1, us1, ops1, ρ1, wa, outs1, wb, hs1, h1, h2, h3, hmr1⟩ := r1 vals hv
       obtain ⟨-, k2, us2, ops2, ρ2, wa', outs2, wb', hs2, -, -, -, hmr2⟩ := r2 vals hv
       obtain ⟨w1', w2', he, hp, hR1, hR⟩ := pair_stop (sem := csem Γ.F ctx' X) csemG_sub' hstep
         (w := q.1) (w' := q.2) hsw hs1 hs2
       injection he with _ _ _ _ hwa _ hwb
       rw [← hwa, ← hwb] at hp
       rw [← hwb] at hR
       exact ⟨hU, k1, us1, ops1, ρ1, (wa, wa'), outs1, (wb, wb'), hp, h1, h2, h3, hmr1, hmr2, hR⟩)
    | (obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, htc⟩ := r1
       obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -⟩ := r2
       obtain ⟨w1', w2', he, hp, -, -⟩ := pair_stop (sem := csem Γ.F ctx' X) csemG_sub' hstep
         (w := q.1) (w' := q.2) hsw hs1 hs2
       exact ⟨hU, k1, i1, ops1, ρ1, (wa, w1'), outs1, (wb, w2'), hp, htc⟩)
    | (refine ⟨r1.1, fun j hj => ?_⟩
       obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, hk, hmr1⟩ := r1.2 j hj
       obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -, hmr2⟩ := r2.2 j hj
       obtain ⟨w1', w2', he, hp, hR1, hR⟩ := pair_stop (sem := csem Γ.F ctx' X) csemG_sub' hstep
         (w := q.1) (w' := q.2) hsw hs1 hs2
       injection he with _ _ _ _ hwa _ hwb
       rw [← hwa, ← hwb] at hp
       rw [← hwb] at hR
       exact ⟨hU, k1, i1, ops1, ρ1, (wa, wa'), outs1, (wb, wb'), hp, hk, hmr1, hmr2, hR⟩)

/-- **The `try_call` calls on pairs of worlds** (`TryCalls` of `pairSem`). -/
theorem tryCalls_pair (hc : Compiled f k vc vcp rf af fa fb)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X) :
    TryCalls f (pairSem (csem F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p
      (RAFrame.compute vcp rf).intBase := by
  intro ctx ti fn args et data sig items targets info trs lo st1 out st' tr hctx hra hd he hph
    hinfo hregs hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hctx' := ctxInv_tryRegs (ctxInv_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  have key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerTryOkP Rd Pc
        (csemG F ⟨fa.k, af.slotBase⟩ X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc) (RelW Γ f c)
        env p
        (tryCtx ctx ti data trs) (.call fn args) info { st1 with emitted := #[] } st'
        st'.emitted.toList := by
    intro Rd Pc
    obtain ⟨ms, hem, hok⟩ := tryOkP_runTerm tryRulesCorrectP tryUnmatchable refines_csemG
      (mrStable_relW Γ f c) (memRefinesR_csemG (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym) (outArgsOk_relW Γ f c)
      (callsRefineP_csemG hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1)) hctx' (externsIn_self f) hra hd he hi
      hinfo hregs' hvb' (st := { st1 with emitted := #[] }) (Nat.le_refl _) hrun
    have : ms = st'.emitted.toList := by
      simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
    rw [← this]; exact hok
  have k0 := key (fun _ => True) (fun _ _ _ _ => True)
  refine ⟨k0.mono, k0.shape, fun fr cm ρ q hfr hvh hdfg hmr => ?_⟩
  obtain ⟨hm1, hm2, hsw⟩ := hmr
  have hff : fr.func = f := hfr.trans hctx'.func
  have L := key (fun b => ¬ Zof F D cm b)
    (StepPin env (f.externs.map (·.2)) (indSigs f) (.call fn args) fr cm)
  have hII : InitIn (fun b => ¬ Zof F D cm b) cm := initIn_zof (Γ := Γ) hm1 D
  have hpin := callPin_stepPin (env := env) (cm := cm) (inst := .call fn args) hff
    (fun _ _ _ _ h => by cases h)
  have r1 := L.run fr cm ρ q.1 hfr hvh hdfg hm1 hII hpin
  have r2 := L.run fr cm ρ q.2 hfr hvh hdfg hm2 hII hpin
  have hstep := guardedStep (D := D) hNI hTls ⟨fa.k, af.slotBase⟩ (.call fn args) fr cm
    (tryFix info st'.emitted.toList)
  revert r1 r2
  rcases ho : instOutcome env p fr cm (.call fn args) with ⟨vals, cm'⟩ | c0 | m <;> intro r1 r2
  · obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, hk, hres, hmr1⟩ := r1
    obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -, -, hmr2⟩ := r2
    obtain ⟨w1', w2', he, hp, hR1, hR⟩ := pair_stop (sem := csem F ⟨fa.k, af.slotBase⟩ X)
      csemG_sub' hstep (w := q.1) (w' := q.2) hsw hs1 hs2
    injection he with _ _ _ _ hwa _ hwb
    rw [← hwa, ← hwb] at hp
    rw [← hwb] at hR
    exact ⟨hU, k1, i1, ops1, ρ1, (wa, wa'), outs1, (wb, wb'), hp, hk, hres, hmr1, hmr2,
      sameWorld_zof hmr1.1.1 hmr2.1.1 hR (zof_sub cm)⟩
  · trivial
  · trivial

/-- **The `try_call_indirect` calls on pairs of worlds** (`TryIndCalls` of `pairSem`). -/
theorem tryIndCalls_pair (hc : Compiled f k vc vcp rf af fa fb)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X) :
    TryIndCalls (pairSem (csem F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p (indSigs f) := by
  intro g ctx ti callee args et data sig items targets info trs lo st1 out st' tr hctx hd he hsig
    h8 hph hinfo hregs hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hctx' := ctxInv_tryRegs (ctxInv_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  have key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerTryOkP Rd Pc
        (csemG F ⟨fa.k, af.slotBase⟩ X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc) (RelW Γ f c)
        env p
        (tryCtx ctx ti data trs) (.callIndirect et.sig callee args) info
        { st1 with emitted := #[] } st' st'.emitted.toList := by
    intro Rd Pc
    obtain ⟨ms, hem, hok⟩ := tryIndOkP_runTerm tryIndRulesCorrectP tryIndUnmatchable
      refines_csemG (mrStable_relW Γ f c) (indCallsRefineP_csemG hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
      hctx' hd he hsig h8 hi hinfo hregs' hvb' (st := { st1 with emitted := #[] })
      (Nat.le_refl _) hrun
    have : ms = st'.emitted.toList := by
      simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
    rw [← this]; exact hok
  have k0 := key (fun _ => True) (fun _ _ _ _ => True)
  refine ⟨k0.mono, k0.shape, fun fr cm ρ q hfr hvh hdfg hmr => ?_⟩
  obtain ⟨hm1, hm2, hsw⟩ := hmr
  have hfg : fr.func = g := hfr.trans hctx'.func
  have hsd := exnTableOpnd_sig he
  let Pc := StepPin env (f.externs.map (·.2)) (indSigs f) (.callIndirect et.sig callee args) fr cm
  have L := key (fun b => ¬ Zof F D cm b) Pc
  have hII : InitIn (fun b => ¬ Zof F D cm b) cm := initIn_zof (Γ := Γ) hm1 D
  have hpin : CallPin Pc env (.callIndirect et.sig callee args) fr cm := by
    refine ⟨(fun _ _ _ _ _ _ _ h => by cases h), fun sg cl ar s x vals n gg rvals cm' hi' hs hc' hv
      hsy hg hgo => ?_⟩
    cases hi'
    rw [hfg, hsd] at hs
    cases hs
    exact ⟨rfl, ⟨.inr hsig, gg, rvals, cm', hg, hgo⟩, .inr ⟨_, _, _, rfl, hfg ▸ hsd, hv⟩⟩
  have r1 := L.run fr cm ρ q.1 hfr hvh hdfg hm1 hII hpin
  have r2 := L.run fr cm ρ q.2 hfr hvh hdfg hm2 hII hpin
  have hstep := guardedStep (D := D) hNI hTls ⟨fa.k, af.slotBase⟩
    (.callIndirect et.sig callee args) fr cm (tryFix info st'.emitted.toList)
  revert r1 r2
  rcases ho : instOutcome env p fr cm (.callIndirect et.sig callee args) with ⟨vals, cm'⟩ | c0 | m <;>
    intro r1 r2
  · obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, hk, hres, hmr1⟩ := r1
    obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -, -, hmr2⟩ := r2
    obtain ⟨w1', w2', he, hp, hR1, hR⟩ := pair_stop (sem := csem F ⟨fa.k, af.slotBase⟩ X)
      csemG_sub' hstep (w := q.1) (w' := q.2) hsw hs1 hs2
    injection he with _ _ _ _ hwa _ hwb
    rw [← hwa, ← hwb] at hp
    rw [← hwb] at hR
    exact ⟨hU, k1, i1, ops1, ρ1, (wa, wa'), outs1, (wb, wb'), hp, hk, hres, hmr1, hmr2,
      sameWorld_zof hmr1.1.1 hmr2.1.1 hR (zof_sub cm)⟩
  · trivial
  · trivial

end

/-! ## Determinism of the VCode run -/

theorem vstep_det {V W : Type} {vc : VCode} {sem : ISem V W} {a b c : VConf V W}
    (h1 : VStep vc sem a b) (h2 : VStep vc sem a c) : b = c := by
  cases h1 with
  | step hvb hi hops hsem hlen hn =>
    cases h2 with
    | step hvb' hi' hops' hsem' hlen' hn' =>
      rw [hvb] at hvb'; cases hvb'
      rw [hi] at hi'; cases hi'
      rw [hops] at hops'; cases hops'
      rw [hsem] at hsem'; cases hsem'
      cases hn with
      | next => cases hn' with
        | next => rfl
      | goto h1 h2 h3 => cases hn' with
        | goto h1' h2' h3' =>
          rw [h2] at h2'; cases h2'
          rw [h3] at h3'; cases h3'
          rfl
      | ret => cases hn' with
        | ret => rfl
      | halt => cases hn' with
        | halt => rfl

theorem star_det {α : Type} {r : α → α → Prop} (hdet : ∀ a b c, r a b → r a c → b = c)
    {a b c : α} (h1 : Star r a b) (h2 : Star r a c) : Star r b c ∨ Star r c b := by
  induction h1 generalizing c with
  | refl => exact .inl h2
  | step hab hbc ih =>
    cases h2 with
    | refl => exact .inr (.step hab hbc)
    | step hab' hb'c =>
      have := hdet _ _ _ hab hab'
      subst this
      exact ih hb'c

/-- From a state at a `rets` whose step returns, the run reaches no other running state. -/
theorem star_rets {V W : Type} {vc : VCode} {sem : ISem V W} {b k : Nat} {ρ : Nat → V} {w : W}
    {vb : VBlock} {us : List (Reg × Reg)} {ops : Array Operand} {outs : List V} {w' : W}
    (hvb : vc.blocks[b]? = some vb) (hk : vb.insts[k]? = some (.rets us))
    (hops : (MInst.rets us).operands = .ok ops)
    (hsem : sem (.rets us) (vuses ops ρ) w = some (outs, w', .ret)) {T : VState V W}
    (h : Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run T)) : T = ⟨b, k, ρ, w⟩ := by
  cases h with
  | refl => rfl
  | step h1 h2 =>
    cases h1 with
    | step hvb' hi' hops' hsem' hlen' hn' =>
      rw [hvb] at hvb'; cases hvb'
      rw [hk] at hi'; cases hi'
      rw [hops] at hops'; cases hops'
      have hs : sem (.rets us) ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w =
          some (outs, w', .ret) := hsem
      rw [hs] at hsem'; cases hsem'
      cases hn' with
      | ret =>
        cases h2 with
        | step h _ => cases h

theorem vRetFrom_det {W : Type} {vc : VCode} {sem : ISem CV W} {vs : VState CV W}
    {us us' : List (Reg × Reg)} {vals vals' : List CV} {w w' : W}
    (h : VRetFrom vc sem vs us vals w) (h' : VRetFrom vc sem vs us' vals' w') :
    us = us' ∧ vals = vals' ∧ w = w' := by
  obtain ⟨b, k, ρ, w₁, vb, ops, outs, hs, hvb, hk, hops, hv, hsem⟩ := h
  obtain ⟨b', k', ρ', w₁', vb', ops', outs', hs', hvb', hk', hops', hv', hsem'⟩ := h'
  subst hv hv'
  have hst : (⟨b', k', ρ', w₁'⟩ : VState CV W) = ⟨b, k, ρ, w₁⟩ := by
    rcases star_det (r := VStep vc sem) (fun _ _ _ h1 h2 => vstep_det h1 h2) hs hs' with h1 | h1
    · exact star_rets hvb hk hops hsem h1
    · exact (star_rets hvb' hk' hops' hsem' h1).symm
  cases hst
  rw [hvb] at hvb'; cases hvb'
  rw [hk] at hk'; cases hk'
  rw [hops] at hops'; cases hops'
  rw [hsem] at hsem'; cases hsem'
  exact ⟨rfl, rfl, rfl⟩

/-! ## Non-interference of the VCode run -/

/-- **Non-interference of a compiled function's VCode run**: two body-entry worlds related to
the same CLIF entry, that agree outside `F ∪ D`, with the same argument registers and
stack-passed argument bytes, return (for a returning CLIF run) through the same `rets`
with the same values, final worlds that agree outside `F ∪ D`. -/
theorem vcode_ni {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {args : List Clif.Val} {cs : Clif.State} {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop}
    (ρ₀ : Nat → CV) (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hrel' : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem
      w₀')
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k))
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w w', VReturns vc (csem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us outs w ∧
        VReturns vc (csem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀' us outs w' ∧
        SameWorld (fun b => F b ∨ D b) w w' := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hRef : Refines F (csem F ⟨fa.k, af.slotBase⟩ X) := refines_csem _ _ X
  have hmem : MemRefines F slotOff syms (csem F ⟨fa.k, af.slotBase⟩ X) :=
    memRefines_csem _ _ X hslot hsym
  have hcalls := callsRefine_csem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hX
  have hicalls := indCallsRefine_csem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hXI hsym
    (fun _ _ _ h => h.1.1.symbols)
  have houtB := outgoing_le_intBase hc
  have H : DriverHyp f vc ctx st0 R gn bl A (csem F ⟨fa.k, af.slotBase⟩ X) (RelW Γ f c) env p := {
    shape := hshape
    cert := hcert
    dsem := (driverSem_csem F ⟨fa.k, af.slotBase⟩ X).toDriverSemG
    insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
      indRulesCorrect memRulesCorrect_program hRef (mrStable_relW Γ f c) hcalls hicalls hmem
      (outArgsOk_relW Γ f c) (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (memRelOk_relW Γ f c)
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef (mrStable_relW Γ f c)
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hc.lowerOk
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨_, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) hcalls, tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef (mrStable_relW Γ f c)
      hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := cfg_of_prepare hc.prepare }
  have HP : DriverHyp f vc ctx st0 R gn bl A (pairSem (csem F ⟨fa.k, af.slotBase⟩ X)) (MRP Γ f c D)
      env p := {
    shape := hshape
    cert := hcert
    dsem := driverSemG_pair F ⟨fa.k, af.slotBase⟩ X
    insts := instCalls_pair hc hX hXI hsym hslot hNI hTls
    terms := termCalls_pair Γ rfl hTls ⟨fa.k, af.slotBase⟩
    ext := H.ext
    indSig := H.indSig
    subE := H.subE
    entryLocs := H.entryLocs
    brIdx := H.brIdx
    noTail := H.noTail
    tries := ⟨_, tryCalls_pair hc hX hsym hslot hNI hTls,
      tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := H.tryExt
    tryInd := tryIndCalls_pair hc hXI hsym hNI hTls
    tryIndSig := H.tryIndSig
    cfg := H.cfg }
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := by
    have hf := hce.func
    exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
        (hf ▸ hB),
      fun s c callee args et hr hs hb hT B hB =>
        htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
      fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
        htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
      fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
        htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩
  have h29 : Arm.r (.GPR 29#5) w₀' = Arm.r (.GPR 29#5) w₀ := (hsw.1 _ (by simp [Masked])).symm
  obtain ⟨kk, ρ₁, w₁, w₁', hs1, hm1, hsw1, hs2, hm2, hsw2⟩ := entry_step2 H
    (driverSem_csem F ⟨fa.k, af.slotBase⟩ X) hmem (mrStable_relW Γ f c) hB0 hce.callers hce.func
    rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hrel' hargs hreg h29 hstk
  have hFD : ∀ a, F a → F a ∨ D a := fun a h => .inl h
  have hmP : Match f ctx R gn bl A (MRP Γ f c D) cs.frame.slots cs ⟨0, kk, ρ₁, (w₁, w₁')⟩ := by
    refine ⟨hm1.1, hm1.2.1, hm1.2.2.1, ⟨hm1.2.2.2.1, hm2.2.2.2.1, ?_⟩, hm1.2.2.2.2⟩
    have h01 : SameWorld (fun b => F b ∨ D b) w₁ w₁' :=
      SameWorld.trans (SameWorld.mono hFD hsw1)
        (SameWorld.trans hsw (SameWorld.symm (SameWorld.mono hFD hsw2)))
    exact sameWorld_zof hm1.2.2.2.1.1.1 hm2.2.2.2.1.1.1 h01 (fun b h => h)
  intro vals cm hrun
  have hR := sim_run HP hP fuel cs ⟨0, kk, ρ₁, (w₁, w₁')⟩ (.refl _) hmP
  rw [hrun] at hR
  obtain ⟨us, outs, w, cm0, hret, -, -, -, hmr, -⟩ := hR
  obtain ⟨h1, h2⟩ := vRetFrom_pair hret
  exact ⟨us, outs, w.1, w.2, VRetFrom.prefix hs1 h1, VRetFrom.prefix hs2 h2,
    SameWorld.mono (zof_sub cm0) hmr.2.2⟩

/-- **The per-function theorem with the final world and non-interference**: as
`backend_correct_world`, and the one VCode outcome of the body-entry world `w₀` is realised also
by every activation entered with a body-entry world `w₀'` related to the same CLIF entry, that
agrees with `w₀` outside `F ∪ D` (when the external semantics keeps the agreement: `XNI`, `XTls`) (with the same argument registers and stack-passed argument
bytes), up to the addresses `F ∪ D`. -/
theorem backend_correct_world_ni {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
          (CallLg env (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n) := by
  intro vals cm hrun
  have hI := iselSim_relW hsub hc hX hXI hsym hslot (fun _ => 0) hcs hrel hargs htr fuel
  have hM6 : ∀ (w₀ : Arm.ArmState) (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
      (s : Arm.ArmState), ActEntry vcp rf af fa fb K F G X H base ra s w₀ → _ :=
    fun w₀ H G base ra s he => by
      have h := regLevelCorrect_world hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
        (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
        (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body)
        (fun _ => 0)
      rw [he.hF] at h
      exact h
  obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
  have hrs : vc.RetsSite us := by
    obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
    exact ⟨b, vb, k, hvb, hk⟩
  refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H G base ra s he => ?_,
    fun hNI hTls D w₀' hrel' hsw hreg hstk H G base ra s he => ?_⟩
  · have hP := prepareCorrect_of_check (driverSem_csem F ⟨fa.k, af.slotBase⟩ X) hc.prepOk
      (fun _ => 0) w₀
    obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ := (hM6 w₀ H G base ra s he).1 us outs w
      (vReturns_gotV (hP.1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩
  · obtain ⟨us', outs', w1, w2, hv1, hv2, hsw12⟩ := vcode_ni hsub hc hX hXI hsym hslot hNI hTls
      (fun _ => 0) hcs hrel hrel' hargs hsw hreg hstk htr fuel vals cm hrun
    obtain ⟨rfl, rfl, rfl⟩ := vRetFrom_det (vs := ⟨0, 0, fun _ => 0, w₀⟩) hv1 hv
    have hP := prepareCorrect_of_check (driverSem_csem F ⟨fa.k, af.slotBase⟩ X) hc.prepOk
      (fun _ => 0) w₀'
    obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ := (hM6 w₀' H G base ra s he).1 us' outs' w2
      (vReturns_gotV (hP.1 _ _ _ hv2))
    refine ⟨n, ⟨h1, h2, fun a ha => ?_, fun g hg h29 h31 => ?_, h5, h6⟩, h7⟩
    · rw [h3 a (fun hf => ha (.inl hf))]
      exact (hsw12.2.1 a ha).symm
    · rw [h4 g hg h29 h31]
      exact (hsw12.1 g hg).symm

end E2E
