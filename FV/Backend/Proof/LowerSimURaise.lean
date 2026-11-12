import FV.E2E.UnwindStatement
import FV.Backend.Proof.IselContractP
import FV.Backend.Proof.IselCtl
import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.IselCtlTryInd
import FV.Backend.Proof.IselLowerAll
import FV.Backend.Proof.IselExcl
import FV.Backend.Proof.IselAtomic
import FV.Backend.Proof.LowerSeq
import FV.Backend.Proof.LowerContract

/-!
# The lowered code of a raising call (S10e, #232)

`docs/plans/unwinding.md`, "The exceptional edge in the per-function theorem". M4's rule
contracts (`LowerInstOk`, `LowerTryOk`) describe the lowered code of a call only for a callee
that returns (`instOutcome`); a callee that unwinds is `stuck` there. This file derives, from
M4's proven rule theorems, what the lowered code does when the CLIF callee unwinds:

* the contracts on the callees' exceptional results (`XRaise`), the counterparts of
  `XCallsOk`/`XCallsIndOk`: `XRaiseOk` (direct calls, `bl`/GOT `blr`), `XRaiseIndOk` (indirect
  calls), and the exclusivity with normal returns `XRaiseExcl` (a returning callee does not
  raise; with it `csemU` refines the callee contract as `csem` does: `E2E.callsRefine_csemU`,
  `E2E.indCallsRefine_csemU`, `FV/E2E/IselSimU.lean`);
* `RaiseSem F X XR sem`: what the proofs use of the activation semantics with unwinding (the
  GOT load, the steps of raising calls); `csemU` has it (`raiseSem_csemU`), so does the
  dead-cleanup chain's `valueSemU`;
* `stmt_raise`: the code of a `call`/`call_indirect` statement whose extern unwinds runs, under
  such a semantics, to a `call` instruction whose callee raises (`XRaise`) the exception object
  `obj` with `ExnRel e obj` and a world related to the extern's memory, where it ends the
  activation;
* `try_raise`: the code of a `try_call`/`try_call_indirect` whose extern unwinds runs to its
  `tryCall`, which continues at the first handler (`.goto 0`) with the payload.

The proof runs M4's rule theorems (`lowerInstOkP_runTerm`, `tryOkP_runTerm`,
`tryIndOkP_runTerm`, for every semantics and environment satisfying the callee contracts) on a
**probe**: the environment in which this one extern call returns (`overEnv`, pinned to the call
by `pinPc`), and the semantics `probe` in which a call returns only if its callee raises an
exception related to the CLIF one (`raiseC`). The rule's run then passes through calls whose
callee raises; the semantics agrees with the probe up to the first of them, where it ends the
activation (`probe_fall_stop`) or, at the `tryCall`, enters the landing pad
(`probe_pre_stop`). The probe's runs exist only in the proof.
-/

namespace Backend.Proof

open Backend Backend.Proof.Driver

/-! ## The contracts on the exceptional results -/

/-- **The callees' exceptional results, direct calls** (`XCallsOk`'s counterpart): a call of the
extern `ext ∈ exts` (`bl name`, or `blr` of its GOT address for a non-colocated declaration)
with its arguments where the ABI puts them (`ArgsAt`), from a world related to the CLIF memory
`cm`, where the CLIF extern unwinds with exception `e` and memory `m`, raises (`XR`) an exception
object related to `e` (`ExnRel`), the world after the unwinder restored the call being related
to `m`. -/
def XRaiseOk (env : Clif.XEnv) (exts : List Clif.ExtFunc) (MR : MemRelT) (X : ExtSem)
    (XR : XRaise) : Prop :=
  ∀ ext ∈ exts, ∀ g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (w : Arm.ArmState)
    (d : Option String) (uses args : List CV) (vals : List Clif.Val) (e : Clif.Exn)
    (m : Clif.Mem),
    env.extern ext.name = some g →
    (d = some ext.name ∧ uses = args ∨
      d = none ∧ ext.colocated = false ∧ uses = ofX (X.sym ext.name 0) :: args) →
    ArgsAt ext.sig vals args w → MR sl cm w → g vals cm = .unwound e m →
    ∃ obj w', XR.raise d uses w = some (obj, w') ∧ E2E.ExnRel e obj ∧ MR sl m w'

/-- **The callees' exceptional results, indirect calls** (`XCallsIndOk`'s counterpart): a `blr`
whose target holds the link-time address of an extern `n` of `env` (call-site signature
`sig ∈ sigs`, at most 8 register arguments) where the CLIF extern unwinds raises an exception
object related to the CLIF exception, the world related to the extern's memory. -/
def XRaiseIndOk (env : Clif.XEnv) (sigs : List Clif.Signature) (MR : MemRelT) (X : ExtSem)
    (XR : XRaise) : Prop :=
  ∀ sig ∈ sigs, ∀ (n : String) g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem)
    (w : Arm.ArmState) (u : CV) (args : List CV) (vals : List Clif.Val) (e : Clif.Exn)
    (m : Clif.Mem),
    env.extern n = some g → (∀ s, env.sigOf n = some s → sig.abiMatch s = true) →
    lo64 u = X.sym n 0 → vals.length ≤ 8 → AllHold vals args → MR sl cm w →
    g vals cm = .unwound e m → vals.map (·.ty) = Clif.AbiParam.tys sig.params →
    ∃ obj w', XR.raise none (u :: args) w = some (obj, w') ∧ E2E.ExnRel e obj ∧ MR sl m w'

/-- **Exclusivity**: at the calls of `XCallsOk`/`XCallsIndOk` whose CLIF extern returns, the
callee does not raise. -/
def XRaiseExcl (env : Clif.XEnv) (exts : List Clif.ExtFunc) (sigs : List Clif.Signature)
    (MR : MemRelT) (X : ExtSem) (XR : XRaise) : Prop :=
  (∀ ext ∈ exts, ∀ g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (w : Arm.ArmState)
    (d : Option String) (uses args : List CV) (vals rvals : List Clif.Val) (cm' : Clif.Mem),
    env.extern ext.name = some g →
    (d = some ext.name ∧ uses = args ∨
      d = none ∧ ext.colocated = false ∧ uses = ofX (X.sym ext.name 0) :: args) →
    ArgsAt ext.sig vals args w → MR sl cm w → g vals cm = .returned rvals cm' →
    XR.raise d uses w = none) ∧
  (∀ sig ∈ sigs, ∀ (n : String) g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem)
    (w : Arm.ArmState) (u : CV) (args : List CV) (vals rvals : List Clif.Val) (cm' : Clif.Mem),
    env.extern n = some g → (∀ s, env.sigOf n = some s → sig.abiMatch s = true) →
    lo64 u = X.sym n 0 → vals.length ≤ 8 → AllHold vals args → MR sl cm w →
    g vals cm = .returned rvals cm' → vals.map (·.ty) = Clif.AbiParam.tys sig.params →
    XR.raise none (u :: args) w = none)

/-! ## The semantics with unwinding, abstractly -/

/-- **What the proofs of this file and of `LowerSimU` use of the activation semantics with
unwinding** (beside `Refines`/`MemRefines` and the driver's facts): the GOT load of a symbol
(`CallsRefine`'s first clause, for the extern symbols `X.sym`), and the steps of a call whose
callee raises (`XR`): a plain `call` ends the activation (defs 0), a supported `tryCall`
(`tryUOk`) continues at its first handler with the payload. `csemU` has them
(`raiseSem_csemU`); so does the dead-cleanup chain's `valueSemU` (`csemU` on calls). -/
structure RaiseSem (F : BitVec 64 → Prop) (X : ExtSem) (XR : XRaise) (sem : Sem) : Prop where
  got : ∀ (rd : Reg) (n : String) (w : Arm.ArmState), ∃ w',
    sem (.loadExtNameGot rd n) [] w = some ([ofX (X.sym n 0)], w', .next) ∧ SameWorldNF F w' w
  call : ∀ ci uses w obj w', XR.raise (callDest ci) uses w = some (obj, w') →
    sem (.call ci) uses w = some ((defCons (.call ci)).map (fun _ => ofX 0), w', .halt)
  tryCall : ∀ ci ti uses w obj w', XR.raise (callDest ci) uses w = some (obj, w') →
    tryUOk ci ti = true → sem (.tryCall ci ti) uses w = some (payloadOuts (.call ci) obj, w', .goto 0)

theorem raiseSem_csemU (F : BitVec 64 → Prop) (fctx : FnCtx) (X : ExtSem) (XR : XRaise) :
    RaiseSem F X XR (csemU F fctx X XR) where
  got := fun _ _ w => ⟨w, rfl, fun _ _ _ => rfl, fun _ _ => rfl, rfl⟩
  call := fun _ _ _ _ _ h => csemU_call_raise h
  tryCall := fun _ _ _ _ _ _ h hok => csemU_try_raise h hok

/-! ## The probe -/

open Classical in
/-- **The probe semantics** (proof device): `sem`, except that a call (`call`/`tryCall`)
continues (`next`, resp. the normal-return successor) exactly when its callee raises (`XR`) an
exception object `obj` with world `w'` such that `C obj w'`, its defs then holding 0. -/
noncomputable def probe (sem : Sem) (XR : XRaise) (C : BitVec 64 → Arm.ArmState → Prop) : Sem :=
  fun i uses w =>
  match i with
  | .call ci =>
    match XR.raise (callDest ci) uses w with
    | some (obj, w') => if C obj w' then some (ci.defs.map (fun _ => ofX 0), w', .next) else none
    | none => none
  | .tryCall ci ti =>
    match XR.raise (callDest ci) uses w with
    | some (obj, w') =>
      if C obj w' then some (ci.defs.map (fun _ => ofX 0), w', .goto ti.handlers.length) else none
    | none => none
  | _ => sem i uses w

section
variable {sem : Sem} {XR : XRaise} {C : BitVec 64 → Arm.ArmState → Prop}

theorem probe_other {i : MInst} (hc : ∀ ci, i ≠ .call ci) (ht : ∀ ci ti, i ≠ .tryCall ci ti) :
    probe sem XR C i = sem i := by
  funext uses w
  cases i with
  | call ci => exact absurd rfl (hc ci)
  | tryCall ci ti => exact absurd rfl (ht ci ti)
  | _ => rfl

theorem probe_call_some {ci : CallInfo} {uses : List CV} {w w' : Arm.ArmState} {outs : List CV}
    {ctl : Ctl} (h : probe sem XR C (.call ci) uses w = some (outs, w', ctl)) :
    ∃ obj, XR.raise (callDest ci) uses w = some (obj, w') ∧ C obj w' ∧
      outs = ci.defs.map (fun _ => ofX 0) ∧ ctl = .next := by
  simp only [probe] at h
  split at h
  · rename_i obj w'' hr
    split at h
    · rename_i hC
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨obj, hr, hC, rfl, rfl⟩
    · cases h
  · cases h

theorem probe_tryCall_some {ci : CallInfo} {ti : TryInfo} {uses : List CV} {w w' : Arm.ArmState}
    {outs : List CV} {ctl : Ctl} (h : probe sem XR C (.tryCall ci ti) uses w = some (outs, w', ctl)) :
    ∃ obj, XR.raise (callDest ci) uses w = some (obj, w') ∧ C obj w' ∧
      outs = ci.defs.map (fun _ => ofX 0) ∧ ctl = .goto ti.handlers.length := by
  simp only [probe] at h
  split at h
  · rename_i obj w'' hr
    split at h
    · rename_i hC
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨obj, hr, hC, rfl, rfl⟩
    · cases h
  · cases h

theorem probe_call_of {ci : CallInfo} {uses : List CV} {w w' : Arm.ArmState} {obj : BitVec 64}
    (hr : XR.raise (callDest ci) uses w = some (obj, w')) (hC : C obj w') :
    probe sem XR C (.call ci) uses w = some (ci.defs.map (fun _ => ofX 0), w', .next) := by
  simp only [probe, hr, hC, ite_true]

theorem probe_tryCall_of {ci : CallInfo} {ti : TryInfo} {uses : List CV} {w w' : Arm.ArmState}
    {obj : BitVec 64} (hr : XR.raise (callDest ci) uses w = some (obj, w')) (hC : C obj w') :
    probe sem XR C (.tryCall ci ti) uses w =
      some (ci.defs.map (fun _ => ofX 0), w', .goto ti.handlers.length) := by
  simp only [probe, hr, hC, ite_true]

/-- The probe refines `ispec` as `sem` does (`ispec` has no call forms). -/
theorem refines_probe {F : BitVec 64 → Prop} (h : Refines F sem) : Refines F (probe sem XR C) := by
  intro i us w outs w' ctl hs
  have hc : ∀ ci, i ≠ .call ci := by rintro ci rfl; simp [ispec] at hs
  have ht : ∀ ci ti, i ≠ .tryCall ci ti := by rintro ci ti rfl; simp [ispec] at hs
  rw [probe_other hc ht]
  exact h i us w outs w' hs

/-- The probe has `sem`'s memory forms. -/
theorem memRefines_probe {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (h : MemRefines F sb syms sem) : MemRefines F sb syms (probe sem XR C) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-! ## Runs of the probe and of the semantics -/

theorem seqRun_cons_next {V W : Type} {s : ISem V W} {i : MInst} {ms : List MInst}
    {ρ : Nat → V} {w : W} {ops : Array Operand} {outs : List V} {w₁ : W}
    (hops : i.operands = .ok ops) (hs : s i (vuses ops ρ) w = some (outs, w₁, .next))
    (hl : outs.length = (ops.toList.filter Operand.isDef).length) :
    seqRun s (i :: ms) ρ w = (seqRun s ms (vdefUpd ops outs ρ) w₁).map SeqEnd.succ := by
  simp only [seqRun, hops, hs, hl, ite_true]

theorem seqRun_cons_halt {V W : Type} {s : ISem V W} {i : MInst} {ms : List MInst}
    {ρ : Nat → V} {w : W} {ops : Array Operand} {outs : List V} {w₁ : W} {ctl : Ctl}
    (hops : i.operands = .ok ops) (hs : s i (vuses ops ρ) w = some (outs, w₁, ctl))
    (hl : outs.length = (ops.toList.filter Operand.isDef).length) (hne : ctl ≠ .next) :
    seqRun s (i :: ms) ρ w = some (.stop 0 i ops ρ w outs w₁ ctl) := by
  cases ctl with
  | next => exact absurd rfl hne
  | _ => simp only [seqRun, hops, hs, hl, ite_true]

/-- **A probe run that falls through a code containing a call** passes through a call whose
callee raises; the run of `sem` stops there if `sem` ends the activation at a raising call. -/
theorem probe_fall_stop
    (hsem : ∀ ci uses w obj w', XR.raise (callDest ci) uses w = some (obj, w') →
      sem (.call ci) uses w = some ((defCons (.call ci)).map (fun _ => ofX 0), w', .halt)) :
    ∀ {ms : List MInst} {ρ : Nat → CV} {w : Arm.ArmState} {ρ' : Nat → CV} {w'' : Arm.ArmState},
    seqRun (probe sem XR C) ms ρ w = some (.fall ρ' w'') → (∃ ci, MInst.call ci ∈ ms) →
    ∃ k ci ops ρ₁ w₁ obj w', seqRun sem ms ρ w =
        some (.stop k (.call ci) ops ρ₁ w₁ ((defCons (.call ci)).map fun _ => ofX 0) w' .halt) ∧
      XR.raise (callDest ci) (vuses ops ρ₁) w₁ = some (obj, w') ∧ C obj w' ∧
      ((defCons (.call ci)).map fun _ => ofX 0).length =
        (ops.toList.filter Operand.isDef).length := by
  intro ms
  induction ms with
  | nil => intro _ _ _ _ _ ⟨ci, h⟩; cases h
  | cons i ms ih =>
    intro ρ w ρ' w'' h hc
    obtain ⟨ops, outs, w₁, hops, hs, hl, hrest⟩ := seqRun_cons_fall h
    by_cases hic : ∃ ci, i = .call ci
    · obtain ⟨ci, rfl⟩ := hic
      obtain ⟨obj, hr, hC, rfl, -⟩ := probe_call_some hs
      have hl' : ((defCons (.call ci)).map fun _ => ofX 0).length =
          (ops.toList.filter Operand.isDef).length := by simp [defCons, hops]
      exact ⟨0, ci, ops, ρ, w, obj, w₁,
        seqRun_cons_halt hops (hsem ci _ w obj w₁ hr) hl' (fun h => by cases h), hr, hC, hl'⟩
    · have hc' : ∀ ci, i ≠ .call ci := fun ci e => hic ⟨ci, e⟩
      have ht : ∀ ci ti, i ≠ .tryCall ci ti := by
        rintro ci ti rfl
        obtain ⟨_, _, _, _, h⟩ := probe_tryCall_some hs
        cases h
      rw [probe_other hc' ht] at hs
      have hc2 : ∃ ci, MInst.call ci ∈ ms := by
        obtain ⟨ci, hci⟩ := hc
        rcases List.mem_cons.mp hci with e | e
        · exact absurd e.symm (hc' ci)
        · exact ⟨ci, e⟩
      obtain ⟨k, ci, ops', ρ₁, w₁', obj, w', h1, h2⟩ := ih hrest hc2
      exact ⟨k + 1, ci, ops', ρ₁, w₁', obj, w', by rw [seqRun_cons_next hops hs hl, h1]; rfl, h2⟩

/-- **A probe run that stops at the last instruction** of a code whose other instructions are
no calls: `sem` runs the other instructions as the probe does. -/
theorem probe_pre_stop :
    ∀ {pre : List MInst} {x : MInst} {ρ : Nat → CV} {w : Arm.ArmState} {k : Nat} {i : MInst}
      {ops : Array Operand} {ρ₁ : Nat → CV} {w₁ : Arm.ArmState} {outs : List CV}
      {w₂ : Arm.ArmState} {ctl : Ctl},
    (∀ m ∈ pre, ∀ ci, m ≠ .call ci) →
    seqRun (probe sem XR C) (pre ++ [x]) ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ ctl) →
    k = pre.length →
    seqRun sem pre ρ w = some (.fall ρ₁ w₁) ∧ i = x ∧ x.operands = .ok ops ∧
      probe sem XR C x (vuses ops ρ₁) w₁ = some (outs, w₂, ctl) ∧
      outs.length = (ops.toList.filter Operand.isDef).length ∧ ctl ≠ .next := by
  intro pre
  induction pre with
  | nil =>
    intro x ρ w k i ops ρ₁ w₁ outs w₂ ctl _ h hk
    rcases seqRun_cons_stop h with ⟨-, rfl, hops, rfl, rfl, hs, hl, hne⟩ |
      ⟨k', _, _, _, hk', -⟩
    · exact ⟨rfl, rfl, hops, hs, hl, hne⟩
    · simp at hk; omega
  | cons m pre ih =>
    intro x ρ w k i ops ρ₁ w₁ outs w₂ ctl hpre h hk
    rcases seqRun_cons_stop h with ⟨rfl, -, -, -, -, -, -, -⟩ |
      ⟨k', ops₀, outs₀, w₃, rfl, hops₀, hs₀, hl₀, hrest⟩
    · simp at hk
    · have hc : ∀ ci, m ≠ .call ci := hpre m (by simp)
      have ht : ∀ ci ti, m ≠ .tryCall ci ti := by
        rintro ci ti rfl
        obtain ⟨_, _, _, _, h⟩ := probe_tryCall_some hs₀
        cases h
      rw [probe_other hc ht] at hs₀
      obtain ⟨h1, h2⟩ := ih (fun m' hm' => hpre m' (by simp [hm'])) hrest
        (by simp at hk; omega)
      exact ⟨by rw [seqRun_cons_next hops₀ hs₀ hl₀, h1]; rfl, h2⟩

end

/-! ## The probe environment and the pinned contracts -/

open Classical in
/-- **The probe environment** (proof device): `E`, except that the extern call of `n` on `vals`
from memory `cm` returns `rv` with memory `m`, and every other extern is stuck on these
arguments and memory. -/
noncomputable def overEnv (E : Clif.Env) (n : String) (vals : List Clif.Val) (cm : Clif.Mem)
    (rv : List Clif.Val) (m : Clif.Mem) : Clif.Env :=
  { E with extern := fun n' => (E.extern n').map fun g v c =>
      if v = vals ∧ c = cm then (if n' = n then .returned rv m else .stuck "probe") else g v c }

/-- The pin of the probe's callee contracts: the extern `n`, signature `s`, arguments `vals`,
memory `cm`. -/
def pinPc (n : String) (s : Clif.Signature) (vals : List Clif.Val) (cm : Clif.Mem) :
    String → Clif.Signature → List Clif.Val → Clif.Mem → Prop :=
  fun n' s' v c => n' = n ∧ s' = s ∧ v = vals ∧ c = cm

/-- Zero values of the given types. -/
def zeroVals (rs : List Clif.AbiParam) : List Clif.Val := rs.map fun r => ⟨r.ty, 0⟩

/-- The memory relation at the slots `slots` only. -/
def pinMR (MR : MemRelT) (slots : List (Clif.SlotId × Nat)) : MemRelT :=
  fun sl cm w => sl = slots ∧ MR sl cm w

/-- The probe's condition on a raise: the object is the CLIF exception's, the world related to
the extern's memory. -/
def raiseC (MR : MemRelT) (slots : List (Clif.SlotId × Nat)) (e : Clif.Exn) (m : Clif.Mem) :
    BitVec 64 → Arm.ArmState → Prop :=
  fun obj w' => E2E.ExnRel e obj ∧ MR slots m w'

theorem overEnv_at {E : Clif.Env} {n : String} {vals : List Clif.Val} {cm : Clif.Mem}
    {rv : List Clif.Val} {m : Clif.Mem} {n' : String} {g' : List Clif.Val → Clif.Mem → Clif.Outcome}
    {rvals : List Clif.Val} {cm' : Clif.Mem}
    (h : (overEnv E n vals cm rv m).extern n' = some g') (hr : g' vals cm = .returned rvals cm') :
    n' = n ∧ rvals = rv ∧ cm' = m := by
  simp only [overEnv, Option.map_eq_some_iff] at h
  obtain ⟨g0, -, rfl⟩ := h
  by_cases hn : n' = n
  · simp only [hn, and_self, ite_true, Clif.Outcome.returned.injEq] at hr
    exact ⟨hn, hr.1.symm, hr.2.symm⟩
  · simp [hn] at hr

theorem overEnv_self {env : Clif.XEnv} {n : String} {g : List Clif.Val → Clif.Mem → Clif.XOutcome}
    (hg : env.extern n = some g) (vals : List Clif.Val) (cm : Clif.Mem) (rv : List Clif.Val)
    (m : Clif.Mem) : ∃ g', (overEnv env.toEnv n vals cm rv m).extern n = some g' ∧
      g' vals cm = .returned rv m := by
  refine ⟨_, by simp [overEnv, Clif.XEnv.toEnv, hg]; rfl, ?_⟩
  simp

theorem prefixHold_zero {rs : List Clif.AbiParam} {ds : List (Reg × Reg)}
    (h : rs.length ≤ ds.length) : PrefixHold (zeroVals rs) (ds.map fun _ => ofX 0) := by
  refine ⟨by simpa [zeroVals] using h, fun j v x hv hx => ?_⟩
  simp only [zeroVals, List.getElem?_map, Option.map_eq_some_iff] at hv hx
  obtain ⟨r, -, rfl⟩ := hv
  obtain ⟨_, -, rfl⟩ := hx
  simp [VHolds, ofX]

theorem zeroVals_tys (rs : List Clif.AbiParam) :
    (zeroVals rs).map (·.ty) = Clif.AbiParam.tys rs := by
  simp [zeroVals, Clif.AbiParam.tys]

section
variable {F : BitVec 64 → Prop} {X : ExtSem} {XR : XRaise} {env : Clif.XEnv}
  {MR : MemRelT} {slots : List (Clif.SlotId × Nat)} {sem : Sem}

/-- **The probe satisfies the pinned callee contract** at a call of `n` on `vals` from `cm`
whose CLIF extern unwinds. -/
theorem callsRefineP_probe {exts : List Clif.ExtFunc} (hRS : RaiseSem F X XR sem)
    (hXR : XRaiseOk env exts MR X XR)
    {n : String} {s : Clif.Signature} {vals : List Clif.Val} {cm : Clif.Mem}
    {g : List Clif.Val → Clif.Mem → Clif.XOutcome} {e : Clif.Exn} {m : Clif.Mem}
    (hg : env.extern n = some g) (hu : g vals cm = .unwound e m) :
    CallsRefineP (pinPc n s vals cm) F (overEnv env.toEnv n vals cm (zeroVals s.returns) m) exts
      (pinMR MR slots) (probe sem XR (raiseC MR slots e m)) := by
  refine ⟨fun n => X.sym n 0, fun rd n w => by
    obtain ⟨w', h1, h2⟩ := hRS.got rd n w
    exact ⟨w', by rw [probe_other (fun _ h => by cases h) (fun _ _ h => by cases h)]; exact h1, h2⟩,
    ?_, ?_⟩
  · intro ext hin g' sl cm0 w dest us ds uses args vals' rvals cm' hg' hd hds hargs hmr hpc hret hrl
    obtain ⟨hn, hs, rfl, rfl⟩ := hpc
    obtain ⟨-, rfl, hcm⟩ := overEnv_at hg' hret
    subst hn hs cm'
    obtain ⟨obj, w', hr, hex, hm⟩ := hXR ext hin g sl cm0 w (callDest ⟨dest, us, ds⟩) uses args
      vals' e m hg (by rcases hd with ⟨rfl, rfl⟩ | ⟨r, rfl, hcol, rfl⟩ <;> simp [callDest, *])
      hargs hmr.2 hu
    exact ⟨_, w', probe_call_of hr ⟨hex, hmr.1 ▸ hm⟩, by simp,
      prefixHold_zero (by rw [hds]; exact Nat.le_refl _), hmr.1, hm⟩
  · intro ext hin g' sl cm0 w dest us ds ti uses args vals' rvals cm' hg' hd hds hti hargs hmr hpc
      hret hrl
    obtain ⟨hn, hs, rfl, rfl⟩ := hpc
    obtain ⟨-, rfl, hcm⟩ := overEnv_at hg' hret
    subst hn hs cm'
    obtain ⟨obj, w', hr, hex, hm⟩ := hXR ext hin g sl cm0 w (callDest ⟨dest, us, ds⟩) uses args
      vals' e m hg (by rcases hd with ⟨rfl, rfl⟩ | ⟨r, rfl, hcol, rfl⟩ <;> simp [callDest, *])
      hargs hmr.2 hu
    exact ⟨_, w', probe_tryCall_of hr ⟨hex, hmr.1 ▸ hm⟩, by simp,
      prefixHold_zero hds, hmr.1, hm⟩

/-- **The probe satisfies the pinned indirect-call contract** at a call of `n` on `vals` from
`cm` whose CLIF extern unwinds. -/
theorem indCallsRefineP_probe {sigs : List Clif.Signature} (hXRi : XRaiseIndOk env sigs MR X XR)
    {syms : String → Option Nat}
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRs : ∀ sl cm w, MR sl cm w → cm.symbols = syms)
    {n : String} {s : Clif.Signature} {vals : List Clif.Val} {cm : Clif.Mem}
    {g : List Clif.Val → Clif.Mem → Clif.XOutcome} {e : Clif.Exn} {m : Clif.Mem}
    (hg : env.extern n = some g) (hu : g vals cm = .unwound e m) :
    IndCallsRefineP (pinPc n s vals cm) (overEnv env.toEnv n vals cm (zeroVals s.returns) m) sigs
      (pinMR MR slots) (probe sem XR (raiseC MR slots e m)) := by
  refine ⟨?_, ?_⟩
  · intro sig hin n' g' sl cm0 w a r us ds u args vals' rvals cm' hg' hsg ha hu' hds hlen hall hmr
      hpc hret hrl hty
    obtain ⟨hn, hs, rfl, rfl⟩ := hpc
    obtain ⟨-, rfl, hcm⟩ := overEnv_at hg' hret
    subst hn hs cm'
    have hX : lo64 u = X.sym n' 0 := by
      rw [hu', hsym n' a (by rw [← hMRs sl _ w hmr.2]; exact ha)]
    obtain ⟨obj, w', hr, hex, hm⟩ := hXRi sig hin n' g sl cm0 w u args vals' e m hg hsg hX hlen
      hall hmr.2 hu hty
    exact ⟨_, w', probe_call_of (ci := ⟨.reg r, us, ds⟩) hr ⟨hex, hmr.1 ▸ hm⟩, by simp,
      prefixHold_zero (by rw [hds]; exact Nat.le_refl _), hmr.1, hm⟩
  · intro sig hin n' g' sl cm0 w a r us ds ti u args vals' rvals cm' hg' hsg ha hu' hds hti hlen
      hall hmr hpc hret hrl hty
    obtain ⟨hn, hs, rfl, rfl⟩ := hpc
    obtain ⟨-, rfl, hcm⟩ := overEnv_at hg' hret
    subst hn hs cm'
    have hX : lo64 u = X.sym n' 0 := by
      rw [hu', hsym n' a (by rw [← hMRs sl _ w hmr.2]; exact ha)]
    obtain ⟨obj, w', hr, hex, hm⟩ := hXRi sig hin n' g sl cm0 w u args vals' e m hg hsg hX hlen
      hall hmr.2 hu hty
    exact ⟨_, w', probe_tryCall_of (ci := ⟨.reg r, us, ds⟩) hr ⟨hex, hmr.1 ▸ hm⟩, by simp,
      prefixHold_zero hds, hmr.1, hm⟩

end

/-! ## The pinned memory relation -/

theorem mrStable_pin {F : BitVec 64 → Prop} {MR : MemRelT} (h : MRStable F MR)
    (slots : List (Clif.SlotId × Nat)) : MRStable F (pinMR MR slots) :=
  fun sl cm w w' hs ⟨h1, h2⟩ => ⟨h1, h sl cm w w' hs h2⟩

theorem outArgsOk_pin {F : BitVec 64 → Prop} {out : Nat} {MR : MemRelT} (h : OutArgsOk F out MR)
    (slots : List (Clif.SlotId × Nat)) : OutArgsOk F out (pinMR MR slots) := by
  intro sl cm w ⟨h1, h2⟩
  obtain ⟨a, b, c⟩ := h sl cm w h2
  exact ⟨a, b, fun k n y hk => ⟨h1, c k n y hk⟩⟩

theorem memRelOk_pin {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {f : Clif.Function} {MR : MemRelT} (h : MemRelOk F sb syms f MR)
    (slots : List (Clif.SlotId × Nat)) : MemRelOk F sb syms f (pinMR MR slots) where
  bytes := fun sl cm w a b hm => h.bytes sl cm w a b hm.2
  valid := fun sl cm w a n hm => h.valid sl cm w a n hm.2
  symbols := fun sl cm w hm => h.symbols sl cm w hm.2
  slots := fun sl cm w id b hm => h.slots sl cm w id b hm.2
  store := fun sl cm w a n y hm hv => ⟨hm.1, h.store sl cm w a n y hm.2 hv⟩


/-! ## The CLIF call that unwinds -/

/-- The exception the call `inst` of frame `fr` raises from memory `cm`, with the extern's
memory (`Clif.raiseAt?` of a statement). -/
def instRaise (env : Clif.XEnv) (p : Clif.Program) (fr : Clif.Frame) (cm : Clif.Mem) :
    Clif.Inst → Option (Clif.Exn × Clif.Mem)
  | .call fn args => Clif.callRaise env p cm fr fn args
  | .callIndirect sig callee args => Clif.callIndRaise env p cm fr sig callee args
  | _ => none

theorem callRaise_spec {env : Clif.XEnv} {p : Clif.Program} {cm : Clif.Mem} {fr : Clif.Frame}
    {fn : Clif.FnRef} {args : List Clif.ValueId} {e : Clif.Exn} {m : Clif.Mem}
    (h : Clif.callRaise env p cm fr fn args = some (e, m)) :
    ∃ ext vals g, fr.func.extern? fn = some ext ∧ fr.getMany args = .ok vals ∧
      vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params ∧ p.func? ext.name = none ∧
      env.extern ext.name = some g ∧ g vals cm = .unwound e m := by
  unfold Clif.callRaise at h
  cases hx : fr.func.extern? fn with
  | none => simp [hx] at h
  | some ext =>
    cases hv : fr.getMany args with
    | trap c => simp [hx, hv] at h
    | stuck s => simp [hx, hv] at h
    | ok vals =>
      by_cases ht : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params
      · simp only [hx, hv, ht, Clif.checkTys, Clif.Res.ofOption_some, Clif.Res.ok_bind, beq_self_eq_true,
          Clif.Res.check_true, Clif.Res.pure_eq] at h
        cases hp : p.func? ext.name with
        | some _ => simp [hp] at h
        | none =>
          cases hg : env.extern ext.name with
          | none => simp [hp, hg] at h
          | some g =>
            simp only [hp, hg] at h
            cases hgo : g vals cm with
            | unwound e' m' =>
              simp only [hgo, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨ext, vals, g, rfl, rfl, ht, hp, hg, hgo⟩
            | _ => simp [hgo] at h
      · have hb : (vals.map (·.ty) == Clif.AbiParam.tys ext.sig.params) = false := by
          simpa using ht
        simp [hx, hv, hb, Clif.checkTys] at h

theorem callIndRaise_spec {env : Clif.XEnv} {p : Clif.Program} {cm : Clif.Mem} {fr : Clif.Frame}
    {sig callee : Nat} {args : List Clif.ValueId} {e : Clif.Exn} {m : Clif.Mem}
    (h : Clif.callIndRaise env p cm fr sig callee args = some (e, m)) :
    ∃ declared x vals name g, fr.func.sigDecls.lookup sig = some declared ∧
      fr.get callee = .ok ⟨.i64, x⟩ ∧ fr.getMany args = .ok vals ∧
      p.funcs.find? (fun f => cm.symbols f.name == some x.toNat) = none ∧
      (env.names ++ p.externNames).find? (fun n => cm.symbols n == some x.toNat) = some name ∧
      env.extern name = some g ∧
      ((env.sigOf name).all declared.abiMatch &&
        vals.map (·.ty) == Clif.AbiParam.tys declared.params) = true ∧
      g vals cm = .unwound e m := by
  unfold Clif.callIndRaise at h
  cases hsd : fr.func.sigDecls.lookup sig with
  | none => simp [hsd] at h
  | some declared =>
    cases hcv : fr.get callee with
    | trap c => simp [hsd, hcv] at h
    | stuck s => simp [hsd, hcv] at h
    | ok cv =>
      cases hx : cv.as? .i64 with
      | none => simp [hsd, hcv, hx] at h
      | some x =>
        have hcv' := Driver.val_as_i64 hx
        subst hcv'
        cases hv : fr.getMany args with
        | trap c => simp [hsd, hcv, hx, hv] at h
        | stuck s => simp [hsd, hcv, hx, hv] at h
        | ok vals =>
          simp only [hsd, hcv, hx, hv, Clif.Res.ofOption_some, Clif.Res.ok_bind,
            Clif.Res.pure_eq] at h
          cases hf : p.funcs.find? (fun f => cm.symbols f.name == some x.toNat) with
          | some _ => simp [hf] at h
          | none =>
            simp only [hf, Clif.externAtRaise] at h
            cases hn : (env.names ++ p.externNames).find? (fun n => cm.symbols n == some x.toNat) with
            | none => simp [hn] at h
            | some name =>
              cases hg : env.extern name with
              | none => simp [hn, hg] at h
              | some g =>
                simp only [hn, hg] at h
                split at h
                · rename_i hchk
                  cases hgo : g vals cm with
                  | unwound e' m' =>
                    simp only [hgo, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact ⟨declared, x, vals, name, g, rfl, rfl, rfl, hf, hn, hg, hchk, hgo⟩
                  | _ => simp [hgo] at h
                · cases h

section
variable {env : Clif.XEnv} {p : Clif.Program} {fr : Clif.Frame} {cm : Clif.Mem}

/-- **The CLIF call that unwinds, in the probe environment**: it returns (zero values of its
signature's returns, the extern's memory), and it is the pinned call. -/
theorem instRaise_spec {inst : Clif.Inst} {e : Clif.Exn} {m : Clif.Mem}
    (h : instRaise env p fr cm inst = some (e, m)) :
    ∃ n s vals g, env.extern n = some g ∧ g vals cm = .unwound e m ∧
      instOutcome (overEnv env.toEnv n vals cm (zeroVals s.returns) m) p fr cm inst =
        .ok (zeroVals s.returns, m) ∧
      CallPin (pinPc n s vals cm) (overEnv env.toEnv n vals cm (zeroVals s.returns) m) inst fr cm := by
  cases inst with
  | call fn args =>
    obtain ⟨ext, vals, g, hx, hv, ht, hp, hg, hgo⟩ := callRaise_spec h
    refine ⟨ext.name, ext.sig, vals, g, hg, hgo, ?_, ?_, ?_⟩
    · simp [instOutcome, hx, hv, ht, Clif.checkTys, hp, overEnv, Clif.XEnv.toEnv, hg,
        zeroVals_tys, Clif.Res.bind]
    · intro fn' args' e' vals' g' rvals cm' hi hx' hv' hg' hr
      simp only [Clif.Inst.call.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      rw [hx] at hx'; cases hx'
      rw [hv] at hv'; cases hv'
      exact ⟨rfl, rfl, rfl, rfl⟩
    · intro _ _ _ _ _ _ _ _ _ _ hi; cases hi
  | callIndirect sig callee args =>
    obtain ⟨declared, x, vals, name, g, hsd, hcv, hv, hf, hn, hg, hchk, hgo⟩ := callIndRaise_spec h
    refine ⟨name, declared, vals, g, hg, hgo, ?_, ?_, ?_⟩
    · simp only [Bool.and_eq_true, beq_iff_eq] at hchk
      simp only [List.find?_append] at hn
      simp [instOutcome, hsd, hcv, hv, hf, Clif.callExternAt, overEnv, Clif.XEnv.toEnv, hn, hg,
        hchk, Clif.checkTys, zeroVals_tys, Clif.Res.bind]
    · intro _ _ _ _ _ _ _ hi; cases hi
    · intro sig' callee' args' s x' vals' n' g' rvals cm' hi hs hcv' hv' hsym hg' hr hty
      simp only [Clif.Inst.callIndirect.injEq] at hi
      obtain ⟨rfl, rfl, rfl⟩ := hi
      rw [hsd] at hs; cases hs
      rw [hv] at hv'; cases hv'
      exact ⟨(overEnv_at hg' hr).1, rfl, rfl, rfl⟩
  | _ => simp [instRaise] at h

end

/-! ## The lowered code of a raising statement -/

/-- **The code of a `call`/`call_indirect` statement whose CLIF extern unwinds** (with exception
`e` and memory `m`) runs, under a semantics with unwinding (`RaiseSem`, e.g. `csemU`), to a
`call` instruction whose callee raises an object related to `e`, the world after the unwinder
related to `m`, where the activation ends — if the code contains a call (a decidable property
of the recorded lowering). From M4's proven rule theorems, run on the probe. -/
theorem stmt_raise {F : BitVec 64 → Prop} {X : ExtSem} {XR : XRaise} {sem : Sem}
    {env : Clif.XEnv} {p : Clif.Program} {f : Clif.Function} {MR : MemRelT} {sb : Nat}
    {syms : String → Option Nat} {out : Nat} (hRS : RaiseSem F X XR sem)
    (hRef : Refines F sem) (hMem : MemRefines F sb syms sem)
    (hMR : MRStable F MR) (hout : OutArgsOk F out MR) (hMRo : MemRelOk F sb syms f MR)
    (hstk : CallsStack f out)
    (hXR : XRaiseOk env (f.externs.map (·.2)) MR X XR) (hXRi : XRaiseIndOk env (indSigs f) MR X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRs : ∀ sl cm w, MR sl cm w → cm.symbols = syms)
    {ctx : Ctx} (hctx : CtxInv f ctx) (hE : Compile.functionE f = true)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hin : ∃ B ∈ f.blocks, ∃ stm ∈ B.body, stm.inst = inst)
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hsig : IndSigOk f (indSigs f) inst) {st : LState} {rss : List (List Reg)} {st' : LState}
    {tr : List Isle.RuleId} (hemp : st.emitted = #[]) (hvb : ValsBelow ctx st)
    (hrun : runTerm ctx "lower" [.inst ii] st = .ok (some (.regsVec rss), st', tr))
    (hcall : ∃ ci, MInst.call ci ∈ st'.emitted.toList)
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (hf : fr.func = ctx.func) (hvh : ValsHeld fr ρ) (hdc : DFGCons ctx fr) (hmr : MR fr.slots cm w)
    {e : Clif.Exn} {m : Clif.Mem} (hr : instRaise env p fr cm inst = some (e, m)) :
    UsesOk st fr st'.emitted.toList ∧ ∃ k ci ops ρ₁ w₁ obj w',
      seqRun sem st'.emitted.toList ρ w =
        some (.stop k (.call ci) ops ρ₁ w₁ ((defCons (.call ci)).map fun _ => ofX 0) w' .halt) ∧
      XR.raise (callDest ci) (vuses ops ρ₁) w₁ = some (obj, w') ∧ E2E.ExnRel e obj ∧
      MR fr.slots m w' ∧
      ((defCons (.call ci)).map fun _ => ofX 0).length =
        (ops.toList.filter Operand.isDef).length := by
  obtain ⟨n, s, vals, g, hg, hu, hO, hpin⟩ := instRaise_spec hr
  obtain ⟨B, hB, stm, hstm, rfl⟩ := hin
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkP_runTerm lowerRulesCorrect_program
    excludedUnmatchable callRulesCorrectP indRulesCorrectP memRulesCorrectR_program
    (Rd := fun _ => True) (Pc := pinPc n s vals cm) (cp := p)
    (refines_probe (XR := XR) (C := raiseC MR fr.slots e m) hRef) (mrStable_pin hMR fr.slots)
    (callsRefineP_probe (slots := fr.slots) hRS hXR hg hu)
    (indCallsRefineP_probe (sem := sem) (slots := fr.slots) hXRi hsym hMRs hg hu)
    (memRefinesR_of (memRefines_probe hMem)) hctx (outArgsOk_pin hout fr.slots)
    (externsIn_self f) hE (memRelOk_pin hMRo fr.slots) hi hc hsig
    (fun fn args e' hc' he => hstk B hB stm hstm fn args e' hc' he) hvb hrun
  have hms : ms = st'.emitted.toList := by
    rw [hemp, Array.empty_append] at hem; rw [hem, List.toList_toArray]
  subst hms
  have hrun' := hok.run fr cm ρ w hf hvh hdc ⟨rfl, hmr⟩ (fun _ _ _ => trivial) hpin
  rw [hO] at hrun'
  obtain ⟨hU, ρ', w'', hsr, -, -⟩ := hrun'
  obtain ⟨k, ci, ops, ρ₁, w₁, obj, w', h1, h2, ⟨h3, h4⟩, h5⟩ :=
    probe_fall_stop (fun ci uses w obj w' hra => hRS.call ci uses w obj w' hra) hsr hcall
  exact ⟨hU, k, ci, ops, ρ₁, w₁, obj, w', h1, h2, h3, h4, h5⟩

/-- **The code of a `try_call`/`try_call_indirect` whose CLIF extern unwinds** (exception `e`,
memory `m`) runs, under a semantics with unwinding, to its `tryCall`, whose callee raises an
object related to `e` (the world related to `m`) and which continues at the first handler
(`.goto 0`) with the payload — if the code before the call contains no call and the call's
shape is supported (`tryUOk`; decidable properties of the recorded lowering). From M4's proven
`try_call` rule theorems, run on the probe. `hT`: the direct call's stack arguments fit the
outgoing area, the indirect call's signature is an indirect-call signature of `f`. -/
theorem try_raise {F : BitVec 64 → Prop} {X : ExtSem} {XR : XRaise} {sem : Sem}
    {env : Clif.XEnv} {p : Clif.Program} {f : Clif.Function} {MR : MemRelT} {sb : Nat}
    {syms : String → Option Nat} {out : Nat} (hRS : RaiseSem F X XR sem)
    (hRef : Refines F sem) (hMem : MemRefines F sb syms sem)
    (hMR : MRStable F MR) (hout : OutArgsOk F out MR)
    (hXR : XRaiseOk env (f.externs.map (·.2)) MR X XR) (hXRi : XRaiseIndOk env (indSigs f) MR X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRs : ∀ sl cm w, MR sl cm w → cm.symbols = syms)
    {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat} {et : Clif.ExnTable} {data : V}
    {sig : Clif.Signature} {items : List (Option Nat)} {targets : List Label} {info : TryInfo}
    {trs : List Reg × List Reg} {lo st1 : LState} {outv : V} {st' : LState}
    {tr : List Isle.RuleId} {ci : Clif.Inst}
    (hT : (∃ fn args, ci = .call fn args ∧ tryCallData f (.tryCall fn args et) = .ok data ∧
        ∀ e, f.extern? fn = some e → SigStackOk e.sig out) ∨
      (∃ callee args, ci = .callIndirect et.sig callee args ∧
        tryCallData f (.tryCallIndirect callee args et) = .ok data ∧ sig ∈ indSigs f ∧
        sig.params.length ≤ 8))
    (he : exnTableOpnd f et = .ok (sig, items))
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    (hinfo : tryInfoOf sig items targets = some info) (hregs : tryRegsOf sig lo = some (trs, st1))
    (hvb : ValsBelow ctx lo)
    (hrun : runTerm (tryCtx ctx ti data trs) "lower_branch" [.inst ti, .labels targets]
      { st1 with emitted := #[] } = .ok (some outv, st', tr))
    {pre : List MInst} {c : CallInfo} (hms : st'.emitted.toList = pre ++ [.call c])
    (hpre : ∀ m ∈ pre, ∀ ci, m ≠ .call ci) (hok : tryUOk c info = true)
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (hf : fr.func = ctx.func) (hvh : ValsHeld fr ρ) (hdc : DFGCons (tryCtx ctx ti data trs) fr)
    (hmr : MR fr.slots cm w) {e : Clif.Exn} {m : Clif.Mem}
    (hr : instRaise env p fr cm ci = some (e, m)) :
    UsesOk { st1 with emitted := #[] } fr st'.emitted.toList ∧ ∃ ops ρ₁ w₁ obj w',
      seqRun sem (pre ++ [.tryCall c info]) ρ w =
        some (.stop pre.length (.tryCall c info) ops ρ₁ w₁ (payloadOuts (.call c) obj) w'
          (.goto 0)) ∧
      XR.raise (callDest c) (vuses ops ρ₁) w₁ = some (obj, w') ∧ E2E.ExnRel e obj ∧
      MR fr.slots m w' := by
  obtain ⟨n, s, vals, g, hg, hu, hO, hpin⟩ := instRaise_spec hr
  have hctx' := ctxInv_tryRegs (ctxInv_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  have hR' := refines_probe (XR := XR) (C := raiseC MR fr.slots e m) hRef
  have hcr := callsRefineP_probe (slots := fr.slots) (s := s) hRS hXR hg hu
  have hicr := indCallsRefineP_probe (sem := sem) (slots := fr.slots) (s := s) hXRi hsym
    hMRs hg hu
  obtain ⟨ms, hem, hlow⟩ : ∃ ms, st'.emitted = ({ st1 with emitted := #[] } : LState).emitted ++
      ms.toArray ∧ LowerTryOkP (fun _ => True) (pinPc n s vals cm)
        (probe sem XR (raiseC MR fr.slots e m)) (pinMR MR fr.slots)
        (overEnv env.toEnv n vals cm (zeroVals s.returns) m) p (tryCtx ctx ti data trs) ci info
        { st1 with emitted := #[] } st' ms := by
    rcases hT with ⟨fn, args, rfl, hd, hra⟩ | ⟨callee, args, rfl, hd, hsg, h8⟩
    · exact tryOkP_runTerm tryRulesCorrectP tryUnmatchable hR' (mrStable_pin hMR fr.slots)
        (memRefinesR_of (memRefines_probe hMem)) (outArgsOk_pin hout fr.slots) hcr hctx'
        (externsIn_self f) hra hd he hi hinfo hregs' hvb' (Nat.le_refl _) hrun
    · exact tryIndOkP_runTerm tryIndRulesCorrectP tryIndUnmatchable hR' (mrStable_pin hMR fr.slots)
        hicr hctx' hd he hsg h8 hi hinfo hregs' hvb' (Nat.le_refl _) hrun
  have hms' : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  subst hms'
  have hrun' := hlow.run fr cm ρ w hf hvh hdc ⟨rfl, hmr⟩ (fun _ _ _ => trivial) hpin
  rw [hO] at hrun'
  obtain ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, hsr, hk, -, -⟩ := hrun'
  rw [hms, tryFix_append] at hsr
  rw [hms] at hk
  have hk' : k = pre.length := by simp only [List.length_append, List.length_singleton] at hk; omega
  obtain ⟨hpre_run, rfl, hops, hprobe, -, -⟩ := probe_pre_stop hpre hsr hk'
  obtain ⟨obj, hra, ⟨hex, hm⟩, -, -⟩ := probe_tryCall_some hprobe
  have hsem := hRS.tryCall c info _ _ obj _ hra hok
  have hops' : (MInst.call c).operands = .ok ops := by rw [← operands_tryCall_call c info]; exact hops
  have hlen' : (payloadOuts (.call c) obj).length = (ops.toList.filter Operand.isDef).length := by
    simp [payloadOuts, defCons, hops']
  refine ⟨hU, ops, ρ₁, w₁, obj, w₂, ?_, hra, hex, hm⟩
  have := seqRun_append_fall_stop sem hpre_run
    (seqRun_cons_halt (ms := []) hops hsem hlen' (by intro h; cases h))
  rwa [Nat.zero_add] at this

end Backend.Proof
