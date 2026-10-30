import FV.Concurrency.CallSegT
import FV.Concurrency.CallResume
import FV.Concurrency.CallEnterClif

/-!
# The event-free steps between segments as `RealizedT` (#473, step (4))

Between two segments of the linking induction the thread takes event-free steps: the caller's
`bl` with the CLIF `call` (the callee's slots added to the mask), the callee's `ret` with the
CLIF return. Here:

* **`cstepS_of_cstepI`**: a `CStepI` step between running states is a `CStepS` step between the
  states encoding the masks (`CStepI` does not see the own bytes of its states);
* **`realizedT_nil`**: an event-free Arm label realizing an event-free `CStepS` step is a
  `RealizedT` of one label, the dirty set kept;
* **`realizedT_call`**: at a direct call of a program function by the thread state
  `pushC ext s` (an activation's state below its callers), the `bl`'s event-free label realizes
  the CLIF call (`CallEnterClif.cstepI_call_entry`): the callee's entry state below the caller's
  frame and `ext`, the callee's placed slot bytes added to the mask.
-/

namespace Concurrency.CallStepT

open Prog ClifThread ClifThreadI ThreadRefine PrivCohT CallComposeT ArmThread ArmAllocThread
  PrepThread ClifCStepTerm ClifLift

variable {env : Clif.Env} {p : Clif.Program} {Bnd : Nat → Prop}

/-- **`CStepI` between running states as `CStepS`** (module doc). -/
theorem cstepS_of_cstepI {s s' : Clif.State} {U U' : Nat → Prop} {evs : List (Ev SKind BVal)}
    (h : CStepI env p (.run s, U) evs (.run s', U')) :
    CStepS env p (encT U (.run s)) evs (encT U' (.run s')) := by
  unfold CStepS
  rw [maskOf_encT, maskOf_encT]
  obtain ⟨hk, hB, hm, hf⟩ := h
  refine ⟨hk, hB, fun a ha => hm a ha, fun B hB' => ?_⟩
  obtain ⟨t'', h1, h2⟩ := hf B hB'
  exact ⟨t'', h1, h2.trans (strip_encT U' (.run s')).symm⟩

theorem evAt_nil1 {α : Type} (q : Nat × Nat) : evAt ([[]] : List (List α)) q = none := by
  obtain ⟨a, b⟩ := q
  cases a <;> simp [evAt]

theorem conv_nil1 : conv ([[]] : List (List ArmThread.Ev)) = [[]] := rfl

/-- **An event-free label realizing an event-free step** (module doc). -/
theorem realizedT_nil {l : Lab} {L : List Lab} (hl : l.evs = []) {c c' : TState}
    (hs : CStepS env p c [] c') (D : Nat → Prop) :
    RealizedT env p Bnd (l :: L) 1 c c' D D := by
  have htr : evTr ((l :: L).take 1) = [[]] := by simp [evTr, hl]
  have href : Refines Maps (fun _ => False) (MonPair [[]]) ([[]] : List (List (Ev SKind BVal)))
      (conv [[]]) id :=
    CallSeg.refines_nilS (by simp) fun q y hy => by rw [evAt_nil1] at hy; cases hy
  have hT := Refines.toTD (D := D) href fun q x hx => by rw [evAt_nil1] at hx; cases hx
  refine ⟨by simp, [[]], id, fun _ _ => False, .cons hs .nil, ?_, ?_, fun _ _ h => h.elim, ?_⟩
  · rw [htr]; exact CallCompose.xClosed_of fun b y hy => by rw [evAt_nil1] at hy; cases hy
  · rw [htr]; exact hT
  · intro a ha
    refine Classical.byContradiction fun hD => ha ⟨fun h => absurd h hD, fun q y hy => ?_⟩
    rw [htr, conv_nil1, evAt_nil1] at hy
    cases hy

/-- **The `bl` realizing the CLIF call** (module doc). -/
theorem realizedT_call {l : Lab} {L : List Lab} (hl : l.evs = [])
    (ext : List (Clif.Frame × List Clif.ValueId)) {s : Clif.State}
    {results : List Clif.ValueId} {fn : Clif.FnRef} {args : List Clif.ValueId}
    {rest : List Clif.Stmt} (hb : s.frame.body = { results, inst := .call fn args } :: rest)
    {e : Clif.ExtFunc} {callee : Clif.Function} (he : s.frame.func.extern? fn = some e)
    (hc : p.func? e.name = some callee) {s1 : Clif.State}
    (hs : Clif.step env p (pushC ext s) = .next s1) (U D : Nat → Prop)
    (hi : ∀ pl, s.mem.place = some pl → pl.init = none) :
    ∃ vals B0 cs, s.frame.getMany args = .ok vals ∧ callee.blocks[0]? = some B0 ∧
      RealizedT env p Bnd (l :: L) 1 (encT U (.run (pushC ext s)))
        (encT (fun a => U a ∨ slotZ callee s.mem a)
          (.run (pushC (({ s.frame with body := rest }, results) :: (s.callers ++ ext)) cs))) D D ∧
      cs.callers = [] ∧ cs.frame.func = callee ∧
      cs.frame.slots = (Clif.enterSlots callee s.mem).1 ∧
      cs.mem = (Clif.enterSlots callee s.mem).2 ∧
      cs.frame.body = B0.body ∧ cs.frame.term = B0.term ∧
      Clif.Regs.empty.setMany (B0.params.map (·.1)) vals = some cs.frame.regs ∧
      vals.map (·.ty) = B0.params.map (·.2) ∧ vals.map (·.ty) = callee.sig.params.map (·.ty) := by
  obtain ⟨vals, B0, cs, h1, h2, hI, h3⟩ :=
    CallEnterClif.cstepI_call_entry (s := pushC ext s) (by exact hb) (by exact he) hc hs U
      (by exact hi)
  exact ⟨vals, B0, cs, h1, h2, realizedT_nil hl (cstepS_of_cstepI hI) D, h3⟩

/-- **A private Arm segment realizing event-free CLIF steps** (the callee's epilogue and `ret`
with the CLIF return): its writes are private (`PrivW P`, no `relXW`), so they end dirty. -/
theorem realizedT_priv {ls : List Lab} {n : Nat} (hn : n ≤ ls.length) {P : Nat → Prop}
    (hW : PrivW P (evTr (ls.take n))) (hk : ∀ l ∈ ls.take n, ∀ e ∈ l.evs, e.k ≠ .relXW)
    {c c' : TState} {trS : List (List (Ev SKind BVal))} (hS : ∀ x ∈ trS, x = [])
    (hrun : CRunS env p c trS c') (hb : ∀ l, P l → Bnd l) (D : Nat → Prop) :
    RealizedT env p Bnd ls n c c' D (fun a => D a ∨ P a) := by
  have href : Refines Maps P (MonPair (evTr (ls.take n))) trS (conv (evTr (ls.take n))) id :=
    CallSeg.refines_nilS hS hW
  have hT := Refines.toTD (D := D) href fun q x hx => by
    rw [CallSeg.evAt_nilS hS] at hx; cases hx
  have hx : CallCompose.XClosed (evTr (ls.take n)) := CallCompose.xClosed_of fun b y hy => by
    obtain ⟨x, hx, hyx⟩ := CallSeg.mem_of_evAt hy
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    exact hk l hl y hyx
  exact ⟨hn, trS, id, fun _ => P, hrun, hx, hT,
    fun _ l h => hb l h, fun a ha => CallSegT.notClean_sub hT ha⟩

/-- **The CLIF return of an activation below its caller** as a `CStepS` step: the returning
frame (no callers of its own, at its `return`) resumes the caller's frame, the mask kept. -/
theorem cstepS_ret_lift {s : Clif.State} (hcl : s.callers = []) (hb : s.frame.body = [])
    {xs : List Clif.ValueId} (hT : s.frame.term = .ret xs)
    {vals : List Clif.Val} (hg : s.frame.getMany xs = .ok vals) {u : Unit}
    (hc : Clif.checkTys s!"return values of %{s.frame.func.name}" vals
      (Clif.AbiParam.tys s.frame.func.sig.returns) = .ok u)
    {caller : Clif.Frame} {results : List Clif.ValueId}
    {cs : List (Clif.Frame × List Clif.ValueId)}
    {regs : Clif.Regs} (hr : caller.regs.setMany results vals = some regs) (U : Nat → Prop) :
    CStepS env p (encT U (.run (pushC ((caller, results) :: cs) s))) []
      (encT U (.run ⟨{ caller with regs := regs }, cs,
        (s.mem.free (s.frame.slots.map (·.2))).leave⟩)) := by
  have h := cstep_ret_pop (env := env) (p := p) (s := pushC ((caller, results) :: cs) s) hb hT hg
    hc (show s.callers ++ _ = _ by rw [hcl]; rfl) hr
  have hI := ClifThreadI.cstepI_of_cstep h (U := U) (fun e he => absurd he List.not_mem_nil)
  have e : (fun a => U a ∧ ¬ writes ([] : List (Ev SKind BVal)) a) = U := by
    funext a
    have : ¬ writes ([] : List (Ev SKind BVal)) a := fun ⟨_, h, _⟩ => absurd h List.not_mem_nil
    exact propext ⟨fun h => h.1, fun h => ⟨h, this⟩⟩
  rw [e] at hI
  exact cstepS_of_cstepI hI

end Concurrency.CallStepT
