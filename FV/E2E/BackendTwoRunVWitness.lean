import FV.E2E.BackendTwoRunEither
import FV.E2E.BackendWorldCleanupIWitness
import FV.E2E.BackendTwoRunLWLslWitness
import FV.E2E.BackendTwoRunLRWitness

/-!
# Witnesses for the cleanup path's paired run and two-run lock (SEM1 #537, #713)

Non-vacuity of `backend_pairRunDF_cleanup`, `backend_twoRunLERWZIUV` and the `CompiledEither`
dispatch `backend_twoRunLERWZIUF_either`, on real compilations through the cleanup path:

* `cleanupChecks`, `cleanupChecks_sound`: a closed check (`native_decide`) that a function compiles
  through the cleanup path (`CompiledCleanup` at the spill allocation) to code whose `blr` lines
  avoid `x30` and that holds no call or TLS line (`noHookLinesB`), so the lock's hook premises are
  vacuous;
* `DeadCleanupWitness.source` (whose cleanup removes an instruction): `source_pairRunDF_cleanup`
  (the paired value run of two entry worlds differing inside `F`), `source_twoRunLERWZIUV` (two
  entries, the lock to the return and `RetAgreeX`), `source_twoRunLERWZIUF_either` (the same through
  the dispatch, `CompiledEither.cleanup`);
* `LinkSlotSysWitness.Lsl`'s `r` (reads its uninitialised slot), run by the linked machine's hooks
  `Lsl.hooks M` at any depth: `r_twoRunLERWZIUV_Lsl` on `r`'s compilation through the cleanup path,
  `r_twoRunLERWZIUF_either_Lsl` on `Lsl`'s own (legacy) compilation through the dispatch
  (`CompiledEither.legacy`).
-/

namespace E2E.TwoRunVWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup E2E.LinkSlotSysWitness
  E2E.LinkCheck
open E2E.LinkWitness (idHooks)

/-- An external semantics without callees and with constant TLS flags. -/
def xQuiet : ExtSem := ⟨fun _ _ _ => none, fun _ _ => 0, 0, fun _ _ => Arm.PState.zero⟩

theorem xQuiet_tls (F : BitVec 64 → Prop) : XTls F xQuiet := fun _ _ _ _ _ _ => rfl

/-- **The cleanup path compiles `f`** (spill allocation, offset `0`) to code whose `blr` lines
avoid `x30` and that holds no call or TLS line. -/
def cleanupChecks (f : Clif.Function) : Bool :=
  match lowerFunction f with
  | .error _ => false
  | .ok vc =>
    lowerCheck f vc &&
    match Backend.prepare (prune vc) with
    | .error _ => false
    | .ok vcp =>
      prepCheck (prune vc) vcp && (checkAlloc vcp (spillAlloc vcp)).isOk &&
      match lowerRFunc vcp (spillAlloc vcp) with
      | .error _ => false
      | .ok af => match emitFunc 0 af with
        | .error _ => false
        | .ok fa => match fa.layout with
          | .error _ => false
          | .ok _ => fa.x30Free (getOk (labelOffsets fa.lines)) && noHookLinesB fa

theorem cleanupChecks_sound {f : Clif.Function} (h : cleanupChecks f = true) :
    ∃ vc vcp af fa fb, CompiledCleanup f 0 vc vcp (spillAlloc vcp) af fa fb ∧
      fa.x30Free (getOk (labelOffsets fa.lines)) = true ∧ noHookLinesB fa = true := by
  unfold cleanupChecks at h
  cases hl : lowerFunction f with
  | error e => rw [hl] at h; cases h
  | ok vc =>
    rw [hl] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hlo, h⟩ := h
    cases hp : Backend.prepare (prune vc) with
    | error e => rw [hp] at h; cases h
    | ok vcp =>
      rw [hp] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hpr, hck⟩, h⟩ := h
      have hc : checkAlloc vcp (spillAlloc vcp) = .ok () := by
        cases he : checkAlloc vcp (spillAlloc vcp) with
        | error e => rw [he] at hck; cases hck
        | ok u => cases u; rfl
      cases ha : lowerRFunc vcp (spillAlloc vcp) with
      | error e => rw [ha] at h; cases h
      | ok af =>
        rw [ha] at h
        simp only at h
        cases he : emitFunc 0 af with
        | error e => rw [he] at h; cases h
        | ok fa =>
          rw [he] at h
          simp only at h
          cases hb : fa.layout with
          | error e => rw [hb] at h; cases h
          | ok fb =>
            rw [hb] at h
            simp only [Bool.and_eq_true] at h
            exact ⟨vc, vcp, af, fa, fb, ⟨hl, hlo, hp, hpr, hc, ha, he, hb⟩, h.1, h.2⟩

open DeadCleanupWitness in
set_option maxHeartbeats 10000000 in
theorem source_cleanupChecks : cleanupChecks source = true := by native_decide

open DeadCleanupWitness in
theorem source_lowerScope : lowerScopeB source = true := by native_decide

set_option maxHeartbeats 10000000 in
theorem fR_cleanupChecks : cleanupChecks fR = true := by native_decide

theorem fR_lowerScope : lowerScopeB fR = true := by native_decide

/-- The hook premises of the lock are vacuous on code without call or TLS lines. -/
theorem noHook_lineDest {fa : FnAsm} (h : noHookLinesB fa = true) {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : fa.lines.toList[j]? = some (.ins x t)) {d : Option String}
    (hd : LineDest x d) : False := by
  obtain ⟨hbl, hblr, -⟩ := noHook_line h hj
  rcases hd with ⟨n, rfl, -⟩ | ⟨r, rfl, -⟩
  · exact hbl n rfl
  · exact hblr r rfl

open DeadCleanupWitness in
/-- **`backend_pairRunDF_cleanup` applies** to the cleanup compilation of `source`, for two entry
worlds related to the CLIF entry that differ inside `F` only. -/
theorem source_pairRunDF_cleanup :
    ∃ vc vcp af fa fb, CompiledCleanup source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (env : Clif.Env) (F D : BitVec 64 → Prop) (c : BitVec 64) (w₀ w₀' : Arm.ArmState)
        (args : List Clif.Val) (cs : Clif.State), (∀ a, D a → F a) →
        ClifEntry source args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          source c cs.frame.slots cs.mem w₀ →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          source c cs.frame.slots cs.mem w₀' →
        ArgsAtEntry F source.sig args w₀ → SameWorld (fun b => F b ∨ D b) w₀ w₀' →
        TrapsExplicit env ({ funcs := [] } : Clif.Program) cs → ∀ fuel vals cm,
        Clif.runLoop env { funcs := [] } fuel cs = .returned vals cm →
        ∃ us outs w,
          VRetFrom vcp (pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩
            (ExtSemI.const xQuiet)) ⟨0, 0, fun _ => 0, ((w₀, w₀'), 0)⟩ us outs w ∧
          SameWorld (fun b => F b ∨ D b) w.1.1 w.1.2 := by
  obtain ⟨vc, vcp, af, fa, fb, hc, -, -⟩ := cleanupChecks_sound source_cleanupChecks
  have hsub : InSubset ({ funcs := [] } : Clif.Program) source :=
    InSubset.of_verifiable input_conditions.1 (fun _ => rfl)
  refine ⟨vc, vcp, af, fa, fb, hc, fun env F D c w₀ w₀' args cs hD hce hrel hrel' hargs hsw htr
    fuel vals cm hrun => ?_⟩
  have hnil : (locsOf source.sig).zip args = [] := by
    rw [show locsOf source.sig = [] from rfl]; rfl
  exact backend_pairRunDF_cleanup hsub hc source_callsOne.1 source_callsOne.2
    (fun _ n _ => source_xcalls _ _ _ n) (fun _ _ _ => XNI.xnif (source_xni _ _ _ _ _))
    (fun _ => xQuiet_tls F) (fun n b h => by cases h) rfl hD (fun _ => 0) hce hrel hrel' hargs hsw
    (fun r v h => by simp [hnil] at h) (fun off v h => by simp [hnil] at h) htr fuel
    vals cm hrun

open DeadCleanupWitness in
set_option maxHeartbeats 4000000 in
/-- **`backend_twoRunLERWZIUV` applies** to the cleanup compilation of `source`, for two entries
(any two agreeing as `EntryAgree` and on `x29`), along the paired value run of the CLIF run
(`backend_pairRunD_cleanup`); the hook premises are vacuous (no call or TLS line). -/
theorem source_twoRunLERWZIUV :
    ∃ vc vcp af fa fb, CompiledCleanup source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (env : Clif.Env) (K : Nat) (F : BitVec 64 → Prop) (c : BitVec 64) (w₀ : Arm.ArmState)
        (args : List Clif.Val) (cs : Clif.State),
        ClifEntry source args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          source c cs.frame.slots cs.mem w₀ →
        ArgsAtEntry F source.sig args w₀ →
        TrapsExplicit env ({ funcs := [] } : Clif.Program) cs → ∀ fuel vals cm,
        Clif.runLoop env { funcs := [] } fuel cs = .returned vals cm →
        ∀ (G G' : BitVec 64 → Prop) (base ra ra' : BitVec 64) (Kp Kp' : Nat) (cc cc' : BitVec 64)
          (Pp Pp' : Nat → BitVec 64 → BitVec 8) (Rr Rr' : Nat → Arm.ArmState) (s t0 : Arm.ArmState),
          ActEntryPR vcp (spillAlloc vcp) af fa fb K F G (ExtSemI.const xQuiet) idHooks base ra Kp cc
            Pp Rr s w₀ →
          ActEntryPR vcp (spillAlloc vcp) af fa fb K F G' (ExtSemI.const xQuiet) idHooks base ra' Kp'
            cc' Pp' Rr' t0 w₀ →
          EntryAgree (frameDrop af + K) s t0 → Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0 →
          ∃ N, RetAgreeX (frameDrop af + K) (spv s)
            (iterN (ArmStepX xQuiet idHooks fa)
              ((prologueLines af.saves af.frameSize af.isCaller).length + N + ((epiLines af.saves af.frameSize).length + 1))
              t0)
            (iterN (ArmStepX xQuiet idHooks fa)
              ((prologueLines af.saves af.frameSize af.isCaller).length + N + ((epiLines af.saves af.frameSize).length + 1))
              s) := by
  obtain ⟨vc, vcp, af, fa, fb, hc, hx30', hnh⟩ := cleanupChecks_sound source_cleanupChecks
  have hsub : InSubset ({ funcs := [] } : Clif.Program) source :=
    InSubset.of_verifiable input_conditions.1 (fun _ => rfl)
  refine ⟨vc, vcp, af, fa, fb, hc, fun env K F c w₀ args cs hce hrel hargs htr fuel vals cm hrun
    G G' base ra ra' Kp Kp' cc cc' Pp Pp' Rr Rr' s t0 he he' hag hx29 => ?_⟩
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨body, psF, hpsF, -, hk⟩ := emitFunc_ok hc.emit
  have hpsF' : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF) := by
    rw [hk]; exact hpsF
  have hx30 : fa.x30Free lm = true := by
    rwa [show getOk (labelOffsets fa.lines) = lm by rw [hlm]; rfl] at hx30'
  have hnil : (locsOf source.sig).zip args = [] := by
    rw [show locsOf source.sig = [] from rfl]; rfl
  obtain ⟨us, outs, w, ⟨b, kk, ρ, w₁, vb, ops, outs', hs, hvb, hkk, hops, hvals, hsem⟩, -⟩ :=
    backend_pairRunD_cleanup (D := fun _ => False) (XI := ExtSemI.const xQuiet) hsub hc
      source_callsOne.1 source_callsOne.2 (fun _ n _ => source_xcalls _ _ _ n)
      (fun _ _ _ => source_xni _ _ _ _ _) (fun _ => xQuiet_tls F) (fun n b h => by cases h) rfl
      (fun _ => 0) hce hrel hrel hargs (SameWorld.refl _ _) (fun r v h => by simp [hnil] at h)
      (fun off v h => by simp [hnil] at h) htr fuel vals cm hrun
  obtain ⟨N, -, -, h, -, -⟩ := backend_twoRunLERWZIUV (D := fun _ => False) hc (fun _ => 0)
    (SameWorld.refl _ _) hs hvb hkk
    hops hvals hsem hlm hpsF' he (he'.toN 0)
    (fun n => (he'.calls n).mono fun _ hu => hu.1)
    (fun ht n => (he'.tries ht n).mono fun _ hu => hu.1)
    rfl (formsCovered_cleanup_complete (lowerScope_of source_lowerScope) hc.lower hc.prepare _) hx30
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, hj, _⟩ hd => (noHook_lineDest hnh hj hd).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨a, b, c, _, _, hj, _⟩ _ _ =>
      (noHook_line hnh hj).2.2 a b c rfl |>.elim)
    hag hx29
  exact ⟨N, h⟩

open DeadCleanupWitness in
set_option maxHeartbeats 4000000 in
/-- **`backend_twoRunLERWZIUF_either` applies** to the cleanup compilation of `source` through the
dispatch (`CompiledEither.cleanup`), for two entries. -/
theorem source_twoRunLERWZIUF_either :
    ∃ vc vcp af fa fb, CompiledEither source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (env : Clif.Env) (K : Nat) (F : BitVec 64 → Prop) (c : BitVec 64) (w₀ : Arm.ArmState)
        (args : List Clif.Val) (cs : Clif.State),
        ClifEntry source args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          source c cs.frame.slots cs.mem w₀ →
        ArgsAtEntry F source.sig args w₀ →
        TrapsExplicit env ({ funcs := [] } : Clif.Program) cs → ∀ fuel vals cm,
        Clif.runLoop env { funcs := [] } fuel cs = .returned vals cm →
        ∀ (G G' : BitVec 64 → Prop) (base ra ra' : BitVec 64) (Kp Kp' : Nat) (cc cc' : BitVec 64)
          (Pp Pp' : Nat → BitVec 64 → BitVec 8) (Rr Rr' : Nat → Arm.ArmState) (s t0 : Arm.ArmState),
          ActEntryPR vcp (spillAlloc vcp) af fa fb K F G (ExtSemI.const xQuiet) idHooks base ra Kp cc
            Pp Rr s w₀ →
          ActEntryPR vcp (spillAlloc vcp) af fa fb K F G' (ExtSemI.const xQuiet) idHooks base ra' Kp'
            cc' Pp' Rr' t0 w₀ →
          EntryAgree (frameDrop af + K) s t0 → Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0 →
          ∃ N, RetAgreeX (frameDrop af + K) (spv s)
            (iterN (ArmStepX xQuiet idHooks fa)
              ((prologueLines af.saves af.frameSize af.isCaller).length + N + ((epiLines af.saves af.frameSize).length + 1))
              t0)
            (iterN (ArmStepX xQuiet idHooks fa)
              ((prologueLines af.saves af.frameSize af.isCaller).length + N + ((epiLines af.saves af.frameSize).length + 1))
              s) := by
  obtain ⟨vc, vcp, af, fa, fb, hc, hx30', hnh⟩ := cleanupChecks_sound source_cleanupChecks
  have hsub : InSubset ({ funcs := [] } : Clif.Program) source :=
    InSubset.of_verifiable input_conditions.1 (fun _ => rfl)
  refine ⟨vc, vcp, af, fa, fb, .cleanup hc, fun env K F c w₀ args cs hce hrel hargs htr fuel vals cm
    hrun G G' base ra ra' Kp Kp' cc cc' Pp Pp' Rr Rr' s t0 he he' hag hx29 => ?_⟩
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨body, psF, hpsF, -, hk⟩ := emitFunc_ok hc.emit
  have hpsF' : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF) := by
    rw [hk]; exact hpsF
  have hx30 : fa.x30Free lm = true := by
    rwa [show getOk (labelOffsets fa.lines) = lm by rw [hlm]; rfl] at hx30'
  have hnil : (locsOf source.sig).zip args = [] := by
    rw [show locsOf source.sig = [] from rfl]; rfl
  obtain ⟨N, -, -, h, -, -⟩ := backend_twoRunLERWZIUF_either (D := fun _ => False)
    (XI := ExtSemI.const xQuiet) hsub (.cleanup hc) source_callsOne.1 source_callsOne.2
    (fun _ n _ => source_xcalls _ _ _ n) (fun _ _ _ => XNI.xnif (source_xni _ _ _ _ _))
    (fun _ => xQuiet_tls F) (fun n b h => by cases h) rfl (fun _ h => h.elim) (fun _ => 0) hce hrel
    hrel hargs (SameWorld.refl _ _) (fun r v h => by simp [hnil] at h)
    (fun off v h => by simp [hnil] at h) htr fuel hrun hlm hpsF' he (he'.toN 0)
    (fun n => (he'.calls n).mono fun _ hu => hu.1)
    (fun ht n => (he'.tries ht n).mono fun _ hu => hu.1)
    rfl (formsCovered_cleanup_complete (lowerScope_of source_lowerScope) hc.lower hc.prepare _) hx30
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, hj, _⟩ hd => (noHook_lineDest hnh hj hd).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨a, b, c, _, _, hj, _⟩ _ _ =>
      (noHook_line hnh hj).2.2 a b c rfl |>.elim)
    hag hx29
  exact ⟨N, h⟩

/-- `r`'s callee contracts (no externs, no indirect call), for every memory relation. -/
theorem fR_xcalls (env' : Clif.Env) (MR : MemRelT) (X : ExtSem) :
    XCallsOk env' (fR.externs.map (·.2)) MR X ∧ XCallsIndOk env' (indSigs fR) MR X := by
  have hext : fR.externs.map (·.2) = [] := by
    have := fR_noExterns
    simp only [List.isEmpty_iff] at this
    simp [this]
  have hind : indSigs fR = [] := indSigs_nil_of_indFree (indFreeB_sound fR_indFree)
  refine ⟨?_, ?_⟩
  · rw [hext]; exact fun _ hin => nomatch hin
  · rw [hind]; exact xCallsIndOk_nil _ _ _

theorem fR_xnif {F : BitVec 64 → Prop} {syms : String → Option Nat} {sp0 : BitVec 64}
    {env' : Clif.Env} {X : ExtSem} :
    XNIF F syms (fR.externs.map (·.2)) (indSigs fR) sp0
      (CallLg env' (fR.externs.map (·.2)) (indSigs fR)) X := by
  have hext : fR.externs.map (·.2) = [] := by
    have := fR_noExterns
    simp only [List.isEmpty_iff] at this
    simp [this]
  have hind : indSigs fR = [] := indSigs_nil_of_indFree (indFreeB_sound fR_indFree)
  rw [hext, hind]
  exact XNI.xnif xNI_nil

set_option maxHeartbeats 4000000 in
/-- **`backend_twoRunLERWZIUV` applies** to `Lsl`'s `r` (reads its uninitialised slot) compiled
through the cleanup path, run by the linked machine's hooks `Lsl.hooks M` at any depth, for two
entries whose worlds differ inside `F` (`D ⊆ F`), along the paired value run of the CLIF run
(`backend_pairRunDF_cleanup`). -/
theorem r_twoRunLERWZIUV_Lsl (M : Nat) :
    ∃ vc vcp af fa fb, CompiledCleanup fR 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (env : Clif.Env) (K : Nat) (F D : BitVec 64 → Prop) (c : BitVec 64) (w₀ w₀' : Arm.ArmState)
        (args : List Clif.Val) (cs : Clif.State), (∀ a, D a → F a) →
        ClifEntry fR args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          fR c cs.frame.slots cs.mem w₀ →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          fR c cs.frame.slots cs.mem w₀' →
        ArgsAtEntry F fR.sig args w₀ → SameWorld (fun b => F b ∨ D b) w₀ w₀' →
        (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf fR.sig).zip args → regVal w₀' r = regVal w₀ r) →
        (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf fR.sig).zip args → ∀ k < v.ty.bytes,
          w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
            w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
        TrapsExplicit env Lsl.P.bare cs → ∀ fuel vals cm,
        Clif.runLoop env Lsl.P.bare fuel cs = .returned vals cm →
        ∀ (G G' : BitVec 64 → Prop) (base ra ra' : BitVec 64) (Kp Kp' : Nat) (cc cc' : BitVec 64)
          (Pp Pp' : Nat → BitVec 64 → BitVec 8) (Rr Rr' : Nat → Arm.ArmState) (s t0 : Arm.ArmState),
          ActEntryPR vcp (spillAlloc vcp) af fa fb K F G (ExtSemI.const Lsl.Xb) (Lsl.hooks M) base ra
            Kp cc Pp Rr s w₀ →
          ActEntryPR vcp (spillAlloc vcp) af fa fb K F G' (ExtSemI.const Lsl.Xb) (Lsl.hooks M) base
            ra' Kp' cc' Pp' Rr' t0 w₀' →
          EntryAgree (frameDrop af + K) s t0 → Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0 →
          ∃ N, RetAgreeX (frameDrop af + K) (spv s)
            (iterN (ArmStepX Lsl.Xb (Lsl.hooks M) fa)
              ((prologueLines af.saves af.frameSize af.isCaller).length + N + ((epiLines af.saves af.frameSize).length + 1))
              t0)
            (iterN (ArmStepX Lsl.Xb (Lsl.hooks M) fa)
              ((prologueLines af.saves af.frameSize af.isCaller).length + N + ((epiLines af.saves af.frameSize).length + 1))
              s) ∧
            ∀ a, ¬ F a → ¬ D a →
              (iterN (ArmStepX Lsl.Xb (Lsl.hooks M) fa)
                ((prologueLines af.saves af.frameSize af.isCaller).length + N +
                  ((epiLines af.saves af.frameSize).length + 1)) t0).mem a =
              (iterN (ArmStepX Lsl.Xb (Lsl.hooks M) fa)
                ((prologueLines af.saves af.frameSize af.isCaller).length + N +
                  ((epiLines af.saves af.frameSize).length + 1)) s).mem a := by
  obtain ⟨vc, vcp, af, fa, fb, hc, hx30', hnh⟩ := cleanupChecks_sound fR_cleanupChecks
  refine ⟨vc, vcp, af, fa, fb, hc, fun env K F D c w₀ w₀' args cs hD hce hrel hrel' hargs hsw hreg
    hstk htr fuel vals cm hrun G G' base ra ra' Kp Kp' cc cc' Pp Pp' Rr Rr' s t0 he he' hag hx29 =>
    ?_⟩
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨body, psF, hpsF, -, hk⟩ := emitFunc_ok hc.emit
  have hpsF' : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF) := by
    rw [hk]; exact hpsF
  have hx30 : fa.x30Free lm = true := by
    rwa [show getOk (labelOffsets fa.lines) = lm by rw [hlm]; rfl] at hx30'
  obtain ⟨us, outs, w, ⟨b, kk, ρ, w₁, vb, ops, outs', hs, hvb, hkk, hops, hvals, hsem⟩, -⟩ :=
    backend_pairRunDF_cleanup (XI := ExtSemI.const Lsl.Xb) (Lsl_ok.subset fR fR_mem) hc
      (instCallsOne_all fR) (tryCallsOne_all fR) (fun _ _ _ => fR_xcalls _ _ _)
      (fun _ _ _ => fR_xnif) (fun _ => lslTls F) (fun n b h => by cases h) rfl hD (fun _ => 0) hce
      hrel hrel' hargs hsw hreg hstk htr fuel vals cm hrun
  obtain ⟨N, -, -, h, hm, -⟩ := backend_twoRunLERWZIUV hc (fun _ => 0) hsw hs hvb hkk
    hops hvals hsem hlm hpsF' he (he'.toN 0)
    (fun n => (he'.calls n).mono fun _ hu => hu.1)
    (fun ht n => (he'.tries ht n).mono fun _ hu => hu.1)
    rfl (formsCovered_cleanup_complete (lowerScope_of fR_lowerScope) hc.lower hc.prepare _) hx30
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, hj, _⟩ hd => (noHook_lineDest hnh hj hd).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨a, b, c, _, _, hj, _⟩ _ _ =>
      (noHook_line hnh hj).2.2 a b c rfl |>.elim)
    hag hx29
  exact ⟨N, h, hm⟩

set_option maxHeartbeats 4000000 in
/-- **`backend_twoRunLERWZIUF_either` applies** to `Lsl`'s `r` with `Lsl`'s own compilation (the
legacy path, `CompiledEither.legacy`), run by the linked machine's hooks at any depth, for two
entries. -/
theorem r_twoRunLERWZIUF_either_Lsl (M : Nat) {F : BitVec 64 → Prop} {c : BitVec 64} {K : Nat}
    {args : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState} {env : Clif.Env}
    (hce : ClifEntry fR args cs)
    (hrel : RelW ⟨F, fun _ => none, (Lsl.A fR).af.slotBase,
      (RAFrame.compute (Lsl.A fR).vcp (Lsl.A fR).rf).intBase⟩ fR c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fR.sig args w₀)
    (htr : TrapsExplicit env Lsl.P.bare cs) (fuel : Nat)
    {G G' : BitVec 64 → Prop} {base ra ra' : BitVec 64} {Kp Kp' : Nat} {cc cc' : BitVec 64}
    {Pp Pp' : Nat → BitVec 64 → BitVec 8} {Rr Rr' : Nat → Arm.ArmState} {s t0 : Arm.ArmState}
    (he : ActEntryPR (Lsl.A fR).vcp (Lsl.A fR).rf (Lsl.A fR).af (Lsl.A fR).fa (Lsl.A fR).fb K F G
      (ExtSemI.const Lsl.Xb) (Lsl.hooks M) base ra Kp cc Pp Rr s w₀)
    (he' : ActEntryPR (Lsl.A fR).vcp (Lsl.A fR).rf (Lsl.A fR).af (Lsl.A fR).fa (Lsl.A fR).fb K F G'
      (ExtSemI.const Lsl.Xb) (Lsl.hooks M) base ra' Kp' cc' Pp' Rr' t0 w₀)
    (hag : EntryAgree (frameDrop (Lsl.A fR).af + K) s t0)
    (hx29 : Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0) :
    ∀ vals cm, Clif.runLoop env Lsl.P.bare fuel cs = .returned vals cm →
      ∃ N, RetAgreeX (frameDrop (Lsl.A fR).af + K) (spv s)
        (iterN (ArmStepX Lsl.Xb (Lsl.hooks M) (Lsl.A fR).fa)
          ((prologueLines (Lsl.A fR).af.saves (Lsl.A fR).af.frameSize (Lsl.A fR).af.isCaller).length + N +
            ((epiLines (Lsl.A fR).af.saves (Lsl.A fR).af.frameSize).length + 1)) t0)
        (iterN (ArmStepX Lsl.Xb (Lsl.hooks M) (Lsl.A fR).fa)
          ((prologueLines (Lsl.A fR).af.saves (Lsl.A fR).af.frameSize (Lsl.A fR).af.isCaller).length + N +
            ((epiLines (Lsl.A fR).af.saves (Lsl.A fR).af.frameSize).length + 1)) s) := by
  have hc := fR_compiled
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨body, psF, hpsF, -, hk⟩ := emitFunc_ok hc.emit
  have hx30 : (Lsl.A fR).fa.x30Free lm = true := by
    have h := fR_x30Free
    rwa [show getOk (labelOffsets (Lsl.A fR).fa.lines) = lm by rw [hlm]; rfl] at h
  have hnh := fR_noHookLines
  intro vals cm hrun
  obtain ⟨N, -, -, h, -, -⟩ := backend_twoRunLERWZIUF_either (D := fun _ => False)
    (XI := ExtSemI.const Lsl.Xb) (Lsl_ok.subset fR fR_mem) (.legacy hc) (instCallsOne_all fR)
    (tryCallsOne_all fR) (fun _ _ _ => fR_xcalls _ _ _) (fun _ _ _ => fR_xnif)
    (fun _ => lslTls F) (fun n b h => by cases h) rfl (fun _ h => h.elim) (fun _ => 0) hce hrel
    hrel hargs (SameWorld.refl _ _) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) htr fuel hrun hlm
    (hk ▸ hpsF) he (he'.toN 0)
    (fun n => (he'.calls n).mono fun _ hu => hu.1)
    (fun ht n => (he'.tries ht n).mono fun _ hu => hu.1)
    rfl (Lsl_ok.covered fR fR_mem) hx30
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, hj, _⟩ hd => (noHook_lineDest hnh hj hd).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨a, b, c, _, _, hj, _⟩ _ _ =>
      (noHook_line hnh hj).2.2 a b c rfl |>.elim)
    hag hx29
  exact ⟨N, h⟩

set_option maxHeartbeats 4000000 in
/-- **`backend_twoRunLERWZIUPV` applies** to `Lsl`'s `r` compiled through the cleanup path, run by
the linked machine's hooks at any depth, for two entries whose worlds differ inside `F`: besides
`RetAgreeX` and the memory outside `F ∪ D`, the second run's frame record holds its entry
`x30`/`x29` at the return (#729). -/
theorem r_twoRunLERWZIUPV_Lsl (M : Nat) :
    ∃ vc vcp af fa fb, CompiledCleanup fR 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (env : Clif.Env) (K : Nat) (F D : BitVec 64 → Prop) (c : BitVec 64) (w₀ w₀' : Arm.ArmState)
        (args : List Clif.Val) (cs : Clif.State), (∀ a, D a → F a) →
        ClifEntry fR args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          fR c cs.frame.slots cs.mem w₀ →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          fR c cs.frame.slots cs.mem w₀' →
        ArgsAtEntry F fR.sig args w₀ → SameWorld (fun b => F b ∨ D b) w₀ w₀' →
        (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf fR.sig).zip args → regVal w₀' r = regVal w₀ r) →
        (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf fR.sig).zip args → ∀ k < v.ty.bytes,
          w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
            w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
        TrapsExplicit env Lsl.P.bare cs → ∀ fuel vals cm,
        Clif.runLoop env Lsl.P.bare fuel cs = .returned vals cm →
        ∀ (G G' : BitVec 64 → Prop) (base ra ra' : BitVec 64) (Kp Kp' : Nat) (cc cc' : BitVec 64)
          (Pp Pp' : Nat → BitVec 64 → BitVec 8) (Rr Rr' : Nat → Arm.ArmState) (s t0 : Arm.ArmState),
          ActEntryPR vcp (spillAlloc vcp) af fa fb K F G (ExtSemI.const Lsl.Xb) (Lsl.hooks M) base ra
            Kp cc Pp Rr s w₀ →
          ActEntryPR vcp (spillAlloc vcp) af fa fb K F G' (ExtSemI.const Lsl.Xb) (Lsl.hooks M) base
            ra' Kp' cc' Pp' Rr' t0 w₀' →
          EntryAgree (frameDrop af + K) s t0 → Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0 →
          ∃ N, RetAgreeX (frameDrop af + K) (spv s)
            (iterN (ArmStepX Lsl.Xb (Lsl.hooks M) fa)
              ((prologueLines af.saves af.frameSize af.isCaller).length + N + ((epiLines af.saves af.frameSize).length + 1))
              t0)
            (iterN (ArmStepX Lsl.Xb (Lsl.hooks M) fa)
              ((prologueLines af.saves af.frameSize af.isCaller).length + N + ((epiLines af.saves af.frameSize).length + 1))
              s) ∧
            Arm.read_mem_bytes 16 (spv t0 - 16#64)
              (iterN (ArmStepX Lsl.Xb (Lsl.hooks M) fa)
                ((prologueLines af.saves af.frameSize af.isCaller).length + N +
                  ((epiLines af.saves af.frameSize).length + 1)) t0) = xreg 30 t0 ++ xreg 29 t0 := by
  obtain ⟨vc, vcp, af, fa, fb, hc, hx30', hnh⟩ := cleanupChecks_sound fR_cleanupChecks
  refine ⟨vc, vcp, af, fa, fb, hc, fun env K F D c w₀ w₀' args cs hD hce hrel hrel' hargs hsw hreg
    hstk htr fuel vals cm hrun G G' base ra ra' Kp Kp' cc cc' Pp Pp' Rr Rr' s t0 he he' hag hx29 =>
    ?_⟩
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨body, psF, hpsF, -, hk⟩ := emitFunc_ok hc.emit
  have hpsF' : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF) := by
    rw [hk]; exact hpsF
  have hx30 : fa.x30Free lm = true := by
    rwa [show getOk (labelOffsets fa.lines) = lm by rw [hlm]; rfl] at hx30'
  obtain ⟨us, outs, w, ⟨b, kk, ρ, w₁, vb, ops, outs', hs, hvb, hkk, hops, hvals, hsem⟩, -⟩ :=
    backend_pairRunDF_cleanup (XI := ExtSemI.const Lsl.Xb) (Lsl_ok.subset fR fR_mem) hc
      (instCallsOne_all fR) (tryCallsOne_all fR) (fun _ _ _ => fR_xcalls _ _ _)
      (fun _ _ _ => fR_xnif) (fun _ => lslTls F) (fun n b h => by cases h) rfl hD (fun _ => 0) hce
      hrel hrel' hargs hsw hreg hstk htr fuel vals cm hrun
  obtain ⟨N, -, -, h, -, -, hw2, -, -, -, -, -, -, -⟩ := backend_twoRunLERWZIUPV hc (fun _ => 0) hsw
    hs hvb hkk hops hvals hsem hlm hpsF' he (he'.toN 0)
    (fun n => (he'.calls n).mono fun _ hu => hu.1)
    (fun ht n => (he'.tries ht n).mono fun _ hu => hu.1)
    rfl (formsCovered_cleanup_complete (lowerScope_of fR_lowerScope) hc.lower hc.prepare _) hx30
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, hj, _⟩ hd => (noHook_lineDest hnh hj hd).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨a, b, c, _, _, hj, _⟩ _ _ =>
      (noHook_line hnh hj).2.2 a b c rfl |>.elim)
    hag hx29
  exact ⟨N, h, hw2⟩

open DeadCleanupWitness in
set_option maxHeartbeats 4000000 in
/-- **`backend_twoRunLERWZIUPF_either` applies** to the cleanup compilation of `source` through the
dispatch (`CompiledEither.cleanup`), for two entries: `RetAgreeX` and the second run's frame record
at the return. -/
theorem source_twoRunLERWZIUPF_either :
    ∃ vc vcp af fa fb, CompiledEither source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (env : Clif.Env) (K : Nat) (F : BitVec 64 → Prop) (c : BitVec 64) (w₀ : Arm.ArmState)
        (args : List Clif.Val) (cs : Clif.State),
        ClifEntry source args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          source c cs.frame.slots cs.mem w₀ →
        ArgsAtEntry F source.sig args w₀ →
        TrapsExplicit env ({ funcs := [] } : Clif.Program) cs → ∀ fuel vals cm,
        Clif.runLoop env { funcs := [] } fuel cs = .returned vals cm →
        ∀ (G G' : BitVec 64 → Prop) (base ra ra' : BitVec 64) (Kp Kp' : Nat) (cc cc' : BitVec 64)
          (Pp Pp' : Nat → BitVec 64 → BitVec 8) (Rr Rr' : Nat → Arm.ArmState) (s t0 : Arm.ArmState),
          ActEntryPR vcp (spillAlloc vcp) af fa fb K F G (ExtSemI.const xQuiet) idHooks base ra Kp cc
            Pp Rr s w₀ →
          ActEntryPR vcp (spillAlloc vcp) af fa fb K F G' (ExtSemI.const xQuiet) idHooks base ra' Kp'
            cc' Pp' Rr' t0 w₀ →
          EntryAgree (frameDrop af + K) s t0 → Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0 →
          ∃ N, RetAgreeX (frameDrop af + K) (spv s)
            (iterN (ArmStepX xQuiet idHooks fa)
              ((prologueLines af.saves af.frameSize af.isCaller).length + N + ((epiLines af.saves af.frameSize).length + 1))
              t0)
            (iterN (ArmStepX xQuiet idHooks fa)
              ((prologueLines af.saves af.frameSize af.isCaller).length + N + ((epiLines af.saves af.frameSize).length + 1))
              s) ∧
            Arm.read_mem_bytes 16 (spv t0 - 16#64)
              (iterN (ArmStepX xQuiet idHooks fa)
                ((prologueLines af.saves af.frameSize af.isCaller).length + N +
                  ((epiLines af.saves af.frameSize).length + 1)) t0) = xreg 30 t0 ++ xreg 29 t0 := by
  obtain ⟨vc, vcp, af, fa, fb, hc, hx30', hnh⟩ := cleanupChecks_sound source_cleanupChecks
  have hsub : InSubset ({ funcs := [] } : Clif.Program) source :=
    InSubset.of_verifiable input_conditions.1 (fun _ => rfl)
  refine ⟨vc, vcp, af, fa, fb, .cleanup hc, fun env K F c w₀ args cs hce hrel hargs htr fuel vals cm
    hrun G G' base ra ra' Kp Kp' cc cc' Pp Pp' Rr Rr' s t0 he he' hag hx29 => ?_⟩
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨body, psF, hpsF, -, hk⟩ := emitFunc_ok hc.emit
  have hpsF' : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF) := by
    rw [hk]; exact hpsF
  have hx30 : fa.x30Free lm = true := by
    rwa [show getOk (labelOffsets fa.lines) = lm by rw [hlm]; rfl] at hx30'
  have hnil : (locsOf source.sig).zip args = [] := by
    rw [show locsOf source.sig = [] from rfl]; rfl
  obtain ⟨N, -, -, h, -, -, hw2, -, -, -, -, -, -, -⟩ := backend_twoRunLERWZIUPF_either
    (D := fun _ => False) (XI := ExtSemI.const xQuiet) hsub (.cleanup hc) source_callsOne.1
    source_callsOne.2 (fun _ n _ => source_xcalls _ _ _ n)
    (fun _ _ _ => XNI.xnif (source_xni _ _ _ _ _)) (fun _ => xQuiet_tls F)
    (fun n b h => by cases h) rfl (fun _ h => h.elim) (fun _ => 0) hce hrel hrel hargs
    (SameWorld.refl _ _) (fun r v h => by simp [hnil] at h) (fun off v h => by simp [hnil] at h)
    htr fuel hrun hlm hpsF' he (he'.toN 0)
    (fun n => (he'.calls n).mono fun _ hu => hu.1)
    (fun ht n => (he'.tries ht n).mono fun _ hu => hu.1)
    rfl (formsCovered_cleanup_complete (lowerScope_of source_lowerScope) hc.lower hc.prepare _) hx30
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, hj, _⟩ hd => (noHook_lineDest hnh hj hd).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨a, b, c, _, _, hj, _⟩ _ _ =>
      (noHook_line hnh hj).2.2 a b c rfl |>.elim)
    hag hx29
  exact ⟨N, h, hw2⟩

end E2E.TwoRunVWitness
