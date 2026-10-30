import FV.E2E.PairDriver

/-!
# The paired run with the reads guarded by the difference set (SEM1 #537, #699, item (1))

The lock-step of two machine runs (determinism clause) needs every world read of the paired
VCode run to avoid the bytes where the two worlds differ. That is a per-step fact of the pair
driver: each step instantiates the rule contracts at the guarded semantics `csemG` with the read
guard `¬ Zof F D cm` (`instCalls_pair`'s `key`), whose reads therefore avoid `Zof F D cm`, which
contains `F` and every byte where the two worlds differ (`MRP`). Here that fact is kept in the
paired semantics:

* `MInst.loadForm` (the forms whose allocated lines read world memory), invariant under renaming
  and retargeting;
* `RdOk Y`: `csem Y` gives a result, or the form is not a load form;
* `PGuard F ctx X i us (w, w')`: some `Y` containing `F` and every byte where `w`, `w'` differ,
  with `RdOk Y` on both worlds;
* `pairSemD sem F ctx X`: `pairSem sem` where `PGuard` holds (+ `_sub`, `_of`, `pGuard_noLoad`);
* `rdOk_of_guardR`, `pGuard_of_csemG`: the guarded rule semantics gives the guard;
* `driverSemG_pairD`; `seqRun_pairP`, `pair_fallP`, `pair_stopP` (`seqRun_pair` for any target
  paired semantics).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- The forms whose allocated lines read world memory: the loads (`ldr`, `ldar`, the scalar
SIMD&FP `ldr`) and the atomic loops. -/
def _root_.Backend.MInst.loadForm : MInst → Bool
  | .load .. | .loadAcquire .. | .fpuLoad .. | .atomicRmwLoop .. | .atomicCasLoop .. => true
  | _ => false

theorem _root_.Backend.MInst.loadForm_mapRegs (g : Reg → Reg) (i : MInst) :
    (i.mapRegs g).loadForm = i.loadForm := by
  cases i <;> rfl

theorem _root_.Backend.MInst.loadForm_setTargets {i i' : MInst} {ls : List Label}
    (h : i.setTargets ls = some i') : i'.loadForm = i.loadForm := by
  unfold MInst.setTargets at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

/-- **The reads of `i` at `w` avoid `Y`**: `csem Y` gives a result (its accesses avoid `Y`), or
`i` is not a load form. -/
def RdOk (Y : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (i : MInst) (us : List CV)
    (w : Arm.ArmState) : Prop :=
  (∃ r, csem Y ctx X i us w = some r) ∨ i.loadForm = false

/-- **The pair guard**: a set `Y` containing `F` and every byte where the two worlds differ, the
reads of `i` avoiding `Y` on both worlds. -/
def PGuard (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (i : MInst) (us : List CV)
    (p : W2) : Prop :=
  ∃ Y, (∀ a, F a → Y a) ∧ (∀ a, p.1.mem a ≠ p.2.mem a → Y a) ∧ RdOk Y ctx X i us p.1 ∧
    RdOk Y ctx X i us p.2

open Classical in
/-- **The paired semantics with the reads guarded by the difference set.** -/
noncomputable def pairSemD (sem : Sem) (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    ISem CV W2 :=
  fun i us p => if PGuard F ctx X i us p then pairSem sem i us p else none

section
variable {sem : Sem} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}

theorem pairSemD_sub {i : MInst} {us : List CV} {p : W2} {r : List CV × W2 × Ctl}
    (h : pairSemD sem F ctx X i us p = some r) :
    PGuard F ctx X i us p ∧ pairSem sem i us p = some r := by
  unfold pairSemD at h
  split at h
  · exact ⟨‹_›, h⟩
  · cases h

theorem pairSemD_of {i : MInst} {us : List CV} {p : W2} (h : PGuard F ctx X i us p) :
    pairSemD sem F ctx X i us p = pairSem sem i us p := by
  simp [pairSemD, h]

/-- A form other than the loads is guarded (`Y` = everything). -/
theorem pGuard_noLoad {i : MInst} (h : i.loadForm = false) (us : List CV) (p : W2) :
    PGuard F ctx X i us p :=
  ⟨fun _ => True, fun _ _ => trivial, fun _ _ => trivial, .inr h, .inr h⟩

end

/-- `loopSem` at two frame sets the access avoids is the same. -/
theorem loopSem_congrF {F Y : BitVec 64 → Prop} {ty : CTy} {a : CV} {body : List Line}
    {regs : List Reg} {uses : List CV} {defs : List Reg} {w : Arm.ArmState}
    (hY : Avoids Y ty.bytes (lo64 a)) (hF : Avoids F ty.bytes (lo64 a)) :
    loopSem Y ty a body regs uses defs w = loopSem F ty a body regs uses defs w := by
  unfold loopSem
  simp only [hY, hF, true_and]

/-- **The guarded rule semantics gives `RdOk`**: a step of `csem F` whose reads satisfy
`GuardR F (¬ Y)` reads outside `Y` (`Y ⊇ F`). -/
theorem rdOk_of_guardR {F Y : BitVec 64 → Prop} (hYF : ∀ a, F a → Y a) {ctx : FnCtx}
    {X : ExtSem} {i : MInst} {us : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (hg : GuardR F (fun b => ¬ Y b) ctx.slotBase i us w) (hs : csem F ctx X i us w = some r) :
    RdOk Y ctx X i us w := by
  cases hlf : i.loadForm
  · exact .inr hlf
  left
  have hAv : ∀ {n : Nat} {a : BitVec 64}, Avoids Y n a → Avoids F n a :=
    fun h k hk hf => h k hk (hYF _ hf)
  cases i <;> simp only [MInst.loadForm, reduceCtorEq] at hlf
  case load op rd am fl =>
    rcases rd with ⟨n, _ | _⟩ | _ | _ | _ | _ <;> (try (simp [GuardR] at hg; done))
    obtain ⟨hop, a, ha, -, hrd⟩ := hg
    obtain ⟨w', h, -⟩ := csem_load Y ctx X op hop n am fl us w a ha hrd
    exact ⟨_, h⟩
  case loadAcquire ty rd rr fl =>
    rcases rd with ⟨n, _ | _⟩ | _ | _ | _ | _ <;> rcases rr with ⟨m, _ | _⟩ | _ | _ | _ | _ <;>
      rcases us with _ | ⟨u, _ | ⟨_, _⟩⟩ <;> (try (simp [GuardR] at hg; done))
    obtain ⟨hty, -, hrd⟩ := hg
    obtain ⟨w', h, -⟩ := csem_loadAcquire Y ctx X ty hty n m fl u w hrd
    exact ⟨_, h⟩
  case fpuLoad => simp [GuardR] at hg
  case atomicRmwLoop ty op fl ra ro rd r1 r2 =>
    rcases us with _ | ⟨u, _ | ⟨x, _ | ⟨_, _⟩⟩⟩ <;> (try (simp [csem] at hs; done))
    have hY : Avoids Y ty.bytes (lo64 u) := hg
    refine ⟨r, ?_⟩
    rw [← hs]
    simp only [csem, loopSem_congrF hY (hAv hY), hY, hAv hY]
  case atomicCasLoop ty fl ra re rx rd r1 =>
    rcases us with _ | ⟨u, _ | ⟨e, _ | ⟨x, _ | ⟨_, _⟩⟩⟩⟩ <;> (try (simp [csem] at hs; done))
    have hY : Avoids Y ty.bytes (lo64 u) := hg
    refine ⟨r, ?_⟩
    rw [← hs]
    simp only [csem, loopSem_congrF hY (hAv hY), hY, hAv hY]

/-- **The guarded rule semantics on two worlds gives the pair guard** at `Y := Zof F D cm`. -/
theorem pGuard_of_csemG {F D : BitVec 64 → Prop} {cm : Clif.Mem} {ctx : FnCtx} {X : ExtSem}
    {syms : String → Option Nat} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
    {sp0 : BitVec 64} {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {i : MInst} {us : List CV} {w w' : Arm.ArmState} {r r' : List CV × Arm.ArmState × Ctl}
    (hw : SameWorld (Zof F D cm) w w')
    (h : csemG F ctx X (fun b => ¬ Zof F D cm b) syms exts sigs sp0 Pc i us w = some r)
    (h' : csemG F ctx X (fun b => ¬ Zof F D cm b) syms exts sigs sp0 Pc i us w' = some r') :
    PGuard F ctx X i us (w, w') := by
  have hFZ : ∀ a, F a → Zof F D cm a := fun a h => .inl h
  obtain ⟨hg, -, hs⟩ := csemG_sub h
  obtain ⟨hg', -, hs'⟩ := csemG_sub h'
  exact ⟨Zof F D cm, hFZ, fun a ha => Classical.byContradiction fun hz => ha (hw.2.1 a hz),
    rdOk_of_guardR hFZ hg hs, rdOk_of_guardR hFZ hg' hs'⟩

/-- `RdOk` does not see a renaming or a retargeting (`csem` does not, `MInst.loadForm` does not). -/
theorem pGuard_rename {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} (g : Reg → Reg)
    (gn : Nat → Nat) (hg : VRenaming g gn) (i : MInst) (us : List CV) (p : W2) :
    PGuard F ctx X (i.mapRegs g) us p ↔ PGuard F ctx X i us p := by
  have e : ∀ Y, (csem Y ctx X (i.mapRegs g)) = csem Y ctx X i := fun Y =>
    (driverSem_csem Y ctx X).rename g gn hg i
  simp only [PGuard, RdOk, e, MInst.loadForm_mapRegs]

theorem pGuard_retarget {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i i' : MInst}
    {ls : List Label} (h : i.setTargets ls = some i') (us : List CV) (p : W2) :
    PGuard F ctx X i' us p ↔ PGuard F ctx X i us p := by
  have e : ∀ Y, (csem Y ctx X i') = csem Y ctx X i := fun Y =>
    (driverSem_csem Y ctx X).retarget i ls i' h
  simp only [PGuard, RdOk, e, MInst.loadForm_setTargets h]

/-- **The guarded paired semantics satisfies the driver's world-independent facts.** -/
theorem driverSemG_pairD (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    DriverSemG (pairSemD (csem F ctx X) F ctx X) where
  jump := fun l q => by
    rw [pairSemD_of (pGuard_noLoad rfl _ _)]
    exact (driverSemG_pair F ctx X).jump l q
  rename := by
    intro g gn hg i
    funext us q
    have e := (driverSemG_pair F ctx X).rename g gn hg i
    by_cases hP : PGuard F ctx X i us q
    · rw [pairSemD_of hP, pairSemD_of ((pGuard_rename g gn hg i us q).2 hP), e]
    · simp only [pairSemD, if_neg hP, if_neg (mt (pGuard_rename g gn hg i us q).1 hP)]
  retarget := by
    intro i ls i' h
    funext us q
    have e := (driverSemG_pair F ctx X).retarget i ls i' h
    by_cases hP : PGuard F ctx X i us q
    · rw [pairSemD_of hP, pairSemD_of ((pGuard_retarget h us q).2 hP), e]
    · simp only [pairSemD, if_neg hP, if_neg (mt (pGuard_retarget h us q).1 hP)]

/-! ## Straight-line runs into any paired semantics -/

section
variable {semP : ISem CV W2} {semA : Sem} {R : Arm.ArmState → Arm.ArmState → Prop}

/-- **`seqRun_pair` for any target paired semantics `semP`** that has the paired step of every
instruction of the run whose two runs agree (`hP`). -/
theorem seqRun_pairP :
    ∀ (ms : List MInst),
    (∀ i ∈ ms, ∀ us w w' o w₁ c o' w₁' c', R w w' → semA i us w = some (o, w₁, c) →
      semA i us w' = some (o', w₁', c') → o = o' ∧ c = c' ∧ R w₁ w₁') →
    (∀ i ∈ ms, ∀ us w w' o w₁ c w₁', R w w' → semA i us w = some (o, w₁, c) →
      semA i us w' = some (o, w₁', c) → semP i us (w, w') = some (o, (w₁, w₁'), c)) →
    ∀ (ρ : Nat → CV) (w w' : Arm.ArmState) (e e' : SeqEnd CV Arm.ArmState), R w w' →
      seqRun semA ms ρ w = some e → seqRun semA ms ρ w' = some e' →
      ∃ ep, seqRun semP ms ρ (w, w') = some ep ∧ ep.mapW Prod.fst = e ∧
        ep.mapW Prod.snd = e' ∧ ep.Rel R
  | [], _, _, ρ, w, w', e, e', hR, h, h' => by
    simp only [seqRun, Option.some.injEq] at h h'
    subst h h'
    exact ⟨.fall ρ (w, w'), rfl, rfl, rfl, hR⟩
  | i :: ms, hstep, hP, ρ, w, w', e, e', hR, h, h' => by
    simp only [seqRun] at h h' ⊢
    cases hops : i.operands with
    | error => simp [hops] at h
    | ok ops =>
      simp only [hops] at h h' ⊢
      cases hs : semA i (vuses ops ρ) w with
      | none => simp [hs] at h
      | some r =>
        obtain ⟨o, w₁, c⟩ := r
        cases hs' : semA i (vuses ops ρ) w' with
        | none => simp [hs'] at h'
        | some r' =>
          obtain ⟨o', w₁', c'⟩ := r'
          simp only [hs] at h
          simp only [hs'] at h'
          obtain ⟨rfl, rfl, hR1⟩ := hstep i List.mem_cons_self _ w w' o w₁ c o' w₁' c' hR hs hs'
          rw [hP i List.mem_cons_self _ w w' o w₁ c w₁' hR hs hs']
          simp only
          by_cases hlen : o.length = (ops.toList.filter Operand.isDef).length
          · rw [if_pos hlen] at h h' ⊢
            cases c with
            | next =>
              simp only [Option.map_eq_some_iff] at h h' ⊢
              obtain ⟨e1, h1, rfl⟩ := h
              obtain ⟨e2, h2, rfl⟩ := h'
              obtain ⟨ep, hp, hp1, hp2, hpr⟩ := seqRun_pairP ms
                (fun j hj => hstep j (List.mem_cons_of_mem _ hj))
                (fun j hj => hP j (List.mem_cons_of_mem _ hj)) _ w₁ w₁' e1 e2 hR1 h1 h2
              exact ⟨ep.succ, ⟨ep, hp, rfl⟩, by rw [SeqEnd.mapW_succ, hp1],
                by rw [SeqEnd.mapW_succ, hp2], SeqEnd.rel_succ hpr⟩
            | _ =>
              simp only [Option.some.injEq] at h h' ⊢
              subst h h'
              exact ⟨_, rfl, rfl, rfl, hR, hR1⟩
          · rw [if_neg hlen] at h
            cases h

theorem pair_fallP {ms : List MInst}
    (hstep : ∀ i ∈ ms, ∀ us w w' o w₁ c o' w₁' c', R w w' → semA i us w = some (o, w₁, c) →
      semA i us w' = some (o', w₁', c') → o = o' ∧ c = c' ∧ R w₁ w₁')
    (hP : ∀ i ∈ ms, ∀ us w w' o w₁ c w₁', R w w' → semA i us w = some (o, w₁, c) →
      semA i us w' = some (o, w₁', c) → semP i us (w, w') = some (o, (w₁, w₁'), c))
    {ρ : Nat → CV} {w w' : Arm.ArmState} {ρ₁ : Nat → CV} {w₁ : Arm.ArmState}
    {e' : SeqEnd CV Arm.ArmState} (hR : R w w')
    (h1 : seqRun semA ms ρ w = some (.fall ρ₁ w₁)) (h2 : seqRun semA ms ρ w' = some e') :
    ∃ w₁', e' = .fall ρ₁ w₁' ∧ seqRun semP ms ρ (w, w') = some (.fall ρ₁ (w₁, w₁')) ∧
      R w₁ w₁' := by
  obtain ⟨ep, hp, hp1, hp2, hpr⟩ := seqRun_pairP ms hstep hP ρ w w' _ _ hR h1 h2
  cases ep with
  | fall ρ' q =>
    simp only [SeqEnd.mapW, SeqEnd.fall.injEq] at hp1 hp2
    obtain ⟨rfl, rfl⟩ := hp1
    exact ⟨q.2, hp2.symm, hp, hpr⟩
  | stop => simp [SeqEnd.mapW] at hp1

theorem pair_stopP {ms : List MInst}
    (hstep : ∀ i ∈ ms, ∀ us w w' o w₁ c o' w₁' c', R w w' → semA i us w = some (o, w₁, c) →
      semA i us w' = some (o', w₁', c') → o = o' ∧ c = c' ∧ R w₁ w₁')
    (hP : ∀ i ∈ ms, ∀ us w w' o w₁ c w₁', R w w' → semA i us w = some (o, w₁, c) →
      semA i us w' = some (o, w₁', c) → semP i us (w, w') = some (o, (w₁, w₁'), c))
    {ρ : Nat → CV} {w w' : Arm.ArmState} {k : Nat} {i : MInst} {ops : Array Operand}
    {ρ₁ : Nat → CV} {w₁ : Arm.ArmState} {outs : List CV} {w₂ : Arm.ArmState} {ctl : Ctl}
    {e' : SeqEnd CV Arm.ArmState} (hR : R w w')
    (h1 : seqRun semA ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ ctl))
    (h2 : seqRun semA ms ρ w' = some e') :
    ∃ w₁' w₂', e' = .stop k i ops ρ₁ w₁' outs w₂' ctl ∧
      seqRun semP ms ρ (w, w') = some (.stop k i ops ρ₁ (w₁, w₁') outs (w₂, w₂') ctl) ∧
      R w₁ w₁' ∧ R w₂ w₂' := by
  obtain ⟨ep, hp, hp1, hp2, hpr⟩ := seqRun_pairP ms hstep hP ρ w w' _ _ hR h1 h2
  cases ep with
  | fall => simp [SeqEnd.mapW] at hp1
  | stop k' i' ops' ρ' q outs' q' ctl' =>
    simp only [SeqEnd.mapW, SeqEnd.stop.injEq] at hp1 hp2
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp1
    exact ⟨q.2, q'.2, hp2.symm, hp, hpr⟩

end

/-- **The guarded paired step** from two `csemG` steps at the read guard `¬ Zof F D cm` on worlds
that agree outside `Zof F D cm`, with the same outputs and control. -/
theorem pairSemD_of_csemG {F D : BitVec 64 → Prop} {cm : Clif.Mem} {ctx : FnCtx} {X : ExtSem}
    {syms : String → Option Nat} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
    {sp0 : BitVec 64} {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    (i : MInst) (us : List CV) (w w' : Arm.ArmState) (o : List CV) (w₁ : Arm.ArmState) (c : Ctl)
    (w₁' : Arm.ArmState) (hw : SameWorld (Zof F D cm) w w')
    (h : csemG F ctx X (fun b => ¬ Zof F D cm b) syms exts sigs sp0 Pc i us w = some (o, w₁, c))
    (h' : csemG F ctx X (fun b => ¬ Zof F D cm b) syms exts sigs sp0 Pc i us w' =
      some (o, w₁', c)) :
    pairSemD (csem F ctx X) F ctx X i us (w, w') = some (o, (w₁, w₁'), c) := by
  rw [pairSemD_of (pGuard_of_csemG hw h h')]
  exact pairSem_eq (csemG_sub h).2.2 (csemG_sub h').2.2

end E2E
