module

public import FV.Backend.Proof.VCodeSemI

@[expose] public section

/-!
# Straight-line runs of the counted VCode semantics (SEM1 step 2, `docs/plans/uninit.md` §5.3)

The instruction-selection contracts (`LowerInstOk`, `seqRun`) are generic in the world type, and
their proofs discharge them for `csem` (world `Arm.ArmState`). On a sequence without calls
(`MInst.isCallI`) the counted semantics `csemI` (world `Arm.ArmState × Nat`) is `csem` at any
call index with the counter kept, so those proofs carry over:

* `SeqEnd.mapW`, `ISem.ProjWOn`/`ISem.LiftsWOn` (a world map along which a semantics projects,
  resp. lifts, on the instructions satisfying `P`), `seqRun_mapW`, `seqRun_liftW`;
* `csem_projWOn_csemI`/`csem_liftsWOn_csemI`: along `(·, n)`, on the non-calls;
* `seqRun_csemI_noCall`: a call-free straight-line run of `csemI` from counter `n` is the
  `csem` run at any index, the counter `n` throughout;
* `LowerInstOk.csemI`: a lowering correct for `csem` and call-free is correct for `csemI`, with
  the memory relation on the first component and any counter invariant `Q` the CLIF
  instruction keeps.
-/

namespace Backend.Proof

open Backend

section
variable {V W₁ W₂ : Type} (π : W₁ → W₂)

/-- A straight-line run's end with its worlds mapped by `π`. -/
def SeqEnd.mapW : SeqEnd V W₁ → SeqEnd V W₂
  | .fall ρ w => .fall ρ (π w)
  | .stop k i ops ρ w outs w' ctl => .stop k i ops ρ (π w) outs (π w') ctl

/-- `sem₁` projects to `sem₂` along `π` on the instructions satisfying `P`. -/
def ISem.ProjWOn (P : MInst → Prop) (sem₁ : ISem V W₁) (sem₂ : ISem V W₂) : Prop :=
  ∀ i, P i → ∀ uses w outs w' ctl, sem₁ i uses w = some (outs, w', ctl) →
    sem₂ i uses (π w) = some (outs, π w', ctl)

/-- On the instructions satisfying `P`, every result of `sem₂` on a mapped world `π w` is the
map of one of `sem₁` on `w`. -/
def ISem.LiftsWOn (P : MInst → Prop) (sem₁ : ISem V W₁) (sem₂ : ISem V W₂) : Prop :=
  ∀ i, P i → ∀ uses w outs v' ctl, sem₂ i uses (π w) = some (outs, v', ctl) →
    ∃ w', π w' = v' ∧ sem₁ i uses w = some (outs, w', ctl)

variable {π}

theorem SeqEnd.mapW_succ (e : SeqEnd V W₁) : e.succ.mapW π = (e.mapW π).succ := by
  cases e <;> rfl

/-- **A straight-line run of `sem₁` on instructions satisfying `P` maps to one of `sem₂`.** -/
theorem seqRun_mapW {P : MInst → Prop} {sem₁ : ISem V W₁} {sem₂ : ISem V W₂}
    (hp : ISem.ProjWOn π P sem₁ sem₂) :
    ∀ (ms : List MInst), (∀ i ∈ ms, P i) → ∀ (ρ : Nat → V) (w : W₁) (e : SeqEnd V W₁),
      seqRun sem₁ ms ρ w = some e → seqRun sem₂ ms ρ (π w) = some (e.mapW π)
  | [], _, ρ, w, e, h => by
    simp only [seqRun, Option.some.injEq] at h
    subst h; rfl
  | i :: ms, hP, ρ, w, e, h => by
    simp only [seqRun] at h ⊢
    cases ho : i.operands with
    | error _ => rw [ho] at h; cases h
    | ok ops =>
      simp only [ho] at h ⊢
      cases hs : sem₁ i (vuses ops ρ) w with
      | none => rw [hs] at h; cases h
      | some r =>
        obtain ⟨outs, w', ctl⟩ := r
        rw [hs] at h
        rw [hp i (hP i List.mem_cons_self) _ _ _ _ _ hs]
        simp only at h ⊢
        by_cases hl : outs.length = (ops.toList.filter Operand.isDef).length
        · simp only [hl, ↓reduceIte] at h ⊢
          cases ctl with
          | next =>
            simp only at h ⊢
            cases hr : seqRun sem₁ ms (vdefUpd ops outs ρ) w' with
            | none => rw [hr] at h; cases h
            | some e1 =>
              rw [hr] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              rw [seqRun_mapW hp ms (fun j hj => hP j (List.mem_cons_of_mem _ hj)) _ _ _ hr]
              simp only [Option.map_some, SeqEnd.mapW_succ]
          | goto j =>
            simp only [Option.some.injEq] at h ⊢
            subst h; rfl
          | ret =>
            simp only [Option.some.injEq] at h ⊢
            subst h; rfl
          | halt =>
            simp only [Option.some.injEq] at h ⊢
            subst h; rfl
        · simp only [hl, ↓reduceIte] at h; cases h

/-- **A straight-line run of `sem₂` from a mapped world, on instructions satisfying `P`, is the
map of one of `sem₁`.** -/
theorem seqRun_liftW {P : MInst → Prop} {sem₁ : ISem V W₁} {sem₂ : ISem V W₂}
    (hl : ISem.LiftsWOn π P sem₁ sem₂) :
    ∀ (ms : List MInst), (∀ i ∈ ms, P i) → ∀ (ρ : Nat → V) (w : W₁) (d : SeqEnd V W₂),
      seqRun sem₂ ms ρ (π w) = some d → ∃ e, e.mapW π = d ∧ seqRun sem₁ ms ρ w = some e
  | [], _, ρ, w, d, h => by
    simp only [seqRun, Option.some.injEq] at h
    exact ⟨.fall ρ w, h, rfl⟩
  | i :: ms, hP, ρ, w, d, h => by
    simp only [seqRun] at h ⊢
    cases ho : i.operands with
    | error _ => rw [ho] at h; cases h
    | ok ops =>
      simp only [ho] at h ⊢
      cases hs : sem₂ i (vuses ops ρ) (π w) with
      | none => rw [hs] at h; cases h
      | some r =>
        obtain ⟨outs, v', ctl⟩ := r
        rw [hs] at h
        obtain ⟨w', rfl, hs'⟩ := hl i (hP i List.mem_cons_self) _ _ _ _ _ hs
        rw [hs']
        simp only at h ⊢
        by_cases hlen : outs.length = (ops.toList.filter Operand.isDef).length
        · simp only [hlen, ↓reduceIte] at h ⊢
          cases ctl with
          | next =>
            simp only at h ⊢
            cases hr : seqRun sem₂ ms (vdefUpd ops outs ρ) (π w') with
            | none => rw [hr] at h; cases h
            | some d1 =>
              rw [hr] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              obtain ⟨e1, rfl, he1⟩ :=
                seqRun_liftW hl ms (fun j hj => hP j (List.mem_cons_of_mem _ hj)) _ _ _ hr
              exact ⟨e1.succ, SeqEnd.mapW_succ e1, by rw [he1]; rfl⟩
          | goto j =>
            simp only [Option.some.injEq] at h ⊢
            exact ⟨.stop 0 i ops ρ w outs w' (.goto j), h, rfl⟩
          | ret =>
            simp only [Option.some.injEq] at h ⊢
            exact ⟨.stop 0 i ops ρ w outs w' .ret, h, rfl⟩
          | halt =>
            simp only [Option.some.injEq] at h ⊢
            exact ⟨.stop 0 i ops ρ w outs w' .halt, h, rfl⟩
        · simp only [hlen, ↓reduceIte] at h; cases h

end

/-! ## `csemI` on call-free sequences -/

/-- On the non-calls `csem` at any index projects to `csemI` along `(·, n)`. -/
theorem csem_projWOn_csemI (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) (m n : Nat) :
    ISem.ProjWOn (fun w => (w, n)) (fun i => i.isCallI = false) (csem F ctx (X.at m))
      (csemI F ctx X) := by
  intro i hi uses w outs w' ctl h
  rw [csemI_noncall F ctx X hi uses w n m, h]
  rfl

/-- On the non-calls every `csemI` result from counter `n` is a `csem` one, the counter kept. -/
theorem csem_liftsWOn_csemI (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) (m n : Nat) :
    ISem.LiftsWOn (fun w => (w, n)) (fun i => i.isCallI = false) (csem F ctx (X.at m))
      (csemI F ctx X) := by
  intro i hi uses w outs v' ctl h
  rw [csemI_noncall F ctx X hi uses w n m] at h
  cases hc : csem F ctx (X.at m) i uses w with
  | none => rw [hc] at h; cases h
  | some r =>
    rw [hc] at h
    obtain ⟨o, u, c⟩ := r
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨u, rfl, rfl⟩

/-- **A call-free straight-line run of `csemI`** from counter `n` is the `csem` run at any call
index `m`, with the counter `n` throughout. -/
theorem seqRun_csemI_noCall (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) (m : Nat)
    {ms : List MInst} (hnc : ∀ i ∈ ms, i.isCallI = false) (ρ : Nat → CV) (w : Arm.ArmState)
    (n : Nat) :
    seqRun (csemI F ctx X) ms ρ (w, n) =
      (seqRun (csem F ctx (X.at m)) ms ρ w).map (SeqEnd.mapW fun w => (w, n)) := by
  cases h : seqRun (csem F ctx (X.at m)) ms ρ w with
  | some e => exact seqRun_mapW (csem_projWOn_csemI F ctx X m n) ms hnc ρ w e h
  | none =>
    cases h' : seqRun (csemI F ctx X) ms ρ (w, n) with
    | none => rfl
    | some d =>
      obtain ⟨e, -, he⟩ := seqRun_liftW (csem_liftsWOn_csemI F ctx X m n) ms hnc ρ w d h'
      rw [h] at he; cases he

/-- **A call-free lowering correct for `csem` is correct for `csemI`**, with the memory relation
`MR` on the Arm world and a counter invariant `Q` that the CLIF instruction keeps. -/
theorem LowerInstOk.csemI {F : BitVec 64 → Prop} {fctx : FnCtx} {X : ExtSemI} {m : Nat}
    {MR : MemRelT} {Q : Clif.Mem → Nat → Prop} {env : Clif.Env} {p : Clif.Program} {ctx : Ctx}
    {inst : Clif.Inst} {results : List Nat} {st : LState} {rss : List (List Reg)} {st' : LState}
    {ms : List MInst} (h : LowerInstOk (csem F fctx (X.at m)) MR env p ctx inst results st rss st' ms)
    (hnc : ∀ i ∈ ms, i.isCallI = false)
    (hQ : ∀ fr cm vals cm' n, instOutcome env p fr cm inst = .ok (vals, cm') → Q cm n → Q cm' n) :
    LowerInstOk (csemI F fctx X) (fun sl cm w => MR sl cm w.1 ∧ Q cm w.2) env p ctx inst results
      st rss st' ms := by
  refine ⟨h.mono, h.defs, fun fr cm ρ ⟨w, n⟩ hf hv hd ⟨hmr, hq⟩ => ?_⟩
  have hr := h.run fr cm ρ w hf hv hd hmr
  have hseq := seqRun_csemI_noCall F fctx X m hnc ρ w n
  cases ho : instOutcome env p fr cm inst with
  | ok r =>
    obtain ⟨vals, cm'⟩ := r
    simp only [ho] at hr ⊢
    obtain ⟨hu, ρ', w', hs, hres, hmr'⟩ := hr
    refine ⟨hu, ρ', (w', n), ?_, hres, hmr', hQ fr cm vals cm' n ho hq⟩
    rw [hseq, hs]; rfl
  | trap c =>
    simp only [ho] at hr ⊢
    intro he
    obtain ⟨hu, k, i, ops, ρ₁, w₁, outs, w₂, hs, htc⟩ := hr he
    refine ⟨hu, k, i, ops, ρ₁, (w₁, n), outs, (w₂, n), ?_, htc⟩
    rw [hseq, hs]; rfl
  | stuck _ => simp only [ho]

end Backend.Proof
