import FV.Backend.Lowering.Stock

namespace Backend.Stock.Proof.FenceColors
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192

abbrev Colors := Array Nat × Nat
private abbrev BodyState := Array Nat × Array Nat × Array (List Nat) × Nat
private abbrev FullState := Array Nat × Array Nat × Array Nat × Array (List Nat) × Nat

def bodyNext (start : Nat) (s : Colors) (x : Clif.Stmt × Nat) : Colors :=
  if colored x.1.inst then (s.1.set! (start+x.2) s.2,s.2+1) else s

def blockNext (ranges : Array (Nat × Nat)) (s : Colors) (x : Clif.Block × Nat) : Colors :=
  let after := x.1.body.zipIdx.foldl (bodyNext ranges[x.2]!.1) (s.1,s.2+1)
  (after.1.set! (ranges[x.2]!.2-1) after.2,after.2+1)

private def bodyFull (start bi : Nat) (x : Clif.Stmt × Nat) (s : BodyState) :
    Id (ForInStep BodyState) :=
  if colored x.1.inst then
    pure (.yield (s.1.set! (start+x.2) bi,s.2.1.set! (start+x.2) s.2.2.2,
      s.2.2.1.set! (start+x.2) (instArgs x.1.inst),s.2.2.2+1))
  else
    pure (.yield (s.1.set! (start+x.2) bi,s.2.1,
      s.2.2.1.set! (start+x.2) (instArgs x.1.inst),s.2.2.2))

private def blockFull (ranges : Array (Nat × Nat)) (x : Clif.Block × Nat) (s : FullState) :
    Id (ForInStep FullState) := do
  let after ← forIn x.1.body.zipIdx (s.1,s.2.1,s.2.2.2.1,s.2.2.2.2+1)
    (bodyFull ranges[x.2]!.1 x.2)
  pure (.yield (after.1.set! (ranges[x.2]!.2-1) x.2,
    after.2.1.set! (ranges[x.2]!.2-1) after.2.2.2,
    s.2.2.1.push (after.2.2.2+1),
    after.2.2.1.set! (ranges[x.2]!.2-1) (termArgs x.1.term),after.2.2.2+1))

private theorem forIn_project {α β γ : Type} (field : α → γ)
    (step : β → α → Id (ForInStep α)) (next : α → β → α) (small : γ → β → γ)
    (runs : ∀ x s,step x s = pure (.yield (next s x)))
    (projects : ∀ s x,field (next s x) = small (field s) x)
    (xs : List β) (s : α) :
    field ((forIn xs s step).run) = xs.foldl small (field s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons,runs]
    change field ((forIn xs (next s x) step).run) = _
    rw [ih,projects,List.foldl_cons]

private theorem body_project (start bi : Nat) (xs : List (Clif.Stmt × Nat)) (s : BodyState) :
    (((forIn xs s (bodyFull start bi)).run).2.1,
     ((forIn xs s (bodyFull start bi)).run).2.2.2) =
      xs.foldl (bodyNext start) (s.2.1,s.2.2.2) := by
  let next : BodyState → Clif.Stmt × Nat → BodyState := fun q x =>
    if colored x.1.inst then
      (q.1.set! (start+x.2) bi,q.2.1.set! (start+x.2) q.2.2.2,
        q.2.2.1.set! (start+x.2) (instArgs x.1.inst),q.2.2.2+1)
    else (q.1.set! (start+x.2) bi,q.2.1,
        q.2.2.1.set! (start+x.2) (instArgs x.1.inst),q.2.2.2)
  exact forIn_project (fun q : BodyState => (q.2.1,q.2.2.2)) (bodyFull start bi) next
    (bodyNext start) (by intro x q; unfold bodyFull next; split <;> rfl)
    (by intro q x; unfold next bodyNext; split <;> rfl) xs s

/-- The real metadata loop has this exact color-array projection.
The projection retains every source instruction and every block. -/
theorem sourceMetadata_projection (ctx : Ctx) (ranges : Array (Nat × Nat)) :
    (sourceMetadata ctx ranges).entryColor =
      (ctx.func.blocks.zipIdx.foldl (blockNext ranges) (Array.replicate ctx.insts.size 0,0)).1 := by
  let initial : FullState := (Array.replicate ctx.insts.size 0,
    Array.replicate ctx.insts.size 0,#[],Array.replicate ctx.insts.size [],0)
  let next : FullState → Clif.Block × Nat → FullState := fun s x =>
    let after := (forIn x.1.body.zipIdx (s.1,s.2.1,s.2.2.2.1,s.2.2.2.2+1)
      (bodyFull ranges[x.2]!.1 x.2)).run
    (after.1.set! (ranges[x.2]!.2-1) x.2,
      after.2.1.set! (ranges[x.2]!.2-1) after.2.2.2,
      s.2.2.1.push (after.2.2.2+1),
      after.2.2.1.set! (ranges[x.2]!.2-1) (termArgs x.1.term),after.2.2.2+1)
  have projected := forIn_project (fun q : FullState => (q.2.1,q.2.2.2.2))
    (blockFull ranges) next (blockNext ranges) (by intro x q; rfl) (by
      intro q x
      have body := body_project ranges[x.2]!.1 x.2 x.1.body.zipIdx
        (q.1,q.2.1,q.2.2.2.1,q.2.2.2.2+1)
      change _ = _
      unfold next blockNext
      rw [← body]) ctx.func.blocks.zipIdx initial
  have arrays := congrArg Prod.fst projected
  change ((forIn ctx.func.blocks.zipIdx initial (blockFull ranges)).run).2.1 = _
  exact arrays

end Backend.Stock.Proof.FenceColors
