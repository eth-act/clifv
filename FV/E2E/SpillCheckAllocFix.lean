import FV.E2E.SpillCheckAllocMono

/-!
# Completeness of `checkAlloc` (2): the fixpoint iteration converges and is accepted

`checkAlloc_complete`: if verified in-states `W` exist (`CheckCtx.verifyBlock` passes on every
block) whose entry state is below `entryState`, every block is reachable from the entry, and every
operand vreg and block parameter is below `vc.classes.size`, then `checkAlloc` accepts.

The iteration's in-states stay above `W` (`Inv.wit`, by `runBlock_mono`/`edge_mono`), so every
block run and edge it performs passes the checker; each round that changes a state lowers the
potential `Phi` (an unreached block counts `M + 1`, a reached one its number of symbols, at most
`M`: `wt_le`), so a round without change comes within `checkAlloc`'s fuel; a round without change
leaves stable in-states (`Stab`), which `verify` accepts and which reach every reachable block.
-/

namespace E2E.CheckComplete

open Backend Backend.Proof Backend.Proof.Spill

/-! ## `forIn` progress -/

theorem forIn_progress {ε α β : Type} (f : α → β → Except ε (ForInStep β)) :
    ∀ (l : List α) (P : Nat → β → Prop) (b : β), P 0 b →
    (∀ k x b, l[k]? = some x → P k b → ∃ b', f x b = .ok (.yield b') ∧ P (k + 1) b') →
    ∃ r, forIn l b f = .ok r ∧ P l.length r
  | [], _, b, h0, _ => ⟨b, rfl, h0⟩
  | x :: l, P, b, h0, hs => by
    obtain ⟨b1, hb1, hP1⟩ := hs 0 x b rfl h0
    obtain ⟨r, hr, hPr⟩ := forIn_progress f l (fun k => P (k + 1)) b1 hP1
      (fun k y c hy hc => hs (k + 1) y c (by simpa using hy) hc)
    refine ⟨r, ?_, by simpa using hPr⟩
    rw [List.forIn_cons]
    simp only [hb1, bind, Except.bind]
    exact hr

theorem forIn_bind_progress {ε α β γ : Type} (f : α → β → Except ε (ForInStep β)) (l : List α)
    (b : β) (g : β → Except ε γ) (P : Nat → β → Prop) (h0 : P 0 b)
    (hs : ∀ k x b, l[k]? = some x → P k b → ∃ b', f x b = .ok (.yield b') ∧ P (k + 1) b')
    (Q : γ → Prop) (hg : ∀ r, P l.length r → ∃ y, g r = .ok y ∧ Q y) :
    ∃ y, (forIn l b f >>= g) = .ok y ∧ Q y := by
  obtain ⟨r, hr, hP⟩ := forIn_progress f l P b h0 hs
  obtain ⟨y, hy, hQ⟩ := hg r hP
  exact ⟨y, by rw [hr]; exact hy, hQ⟩

theorem forIn_bind_yield {ε α β β' : Type} (f : α → β → Except ε (ForInStep β)) (l : List α)
    (b : β) (g : β → Except ε (ForInStep β')) (P : Nat → β → Prop) (h0 : P 0 b)
    (hs : ∀ k x b, l[k]? = some x → P k b → ∃ b', f x b = .ok (.yield b') ∧ P (k + 1) b')
    (Q : β' → Prop) (hg : ∀ r, P l.length r → ∃ y, g r = .ok (.yield y) ∧ Q y) :
    ∃ y, (forIn l b f >>= g) = .ok (.yield y) ∧ Q y := by
  obtain ⟨r, hr, hP⟩ := forIn_progress f l P b h0 hs
  obtain ⟨y, hy, hQ⟩ := hg r hP
  exact ⟨y, by rw [hr]; exact hy, hQ⟩

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-! ## Arrays of in-states -/

theorem get!_eq (a : Array (Option AState)) (i : Nat) : a[i]! = a[i]?.getD none := by
  rw [getElem!_def]; cases a[i]? <;> rfl

theorem succs!_eq (a : Array (Array Nat)) (i : Nat) : a[i]! = a[i]?.getD #[] := by
  rw [getElem!_def]; cases a[i]? <;> rfl

theorem get!_some {a : Array (Option AState)} {i : Nat} {x : AState} (h : a[i]! = some x) :
    a[i]? = some (some x) := by
  rw [get!_eq] at h
  cases e : a[i]? with
  | none => rw [e] at h; cases h
  | some y => rw [e] at h; exact congrArg some h

theorem get!_of_some {a : Array (Option AState)} {i : Nat} {x : Option AState} (h : a[i]? = some x) :
    a[i]! = x := by
  rw [get!_eq, h]; rfl

theorem get!_set_self {a : Array (Option AState)} {s : Nat} (h : s < a.size) (v : Option AState) :
    (a.set! s v)[s]! = v := by
  rw [get!_eq]; simp [h]

theorem get!_set_ne {a : Array (Option AState)} {s b : Nat} (h : b ≠ s) (v : Option AState) :
    (a.set! s v)[b]! = a[b]! := by
  rw [get!_eq, get!_eq, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm h)]

/-! ## The potential -/

/-- The weight of an in-state: `M + 1` unreached, its number of symbols reached. -/
def phi (M : Nat) : Option AState → Nat
  | none => M + 1
  | some a => wt a

/-- The potential of the iteration's in-states. -/
def Phi (M : Nat) (ins : Array (Option AState)) : Nat := (ins.toList.map (phi M)).sum

theorem sum_set {α : Type} (f : α → Nat) (v : α) : ∀ (L : List α) (i : Nat) (h : i < L.length),
    ((L.set i v).map f).sum + f L[i] = (L.map f).sum + f v
  | [], _, h => by simp at h
  | x :: L, 0, _ => by simp; omega
  | x :: L, i + 1, h => by
    have := sum_set f v L i (by simpa using h)
    simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
    omega

theorem Phi_set (M : Nat) {ins : Array (Option AState)} {s : Nat} (h : s < ins.size)
    (v : Option AState) : Phi M (ins.set! s v) + phi M ins[s]! = Phi M ins + phi M v := by
  unfold Phi
  rw [Array.toList_set!]
  have := sum_set (phi M) v ins.toList s (by simpa using h)
  rw [show ins[s]! = ins.toList[s]'(by simpa using h) by
    rw [get!_eq, Array.getElem?_eq_getElem h]; simp]
  exact this

/-! ## The setting and the invariant -/

/-- What the completeness proof needs of a checker context `c`: a non-empty CFG, the universe
bound `K` of the vregs, the state size `N`, and verified in-states `W` with an entry state below
`entryState N`. -/
structure Setting (c : CheckCtx) (K N : Nat) (W : Array (Option AState)) : Prop where
  size_eq : c.size = N
  nonempty : c.vc.blocks.size ≠ 0
  succ_lt : ∀ b s : Nat, s ∈ (c.succs[b]!).toList → b < c.vc.blocks.size ∧ s < c.vc.blocks.size
  ops : ∀ (b : Nat) vb, c.vc.blocks[b]? = some vb → OpsBelow K vb
  params : ∀ (s : Nat) sb, c.vc.blocks[s]? = some sb → ParamsBelow K sb
  wit : ∀ b < c.vc.blocks.size, ∃ w, W[b]? = some (some w) ∧ w.size = N
  ver : ∀ b < c.vc.blocks.size, c.verifyBlock W b = .ok ()
  entry : ∃ w0, W[0]? = some (some w0) ∧ w0.le (entryState N) = true

section
variable (c : CheckCtx) (K N : Nat) (W : Array (Option AState))

/-- The invariant of the iteration's in-states. -/
structure Inv (ins : Array (Option AState)) : Prop where
  size : ins.size = c.vc.blocks.size
  good : ∀ (b : Nat) a, ins[b]! = some a → Good K N a
  wit : ∀ (b : Nat) a w, ins[b]! = some a → W[b]? = some (some w) → Sub w a
  entry : ∃ a0, ins[0]! = some a0 ∧ Sub a0 (entryState N)

/-- Block `b` is stable in `ins`: its run and edges pass, and meeting its edges into its
successors' in-states changes nothing. -/
def Stab (ins : Array (Option AState)) (b : Nat) : Prop :=
  ∀ a, ins[b]! = some a → ∃ out, c.runBlock b a = .ok out ∧
    ∀ s ∈ (c.succs[b]!).toList, ∃ e old, c.edge b s out = .ok e ∧ ins[s]! = some old ∧
      old.meet e = old

end

variable {c : CheckCtx} {K N : Nat} {W : Array (Option AState)}

/-- The witness facts of block `b`. -/
theorem wit_block (hS : Setting c K N W) {b : Nat} (hb : b < c.vc.blocks.size) :
    ∃ w out, W[b]? = some (some w) ∧ c.runBlock b w = .ok out ∧
      ∀ s ∈ (c.succs[b]!).toList, ∃ e w', c.edge b s out = .ok e ∧ W[s]? = some (some w') ∧
        w'.le e = true := by
  obtain ⟨w, out, hw, hr, he⟩ := verifyBlock_ok (hS.ver b hb)
  refine ⟨w, out, hw, hr, fun s hs => he s ?_⟩
  rw [succs!_eq] at hs
  exact hs

/-! ## Runs and edges keep the size of a state -/

theorem runItems_size (vb : VBlock) : ∀ (its : List RItem) (next : Nat) (y y' : AState),
    c.runItems vb next its y = .ok y' → y'.size = y.size
  | [], _, _, _, h => by
    obtain ⟨-, rfl⟩ := runItems_nil h
    rfl
  | .move src dst :: its, next, y, y', h => by
    obtain ⟨-, hr⟩ := runItems_move h
    rw [runItems_size vb its next _ y' hr, size_put]
  | .op k allocs :: its, _, y, y', h => by
    obtain ⟨-, rfl, i, ops, y1, -, -, hst, hr⟩ := runItems_op h
    obtain ⟨-, -, -, rfl, -⟩ := stepOp_ok hst
    rw [runItems_size vb its (k + 1) _ y' hr, size_transferOp]

theorem runBlock_size {b : Nat} {y y' : AState} (h : c.runBlock b y = .ok y') :
    y'.size = y.size := by
  obtain ⟨vb, items, -, -, hr⟩ := runBlock_ok h
  exact runItems_size vb items.toList 0 y y' hr

theorem edge_size {b s : Nat} {y y' : AState} (h : c.edge b s y = .ok y') : y'.size = y.size := by
  obtain ⟨os, hos⟩ := edgeForget_eq c b s
  have hz : (c.edgeForget b s y).size = y.size := by rw [hos]; simp [forgetOps]
  unfold CheckCtx.edge CheckCtx.edgeCopy at h
  rw [← hz]
  generalize c.edgeForget b s y = z at h
  split at h
  · obtain ⟨-, h⟩ := Except.seq_ok h
    split at h
    · rw [← Except.ok.inj h]
    · obtain ⟨ps, -, h⟩ := Except.bind_ok h
      obtain ⟨xs, -, h⟩ := Except.bind_ok h
      obtain ⟨-, h⟩ := Except.seq_ok h
      rw [← Except.ok.inj h]
      simp [AState.parCopy]
  · cases h
  · cases h

/-! ## One edge (the inner loop's body) -/

/-- The inner loop's invariant for block `b` with out-state `out`, from the round's input `ins₀`
and the round's flag `ch₀` on entry to the inner loop. -/
def InnerInv (c : CheckCtx) (K N : Nat) (W : Array (Option AState)) (ins₀ : Array (Option AState))
    (b : Nat) (out : AState) (ch₀ : Bool) (j : Nat) (st : Array (Option AState) × Bool) : Prop :=
  Inv c K N W st.1 ∧ Phi (N * (K + calleeSaved.length)) st.1 + (if st.2 then 1 else 0) ≤
      Phi (N * (K + calleeSaved.length)) ins₀ ∧
    (ch₀ = true → st.2 = true) ∧
    (st.2 = false → st.1 = ins₀ ∧ ∀ j' < j, ∀ s, (c.succs[b]!).toList[j']? = some s →
      ∃ e old, c.edge b s out = .ok e ∧ ins₀[s]! = some old ∧ old.meet e = old)

theorem inner_step (hS : Setting c K N W) {ins₀ : Array (Option AState)} {b : Nat}
    (hb : b < c.vc.blocks.size) {wout out : AState} (hwr : ∃ w, W[b]? = some (some w) ∧
      c.runBlock b w = .ok wout) (hout : Sub wout out) (hgo : Good K N out) {ch₀ : Bool}
    (j s : Nat) (st : Array (Option AState) × Bool) (hj : (c.succs[b]!).toList[j]? = some s)
    (hI : InnerInv c K N W ins₀ b out ch₀ j st) :
    ∃ st', (do
      let e ← c.edge b s out
      if (st.1[s]! != some (match st.1[s]! with
          | none => e
          | some old => old.meet e)) = true then
        pure (ForInStep.yield (st.1.set! s (some (match st.1[s]! with
          | none => e
          | some old => old.meet e)), true))
      else pure (ForInStep.yield (st.1, st.2)) : Except String (ForInStep _)) = .ok (.yield st') ∧
      InnerInv c K N W ins₀ b out ch₀ (j + 1) st' := by
  obtain ⟨hInv, hPhi, hch, hst⟩ := hI
  have hsL : s ∈ (c.succs[b]!).toList := List.mem_of_getElem? hj
  have hsn : s < c.vc.blocks.size := (hS.succ_lt b s hsL).2
  -- the witness edge
  obtain ⟨w, wout', hw, hwr', hwe⟩ := wit_block hS hb
  obtain ⟨w1, hw1, hwr1⟩ := hwr
  rw [hw] at hw1
  cases hw1
  rw [hwr'] at hwr1
  cases hwr1
  obtain ⟨ew, ws, hew, hws, hwle⟩ := hwe s hsL
  obtain ⟨e, he, hse⟩ := edge_mono c hew hout
  have hge : Good K N e := edge_good c he (hS.params s) hgo
  have hwse : Sub ws e := by
    obtain ⟨w', hw', hsz⟩ := hS.wit s hsn
    rw [hws] at hw'
    cases hw'
    obtain ⟨w'', hw'', hsz'⟩ := hS.wit b hb
    rw [hw] at hw''
    cases hw''
    refine sub_trans (sub_of_le ?_ hwle) hse
    rw [edge_size hew, runBlock_size hwr', hsz, hsz']
    exact Nat.le_refl _
  simp only [he, bind, Except.bind]
  -- the new in-state of `s`
  generalize hnew : (match st.1[s]! with
    | none => e
    | some old => old.meet e) = new
  have hgn : Good K N new := by
    rw [← hnew]; split
    · exact hge
    · rename_i old hold; exact good_meet (hInv.good s old hold) e
  have hwn : Sub ws new := by
    rw [← hnew]; split
    · exact hwse
    · rename_i old hold; exact sub_meet (hInv.wit s old ws hold hws) hwse
  by_cases hc : (st.1[s]! != some new) = true
  · simp only [hc, ↓reduceIte, pure, Except.pure]
    refine ⟨_, rfl, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, fun _ => rfl, fun h => by cases h⟩⟩
    · rw [Array.size_set!]; exact hInv.size
    · intro b' a h'
      by_cases e' : b' = s
      · subst e'; rw [get!_set_self (by rw [hInv.size]; exact hsn)] at h'; cases h'; exact hgn
      · rw [get!_set_ne e'] at h'; exact hInv.good b' a h'
    · intro b' a w' h' hw'
      by_cases e' : b' = s
      · subst e'
        rw [get!_set_self (by rw [hInv.size]; exact hsn)] at h'
        cases h'
        rw [hws] at hw'; cases hw'; exact hwn
      · rw [get!_set_ne e'] at h'; exact hInv.wit b' a w' h' hw'
    · obtain ⟨a0, h0, hs0⟩ := hInv.entry
      by_cases e' : s = 0
      · subst e'
        refine ⟨new, get!_set_self (by rw [hInv.size]; exact hsn) _, ?_⟩
        rw [← hnew, h0]
        exact sub_trans (sub_meet_left a0 e) hs0
      · exact ⟨a0, by rw [get!_set_ne (Ne.symm e')]; exact h0, hs0⟩
    · -- the potential drops
      have hset := Phi_set (N * (K + calleeSaved.length)) (ins := st.1)
        (by rw [hInv.size]; exact hsn) (some new)
      have hlt : phi (N * (K + calleeSaved.length)) (some new) <
          phi (N * (K + calleeSaved.length)) st.1[s]! := by
        have hwn' := wt_le hgn
        rw [← hnew] at hc ⊢
        revert hc
        cases hold : st.1[s]! with
        | none => intro _; have := wt_le hge; simp only [phi]; omega
        | some old =>
          intro hc
          simp only [phi]
          refine (wt_meet old e).2 fun eq => ?_
          simp [eq] at hc
      simp only [↓reduceIte]
      have : Phi (N * (K + calleeSaved.length)) st.1 + (if st.2 then 1 else 0) ≤
          Phi (N * (K + calleeSaved.length)) ins₀ := hPhi
      split at this <;> omega
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
    refine ⟨_, rfl, hInv, hPhi, hch, fun h2 => ⟨(hst h2).1, fun j' hj' s' hs' => ?_⟩⟩
    obtain ⟨heq, hprev⟩ := hst h2
    by_cases e' : j' = j
    · subst e'
      rw [hj] at hs'
      cases hs'
      have hsome : st.1[s]! = some new := by simpa using hc
      revert hnew
      rw [hsome]
      intro hnew
      have : st.1[s]! = ins₀[s]! := by rw [heq]
      refine ⟨e, new, he, by rw [← this, hsome], ?_⟩
      exact hnew
    · exact hprev j' (by omega) s' hs'

/-! ## One round -/

/-- The outer loop's invariant before block `k`. -/
def OuterInv (c : CheckCtx) (K N : Nat) (W : Array (Option AState)) (ins₀ : Array (Option AState))
    (k : Nat) (st : Array (Option AState) × Bool) : Prop :=
  Inv c K N W st.1 ∧ Phi (N * (K + calleeSaved.length)) st.1 + (if st.2 then 1 else 0) ≤
      Phi (N * (K + calleeSaved.length)) ins₀ ∧
    (st.2 = false → st.1 = ins₀ ∧ ∀ b < k, Stab c ins₀ b)

/-- **One round** passes, keeps the invariant, and either lowers the potential or changes nothing
and leaves every block stable. -/
theorem round_ok (hS : Setting c K N W) {ins₀ : Array (Option AState)} (hI : Inv c K N W ins₀) :
    ∃ r : Array (Option AState) × Bool, c.round ins₀ = .ok r ∧ Inv c K N W r.1 ∧
      (r.2 = true → Phi (N * (K + calleeSaved.length)) r.1 + 1 ≤
        Phi (N * (K + calleeSaved.length)) ins₀) ∧
      (r.2 = false → r.1 = ins₀ ∧ ∀ b < c.vc.blocks.size, Stab c ins₀ b) := by
  unfold CheckCtx.round
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  refine forIn_bind_progress _ _ _ _ (OuterInv c K N W ins₀) ⟨hI, by simp, fun _ => ⟨rfl,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩ ?_ _ ?_
  · intro k x st hx hP
    have hk : k < c.vc.blocks.size := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      simpa [Std.Legacy.Range.size] using this
    have hxk : x = k := by
      have := (List.getElem?_eq_some_iff.mp hx).2
      simp at this
      omega
    subst hxk
    obtain ⟨hInv, hPhi, hst⟩ := hP
    rcases hka : st.fst[x]! with _ | a
    · simp only
      refine ⟨_, rfl, hInv, hPhi, fun h2 => ⟨(hst h2).1, fun b hb a' ha' => ?_⟩⟩
      by_cases e : b = x
      · subst e; rw [← (hst h2).1, hka] at ha'; cases ha'
      · exact (hst h2).2 b (by omega) a' ha'
    · simp only
      obtain ⟨w, wout, hw, hwr, -⟩ := wit_block hS hk
      obtain ⟨out, hrun, hout⟩ := runBlock_mono c hwr (hInv.wit x a w hka hw)
      have hgo : Good K N out := runBlock_good c hrun (hS.ops x) (hInv.good x a hka)
      rw [hrun, ok_bind]
      refine forIn_bind_yield _ _ _ _ (InnerInv c K N W ins₀ x out st.2)
        ⟨hInv, hPhi, fun h => h, fun h2 => ⟨(hst h2).1, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
        (fun j s st' hj hI' => inner_step hS hk ⟨w, hw, hwr⟩ hout hgo j s st' hj hI') _ ?_
      intro r hr
      obtain ⟨hInv', hPhi', hch', hst'⟩ := hr
      refine ⟨_, rfl, hInv', hPhi', fun h2 => ?_⟩
      have h1 : st.2 = false := by
        cases e : st.2
        · rfl
        · have h2' : r.2 = false := h2
          rw [hch' e] at h2'
          cases h2'
      obtain ⟨heq, hprev⟩ := hst h1
      obtain ⟨heq', hedges⟩ := hst' h2
      refine ⟨heq', fun b hb a' ha' => ?_⟩
      by_cases e : b = x
      · subst e
        rw [← heq, hka] at ha'
        cases ha'
        refine ⟨out, hrun, fun s hs => ?_⟩
        obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.mp hs
        exact hedges j' (List.getElem?_eq_some_iff.mp hj').1 s hj'
      · exact hprev b (by omega) a' ha'
  · intro r hr
    obtain ⟨hInv', hPhi', hst'⟩ := hr
    refine ⟨(r.1, r.2), rfl, hInv', fun h => ?_, fun h => ?_⟩
    · have h' : r.2 = true := h
      rw [h'] at hPhi'
      exact hPhi'
    · obtain ⟨e, hs⟩ := hst' h
      exact ⟨e, fun b hb => hs b (by simpa [Std.Legacy.Range.size] using hb)⟩

/-! ## The fixpoint -/

theorem fixpoint_ok (hS : Setting c K N W) : ∀ (fuel : Nat) (ins : Array (Option AState)),
    Inv c K N W ins → Phi (N * (K + calleeSaved.length)) ins < fuel →
    ∃ ins', c.fixpoint fuel ins = .ok ins' ∧ Inv c K N W ins' ∧
      ∀ b < c.vc.blocks.size, Stab c ins' b
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, ins, hI, hlt => by
    obtain ⟨⟨ins1, ch⟩, hr, hI1, hdec, hfix⟩ := round_ok hS hI
    unfold CheckCtx.fixpoint
    rw [hr, ok_bind]
    cases ch with
    | true =>
      obtain ⟨ins', h', hI', hst'⟩ := fixpoint_ok hS fuel ins1 hI1
        (by have : Phi _ ins1 + 1 ≤ Phi _ ins := hdec rfl; omega)
      exact ⟨ins', h', hI', hst'⟩
    | false =>
      obtain ⟨e, hst⟩ := hfix rfl
      simp only at e
      subst e
      exact ⟨ins1, rfl, hI1, hst⟩

/-! ## Stable in-states are accepted -/

theorem reached (hS : Setting c K N W) {ins : Array (Option AState)} (hI : Inv c K N W ins)
    (hst : ∀ b < c.vc.blocks.size, Stab c ins b) {b : Nat} (hr : Prep.Reach c.succs b) :
    ∃ a, ins[b]! = some a := by
  induction hr with
  | entry => obtain ⟨a0, h0, -⟩ := hI.entry; exact ⟨a0, h0⟩
  | @step b s _ hs ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨out, -, he⟩ := hst b (hS.succ_lt b s hs).1 a ha
    obtain ⟨e, old, -, hold, -⟩ := he s hs
    exact ⟨old, hold⟩

theorem verify_stable (hS : Setting c K N W) {ins : Array (Option AState)} (hI : Inv c K N W ins)
    (hst : ∀ b < c.vc.blocks.size, Stab c ins b)
    (hreach : ∀ b < c.vc.blocks.size, Prep.Reach c.succs b) :
    c.verify ins = .ok () ∧ ∀ b < c.vc.blocks.size, ∃ a, ins[b]? = some (some a) := by
  have hall : ∀ b < c.vc.blocks.size, ∃ a, ins[b]! = some a :=
    fun b hb => reached hS hI hst (hreach b hb)
  refine ⟨?_, fun b hb => let ⟨a, ha⟩ := hall b hb; ⟨a, get!_some ha⟩⟩
  obtain ⟨a0, h0, hs0⟩ := hI.entry
  unfold CheckCtx.verify
  rw [get!_some h0]
  simp only [hS.size_eq, ensure_true (le_of_mem hs0.2), bind, Except.bind]
  refine Spill.forM_ok fun b hb => ?_
  have hb' : b < c.vc.blocks.size := List.mem_range.mp hb
  obtain ⟨a, ha⟩ := hall b hb'
  obtain ⟨out, hrun, he⟩ := hst b hb' a ha
  refine verifyBlock_of (get!_some ha) hrun fun s hs => ?_
  rw [← succs!_eq] at hs
  obtain ⟨e, old, hedge, hold, hmeet⟩ := he s hs
  exact ⟨e, old, hedge, get!_some hold, le_of_meet_eq hmeet⟩

/-! ## The initial in-states -/

theorem good_replicate (K N : Nat) : Good K N (Array.replicate N []) := by
  refine ⟨by simp, fun l => ?_⟩
  have : AState.get (Array.replicate N ([] : List Sym)) l = [] := by
    unfold AState.get
    split
    · simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    · rfl
  rw [this]
  exact ⟨List.nodup_nil, by simp⟩

theorem good_entryState (K N : Nat) : Good K N (entryState N) := by
  unfold entryState
  suffices ∀ (rs : List Reg) (a : AState), (∀ r ∈ rs, r ∈ calleeSaved) → Good K N a →
      Good K N (rs.foldl (fun a r => a.put (.reg r) [.entry r]) a) from
    this calleeSaved _ (fun _ h => h) (good_replicate K N)
  intro rs
  induction rs with
  | nil => intro a _ h; exact h
  | cons r rs ih =>
    intro a hr h
    simp only [List.foldl_cons]
    refine ih _ (fun r' h' => hr r' (List.mem_cons_of_mem _ h')) (good_put h _ ?_)
    exact ⟨List.pairwise_singleton _ _, fun s hs => by
      rw [List.mem_singleton.mp hs]; exact hr r List.mem_cons_self⟩

theorem inv_init (hS : Setting c K N W) :
    Inv c K N W ((Array.replicate c.vc.blocks.size none).set! 0 (some (entryState N))) := by
  have h0 : 0 < (Array.replicate c.vc.blocks.size (none : Option AState)).size := by
    simp only [Array.size_replicate]; exact Nat.pos_of_ne_zero hS.nonempty
  have hrest : ∀ b, b ≠ 0 →
      ((Array.replicate c.vc.blocks.size none).set! 0 (some (entryState N)))[b]! = none := by
    intro b hb
    rw [get!_set_ne hb, get!_eq]
    simp [Array.getElem?_replicate]
    split <;> rfl
  refine ⟨by simp, fun b a h => ?_, fun b a w h hw => ?_, ⟨_, get!_set_self h0 _, sub_refl _⟩⟩
  · by_cases hb : b = 0
    · subst hb; rw [get!_set_self h0] at h; rw [← Option.some.inj h]; exact good_entryState K N
    · rw [hrest b hb] at h; cases h
  · by_cases hb : b = 0
    · subst hb
      rw [get!_set_self h0] at h
      rw [← Option.some.inj h]
      obtain ⟨w0, hw0, hle⟩ := hS.entry
      rw [hw0] at hw
      cases hw
      obtain ⟨w', hw', hsz⟩ := hS.wit 0 (Nat.pos_of_ne_zero hS.nonempty)
      rw [hw0] at hw'
      cases hw'
      exact sub_of_le (by rw [(good_entryState K N).1]; exact Nat.le_of_eq hsz) hle
    · rw [hrest b hb] at h; cases h

theorem Phi_init (hS : Setting c K N W) :
    Phi (N * (K + calleeSaved.length))
      ((Array.replicate c.vc.blocks.size none).set! 0 (some (entryState N))) <
      c.vc.blocks.size * (N * (K + calleeSaved.length) + 1) + 2 := by
  have h0 : 0 < (Array.replicate c.vc.blocks.size (none : Option AState)).size := by
    simp only [Array.size_replicate]; exact Nat.pos_of_ne_zero hS.nonempty
  have hset := Phi_set (N * (K + calleeSaved.length)) h0 (some (entryState N))
  have hrep : Phi (N * (K + calleeSaved.length)) (Array.replicate c.vc.blocks.size none) =
      c.vc.blocks.size * (N * (K + calleeSaved.length) + 1) := by
    simp [Phi, phi, List.sum_replicate_nat]
  have h0' : (Array.replicate c.vc.blocks.size (none : Option AState))[0]! = none := by
    rw [get!_eq]; simp [Array.getElem?_replicate]; split <;> rfl
  rw [hrep, h0'] at hset
  have hw := wt_le (good_entryState K N)
  simp only [phi] at hset
  omega

/-! ## Completeness -/

theorem mapM_okL {α β : Type} (f : α → Except String β) :
    ∀ (l : List α), (∀ x ∈ l, ∃ y, f x = .ok y) → ∃ ys, l.mapM f = .ok ys
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys⟩ := mapM_okL f l fun z hz => h z (List.mem_cons_of_mem _ hz)
    exact ⟨y :: ys, by rw [List.mapM_cons, hy, hys]; rfl⟩

theorem mapM_okA {α β : Type} (l : Array α) (f : α → Except String β)
    (h : ∀ x ∈ l.toList, ∃ y, f x = .ok y) : ∃ ys, l.mapM f = .ok ys := by
  rw [Array.mapM_eq_mapM_toList]
  obtain ⟨ys, hys⟩ := mapM_okL f l.toList h
  exact ⟨ys.toArray, by rw [hys]; rfl⟩

/-- **Completeness of `checkAlloc`**: verified in-states `W` (with an entry state below
`entryState`), reachable blocks, operand vregs and parameters below `vc.classes.size`, and the
structural conditions `checkAlloc` checks, make `checkAlloc` accept. -/
theorem checkAlloc_complete {vc : VCode} {rf : RFunc} {succs preds : Array (Array Nat)}
    {W : Array (Option AState)} (hcfg : vc.cfg = .ok (succs, preds))
    (hsz : rf.blocks.size = vc.blocks.size) (hp0 : preds[0]? = some #[])
    (hpar0 : (vc.blocks[0]!).params = #[]) (hsaved : ∀ r ∈ rf.saved, r ∈ calleeSaved)
    (hops : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, ∃ ops, i.operands = .ok ops)
    (hreach : ∀ b < vc.blocks.size, Prep.Reach succs b)
    (hS : Setting ⟨vc, succs, rf, 128 + 2 * rf.spillSlots⟩ vc.classes.size
      (128 + 2 * rf.spillSlots) W) :
    checkAlloc vc rf = .ok () := by
  have hne : vc.blocks.size ≠ 0 := hS.nonempty
  obtain ⟨ins, hfix, hI, hst⟩ := fixpoint_ok hS _ _ (inv_init hS) (Phi_init hS)
  obtain ⟨hver, hall⟩ := verify_stable hS hI hst hreach
  obtain ⟨_, hmap⟩ := mapM_okA vc.blocks (fun b => b.insts.mapM MInst.operands) fun vb hvb =>
    mapM_okA vb.insts MInst.operands fun i hi => hops vb hvb i hi
  have hsome : (ins.zipIdx.toList.forM fun x =>
      ensure x.fst.isSome fun _ =>
        toString "block " ++ toString vc.blocks[x.snd]!.label ++ toString " is never reached") =
      .ok () := by
    refine Spill.forM_ok fun ⟨x, i⟩ hx => ensure_true ?_
    rw [Array.toList_zipIdx] at hx
    have hx' : ins[i]? = some x := by simpa using List.mem_zipIdx_iff_getElem?.mp hx
    have hi : i < vc.blocks.size := by
      rw [← hI.size]; exact (Array.getElem?_eq_some_iff.mp hx').1
    obtain ⟨a, ha⟩ := hall i hi
    rw [hx'] at ha
    cases ha
    rfl
  unfold checkAlloc
  rw [hcfg]
  simp only [bind, Except.bind]
  rw [ensure_true (by simpa using hne), ensure_true (by simpa using hsz),
    ensure_true (by rw [succs!_eq, hp0]; rfl),
    ensure_true (by simp [hpar0]),
    ensure_true (by simpa using hsaved), hmap]
  simp only
  rw [hfix]
  simp only
  rw [hsome]
  exact hver

end E2E.CheckComplete
