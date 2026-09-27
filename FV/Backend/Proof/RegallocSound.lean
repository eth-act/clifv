import FV.Backend.Proof.RegallocLemmas

/-!
# Soundness of the register-allocation checker (M6)

`checkAlloc_sound`: if `checkAlloc vc rf = .ok ()`, the allocated code `rf` (abstract
semantics `MStep`, `FV/Backend/Proof/VCodeSem.lean`) simulates the VCode `vc` (`VStep`), for
every instruction semantics `sem`, every `keep` (the part of a callee-saved register the
callee preserves) and every initial state (`IsSimulation`): each step of the allocated code is
matched by one VCode step or is a move (no VCode step, strictly smaller measure); the
allocated code can step whenever the VCode can; related returns have equal values and worlds;
at a return, callee-saved registers hold their entry values (`keep`-part).
Corollaries: `checkAlloc_ret`, `checkAlloc_halt`, `checkAlloc_stuck`, `checkAlloc_diverges`.

Proof: the relation `Match` says the machine store and the VCode vreg file satisfy the
checker's abstract state (`Inv`) at the current item, and the block's out-state feeds the
verified successor in-states (`EdgesOk`). `sim_step` (moves by `Inv_move`, instructions by
`op_sound`, branches by `edge_ok` and `Inv_mono` against the verified in-state) and
`sim_progress`; the entry by `Inv_entryState`.
-/

namespace Backend.Proof
open Backend

section
variable {V W : Type}

/-- The simulation relation between run states: same block and world; the machine's remaining
items check from an abstract state `a` that the machine store and the VCode vreg file satisfy;
the block's out-state feeds the verified successors. -/
def MatchRun (c : CheckCtx) (ins : Array (Option AState)) (keep : Reg → V → V) (r₀ : Reg → V)
    (ms : MState V W) (vs : VState V W) : Prop :=
  ms.b = vs.b ∧ ms.w = vs.w ∧ ∃ vb a out, c.vc.blocks[vs.b]? = some vb ∧
    c.runItems vb vs.k ms.its a = .ok out ∧ Inv keep a ms.m vs.ρ r₀ ∧ EdgesOk c ins vs.b out

def Match (c : CheckCtx) (ins : Array (Option AState)) (keep : Reg → V → V) (r₀ : Reg → V) :
    MConf V W → VConf V W → Prop
  | .run ms, .run vs => MatchRun c ins keep r₀ ms vs
  | .ret vals m w, .ret vals' w' =>
    vals = vals' ∧ w = w' ∧ ∀ r ∈ calleeSaved, keep r (m (.reg r)) = keep r (r₀ r)
  | .halt w, .halt w' => w = w'
  | _, _ => False

/-- What `checkAlloc vc rf = .ok ()` establishes (`checked_of_checkAlloc`). -/
structure Checked (vc : VCode) (rf : RFunc) (c : CheckCtx) (ins : Array (Option AState)) :
    Prop where
  vc_eq : c.vc = vc
  rf_eq : c.rf = rf
  cfg : ∃ preds, vc.cfg = .ok (c.succs, preds)
  size : rf.blocks.size = vc.blocks.size
  nonempty : vc.blocks.size ≠ 0
  entry : ∃ a0, ins[0]? = some (some a0) ∧ a0.le (entryState c.size) = true
  blocks : ∀ b < vc.blocks.size, c.verifyBlock ins b = .ok ()

theorem checked_of_checkAlloc {vc : VCode} {rf : RFunc} (h : checkAlloc vc rf = .ok ()) :
    ∃ c ins, Checked vc rf c ins := by
  obtain ⟨succs, preds, ins, hcfg, hne, hsz, hv⟩ := checkAlloc_ok h
  obtain ⟨he, hb⟩ := verify_ok hv
  exact ⟨_, ins, ⟨rfl, rfl, ⟨preds, hcfg⟩, hsz, hne, he, hb⟩⟩

variable {vc : VCode} {rf : RFunc} {c : CheckCtx} {ins : Array (Option AState)}
  (sem : ISem V W) (keep : Reg → V → V) {r₀ : Reg → V}

/-- Entering block `s` with an environment satisfying the (verified) in-state of `s`. -/
theorem enter_block (hc : Checked vc rf c ins) {s : Nat} {e a' : AState} {m : Loc → V}
    {ρ : Nat → V} {w : W} (hs : s < vc.blocks.size) (hins : ins[s]? = some (some a'))
    (hle : a'.le e = true) (hinv : Inv keep e m ρ r₀) :
    ∃ items, rf.blocks[s]? = some items ∧
      MatchRun c ins keep r₀ ⟨s, items.toList, m, w⟩ ⟨s, 0, ρ, w⟩ := by
  obtain ⟨a₁, out, h1, h2, h3⟩ := verifyBlock_ok (hc.blocks s hs)
  rw [hins] at h1
  cases h1
  obtain ⟨vb, items, hvb, hitems, hrun⟩ := runBlock_ok h2
  rw [hc.rf_eq] at hitems
  exact ⟨items, hitems, rfl, rfl, vb, a', out, hvb, hrun, Inv_mono hle hinv, h3⟩

theorem edgeEnv_lt {b s : Nat} {ρ ρ' : Nat → V} (h : edgeEnv vc b s ρ = some ρ') :
    s < vc.blocks.size := by
  unfold edgeEnv at h
  cases hs : vc.blocks[s]? with
  | none => cases hb : vc.blocks[b]? <;> simp [hs, hb] at h
  | some sb => exact (Array.getElem?_eq_some_iff.mp hs).1

theorem sim_step (hc : Checked vc rf c ins) {ms : MState V W} {vs : VState V W} {c' : MConf V W}
    (hm : MatchRun c ins keep r₀ ms vs) (hs : MStep vc sem keep rf (.run ms) c') :
    (∃ ms', c' = .run ms' ∧ MatchRun c ins keep r₀ ms' vs ∧ ms'.its.length < ms.its.length) ∨
    (∃ v', VStep vc sem (.run vs) v' ∧ Match c ins keep r₀ c' v') := by
  obtain ⟨b, its, m, w⟩ := ms
  obtain ⟨b', k, ρ, w''⟩ := vs
  obtain ⟨hb, hw, vb, a, out, hvb, hrun, hinv, hedges⟩ := hm
  simp only at hb hw
  subst hb hw
  cases hs with
  | move =>
    obtain ⟨_, hrun'⟩ := runItems_move hrun
    left
    exact ⟨_, rfl, ⟨rfl, rfl, vb, _, out, hvb, hrun', Inv_move _ _ hinv, hedges⟩, by simp⟩
  | @op _ _ allocs its _ _ _ i ops outs w' ctl m2 _ hvb' hi hops hsz hsem hlen hclob hnext =>
    right
    rw [hc.vc_eq] at hvb
    rw [hvb] at hvb'
    cases hvb'
    obtain ⟨_, hk, i', ops', a', hi', hops', hstep, hrun'⟩ := runItems_op hrun
    subst hk
    rw [hi] at hi'
    cases hi'
    rw [hops] at hops'
    cases hops'
    obtain ⟨_, huse, hinv', hret⟩ := op_sound hstep hinv hlen hclob
    rw [huse] at hsem hnext
    have hlen' : outs.length = (ops.toList.filter Operand.isDef).length := by
      rw [hlen, ← pairs_fst hsz.symm, List.length_map]
    have hvbc : c.vc.blocks[b]? = some vb := by rw [hc.vc_eq]; exact hvb
    cases hnext with
    | next hk1 =>
      exact ⟨_, VStep.step hvb hi hops hsem hlen' (VNext.next hk1),
        rfl, rfl, vb, _, out, hvbc, hrun', hinv', hedges⟩
    | ret hus =>
      exact ⟨_, VStep.step hvb hi hops hsem hlen' (VNext.ret hus), rfl, rfl,
        fun r hr => (hinv' _ _ (hret _ hus r hr)).2⟩
    | halt =>
      exact ⟨_, VStep.step hvb hi hops hsem hlen' VNext.halt, rfl⟩
    | goto hk1 hsucc hitems =>
      have hits : its = [] := by
        cases its with
        | nil => rfl
        | cons it its =>
          cases it with
          | move => exact absurd hk1 (runItems_move hrun').1
          | op => exact absurd hk1 (runItems_op hrun').1
      subst hits
      obtain ⟨_, rfl⟩ := runItems_nil hrun'
      obtain ⟨preds, hcfg⟩ := hc.cfg
      obtain ⟨e, a'', hedge, hins, hle⟩ := hedges _ (succOf_mem hcfg hsucc)
      obtain ⟨ρ', henv, hinve⟩ := edge_ok hedge hinv'
      rw [hc.vc_eq] at henv
      obtain ⟨items', hitems', hmr⟩ := enter_block keep hc (w := w') (edgeEnv_lt henv) hins hle hinve
      rw [hitems] at hitems'
      cases hitems'
      exact ⟨_, VStep.step hvb hi hops hsem hlen' (VNext.goto hk1 hsucc henv), hmr⟩

theorem sim_progress (hc : Checked vc rf c ins) {ms : MState V W} {vs : VState V W}
    {v' : VConf V W} (hm : MatchRun c ins keep r₀ ms vs) (hv : VStep vc sem (.run vs) v') :
    ∃ c', MStep vc sem keep rf (.run ms) c' := by
  obtain ⟨b, its, m, w⟩ := ms
  obtain ⟨b', k, ρ, w''⟩ := vs
  obtain ⟨hb, hw, vb, a, out, hvb, hrun, hinv, hedges⟩ := hm
  simp only at hb hw
  subst hb hw
  rw [hc.vc_eq] at hvb
  cases hv with
  | @step _ _ _ _ _ i ops outs w' ctl _ hvb' hi hops hsem hlen hnext =>
  rw [hvb] at hvb'
  cases hvb'
  cases its with
  | nil =>
    obtain ⟨hk, _⟩ := runItems_nil hrun
    subst hk
    simp at hi
  | cons it its =>
    cases it with
    | move src dst => exact ⟨_, MStep.move⟩
    | op k' allocs =>
      obtain ⟨_, hk, i', ops', a', hi', hops', hstep, _⟩ := runItems_op hrun
      subst hk
      rw [hi] at hi'
      cases hi'
      rw [hops] at hops'
      cases hops'
      obtain ⟨hst, -⟩ := stepOp_ok hstep
      obtain ⟨hsz, -⟩ := checkStatic_ok hst
      have hlen' : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length := by
        rw [hlen, ← pairs_fst hsz, List.length_map]
      have hclob : Clobbered keep i.clobbers
          (writeM m ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs).filter (·.1.1.isEarly)))
          (writeM m ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs).filter (·.1.1.isEarly))) :=
        ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
      obtain ⟨-, huse, -, -⟩ := op_sound hstep hinv hlen' hclob
      rw [← huse] at hsem hnext
      cases hnext with
      | next h => exact ⟨_, MStep.op hvb hi hops hsz.symm hsem hlen' hclob (MNext.next h)⟩
      | ret h => exact ⟨_, MStep.op hvb hi hops hsz.symm hsem hlen' hclob (MNext.ret h)⟩
      | halt => exact ⟨_, MStep.op hvb hi hops hsz.symm hsem hlen' hclob MNext.halt⟩
      | goto h hsucc henv =>
        have hs := edgeEnv_lt henv
        rw [← hc.size] at hs
        exact ⟨_, MStep.op hvb hi hops hsz.symm hsem hlen' hclob
          (MNext.goto h hsucc (Array.getElem?_eq_getElem hs))⟩


end

/-! ## The theorem -/

section
variable {V W : Type}

def MConf.measure : MConf V W → Nat
  | .run s => s.its.length
  | _ => 0

variable (vc : VCode) (rf : RFunc) (sem : ISem V W) (keep : Reg → V → V)

/-- `R` relates configurations of the allocated code (left) to VCode configurations (right) such
that every step of the allocated code is matched by zero VCode steps with a strictly smaller
measure (a move) or by one VCode step; the allocated code can step whenever the VCode can; and
related final configurations are equal (same returned values, same world). -/
structure IsSimulation (R : MConf V W → VConf V W → Prop) : Prop where
  step : ∀ {c v c'}, R c v → MStep vc sem keep rf c c' →
    (R c' v ∧ c'.measure < c.measure) ∨ ∃ v', VStep vc sem v v' ∧ R c' v'
  progress : ∀ {c v v'}, R c v → VStep vc sem v v' → ∃ c', MStep vc sem keep rf c c'
  ret : ∀ {vals m w v}, R (.ret vals m w) v → v = .ret vals w
  halt : ∀ {w v}, R (.halt w) v → v = .halt w
  run : ∀ {s v}, R (.run s) v → ∃ s', v = .run s'

/-- The initial configuration of the allocated code: block 0, store `m₀`, world `w₀`. -/
def MConf.init (m₀ : Loc → V) (w₀ : W) : MConf V W := .run ⟨0, rf.blocks[0]!.toList, m₀, w₀⟩

/-- The initial configuration of the VCode: block 0, vreg file `ρ₀`, world `w₀`. -/
def VConf.init (ρ₀ : Nat → V) (w₀ : W) : VConf V W := .run ⟨0, 0, ρ₀, w₀⟩

/-- **Soundness of the register-allocation checker.** If `checkAlloc vc rf` accepts, then for
every instruction semantics `sem`, every notion `keep` of the callee-preserved part of a
register, every initial store `m₀` (its registers are the entry register file), vreg file `ρ₀`
and world `w₀`, the allocated code simulates the VCode from the initial configurations, and
whenever it returns, every callee-saved register holds its entry value (`keep`-part). -/
theorem checkAlloc_sound (h : checkAlloc vc rf = .ok ()) (m₀ : Loc → V) (ρ₀ : Nat → V) (w₀ : W) :
    ∃ R, IsSimulation vc rf sem keep R ∧ R (MConf.init rf m₀ w₀) (VConf.init ρ₀ w₀) ∧
      ∀ {vals m w v}, R (.ret vals m w) v →
        ∀ r ∈ calleeSaved, keep r (m (.reg r)) = keep r (m₀ (.reg r)) := by
  obtain ⟨c, ins, hc⟩ := checked_of_checkAlloc h
  refine ⟨Match c ins keep (fun r => m₀ (.reg r)), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro cf v c' hR hs
    cases cf with
    | run ms =>
      cases v with
      | run vs =>
        rcases sim_step sem keep hc hR hs with ⟨ms', rfl, hmr, hlt⟩ | hr
        · exact .inl ⟨hmr, hlt⟩
        · exact .inr hr
      | ret => exact hR.elim
      | halt => exact hR.elim
    | ret => cases hs
    | halt => cases hs
  · intro cf v v' hR hv
    cases cf with
    | run ms =>
      cases v with
      | run vs => exact sim_progress sem keep hc hR hv
      | ret => exact hR.elim
      | halt => exact hR.elim
    | ret => cases v <;> first | exact hR.elim | cases hv
    | halt => cases v <;> first | exact hR.elim | cases hv
  · intro vals m w v hR
    cases v with
    | ret vals' w' => obtain ⟨rfl, rfl, -⟩ := hR; rfl
    | _ => exact hR.elim
  · intro w v hR
    cases v with
    | halt w' => cases hR; rfl
    | _ => exact hR.elim
  · intro s v hR
    cases v with
    | run s' => exact ⟨s', rfl⟩
    | _ => exact hR.elim
  · obtain ⟨a0, h0, hle⟩ := hc.entry
    obtain ⟨a, out, ha, hrb, hedges⟩ :=
      verifyBlock_ok (hc.blocks 0 (Nat.pos_of_ne_zero hc.nonempty))
    rw [h0] at ha
    cases ha
    obtain ⟨vb, items, hvb, hitems, hrun⟩ := runBlock_ok hrb
    rw [hc.rf_eq] at hitems
    have : rf.blocks[0]! = items := by simp [getElem!_def, hitems]
    simp only [MConf.init, VConf.init, this]
    exact ⟨rfl, rfl, vb, a0, out, hvb, hrun, Inv_mono hle Inv_entryState, hedges⟩
  · intro vals m w v hR
    cases v with
    | ret => exact hR.2.2
    | _ => exact hR.elim

variable {vc rf sem keep}

theorem IsSimulation.star {R : MConf V W → VConf V W → Prop} (hR : IsSimulation vc rf sem keep R)
    {c c' : MConf V W} {v : VConf V W} (hs : Star (MStep vc sem keep rf) c c') (h : R c v) :
    ∃ v', Star (VStep vc sem) v v' ∧ R c' v' := by
  induction hs generalizing v with
  | refl => exact ⟨v, .refl _, h⟩
  | step hs _ ih =>
    rcases hR.step h hs with ⟨h', _⟩ | ⟨v', hv, h'⟩
    · exact ih h'
    · obtain ⟨v'', hv', h''⟩ := ih h'
      exact ⟨v'', .step hv hv', h''⟩

/-- A return of the allocated code is a return of the VCode with the same values and world,
and callee-saved registers are restored. -/
theorem checkAlloc_ret (h : checkAlloc vc rf = .ok ()) {m₀ : Loc → V} (ρ₀ : Nat → V) {w₀ : W}
    {vals : List V} {m : Loc → V} {w : W}
    (hs : Star (MStep vc sem keep rf) (MConf.init rf m₀ w₀) (.ret vals m w)) :
    Star (VStep vc sem) (VConf.init ρ₀ w₀) (.ret vals w) ∧
      ∀ r ∈ calleeSaved, keep r (m (.reg r)) = keep r (m₀ (.reg r)) := by
  obtain ⟨R, hR, h0, hcs⟩ := checkAlloc_sound vc rf sem keep h m₀ ρ₀ w₀
  obtain ⟨v, hv, hRv⟩ := hR.star hs h0
  rw [hR.ret hRv] at hv
  exact ⟨hv, hcs hRv⟩

/-- A trap (halt) of the allocated code is a halt of the VCode with the same world. -/
theorem checkAlloc_halt (h : checkAlloc vc rf = .ok ()) {m₀ : Loc → V} (ρ₀ : Nat → V) {w₀ w : W}
    (hs : Star (MStep vc sem keep rf) (MConf.init rf m₀ w₀) (.halt w)) :
    Star (VStep vc sem) (VConf.init ρ₀ w₀) (.halt w) := by
  obtain ⟨R, hR, h0, -⟩ := checkAlloc_sound vc rf sem keep h m₀ ρ₀ w₀
  obtain ⟨v, hv, hRv⟩ := hR.star hs h0
  rw [hR.halt hRv] at hv
  exact hv

/-- The allocated code gets stuck only where the VCode gets stuck. -/
theorem checkAlloc_stuck (h : checkAlloc vc rf = .ok ()) {m₀ : Loc → V} (ρ₀ : Nat → V) {w₀ : W}
    {s : MState V W} (hs : Star (MStep vc sem keep rf) (MConf.init rf m₀ w₀) (.run s))
    (hstuck : ∀ c', ¬ MStep vc sem keep rf (.run s) c') :
    ∃ vs, Star (VStep vc sem) (VConf.init ρ₀ w₀) (.run vs) ∧ ∀ v', ¬ VStep vc sem (.run vs) v' := by
  obtain ⟨R, hR, h0, -⟩ := checkAlloc_sound vc rf sem keep h m₀ ρ₀ w₀
  obtain ⟨v, hv, hRv⟩ := hR.star hs h0
  obtain ⟨vs, rfl⟩ := hR.run hRv
  refine ⟨vs, hv, fun v' hv' => ?_⟩
  obtain ⟨c', hc'⟩ := hR.progress hRv hv'
  exact hstuck c' hc'

/-- Exactly `n` steps. -/
inductive StepsN {α : Type} (r : α → α → Prop) : Nat → α → α → Prop
  | zero (a : α) : StepsN r 0 a a
  | succ {n : Nat} {a b c : α} : r a b → StepsN r n b c → StepsN r (n + 1) a c

theorem StepsN.snoc {α : Type} {r : α → α → Prop} {n : Nat} {a b c : α}
    (h : StepsN r n a b) (h' : r b c) : StepsN r (n + 1) a c := by
  induction h with
  | zero => exact .succ h' (.zero _)
  | succ hab _ ih => exact .succ hab (ih h')

theorem IsSimulation.next_vstep {R : MConf V W → VConf V W → Prop}
    (hR : IsSimulation vc rf sem keep R) {f : Nat → MConf V W}
    (hf : ∀ n, MStep vc sem keep rf (f n) (f (n + 1))) :
    ∀ k n v, R (f n) v → (f n).measure ≤ k → ∃ n' v', VStep vc sem v v' ∧ R (f n') v' := by
  intro k
  induction k with
  | zero =>
    intro n v h hk
    rcases hR.step h (hf n) with ⟨_, hlt⟩ | ⟨v', hv, h'⟩
    · omega
    · exact ⟨n + 1, v', hv, h'⟩
  | succ k ih =>
    intro n v h hk
    rcases hR.step h (hf n) with ⟨h', hlt⟩ | ⟨v', hv, h'⟩
    · exact ih (n + 1) v h' (by omega)
    · exact ⟨n + 1, v', hv, h'⟩

/-- An infinite execution of the allocated code is matched by VCode executions of every
length (the VCode diverges too). -/
theorem checkAlloc_diverges (h : checkAlloc vc rf = .ok ()) {m₀ : Loc → V} (ρ₀ : Nat → V)
    {w₀ : W} (f : Nat → MConf V W) (h0 : f 0 = MConf.init rf m₀ w₀)
    (hf : ∀ n, MStep vc sem keep rf (f n) (f (n + 1))) :
    ∀ N, ∃ v, StepsN (VStep vc sem) N (VConf.init ρ₀ w₀) v := by
  obtain ⟨R, hR, hinit, -⟩ := checkAlloc_sound vc rf sem keep h m₀ ρ₀ w₀
  suffices ∀ N, ∃ n v, StepsN (VStep vc sem) N (VConf.init ρ₀ w₀) v ∧ R (f n) v from
    fun N => (this N).elim fun _ ⟨v, hv, _⟩ => ⟨v, hv⟩
  intro N
  induction N with
  | zero => exact ⟨0, _, .zero _, h0 ▸ hinit⟩
  | succ N ih =>
    obtain ⟨n, v, hv, hRv⟩ := ih
    obtain ⟨n', v', hvv, hR'⟩ := hR.next_vstep hf _ n v hRv (Nat.le_refl _)
    exact ⟨n', v', hv.snoc hvv, hR'⟩

end

end Backend.Proof
