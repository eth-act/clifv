import FV.Backend.Proof.SpillInvariant
import FV.Backend.Proof.SpillLocalState
import FV.Backend.Proof.RegallocLemmas

/-!
# Running the checker over a spilled block (V4 (a), step 4): the machinery

`Runs c vb k its a Q`: the checker's `runItems` over the items `its` of block `vb`, from
instruction index `k` and abstract state `a`, does not fail and reaches only states satisfying
`Q`, whatever items follow (`Runs.append`, `Runs.run`). Single moves (`Runs.move`), lists of moves
with pairwise distinct destinations none of which is a source (`Runs.moves`), and instructions
(`Runs.op`, with `stepOp_of`). On abstract states: states built from a content function
(`mkState`, `get_mkState`), inclusion from membership (`le_of_mem`), what an instruction's
transfer keeps (`transferOp_keep`), `parCopy` and the `map`-based state updates (`get_map`).
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof

/-! ## Partial runs -/

section
variable (c : CheckCtx) (vb : VBlock)

/-- Running `its` from instruction index `k` and state `a` succeeds and reaches only states
satisfying `Q`, whatever follows. -/
def Runs (k : Nat) (its : List RItem) (a : AState) (Q : Nat → AState → Prop) : Prop :=
  ∀ (rest : List RItem) (R : AState → Prop),
    (∀ k' a', Q k' a' → ∃ o, c.runItems vb k' rest a' = .ok o ∧ R o) →
    ∃ o, c.runItems vb k (its ++ rest) a = .ok o ∧ R o

variable {c vb}

theorem Runs.nil {k : Nat} {a : AState} {Q : Nat → AState → Prop} (h : Q k a) :
    Runs c vb k [] a Q :=
  fun _ _ hR => hR k a h

theorem Runs.append {k : Nat} {a : AState} {its its' : List RItem} {Q Q' : Nat → AState → Prop}
    (h : Runs c vb k its a Q) (h' : ∀ k' a', Q k' a' → Runs c vb k' its' a' Q') :
    Runs c vb k (its ++ its') a Q' := by
  intro rest R hR
  rw [List.append_assoc]
  exact h (its' ++ rest) R fun k' a' hq => h' k' a' hq rest R hR

theorem Runs.mono {k : Nat} {a : AState} {its : List RItem} {Q Q' : Nat → AState → Prop}
    (h : Runs c vb k its a Q) (hq : ∀ k a, Q k a → Q' k a) : Runs c vb k its a Q' :=
  fun rest R hR => h rest R fun k' a' hx => hR k' a' (hq _ _ hx)

theorem ensure_true {b : Bool} {msg : Unit → String} (h : b = true) : ensure b msg = .ok () := by
  simp [ensure, h]; rfl

theorem Runs.move {k : Nat} {a : AState} {src dst : Loc} {Q : Nat → AState → Prop}
    (hk : k ≠ vb.insts.size) (hm : c.checkMove s!"block {vb.label}" src dst = .ok ())
    (hq : Q k (a.put dst (a.get src))) : Runs c vb k [.move src dst] a Q := by
  intro rest R hR
  obtain ⟨o, ho, hRo⟩ := hR _ _ hq
  refine ⟨o, ?_, hRo⟩
  have he : ensure (k != vb.insts.size) (fun _ => s!"block {vb.label}: code after the terminator") =
      .ok () := ensure_true (by simpa using hk)
  simp only [List.cons_append, List.nil_append, CheckCtx.runItems, he, CheckCtx.stepMove, hm,
    bind, Except.bind, pure, Except.pure]
  exact ho

theorem Runs.op {k : Nat} {a a' : AState} {allocs : Array Loc} {i : MInst} {ops : Array Operand}
    {Q : Nat → AState → Prop} (hk : k ≠ vb.insts.size) (hi : vb.insts[k]? = some i)
    (hops : i.operands = .ok ops)
    (hs : c.stepOp s!"block {vb.label} inst {k}" i ops allocs a = .ok a') (hq : Q (k + 1) a') :
    Runs c vb k [.op k allocs] a Q := by
  intro rest R hR
  obtain ⟨o, ho, hRo⟩ := hR _ _ hq
  refine ⟨o, ?_, hRo⟩
  have he : ensure (k != vb.insts.size) (fun _ => s!"block {vb.label}: code after the terminator") =
      .ok () := ensure_true (by simpa using hk)
  have he' : ensure (k == k) (fun _ => s!"block {vb.label}: instruction {k} where {k} is due") =
      .ok () := ensure_true (by simp)
  simp only [List.cons_append, List.nil_append, CheckCtx.runItems, he, he', hi, hops, hs,
    bind, Except.bind, pure, Except.pure]
  exact ho

theorem Runs.run {its : List RItem} {a : AState} {P : AState → Prop}
    (h : Runs c vb 0 its a fun k a' => k = vb.insts.size ∧ P a') :
    ∃ o, c.runItems vb 0 its a = .ok o ∧ P o := by
  have := h [] P fun k' a' ⟨hk, hp⟩ => ⟨a', by
    subst hk
    simp only [CheckCtx.runItems, ensure_true (b := vb.insts.size == vb.insts.size) (by simp),
      bind, Except.bind, pure, Except.pure], hp⟩
  simpa using this

/-- A move item. -/
def mv (m : Loc × Loc) : RItem := .move m.1 m.2

/-- **Moves with distinct destinations, none of which is a source**: each destination gets its
source's symbols, every other location keeps its own. -/
theorem Runs.moves {k : Nat} (hk : k ≠ vb.insts.size) : ∀ (ms : List (Loc × Loc)) (a : AState),
    (∀ m ∈ ms, c.checkMove s!"block {vb.label}" m.1 m.2 = .ok ()) →
    (∀ m ∈ ms, ∀ m' ∈ ms, m.1 ≠ m'.2) → (ms.map (·.2)).Nodup →
    (∀ m ∈ ms, ∃ i, m.2.index = some i ∧ i < a.size) →
    Runs c vb k (ms.map mv) a fun k' a' => k' = k ∧ a'.size = a.size ∧
      (∀ m ∈ ms, a'.get m.2 = a.get m.1) ∧ ∀ l, (∀ m ∈ ms, m.2 ≠ l) → a'.get l = a.get l
  | [], a, _, _, _, _ => Runs.nil ⟨rfl, rfl, by simp, fun _ _ => rfl⟩
  | m :: ms, a, hc, hsd, hnd, hi => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨i, hi1, hi2⟩ := hi m List.mem_cons_self
    have hsz1 : (a.put m.2 (a.get m.1)).size = a.size := size_put _ _ _
    have ih := Runs.moves hk ms (a.put m.2 (a.get m.1)) (fun m' h => hc m' (.tail _ h))
      (fun x hx y hy => hsd x (.tail _ hx) y (.tail _ hy)) hnd.2
      (fun x hx => by
        obtain ⟨i, h1, h2⟩ := hi x (.tail _ hx)
        exact ⟨i, h1, by rw [hsz1]; exact h2⟩)
    rw [List.map_cons, ← List.singleton_append]
    refine Runs.append (Q := fun k' a' => k' = k ∧ a' = a.put m.2 (a.get m.1))
      (Runs.move hk (hc m List.mem_cons_self) ⟨rfl, rfl⟩) fun k' a' ⟨hk', ha'⟩ => ?_
    subst hk' ha'
    refine ih.mono fun k2 a2 ⟨e1, e2, e3, e4⟩ => ⟨e1, by rw [e2, hsz1], ?_, ?_⟩
    · intro m' hm'
      rcases List.mem_cons.mp hm' with rfl | hm'
      · rw [e4 m'.2 (fun x hx he => hnd.1 (he ▸ List.mem_map_of_mem hx)),
          get_put_self hi1 (by omega)]
      · rw [e3 m' hm', get_put_ne (fun he => hsd m' (.tail _ hm') m List.mem_cons_self he.symm)]
    · intro l hl
      rw [e4 l (fun x hx => hl x (.tail _ hx)), get_put_ne (hl m List.mem_cons_self)]

/-- The checker's `runMoves` as a partial run. -/
theorem Runs.ofRunMoves {k : Nat} (hk : k ≠ vb.insts.size) : ∀ (ms : List (Loc × Loc))
    (a a' : AState), runMoves c s!"block {vb.label}" ms a = .ok a' →
    Runs c vb k (ms.map mv) a fun k' a'' => k' = k ∧ a'' = a'
  | [], a, a', h => Runs.nil ⟨rfl, Except.ok.inj h⟩
  | m :: ms, a, a', h => by
    obtain ⟨a1, h1, h2⟩ := Except.bind_ok h
    have hc := (Except.seq_ok h1).1
    rw [stepMove_ok h1] at h2
    rw [List.map_cons, ← List.singleton_append]
    exact Runs.append (Q := fun k' a'' => k' = k ∧ a'' = a.put m.2 (a.get m.1))
      (Runs.move hk hc ⟨rfl, rfl⟩) fun k' a'' ⟨e1, e2⟩ => by
        subst e1 e2; exact Runs.ofRunMoves hk ms _ a' h2

end

/-- `runMoves` keeps every location no move writes. -/
theorem runMoves_frame (c : CheckCtx) (w : String) : ∀ (ms : List (Loc × Loc)) (a a' : AState),
    runMoves c w ms a = .ok a' → ∀ l, (∀ m ∈ ms, m.2 ≠ l) → a'.get l = a.get l
  | [], a, a', h, _, _ => by cases h; rfl
  | m :: ms, a, a', h, l, hl => by
    obtain ⟨a1, h1, h2⟩ := Except.bind_ok h
    rw [stepMove_ok h1] at h2
    rw [runMoves_frame c w ms _ a' h2 l (fun x hx => hl x (.tail _ hx)),
      get_put_ne (hl m List.mem_cons_self)]

theorem size_runMoves (c : CheckCtx) (w : String) : ∀ (ms : List (Loc × Loc)) (a a' : AState),
    runMoves c w ms a = .ok a' → a'.size = a.size
  | [], a, a', h => by cases h; rfl
  | m :: ms, a, a', h => by
    obtain ⟨a1, h1, h2⟩ := Except.bind_ok h
    rw [stepMove_ok h1] at h2
    rw [size_runMoves c w ms _ a' h2, size_put]

/-! ## Instructions -/

theorem needs_of {w : String} {a : AState} {l : Loc} {s : Sym} (h : s ∈ a.get l) :
    needs w a l s = .ok () :=
  ensure_true (List.contains_iff_mem.mpr h)

/-- `stepOp` accepts an instruction whose static checks pass, whose uses are where they should be,
and whose return check passes. -/
theorem stepOp_of {c : CheckCtx} {w : String} {i : MInst} {ops : Array Operand} {allocs : Array Loc}
    {a : AState} (hs : c.checkStatic w ops allocs i.clobbers = .ok ())
    (he : ∀ p ∈ atPos (ops.zip allocs).toList .use .early, Sym.vreg p.1.vreg ∈ a.get p.2)
    (hl : atPos (ops.zip allocs).toList .use .late = [])
    (hr : retCheck w i (transferOp i (ops.zip allocs).toList a) = .ok ()) :
    c.stepOp w i ops allocs a = .ok (transferOp i (ops.zip allocs).toList a) := by
  have h1 : (atPos (ops.zip allocs).toList .use .early).forM
      (fun p => needs w a p.2 (.vreg p.1.vreg)) = .ok () :=
    Spill.forM_ok fun p hp => needs_of (he p hp)
  unfold CheckCtx.stepOp
  simp only [hs, h1, hl, hr, bind, Except.bind, pure, Except.pure]
  rfl

theorem retCheck_other {w : String} {i : MInst} (h : ∀ us, i ≠ .rets us) (a : AState) :
    retCheck w i a = .ok () := by
  unfold retCheck
  split
  · exact absurd rfl (h _)
  · rfl

theorem retCheck_rets {w : String} {us : List (Reg × Reg)} {a : AState}
    (h : ∀ r ∈ calleeSaved, Sym.entry r ∈ a.get (.reg r)) : retCheck w (.rets us) a = .ok () :=
  Spill.forM_ok fun r hr => needs_of (h r hr)

theorem size_forgetDefs (a : AState) (ps : List (Operand × Loc)) :
    (forgetDefs a ps).size = a.size := by simp [forgetDefs]

theorem size_transferOp (i : MInst) (P : List (Operand × Loc)) (a : AState) :
    (transferOp i P a).size = a.size := by
  unfold transferOp
  split <;> simp only [size_forgetDefs, size_defineAll, size_clobberAll]

/-- **What an instruction's transfer keeps**: a symbol of a location that is no def's location and
not clobbered, unless it is a def's vreg. -/
theorem transferOp_keep {i : MInst} {P : List (Operand × Loc)} {a : AState} {l : Loc} {s : Sym}
    (hl : ∀ x ∈ P, x.1.kind = .def → x.2 ≠ l) (hc : ∀ r ∈ i.clobbers, Loc.reg r ≠ l)
    (hs : s ∈ a.get l) (hd : ∀ x ∈ P, x.1.kind = .def → s ≠ .vreg x.1.vreg) :
    s ∈ (transferOp i P a).get l := by
  have hpos : ∀ p, ∀ x ∈ atPos P .def p, x ∈ P ∧ x.1.kind = .def := fun p x hx =>
    ⟨(mem_atPos.mp hx).1, (mem_atPos.mp hx).2.1⟩
  have hE := defineAll_get_other (atPos P .def .early) a l
    (fun x hx => hl x (hpos _ x hx).1 (hpos _ x hx).2)
  have hC := clobberAll_get_other i.clobbers (defineAll a (atPos P .def .early)) l hc
  have hL := defineAll_get_other (atPos P .def .late)
    (clobberAll (defineAll a (atPos P .def .early)) i.clobbers) l
    (fun x hx => hl x (hpos _ x hx).1 (hpos _ x hx).2)
  have hnot : ∀ p, ((atPos P .def p).any fun x => s == .vreg x.1.vreg) = false := by
    intro p
    rw [Bool.eq_false_iff]
    intro hany
    obtain ⟨x, hx, hxe⟩ := List.any_eq_true.mp hany
    exact hd x (hpos _ x hx).1 (hpos _ x hx).2 (by simpa using hxe)
  have hmid : s ∈ (defineAll (clobberAll (defineAll a (atPos P .def .early)) i.clobbers)
      (atPos P .def .late)).get l := by
    rw [hL, hC, hE]
    simp only [List.mem_filter, hnot, Bool.not_false, and_true]
    exact hs
  unfold transferOp
  split
  · exact hmid
  · rw [forgetDefs_get]
    refine List.mem_filter.mpr ⟨hmid, ?_⟩
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro hany
    obtain ⟨x, hx, hxe⟩ := List.any_eq_true.mp hany
    have hx' := List.mem_of_mem_drop hx
    rw [List.mem_filter] at hx'
    simp at hxe
    exact hd x hx'.1 (by simpa using hx'.2) hxe.2

/-! ## Abstract states -/

/-- The location with dense index `i` (`Loc.index`'s inverse). -/
def ofIndex (i : Nat) : Loc :=
  if i < 32 then .reg (.x i) else if i < 64 then .reg (.v (i - 32))
  else if i < 96 then .save (.x (i - 64)) else if i < 128 then .save (.v (i - 96))
  else .stack ((i - 128) / 2) (if (i - 128) % 2 = 0 then .int else .float)

theorem index_ofIndex (i : Nat) : (ofIndex i).index = some i := by
  unfold ofIndex
  by_cases h1 : i < 32
  · simp [h1, Loc.index]
  by_cases h2 : i < 64
  · have : i - 32 < 32 := by omega
    simp [h1, h2, Loc.index, this]; omega
  by_cases h3 : i < 96
  · have : i - 64 < 32 := by omega
    simp [h1, h2, h3, Loc.index, this]; omega
  by_cases h4 : i < 128
  · have : i - 96 < 32 := by omega
    simp [h1, h2, h3, h4, Loc.index, this]; omega
  by_cases h5 : (i - 128) % 2 = 0
  · simp [h1, h2, h3, h4, h5, Loc.index]; omega
  · simp [h1, h2, h3, h4, h5, Loc.index]; omega

/-- The abstract state of size `N` with content `F`. -/
def mkState (N : Nat) (F : Loc → List Sym) : AState := Array.ofFn (n := N) fun i => F (ofIndex i)

theorem size_mkState (N : Nat) (F : Loc → List Sym) : (mkState N F).size = N := by simp [mkState]

theorem get_mkState {N : Nat} {F : Loc → List Sym} {l : Loc} {i : Nat} (hi : l.index = some i)
    (hlt : i < N) : (mkState N F).get l = F l := by
  have : ofIndex i = l := index_inj (index_ofIndex i) hi
  simp [AState.get, hi, mkState, Array.getD_eq_getD_getElem?, hlt, this]

theorem mem_get_mkState {N : Nat} {F : Loc → List Sym} {l : Loc} {s : Sym}
    (h : s ∈ (mkState N F).get l) : s ∈ F l ∧ ∃ i, l.index = some i ∧ i < N := by
  unfold AState.get at h
  split at h
  · rename_i i hi
    by_cases hlt : i < N
    · have : ofIndex i = l := index_inj (index_ofIndex i) hi
      simp [mkState, Array.getD_eq_getD_getElem?, hlt, this] at h
      exact ⟨h, i, hi, hlt⟩
    · simp [mkState, Array.getD_eq_getD_getElem?, hlt] at h
  · cases h

/-- Inclusion from membership. -/
theorem le_of_mem {a b : AState} (h : ∀ l s, s ∈ a.get l → s ∈ b.get l) : a.le b = true := by
  unfold AState.le
  rw [List.all_eq_true]
  intro i _
  rw [List.all_eq_true]
  intro s hs
  have h1 : a.get (ofIndex i) = a.getD i [] := by simp [AState.get, index_ofIndex]
  have h2 : b.get (ofIndex i) = b.getD i [] := by simp [AState.get, index_ofIndex]
  rw [← h1] at hs
  rw [← h2]
  exact List.contains_iff_mem.mpr (h _ _ hs)

/-- A pointwise update of every location (that keeps `[]`). -/
theorem get_map (a : AState) (f : List Sym → List Sym) (hf : f [] = []) (l : Loc) :
    AState.get (a.map f) l = f (a.get l) := by
  unfold AState.get
  split
  · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases a[‹Nat›]? <;> simp [hf]
  · exact hf.symm

theorem mem_parCopy_keep {a : AState} {ps xs : List Nat} {l : Loc} {s : Sym} (hs : s ∈ a.get l)
    (hp : ∀ p ∈ ps, s ≠ .vreg p) : s ∈ (a.parCopy ps xs).get l := by
  unfold AState.parCopy
  rw [get_map _ _ (by simp)]
  refine List.mem_append_left _ (List.mem_filter.mpr ⟨hs, ?_⟩)
  simp only [Bool.not_eq_true', Bool.eq_false_iff]
  intro hc
  obtain ⟨p, hp', he⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
  exact hp p hp' he.symm

theorem mem_parCopy_add {a : AState} {ps xs : List Nat} {l : Loc} {p y : Nat}
    (hpy : (p, y) ∈ ps.zip xs) (hy : Sym.vreg y ∈ a.get l) : Sym.vreg p ∈ (a.parCopy ps xs).get l := by
  unfold AState.parCopy
  rw [get_map _ _ (by simp)]
  by_cases hk : Sym.vreg p ∈ (a.get l).filter (fun s => !(ps.map Sym.vreg).contains s)
  · exact List.mem_append_left _ hk
  · refine List.mem_append_right _ (List.mem_filter.mpr ⟨?_, ?_⟩)
    · exact List.mem_filterMap.mpr ⟨(p, y), hpy, by simp [hy]⟩
    · simp [List.contains_iff_mem] at hk ⊢
      by_cases h : Sym.vreg p ∈ a.get l
      · exact .inr (hk h)
      · exact .inl h

theorem mem_forgetOps {a : AState} {os : List Operand} {l : Loc} {s : Sym} (hs : s ∈ a.get l)
    (h : ∀ o ∈ os, o.kind = .def → s ≠ .vreg o.vreg) : s ∈ (forgetOps a os).get l := by
  unfold forgetOps
  rw [get_map _ _ (by simp)]
  refine List.mem_filter.mpr ⟨hs, ?_⟩
  rw [Bool.not_eq_true', Bool.eq_false_iff]
  intro hany
  obtain ⟨o, ho, he⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, beq_iff_eq] at he
  exact h o ho he.1 he.2

/-- `verifyBlock` from a run of the block and the successor checks. -/
theorem verifyBlock_of {c : CheckCtx} {ins : Array (Option AState)} {b : Nat} {a out : AState}
    (hin : ins[b]? = some (some a)) (hr : c.runBlock b a = .ok out)
    (he : ∀ s ∈ (c.succs[b]?.getD #[]).toList, ∃ e a', c.edge b s out = .ok e ∧
      ins[s]? = some (some a') ∧ a'.le e = true) :
    c.verifyBlock ins b = .ok () := by
  unfold CheckCtx.verifyBlock
  rw [hin]
  simp only [hr, bind, Except.bind]
  refine Spill.forM_ok fun s hs => ?_
  obtain ⟨e, a', h1, h2, h3⟩ := he s hs
  simp only [h1, h2, ensure_true h3]

end Backend.Proof.Spill
