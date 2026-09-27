import FV.Backend.Proof.RegallocState

/-!
# Soundness of the register-allocation checker (M6)

`checkAlloc_sound`: if `checkAlloc vc rf = .ok ()`, the allocated code `rf` (abstract
semantics `MStep`, `FV/Backend/Proof/VCodeSem.lean`) simulates the VCode `vc` (`VStep`), for
every instruction semantics `sem`, every `keep` (the part of a callee-saved register the
callee preserves) and every initial state: the allocated code only takes steps the VCode can
match (moves are silent and strictly decrease a measure), it can always step when the VCode
can, it returns the values the VCode returns with the same world, callee-saved registers hold
their entry values (`keep`-part), and it halts exactly with the VCode's world.

Proof: `op_sound` (one original instruction: the use checks give equal inputs, the
invariant survives early defs, clobbers and late defs), `Inv_move`, `edge_ok` (parallel copy),
`Inv_mono` against the verified in-states (`verify_ok`, `verifyBlock_ok`), `Inv_entryState`.
-/

namespace Backend.Proof

open Backend

theorem Except.bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem Except.seq_ok {ε β : Type} {x : Except ε PUnit} {f : PUnit → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : x = .ok () ∧ f () = .ok b := by
  obtain ⟨⟨⟩, h1, h2⟩ := Except.bind_ok h
  exact ⟨h1, h2⟩

theorem ensure_ok {b : Bool} {msg : Unit → String} (h : ensure b msg = .ok ()) : b = true := by
  unfold ensure at h
  split at h
  · assumption
  · cases h

theorem forM_ok {ε α : Type} {l : List α} {f : α → Except ε PUnit}
    (h : l.forM f = .ok ()) : ∀ x ∈ l, f x = .ok () := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have h' : (f y >>= fun _ => l.forM f) = .ok () := h
    obtain ⟨hu, hr⟩ := Except.seq_ok h'
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hu
    · exact ih hr x hx

theorem needs_ok {w : String} {a : AState} {l : Loc} {s : Sym} (h : needs w a l s = .ok ()) :
    s ∈ a.get l := by
  simpa using ensure_ok h

variable {c : CheckCtx}

theorem stepMove_ok {w : String} {src dst : Loc} {a a' : AState}
    (h : c.stepMove w src dst a = .ok a') : a' = a.put dst (a.get src) := by
  obtain ⟨_, h⟩ := Except.seq_ok h
  exact (Except.ok.inj h).symm

theorem stepOp_ok {w : String} {i : MInst} {ops : Array Operand} {allocs : Array Loc} {a a' : AState}
    (h : c.stepOp w i ops allocs a = .ok a') :
    c.checkStatic w ops allocs i.clobbers = .ok () ∧
    (∀ p ∈ atPos (ops.zip allocs).toList .use .early, Sym.vreg p.1.vreg ∈ a.get p.2) ∧
    (∀ p ∈ atPos (ops.zip allocs).toList .use .late,
      Sym.vreg p.1.vreg ∈ (defineAll a (atPos (ops.zip allocs).toList .def .early)).get p.2) ∧
    a' = transferOp i (ops.zip allocs).toList a ∧
    retCheck w i a' = .ok () := by
  obtain ⟨h1, h⟩ := Except.seq_ok h
  obtain ⟨h2, h⟩ := Except.seq_ok h
  obtain ⟨h3, h⟩ := Except.seq_ok h
  obtain ⟨h4, h⟩ := Except.seq_ok h
  have h5 := (Except.ok.inj h).symm
  subst h5
  exact ⟨h1, fun p hp => needs_ok (forM_ok h2 p hp), fun p hp => needs_ok (forM_ok h3 p hp), rfl, h4⟩

theorem retCheck_ok {w : String} {us : List (Reg × Reg)} {a : AState}
    (h : retCheck w (.rets us) a = .ok ()) : ∀ r ∈ calleeSaved, Sym.entry r ∈ a.get (.reg r) :=
  fun r hr => needs_ok (forM_ok h r hr)

theorem runItems_nil {vb : VBlock} {next : Nat} {a out : AState}
    (h : c.runItems vb next [] a = .ok out) : next = vb.insts.size ∧ out = a := by
  unfold CheckCtx.runItems at h
  obtain ⟨h1, h⟩ := Except.seq_ok h
  exact ⟨by simpa using ensure_ok h1, (Except.ok.inj h).symm⟩

theorem runItems_move {vb : VBlock} {next : Nat} {src dst : Loc} {its : List RItem} {a out : AState}
    (h : c.runItems vb next (.move src dst :: its) a = .ok out) :
    next ≠ vb.insts.size ∧ c.runItems vb next its (a.put dst (a.get src)) = .ok out := by
  unfold CheckCtx.runItems at h
  obtain ⟨h1, h⟩ := Except.seq_ok h
  obtain ⟨a', h2, h⟩ := Except.bind_ok h
  rw [stepMove_ok h2] at h
  exact ⟨by simpa using ensure_ok h1, h⟩

theorem runItems_op {vb : VBlock} {next k : Nat} {allocs : Array Loc} {its : List RItem} {a out : AState}
    (h : c.runItems vb next (.op k allocs :: its) a = .ok out) :
    next ≠ vb.insts.size ∧ k = next ∧ ∃ i ops a', vb.insts[k]? = some i ∧ i.operands = .ok ops ∧
      c.stepOp s!"block {vb.label} inst {k}" i ops allocs a = .ok a' ∧
      c.runItems vb (next + 1) its a' = .ok out := by
  unfold CheckCtx.runItems at h
  obtain ⟨h1, h⟩ := Except.seq_ok h
  obtain ⟨h2, h⟩ := Except.seq_ok h
  refine ⟨by simpa using ensure_ok h1, by simpa using ensure_ok h2, ?_⟩
  split at h
  · cases h
  · rename_i i hi
    obtain ⟨ops, h3, h⟩ := Except.bind_ok h
    obtain ⟨a', h4, h⟩ := Except.bind_ok h
    exact ⟨i, ops, a', hi, h3, h4, h⟩

theorem runBlock_ok {b : Nat} {a out : AState} (h : c.runBlock b a = .ok out) :
    ∃ vb items, c.vc.blocks[b]? = some vb ∧ c.rf.blocks[b]? = some items ∧
      c.runItems vb 0 items.toList a = .ok out := by
  unfold CheckCtx.runBlock at h
  split at h
  · exact ⟨_, _, ‹_›, ‹_›, h⟩
  · cases h
  · cases h


theorem checkStatic_ok {w : String} {ops : Array Operand} {allocs : Array Loc} {clob : List Reg}
    (h : c.checkStatic w ops allocs clob = .ok ()) :
    ops.size = allocs.size ∧
    ∀ d ∈ atPos (ops.zip allocs).toList .def .early, ∀ u ∈ (ops.zip allocs).toList,
      u.1.kind = .use → u.2 ≠ d.2 := by
  unfold CheckCtx.checkStatic at h
  obtain ⟨h1, h⟩ := Except.seq_ok h
  dsimp only at h
  obtain ⟨_, h⟩ := Except.seq_ok h
  obtain ⟨_, h⟩ := Except.seq_ok h
  obtain ⟨h4, _⟩ := Except.seq_ok h
  refine ⟨by simpa using ensure_ok h1, ?_⟩
  intro d hd u hu hk e
  simp only [atPos, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hd
  have hd' : d ∈ (ops.zip allocs).toList.filter (·.1.kind == .def) :=
    List.mem_filter.mpr ⟨hd.1, by simp [hd.2.1]⟩
  have := ensure_ok (forM_ok h4 d hd')
  rw [hd.2.2] at this
  have hmem : d.2 ∈ defConflicts ((ops.zip allocs).toList.filter (·.1.kind == .use))
      (clob.map Loc.reg) .early := by
    simp only [defConflicts, List.mem_append, List.mem_map]
    exact .inl ⟨u, List.mem_filter.mpr ⟨hu, by simp [hk]⟩, e⟩
  simp at this
  exact this (by simpa using hmem)


/-- The successor facts `verifyBlock` establishes for the out-state `out` of block `b`. -/
def EdgesOk (c : CheckCtx) (ins : Array (Option AState)) (b : Nat) (out : AState) : Prop :=
  ∀ s ∈ (c.succs[b]?.getD #[]).toList, ∃ e a', c.edge b s out = .ok e ∧
    ins[s]? = some (some a') ∧ a'.le e = true

theorem verifyBlock_ok {ins : Array (Option AState)} {b : Nat} (h : c.verifyBlock ins b = .ok ()) :
    ∃ a out, ins[b]? = some (some a) ∧ c.runBlock b a = .ok out ∧ EdgesOk c ins b out := by
  unfold CheckCtx.verifyBlock at h
  split at h
  · rename_i a ha
    obtain ⟨out, h1, h⟩ := Except.bind_ok h
    refine ⟨a, out, ha, h1, ?_⟩
    intro s hs
    obtain ⟨e, h2, h⟩ := Except.bind_ok (forM_ok h s hs)
    split at h
    · rename_i a' ha'
      exact ⟨e, a', h2, ha', ensure_ok h⟩
    · cases h
  · cases h

theorem verify_ok {ins : Array (Option AState)} (h : c.verify ins = .ok ()) :
    (∃ a0, ins[0]? = some (some a0) ∧ a0.le (entryState c.size) = true) ∧
    ∀ b < c.vc.blocks.size, c.verifyBlock ins b = .ok () := by
  unfold CheckCtx.verify at h
  split at h
  · rename_i a0 ha0
    obtain ⟨h1, h⟩ := Except.seq_ok h
    exact ⟨⟨a0, ha0, ensure_ok h1⟩, fun b hb => forM_ok h b (List.mem_range.mpr hb)⟩
  · cases h

theorem checkAlloc_ok {vc : VCode} {rf : RFunc} (h : checkAlloc vc rf = .ok ()) :
    ∃ succs preds ins, vc.cfg = .ok (succs, preds) ∧ vc.blocks.size ≠ 0 ∧
      rf.blocks.size = vc.blocks.size ∧
      CheckCtx.verify ⟨vc, succs, rf, 128 + 2 * rf.spillSlots⟩ ins = .ok () := by
  unfold checkAlloc at h
  obtain ⟨⟨succs, preds⟩, hcfg, h⟩ := Except.bind_ok h
  dsimp only at h
  obtain ⟨h1, h⟩ := Except.seq_ok h
  obtain ⟨h2, h⟩ := Except.seq_ok h
  obtain ⟨_, h⟩ := Except.seq_ok h
  obtain ⟨_, h⟩ := Except.seq_ok h
  obtain ⟨_, h⟩ := Except.seq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_ok h
  obtain ⟨ins, _, h⟩ := Except.bind_ok h
  obtain ⟨_, h⟩ := Except.seq_ok h
  exact ⟨succs, preds, ins, hcfg, by simpa using ensure_ok h1, by simpa using ensure_ok h2, h⟩

theorem edge_ok {V : Type} {keep : Reg → V → V} {b s : Nat} {out e : AState}
    (h : c.edge b s out = .ok e) {m : Loc → V} {ρ : Nat → V} {r₀ : Reg → V}
    (hi : Inv keep out m ρ r₀) :
    ∃ ρ', edgeEnv c.vc b s ρ = some ρ' ∧ Inv keep e m ρ' r₀ := by
  unfold CheckCtx.edge at h
  split at h
  · rename_i vb sb hb hs
    obtain ⟨h1, h⟩ := Except.seq_ok h
    have hsz : vb.branchArgs.size = sb.params.size := by simpa using ensure_ok h1
    split at h
    · rename_i he
      have e1 : vb.branchArgs.toList = [] := by simpa using he
      have e2 : sb.params.toList = [] := by
        have : sb.params.size = 0 := by rw [← hsz]; simpa using he
        simpa using this
      refine ⟨ρ, ?_, ?_⟩
      · have : parCopyEnv ρ [] [] = ρ := by funext v; simp [parCopyEnv]
        simp [edgeEnv, hb, hs, hsz, e1, e2, Except.toOption, List.mapM_nil, this]
        rfl
      · rw [(Except.ok.inj h).symm]; exact hi
    · obtain ⟨ps, hps, h⟩ := Except.bind_ok h
      obtain ⟨xs, hxs, h⟩ := Except.bind_ok h
      obtain ⟨h3, h⟩ := Except.seq_ok h
      refine ⟨parCopyEnv ρ ps xs, ?_, ?_⟩
      · simp [edgeEnv, hb, hs, hsz, hps, hxs, Except.toOption]
      · rw [(Except.ok.inj h).symm]
        exact Inv_parCopy (by simpa using ensure_ok h3) hi
  · cases h
  · cases h

theorem succOf_mem {vc : VCode} {succs preds} (hcfg : vc.cfg = .ok (succs, preds)) {b j s : Nat}
    (h : succOf vc b j = some s) : s ∈ (succs[b]?.getD #[]).toList := by
  simp only [succOf, hcfg] at h
  cases hb : succs[b]? with
  | none => simp [hb] at h
  | some ss =>
    simp only [hb, Option.bind_some] at h
    simp only [Option.getD_some, Array.mem_toList_iff]
    exact Array.mem_of_getElem? h


/-! ## Operand lists of the two semantics -/

theorem filter_zip_fst {α β : Type} (q : α → Bool) :
    ∀ (l1 : List α) (l2 : List β), l1.length = l2.length →
      ((l1.zip l2).filter (fun p => q p.1)).map Prod.fst = l1.filter q
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: l1, b :: l2, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zip_cons_cons, List.filter_cons]
    split <;> simp [filter_zip_fst q l1 l2 h]

theorem pairs_fst {ops : Array Operand} {allocs : Array Loc} (hsz : ops.size = allocs.size)
    (q : Operand → Bool) :
    ((ops.zip allocs).toList.filter (fun p => q p.1)).map Prod.fst = ops.toList.filter q := by
  rw [Array.toList_zip]
  exact filter_zip_fst q _ _ (by simp [hsz])

theorem uses_eq {V : Type} {ops : Array Operand} {allocs : Array Loc} (hsz : ops.size = allocs.size)
    {m : Loc → V} {ρ : Nat → V}
    (hU : ∀ p ∈ (ops.zip allocs).toList, p.1.isUse = true → m p.2 = ρ p.1.vreg) :
    ((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2) =
      (ops.toList.filter Operand.isUse).map (ρ ·.vreg) := by
  rw [← pairs_fst hsz Operand.isUse, List.map_map]
  apply List.map_congr_left
  intro p hp
  rw [List.mem_filter] at hp
  exact hU p hp.1 hp.2

theorem defs_early {V : Type} {ops : Array Operand} {allocs : Array Loc} {outs : List V}
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length) :
    ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs).filter (·.1.1.isEarly)).map (·.1) =
      atPos (ops.zip allocs).toList .def .early := by
  rw [filter_zip_fst (fun p : Operand × Loc => p.1.isEarly) _ _ hlen.symm, List.filter_filter]
  apply List.filter_congr
  intro p _
  simp [Operand.isEarly, Operand.isDef, atPos, Bool.and_comm]

theorem defs_late {V : Type} {ops : Array Operand} {allocs : Array Loc} {outs : List V}
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length) :
    ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs).filter (·.1.1.isLate)).map (·.1) =
      atPos (ops.zip allocs).toList .def .late := by
  rw [filter_zip_fst (fun p : Operand × Loc => p.1.isLate) _ _ hlen.symm, List.filter_filter]
  apply List.filter_congr
  intro p _
  simp [Operand.isLate, Operand.isDef, atPos, Bool.and_comm]

theorem defs_vcode {V : Type} {ops : Array Operand} {allocs : Array Loc} (hsz : ops.size = allocs.size)
    (outs : List V) (q : Operand → Bool) :
    ((ops.toList.filter Operand.isDef).zip outs).filter (fun p => q p.1) =
      ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs).filter (fun p => q p.1.1)).map
        (fun p => (p.1.1, p.2)) := by
  rw [← pairs_fst hsz Operand.isDef, List.zip_map_left, List.filter_map]
  rfl


/-! ## One original instruction -/

section
variable {V : Type} {keep : Reg → V → V}

/-- The checker's step of an original instruction is sound: the allocated code reads the
values the VCode reads, and the invariant holds after the instruction (early defs, clobbers,
late defs). -/
theorem op_sound {w : String} {i : MInst} {ops : Array Operand} {allocs : Array Loc}
    {a a' : AState} (hstep : c.stepOp w i ops allocs a = .ok a')
    {m : Loc → V} {ρ : Nat → V} {r₀ : Reg → V} (hinv : Inv keep a m ρ r₀)
    {outs : List V} (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    {m2 : Loc → V}
    (hclob : Clobbered keep i.clobbers
      (writeM m ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs).filter (·.1.1.isEarly))) m2) :
    ops.size = allocs.size ∧
    ((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2) =
      (ops.toList.filter Operand.isUse).map (ρ ·.vreg) ∧
    Inv keep a'
      (writeM m2 ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs).filter (·.1.1.isLate)))
      (writeV (writeV ρ (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isEarly)))
        (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isLate))) r₀ ∧
    (∀ us, i = .rets us → ∀ r ∈ calleeSaved, Sym.entry r ∈ a'.get (.reg r)) := by
  obtain ⟨hst, hE, hL, rfl, hret⟩ := stepOp_ok hstep
  obtain ⟨hsz, hdisj⟩ := checkStatic_ok hst
  refine ⟨hsz, ?_, ?_, ?_⟩
  · apply uses_eq hsz
    intro p hp hu
    have hk : p.1.kind = .use := by simpa [Operand.isUse] using hu
    cases hpos : p.1.pos with
    | early =>
      have := hE p (List.mem_filter.mpr ⟨hp, by simp [hk, hpos]⟩)
      exact hinv _ _ this
    | late =>
      have := hL p (List.mem_filter.mpr ⟨hp, by simp [hk, hpos]⟩)
      refine hinv _ _ (mem_get_defineAll ?_ this)
      intro hm
      obtain ⟨d, hd, e⟩ := List.mem_map.mp hm
      exact hdisj d hd p hp hk e.symm
  · have h1 := Inv_defineAll
      ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs).filter (·.1.1.isEarly)) hinv
    rw [defs_early hlen, ← defs_vcode hsz outs Operand.isEarly] at h1
    have h2 := Inv_clobberAll h1 hclob
    have h3 := Inv_defineAll
      ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs).filter (·.1.1.isLate)) h2
    rw [defs_late hlen, ← defs_vcode hsz outs Operand.isLate] at h3
    exact h3
  · intro us hi
    subst hi
    exact retCheck_ok hret

end

end Backend.Proof
