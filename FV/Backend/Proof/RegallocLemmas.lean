import FV.Backend.Proof.RegallocState

/-!
# Facts about the checker's functions (M6 proof)

What an accepting run of each checker function establishes (`stepOp_ok`, `runItems_*`,
`edge_ok`, `verify_ok`, `checkAlloc_ok`, ...), the correspondence between the operand lists of
the two semantics, and the per-instruction soundness `op_sound`.
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

theorem edgeCopy_ok {V : Type} {keep : Reg → V → V} {b s : Nat} {out e : AState}
    (h : c.edgeCopy b s out = .ok e) {m : Loc → V} {ρ : Nat → V} {r₀ : Reg → V}
    (hi : Inv keep out m ρ r₀) :
    ∃ ρ', edgeEnv c.vc b s ρ = some ρ' ∧ Inv keep e m ρ' r₀ := by
  unfold CheckCtx.edgeCopy at h
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

/-- An edge of the checker from a state whose dead defs are already forgotten
(`CheckCtx.edgeForget`). -/
theorem edge_ok {V : Type} {keep : Reg → V → V} {b s : Nat} {out e : AState}
    (h : c.edge b s out = .ok e) {m : Loc → V} {ρ : Nat → V} {r₀ : Reg → V}
    (hi : Inv keep (c.edgeForget b s out) m ρ r₀) :
    ∃ ρ', edgeEnv c.vc b s ρ = some ρ' ∧ Inv keep e m ρ' r₀ :=
  edgeCopy_ok h hi

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

theorem writeV_notDef {ρ : Nat → V} :
    ∀ (dv : List (Operand × V)) (u : Nat), (∀ p ∈ dv, p.1.vreg ≠ u) → writeV ρ dv u = ρ u
  | [], _, _ => rfl
  | p :: dv, u, h => by
    simp only [writeV, List.foldl_cons] at h ⊢
    have := writeV_notDef (ρ := upd ρ p.1.vreg p.2) dv u (fun q hq => h q (by simp [hq]))
    simp only [writeV] at this
    rw [this]
    simp [upd, Ne.symm (h p (by simp))]

theorem writeV_cons (ρ : Nat → V) (p : Operand × V) (dv : List (Operand × V)) :
    writeV ρ (p :: dv) = writeV (upd ρ p.1.vreg p.2) dv := rfl

/-- Writing the same defs with values that agree on every def of vreg `u` (from files that agree
at `u`) agrees at `u`. -/
theorem writeV_zip_filter_congr (q : Operand → Bool) (u : Nat) :
    ∀ (L : List Operand) (o o' : List V) (ρ ρ' : Nat → V), ρ u = ρ' u → o.length = o'.length →
      (∀ (k : Nat) (d : Operand), L[k]? = some d → d.vreg = u → o[k]? = o'[k]?) →
      writeV ρ ((L.zip o).filter (fun p => q p.1)) u =
        writeV ρ' ((L.zip o').filter (fun p => q p.1)) u
  | [], _, _, _, _, h, _, _ => by simpa [writeV] using h
  | _ :: _, [], [], _, _, h, _, _ => by simpa [writeV] using h
  | _ :: _, [], _ :: _, _, _, _, hl, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, _, hl, _ => by simp at hl
  | d :: L, a :: o, a' :: o', ρ, ρ', h, hl, hk => by
    have hl' : o.length = o'.length := by simpa using hl
    have hk' : ∀ (k : Nat) (d' : Operand), L[k]? = some d' → d'.vreg = u → o[k]? = o'[k]? :=
      fun k d' hd hu => by simpa using hk (k + 1) d' (by simpa using hd) hu
    simp only [List.zip_cons_cons, List.filter_cons]
    split
    · rw [writeV_cons, writeV_cons]
      refine writeV_zip_filter_congr q u L o o' _ _ ?_ hl' hk'
      by_cases hu : u = d.vreg
      · have := hk 0 d rfl hu.symm
        simp only [List.getElem?_cons_zero, Option.some.injEq] at this
        simp [upd, hu, this]
      · simp [upd, hu, h]
    · exact writeV_zip_filter_congr q u L o o' ρ ρ' h hl' hk'

theorem AState.mem_get_forgetDefs {a : AState} {pairs : List (Operand × Loc)} {l : Loc} {s : Sym}
    (h : s ∈ (forgetDefs a pairs).get l) :
    s ∈ a.get l ∧ ∀ p ∈ pairs, p.1.kind = .def → s ≠ .vreg p.1.vreg := by
  have h := AState.mem_get_map h
  simp only [List.mem_filter, Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true,
    beq_iff_eq, not_and] at h
  exact ⟨h.1, fun p hp hk e => h.2 p hp hk e⟩

theorem Inv_forgetDefs {a : AState} {pairs : List (Operand × Loc)} {m : Loc → V} {ρ ρ' : Nat → V}
    {r₀ : Reg → V} (h : Inv keep a m ρ r₀)
    (hρ : ∀ u, (∀ p ∈ pairs, p.1.kind = .def → u ≠ p.1.vreg) → ρ u = ρ' u) :
    Inv keep (forgetDefs a pairs) m ρ' r₀ := by
  intro l s hs
  obtain ⟨hs, hn⟩ := AState.mem_get_forgetDefs hs
  have := h l s hs
  cases s with
  | vreg u =>
    simp only [Holds] at this ⊢
    rw [this, hρ u (fun p hp hk e => hn p hp hk (by rw [e]))]
  | entry r => exact this

theorem forgetDefs_eq_forgetOps (a : AState) (pairs : List (Operand × Loc)) :
    forgetDefs a pairs = forgetOps a (pairs.map (·.1)) := by
  simp [forgetDefs, forgetOps, List.any_map, Function.comp_def]

/-- Forgetting defs keeps the invariant (for a file agreeing on the vregs not forgotten). -/
theorem Inv_forgetOps {a : AState} {os : List Operand} {m : Loc → V} {ρ ρ' : Nat → V}
    {r₀ : Reg → V} (h : Inv keep a m ρ r₀)
    (hρ : ∀ u, (∀ o ∈ os, o.kind = .def → u ≠ o.vreg) → ρ u = ρ' u) :
    Inv keep (forgetOps a os) m ρ' r₀ := by
  have e : forgetOps a os = forgetDefs a (os.map fun o => (o, Loc.reg (.x 0))) := by
    rw [forgetDefs_eq_forgetOps, List.map_map]
    simp [Function.comp_def]
  rw [e]
  refine Inv_forgetDefs h fun u hu => hρ u fun o ho hk => ?_
  exact hu (o, Loc.reg (.x 0)) (List.mem_map_of_mem ho) hk

/-- The abstract state after instruction `i` (operands `ops`) with control outcome `ctl`, from
its transfer `a`: the defs past `havocFrom` that `transferOp` keeps (the exception payload defs
of a `try_call`'s call, on its normal return) forgotten — the checker forgets them on that edge
(`CheckCtx.edgeForget`). -/
def tryForget (i : MInst) (ctl : Ctl) (ops : Array Operand) (a : AState) : AState :=
  match i.keptDefs, havocFrom i ctl with
  | none, some n => forgetOps a ((ops.toList.filter (·.kind == .def)).drop n)
  | _, _ => a

theorem tryForget_of_ne {i : MInst} {ctl : Ctl} (h : ∀ j, ctl ≠ .goto j) (ops : Array Operand)
    (a : AState) : tryForget i ctl ops a = a := by
  unfold tryForget havocFrom
  cases i.keptDefs with
  | some n => rfl
  | none =>
    cases i.normalDead with
    | none => rfl
    | some p => cases ctl with
      | goto j => exact absurd rfl (h j)
      | _ => rfl

/-- The checker's step of an original instruction is sound: the allocated code reads the
values the VCode reads, and the invariant holds after the instruction (early defs, clobbers,
late defs; the havocked defs `outs'`, past `havocFrom`, are forgotten: by the transfer for a
branch's defs and the LL/SC loops' scratch registers, by `tryForget` for a `try_call`'s
exception payloads on its normal return). -/
theorem op_sound {w : String} {i : MInst} {ops : Array Operand} {allocs : Array Loc}
    {a a' : AState} (hstep : c.stepOp w i ops allocs a = .ok a')
    {m : Loc → V} {ρ : Nat → V} {r₀ : Reg → V} (hinv : Inv keep a m ρ r₀)
    {outs outs' : List V} (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    {ctl : Ctl} (hho : HavocOuts i ctl outs outs') {m2 : Loc → V}
    (hclob : Clobbered keep i.clobbers
      (writeM m ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs').filter (·.1.1.isEarly))) m2) :
    ops.size = allocs.size ∧
    ((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2) =
      (ops.toList.filter Operand.isUse).map (ρ ·.vreg) ∧
    Inv keep (tryForget i ctl ops a')
      (writeM m2 ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs').filter (·.1.1.isLate)))
      (writeV (writeV ρ (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isEarly)))
        (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isLate))) r₀ ∧
    (∀ us, i = .rets us → ∀ r ∈ calleeSaved, Sym.entry r ∈ a'.get (.reg r)) := by
  obtain ⟨hst, hE, hL, rfl, hret⟩ := stepOp_ok hstep
  obtain ⟨hsz, hdisj⟩ := checkStatic_ok hst
  have hlen' : outs'.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length := by
    rw [hho.1, hlen]
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
      ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs').filter (·.1.1.isEarly)) hinv
    rw [defs_early hlen', ← defs_vcode hsz outs' Operand.isEarly] at h1
    have h2 := Inv_clobberAll h1 hclob
    have h3 := Inv_defineAll
      ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs').filter (·.1.1.isLate)) h2
    rw [defs_late hlen', ← defs_vcode hsz outs' Operand.isLate] at h3
    -- forgetting the defs past `nk`, where both def lists agree on the first `nk`
    have key : ∀ nk, outs'.take nk = outs.take nk → Inv keep
        (forgetDefs (defineAll (clobberAll (defineAll a (atPos (ops.zip allocs).toList .def .early))
          i.clobbers) (atPos (ops.zip allocs).toList .def .late))
          (((ops.zip allocs).toList.filter (·.1.kind == .def)).drop nk))
        (writeM m2 ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs').filter (·.1.1.isLate)))
        (writeV (writeV ρ (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isEarly)))
          (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isLate))) r₀ := by
      intro nk htk
      refine Inv_forgetDefs h3 fun u hu => ?_
      -- `u` is no forgotten def's vreg: the kept defs (the first `nk`) have the same values in
      -- both files
      have hD : ∀ (k : Nat) (d : Operand), (ops.toList.filter Operand.isDef)[k]? = some d →
          d.vreg = u → outs'[k]? = outs[k]? := by
        intro k d hd hdu
        by_cases hkn : k < nk
        · have := congrArg (·[k]?) htk
          simpa [List.getElem?_take, hkn] using this
        · exfalso
          have hfst := pairs_fst hsz Operand.isDef
          have hk' : (((ops.zip allocs).toList.filter (·.1.isDef)).map Prod.fst)[k]? = some d := by
            rw [hfst]; exact hd
          rw [List.getElem?_map] at hk'
          obtain ⟨pp, hpp, rfl⟩ := Option.map_eq_some_iff.mp hk'
          have hmem : pp ∈ ((ops.zip allocs).toList.filter (·.1.kind == .def)).drop nk := by
            have e : (((ops.zip allocs).toList.filter (·.1.kind == .def)).drop nk)[k - nk]? =
                some pp := by
              rw [List.getElem?_drop, show nk + (k - nk) = k by omega]
              simpa [Operand.isDef] using hpp
            exact List.mem_of_getElem? e
          have hkd : pp.1.kind = .def := by
            have := List.mem_of_getElem? hpp
            simpa [Operand.isDef] using (List.mem_filter.mp this).2
          exact hu pp hmem hkd hdu.symm
      have hl : outs'.length = outs.length := hho.1
      exact writeV_zip_filter_congr _ u _ _ _ _ _
        (writeV_zip_filter_congr _ u _ _ _ ρ ρ rfl hl hD) hl hD
    cases hk : i.keptDefs with
    | none =>
      cases hh : havocFrom i ctl with
      | none =>
        have e := hho.2.1 hh
        subst e
        simpa only [tryForget, transferOp, hk, hh] using h3
      | some n =>
        have e : forgetOps (defineAll (clobberAll (defineAll a (atPos (ops.zip allocs).toList .def
            .early)) i.clobbers) (atPos (ops.zip allocs).toList .def .late))
            ((ops.toList.filter (·.kind == .def)).drop n) =
            forgetDefs (defineAll (clobberAll (defineAll a (atPos (ops.zip allocs).toList .def
            .early)) i.clobbers) (atPos (ops.zip allocs).toList .def .late))
            (((ops.zip allocs).toList.filter (·.1.kind == .def)).drop n) := by
          rw [forgetDefs_eq_forgetOps, List.map_drop]
          congr 2
          exact (pairs_fst hsz (·.kind == .def)).symm
        simp only [tryForget, transferOp, hk, hh]
        rw [e]
        exact key n (hho.2.2 n hh)
    | some nk =>
      have hh : havocFrom i ctl = some nk := by simp [havocFrom, hk]
      simp only [tryForget, transferOp, hk]
      exact key nk (hho.2.2 nk hh)
  · intro us hi
    subst hi
    simpa [transferOp, tryForget, havocFrom, MInst.keptDefs, MInst.normalDead, MInst.isBranch]
      using retCheck_ok hret

/-- **The edge from a terminator**: the invariant after terminator `i` (instruction `k`, the
last, of block `b`) with outcome `goto j` (`tryForget`) gives the invariant of the state
entering the successor `s` before the parallel copy (`CheckCtx.edgeForget`): both forget a
`try_call`'s exception payload defs on the normal-return edge; when `s` is the normal-return
successor reached by another successor number, `edgeForget` forgets more. -/
theorem edgeForget_inv {preds : Array (Array Nat)} (hcfg : c.vc.cfg = .ok (c.succs, preds))
    {b k j s : Nat} {vb : VBlock} {i : MInst} {ops : Array Operand} {a : AState}
    {m : Loc → V} {ρ : Nat → V} {r₀ : Reg → V}
    (hvb : c.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hk1 : k + 1 = vb.insts.size)
    (hops : i.operands = .ok ops) (hsucc : succOf c.vc b j = some s)
    (h : Inv keep (tryForget i (.goto j) ops a) m ρ r₀) : Inv keep (c.edgeForget b s a) m ρ r₀ := by
  have hback : vb.insts.back? = some i := by
    rw [Array.back?_eq_getElem?, show vb.insts.size - 1 = k by omega, hi]
  have hsucc' : c.succs[b]?.bind (·[j]?) = some s := by simpa [succOf, hcfg] using hsucc
  unfold CheckCtx.edgeForget
  simp only [hvb, hback]
  cases hnd : i.normalDead with
  | none =>
    have e : tryForget i (.goto j) ops a = a := by
      unfold tryForget havocFrom
      cases i.keptDefs <;> simp [hnd]
    rwa [e] at h
  | some p =>
    obtain ⟨j0, n⟩ := p
    have hkd : i.keptDefs = none := by
      cases i <;> simp_all [MInst.normalDead, MInst.keptDefs, MInst.isBranch]
    simp only [hops]
    by_cases hj : j = j0
    · subst hj
      simp only [hsucc', ↓reduceIte]
      have e : tryForget i (.goto j) ops a = forgetOps a ((ops.toList.filter (·.kind == .def)).drop n) := by
        simp [tryForget, havocFrom, hkd, hnd]
      rwa [e] at h
    · have e : tryForget i (.goto j) ops a = a := by
        simp [tryForget, havocFrom, hkd, hnd, hj]
      rw [e] at h
      split
      · exact Inv_forgetOps h fun _ _ => rfl
      · exact h

end

end Backend.Proof
