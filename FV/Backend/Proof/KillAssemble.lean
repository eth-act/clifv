import FV.Backend.Proof.KillBase
import FV.Backend.Proof.SpillEdgesLow
import FV.Backend.Proof.SpillStep4Cfg
import FV.Backend.Proof.SpillLocalCheck
import FV.Backend.Proof.SpillStep4State
import FV.Backend.Proof.IselCtlCallRules

/-!
# Killed vregs of `lowerFunction`'s VCode: the driver's assembly (V4, `SpillKillFree`)

`killFreeB_lower`: from the run facts `KillRunsHyp` and the exact defs of a `try_call`'s call
(`TryDefsExact`), `lowerFunction`'s VCode passes `Spill.killFreeB`.
-/

namespace Backend.Proof.Kill

open Backend Backend.Proof Backend.Proof.Spill Backend.Proof.Driver

/-! ## Instructions -/

theorem asm_isTerminator_mapRegs (g : Reg → Reg) (m : MInst) :
    (m.mapRegs g).isTerminator = m.isTerminator := by
  cases m <;> rfl

theorem asm_keptDefs_mapRegs (g : Reg → Reg) (m : MInst) :
    (m.mapRegs g).keptDefs = m.keptDefs := by
  cases m <;> rfl

theorem asm_normalDead_mapRegs (g : Reg → Reg) (m : MInst) :
    (m.mapRegs g).normalDead = m.normalDead := by
  cases m <;> rfl

/-- An instruction that is no terminator and keeps all its defs kills nothing. -/
theorem asm_unstored_nil {m : MInst} (h1 : m.isTerminator = false) (h2 : m.keptDefs = none) :
    unstored m = [] := by
  unfold unstored
  split
  · rfl
  · rw [List.filter_eq_nil_iff]
    intro v hv
    simp only [storedDefs, h1, h2, Bool.false_eq_true, ite_false]
    simp [hv]

theorem asm_filter_rn (gn : Nat → Nat) (ops : Array Operand) (k : OpKind) :
    ((ops.map (rnOp gn)).toList.filter (·.kind == k)).map (·.vreg) =
      ((ops.toList.filter (·.kind == k)).map (·.vreg)).map gn := by
  rw [Array.toList_map, List.filter_map]
  simp only [List.map_map]
  rfl

theorem asm_storedDefs_rn {g : Reg → Reg} (gn : Nat → Nat) (m : MInst) (ops : Array Operand) :
    storedDefs (m.mapRegs g) (ops.map (rnOp gn)) = (storedDefs m ops).map gn := by
  unfold storedDefs
  rw [asm_isTerminator_mapRegs, asm_keptDefs_mapRegs]
  split
  · rfl
  · have e : (ops.map (rnOp gn)).toList.filter (·.kind == .def) =
        (ops.toList.filter (·.kind == .def)).map (rnOp gn) := by
      rw [Array.toList_map, List.filter_map]; rfl
    rw [e]
    split <;> simp [List.map_map, List.map_take] <;> intros <;> rfl

/-- What a renamed instruction kills is the renaming of what it kills. -/
theorem asm_unstored_mapRegs {g : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming g gn) {m : MInst}
    {k : Nat} (h : k ∈ unstored (m.mapRegs g)) : ∃ k0 ∈ unstored m, k = gn k0 := by
  unfold unstored at h ⊢
  rw [operands_mapRegs hg] at h
  cases hm : m.operands with
  | error e => rw [hm] at h; cases h
  | ok ops =>
    rw [hm] at h
    simp only [Except.map] at h
    rw [asm_storedDefs_rn, asm_filter_rn, List.mem_filter] at h
    obtain ⟨hk, hn⟩ := h
    obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk
    refine ⟨k0, List.mem_filter.mpr ⟨hk0, ?_⟩, rfl⟩
    cases hc : (storedDefs m ops).contains k0
    · rfl
    · exfalso
      simp at hn
      exact hn k0 (by simpa using hc) rfl

/-- What a renamed instruction reads is the renaming of what it reads. -/
theorem asm_useVregs_mapRegs {g : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming g gn) {m : MInst}
    {u : Nat} (h : u ∈ useVregs (m.mapRegs g)) : ∃ u0 ∈ useVregs m, u = gn u0 := by
  unfold useVregs at h ⊢
  rw [operands_mapRegs hg] at h
  cases hm : m.operands with
  | error e => rw [hm] at h; cases h
  | ok ops =>
    rw [hm] at h
    simp only [Except.map] at h
    rw [asm_filter_rn] at h
    obtain ⟨u0, hu0, rfl⟩ := List.mem_map.mp h
    exact ⟨u0, hu0, rfl⟩

theorem asm_jump (l : Label) : unstored (.jump l) = [] ∧ useVregs (.jump l) = [] := ⟨rfl, rfl⟩

theorem asm_load (op : LoadOp) (n : Nat) (o : Int) (fl : Clif.MemFlags) :
    useVregs (.load op (.vreg n .int) (.fpOffset o) fl) = [] := rfl

theorem asm_collect_real {sp : OpSpec} {r : Reg} (hr : ∀ n c, r ≠ .vreg n c) {s s' : Array Operand}
    {a : Reg} (h : (collectOp sp r).run s = .ok (a, s')) : s' = s := by
  cases r with
  | vreg n c => exact absurd rfl (hr n c)
  | _ =>
    simp only [collectOp] at h
    split at h
    · cases h
    · cases h; rfl

theorem asm_mov_uses (s : OperandSize) (r : Nat) (out : Reg) (hout : ∀ n c, out ≠ .vreg n c) :
    useVregs (.mov s (.vreg r .int) out) = [] := by
  unfold useVregs
  rw [operands_eq]
  simp only [MInst.visitOperands, StateT.run_bind]
  have h1 : (collectOp OpSpec.def_ (Reg.vreg r .int)).run #[] =
      .ok (.vreg r .int, #[⟨r, .int, OpSpec.def_.kind, OpSpec.def_.pos, OpSpec.def_.con⟩]) := rfl
  rw [h1, Driver.except_ok_bind]
  cases h2 : (collectOp OpSpec.use out).run
      #[⟨r, .int, OpSpec.def_.kind, OpSpec.def_.pos, OpSpec.def_.con⟩] with
  | error e => rfl
  | ok p =>
    obtain ⟨a, s'⟩ := p
    have := asm_collect_real hout h2
    subst this
    rfl


theorem asm_collect_kind {sp : OpSpec} {r : Reg} {s s' : Array Operand} {a : Reg} {k : OpKind}
    (h : (collectOp sp r).run s = .ok (a, s')) (hk : sp.kind ≠ k) :
    s'.toList.filter (·.kind == k) = s.toList.filter (·.kind == k) := by
  cases r with
  | vreg n c =>
    simp only [collectOp, StateT.run, modify, modifyGet, MonadStateOf.modifyGet] at h
    cases h
    simp [List.filter_append, hk]
  | _ =>
    simp only [collectOp] at h
    split at h
    · cases h
    · cases h; rfl

theorem asm_mapM_def : ∀ (l : List (Reg × Reg)) (s s' : Array Operand) (a : List (Reg × Reg)),
    (l.mapM (fun (x : Reg × Reg) => do
      let r ← collectOp (OpSpec.fixedDef x.2) x.1; pure (r, x.2))).run s = .ok (a, s') →
    s'.toList.filter (·.kind == .use) = s.toList.filter (·.kind == .use)
  | [], s, s', a, h => by cases h; rfl
  | q :: l, s, s', a, h => by
    simp only [List.mapM_cons, StateT.run_bind] at h
    cases h1 : (collectOp (OpSpec.fixedDef q.2) q.1).run s with
    | error e => rw [h1] at h; cases h
    | ok p =>
      obtain ⟨r, s1⟩ := p
      rw [h1, Driver.except_ok_bind, StateT.run_pure, Driver.except_pure,
        Driver.except_ok_bind] at h
      cases h2 : (l.mapM (fun (x : Reg × Reg) => do
          let r ← collectOp (OpSpec.fixedDef x.2) x.1; pure (r, x.2))).run s1 with
      | error e => rw [h2] at h; cases h
      | ok p2 =>
        obtain ⟨a2, s2⟩ := p2
        rw [h2, Driver.except_ok_bind] at h
        cases h
        rw [asm_mapM_def l s1 s2 a2 h2, asm_collect_kind h1 (by simp [OpSpec.fixedDef])]

theorem asm_args_uses (ps : List (Reg × Reg)) : useVregs (.args ps) = [] := by
  unfold useVregs
  rw [operands_eq]
  simp only [MInst.visitOperands, StateT.run_bind]
  cases h : (ps.mapM (fun (x : Reg × Reg) => do
      let r ← collectOp (OpSpec.fixedDef x.2) x.1; pure (r, x.2))).run #[] with
  | error e => rfl
  | ok p =>
    obtain ⟨a, s'⟩ := p
    have := asm_mapM_def ps #[] s' a h
    simp only [Driver.except_ok_bind, StateT.run_pure, Driver.except_pure]
    show ((s'.toList.filter (·.kind == .use)).map (·.vreg)) = []
    rw [this]; rfl


theorem asm_mapM_use : ∀ (l : List (Reg × Reg)) (s s' : Array Operand) (a : List (Reg × Reg)),
    (l.mapM (fun (x : Reg × Reg) => do
      let r ← collectOp (OpSpec.fixedUse x.2) x.1; pure (r, x.2))).run s = .ok (a, s') →
    s'.toList.filter (·.kind == .def) = s.toList.filter (·.kind == .def)
  | [], s, s', a, h => by cases h; rfl
  | q :: l, s, s', a, h => by
    simp only [List.mapM_cons, StateT.run_bind] at h
    cases h1 : (collectOp (OpSpec.fixedUse q.2) q.1).run s with
    | error e => rw [h1] at h; cases h
    | ok p =>
      obtain ⟨r, s1⟩ := p
      rw [h1, Driver.except_ok_bind, StateT.run_pure, Driver.except_pure,
        Driver.except_ok_bind] at h
      cases h2 : (l.mapM (fun (x : Reg × Reg) => do
          let r ← collectOp (OpSpec.fixedUse x.2) x.1; pure (r, x.2))).run s1 with
      | error e => rw [h2] at h; cases h
      | ok p2 =>
        obtain ⟨a2, s2⟩ := p2
        rw [h2, Driver.except_ok_bind] at h
        cases h
        rw [asm_mapM_use l s1 s2 a2 h2, asm_collect_kind h1 (by simp [OpSpec.fixedUse])]

theorem filter_isDef_callDefOps' (D : List (Reg × Nat)) :
    (callDefOps D).filter (·.kind == .def) = callDefOps D := by
  induction D with
  | nil => rfl
  | cons q D ih => simp only [callDefOps, List.map_cons] at ih ⊢; rw [List.filter_cons_of_pos rfl, ih]

/-- The def operands of a call with defs `callDefs D`. -/
theorem asm_call_defs {c : CallInfo} {D : List (Reg × Nat)} (hD : c.defs = callDefs D)
    {ops : Array Operand} (h : (MInst.call c).operands = .ok ops) :
    ops.toList.filter (·.kind == .def) = callDefOps D := by
  obtain ⟨dest, uses, defs⟩ := c
  simp only at hD
  subst hD
  rw [operands_eq] at h
  have fin : ∀ (s0 : Array Operand), s0.toList.filter (·.kind == .def) = [] →
      ∀ (s1 : Array Operand) (a : List (Reg × Reg)),
      (uses.mapM (fun (x : Reg × Reg) => do
        let r ← collectOp (OpSpec.fixedUse x.2) x.1; pure (r, x.2))).run s0 = .ok (a, s1) →
      (s1 ++ (callDefOps D).toArray) = ops →
      ops.toList.filter (·.kind == .def) = callDefOps D := by
    intro s0 h0 s1 a hu he
    subst he
    rw [Array.toList_append, List.filter_append, asm_mapM_use uses s0 s1 a hu, h0, List.nil_append,
      List.toList_toArray, filter_isDef_callDefOps' D]
  cases dest with
  | sym nm =>
    simp only [MInst.visitOperands, StateT.run_bind, StateT.run_pure, Driver.except_pure,
      Driver.except_ok_bind] at h
    cases hu : (uses.mapM (fun (x : Reg × Reg) => do
        let r ← collectOp (OpSpec.fixedUse x.2) x.1; pure (r, x.2))).run #[] with
    | error e => rw [hu] at h; cases h
    | ok p =>
      obtain ⟨a, s1⟩ := p
      rw [hu, Driver.except_ok_bind, mapM_callDefs, Driver.except_ok_bind] at h
      exact fin #[] rfl s1 a hu (by
        simpa only [Driver.except_pure, Driver.except_ok_bind, Except.ok.injEq] using h)
  | reg r =>
    simp only [MInst.visitOperands, StateT.run_bind, StateT.run_pure] at h
    cases hr : (collectOp OpSpec.use r).run #[] with
    | error e => rw [hr] at h; cases h
    | ok p0 =>
      obtain ⟨r', s0⟩ := p0
      have h0 : s0.toList.filter (·.kind == .def) = [] := by
        rw [asm_collect_kind hr (by simp [OpSpec.use])]; rfl
      rw [hr, Driver.except_ok_bind, Driver.except_pure, Driver.except_ok_bind] at h
      cases hu : (uses.mapM (fun (x : Reg × Reg) => do
          let r ← collectOp (OpSpec.fixedUse x.2) x.1; pure (r, x.2))).run s0 with
      | error e => rw [hu] at h; cases h
      | ok p =>
        obtain ⟨a, s1⟩ := p
        rw [hu, Driver.except_ok_bind, mapM_callDefs, Driver.except_ok_bind] at h
        exact fin s0 h0 s1 a hu (by
          simpa only [Driver.except_pure, Driver.except_ok_bind, Except.ok.injEq] using h)


theorem asm_unstored_sub {m : MInst} {k : Nat} (h : k ∈ unstored m) :
    ∃ ops, m.operands = .ok ops ∧ k ∈ (ops.toList.filter (·.kind == .def)).map (·.vreg) := by
  unfold unstored at h
  split at h
  · cases h
  · rename_i ops hops
    exact ⟨ops, hops, (List.mem_filter.mp h).1⟩

theorem asm_callDefOps_vregs (D : List (Reg × Nat)) : (callDefOps D).map (·.vreg) = D.map (·.2) := by
  simp [callDefOps]

theorem asm_outDefs_vregs (b n : Nat) : (outDefs b n).map (·.2) = (List.range n).map (b + ·) := by
  simp [outDefs]

/-! ## The alias chase -/

theorem asm_chase (sf : Nat → Option Nat) : ∀ k n, chaseF sf k n = n ∨ ∃ m, sf m = some (chaseF sf k n)
  | 0, n => .inl rfl
  | k + 1, n => by
    cases h : sf n with
    | none => left; simp [chaseF, h]
    | some o =>
      have e1 : chaseF sf (k + 1) n = chaseF sf k o := by simp [chaseF, h]
      rw [e1]
      rcases asm_chase sf k o with e | ⟨m, hm⟩
      · exact .inr ⟨n, by rw [h, e]⟩
      · exact .inr ⟨m, hm⟩

/-! ## The entry stores of a `try_call`'s successor -/

theorem asm_zip_filter {α β : Type} (p : α → Bool) : ∀ (l : List α) (l' : List β),
    l.length ≤ l'.length → ((l.zip l').filter (fun q => p q.1)).map Prod.fst = l.filter p
  | [], _, _ => rfl
  | a :: l, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.zip_cons_cons, List.filter_cons]
    have ih := asm_zip_filter p l l' (by simp at h; omega)
    split <;> simp [ih]

/-- The vregs a `try_call` block's terminator leaves live on the edge to successor `j`. -/
theorem asm_termEdge_try {vb : VBlock} {c : CallInfo} {ti : TryInfo}
    (hb : vb.insts.back? = some (.tryCall c ti)) {ops : Array Operand}
    (hops : (MInst.tryCall c ti).operands = .ok ops) {D : List (Reg × Nat)}
    (hD : ops.toList.filter (·.kind == .def) = callDefOps D) (j : Nat) :
    (termEdgeDefs vb j).map (·.1.vreg) =
      if j = ti.handlers.length then (D.map (·.2)).take ti.rets else D.map (·.2) := by
  have hk : (keptPairs (.tryCall c ti) (ops.zip (spillLocs ops (MInst.tryCall c ti).clobbers)).toList).map
      (·.1.vreg) = D.map (·.2) := by
    simp only [keptPairs, MInst.keptDefs, MInst.isBranch, Bool.false_eq_true, ite_false]
    rw [Array.toList_zip, ← asm_callDefOps_vregs, ← hD,
      ← asm_zip_filter (fun o : Operand => o.kind == .def) ops.toList
        (spillLocs ops (MInst.tryCall c ti).clobbers).toList
        (by simp [spillLocs_size]), List.map_map]
    rfl
  unfold termEdgeDefs
  rw [hb]
  simp only [MInst.isTerminator, MInst.isBranch, MInst.isRet, Bool.false_or, Bool.not_true,
    Bool.false_eq_true, ite_false, hops, MInst.normalDead]
  by_cases hj : j = ti.handlers.length
  · simp only [hj, beq_self_eq_true, ite_true]
    rw [List.map_take, hk]
  · simp only [hj, ite_false]
    rw [show (j == ti.handlers.length) = false from by simpa using hj]
    exact hk


/-! ## The run segments of the recorded lowering -/

/-- A run segment of block `bi` (lowered as `L`): a statement's code (vregs `[lo, hi)`), or the
terminator's code (vregs `[lo, hi)`; a `try_call`'s results `[lo, mid)`, its rule's `[mid, hi)`). -/
def SegIn (bl : List BLow) (bi : Nat) (L : BLow) (lo mid hi : Nat) (code : List MInst) : Prop :=
  bl[bi]? = some L ∧
  ((∃ (j : Nat) (sl : SLow), L.sl[j]? = some sl ∧ lo = sl.st.nextVreg ∧ mid = lo ∧ hi = sl.st'.nextVreg ∧
      code = sl.st'.emitted.toList) ∨
    (lo = L.tst.nextVreg ∧ hi = L.tst'.nextVreg ∧
      mid = (match L.tl with | some T => T.st1.nextVreg | none => lo) ∧
      code = fixTry L.tl L.tst'.emitted.toList))

/-- A run segment of the recorded lowering. -/
def Seg (f : Clif.Function) (bl : List BLow) (lo mid hi : Nat) (code : List MInst) : Prop :=
  ∃ bi B L, f.blocks[bi]? = some B ∧ SegIn bl bi L lo mid hi code

section Disj
variable {v : Nat} {bl : List BLow}
  (hO1 : ∀ (bi : Nat) (L : BLow), bl[bi]? = some L → BlockOrd v L)
  (hO2 : ∀ (bi bi' : Nat) (L L' : BLow), bi < bi' → bl[bi]? = some L → bl[bi']? = some L' →
    BlockOrd L.tst'.nextVreg L')

include hO1 in
theorem segIn_hi {bi : Nat} {L : BLow} {lo mid hi : Nat} {c : List MInst}
    (h : SegIn bl bi L lo mid hi c) : hi ≤ L.tst'.nextVreg := by
  obtain ⟨hL, ⟨j, sl, hsl, -, -, rfl, -⟩ | ⟨-, rfl, -, -⟩⟩ := h
  · have := (hO1 bi L hL).stmt j sl hsl
    have := (hO1 bi L hL).term
    omega
  · exact Nat.le_refl _

include hO2 in
theorem segIn_lo {bi bi' : Nat} {L L' : BLow} {lo mid hi : Nat} {c : List MInst} (hlt : bi < bi')
    (hL : bl[bi]? = some L) (h : SegIn bl bi' L' lo mid hi c) : L.tst'.nextVreg ≤ lo := by
  obtain ⟨hL', ⟨j, sl, hsl, rfl, -, -, -⟩ | ⟨rfl, -, -, -⟩⟩ := h
  · exact ((hO2 bi bi' L L' hlt hL hL').stmt j sl hsl).1
  · exact (hO2 bi bi' L L' hlt hL hL').term.1

include hO1 in
theorem segIn_same {bi : Nat} {L L' : BLow} {lo mid hi lo' mid' hi' x : Nat} {c c' : List MInst}
    (h : SegIn bl bi L lo mid hi c) (h' : SegIn bl bi L' lo' mid' hi' c') (h1 : lo ≤ x) (h2 : x < hi)
    (h1' : lo' ≤ x) (h2' : x < hi') : c = c' := by
  obtain ⟨hL, hc⟩ := h
  obtain ⟨hL', hc'⟩ := h'
  rw [hL] at hL'
  cases hL'
  have hB := hO1 bi L hL
  rcases hc with ⟨j, sl, hsl, rfl, -, rfl, rfl⟩ | ⟨rfl, rfl, -, rfl⟩ <;>
    rcases hc' with ⟨j', sl', hsl', rfl, -, rfl, rfl⟩ | ⟨rfl, rfl, -, rfl⟩
  · rcases Nat.lt_trichotomy j j' with hj | rfl | hj
    · have := (hB.stmt j sl hsl).2.2.2 j' sl' hj hsl'
      omega
    · rw [hsl] at hsl'; cases hsl'; rfl
    · have := (hB.stmt j' sl' hsl').2.2.2 j sl hj hsl
      omega
  · have := (hB.stmt j sl hsl).2.2.1
    omega
  · have := (hB.stmt j' sl' hsl').2.2.1
    omega
  · rfl

include hO1 hO2 in
/-- **Run segments are disjoint**: a vreg in the ranges of two segments names one segment. -/
theorem seg_disj {f : Clif.Function} {lo mid hi lo' mid' hi' x : Nat} {c c' : List MInst}
    (h : Seg f bl lo mid hi c) (h' : Seg f bl lo' mid' hi' c') (h1 : lo ≤ x) (h2 : x < hi)
    (h1' : lo' ≤ x) (h2' : x < hi') : c = c' := by
  obtain ⟨bi, B, L, -, hs⟩ := h
  obtain ⟨bi', B', L', -, hs'⟩ := h'
  rcases Nat.lt_trichotomy bi bi' with hlt | rfl | hlt
  · have := segIn_hi hO1 hs
    have := segIn_lo hO2 hlt hs.1 hs'
    omega
  · exact segIn_same hO1 hs hs' h1 h2 h1' h2'
  · have := segIn_hi hO1 hs'
    have := segIn_lo hO2 hlt hs'.1 hs
    omega

end Disj


/-! ## The segments' facts -/

/-- **The exact defs of a `try_call`'s call** (an open hypothesis, alongside `KillRunsHyp`): in
a `try_call`'s `lower_branch` run (as in `KillRunsHyp`'s third clause), every emitted call
defines `x j ↦ vreg (lo.nextVreg + j)` for `j < max n 2` (`n` the ABI returns): the return vregs
in order, then the payload vregs (`gen_try_call_rets`, `tryDefs_eq`). The membership of the defs
in the result vregs (`KillRunsHyp`) does not suffice: the normal edge keeps only the first
`n` defs (`MInst.normalDead`), so a permuted def list would kill a passed return value. -/
def TryDefsExact : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState),
    Dominated f → LowerScope f → AbiSigsOk f → buildCtx f = .ok (ctx, ranges, st0) →
    ∀ ti t et data sig items lo trs st1 targets out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → IsTryWith t et → (∃ B ∈ f.blocks, B.term = t) →
      tryCallData f t = .ok data → exnTableOpnd f et = .ok (sig, items) →
      ctx.valDef.size ≤ lo.nextVreg → tryRegsOf sig lo = some (trs, st1) →
      tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (out, s', tr) →
      ∀ m ∈ s'.emitted.toList, ∀ c, m = .call c →
        c.defs = callDefs (outDefs lo.nextVreg (max (sigRets sig).length 2))

theorem asm_mem_killedL {ms : List MInst} {m : MInst} (hm : m ∈ ms) {k : Nat} (hk : k ∈ unstored m) :
    k ∈ killedL ms :=
  List.mem_flatMap.mpr ⟨m, hm, hk⟩

/-- `RunKill` from a state with nothing emitted, on the emitted code. -/
theorem asm_runKill {nV lo : Nat} {s s' : LState} (h : RunKill nV lo s s') (he : s.emitted = #[]) :
    (∀ m ∈ s'.emitted.toList, ∀ k ∈ unstored m, lo ≤ k ∧ k < s'.nextVreg) ∧
    ∀ m ∈ s'.emitted.toList, ∀ u ∈ useVregs m, (u < nV ∨ (lo ≤ u ∧ u < s'.nextVreg)) ∧
      ∀ m' ∈ s'.emitted.toList, u ∉ unstored m' := by
  obtain ⟨ms, hms, -, hk, hu⟩ := h
  rw [he, Array.empty_append] at hms
  have e : s'.emitted.toList = ms := by rw [hms]
  rw [e]
  exact ⟨fun m hm k hkm => hk k (asm_mem_killedL hm hkm),
    fun m hm u huu => ⟨(hu m hm u huu).1, fun m' hm' hu' => (hu m hm u huu).2 (asm_mem_killedL hm' hu')⟩⟩

theorem asm_useVregs_tryCall (c : CallInfo) (ti : TryInfo) :
    useVregs (.tryCall c ti) = useVregs (.call c) := by
  unfold useVregs; rw [operands_tryCall_call]

theorem asm_unstored_tryCall {c : CallInfo} {ti : TryInfo} {D : List (Reg × Nat)}
    (hD : c.defs = callDefs D) {k : Nat} (hk : k ∈ unstored (.tryCall c ti)) : k ∈ D.map (·.2) := by
  obtain ⟨ops, hops, hk⟩ := asm_unstored_sub hk
  rw [operands_tryCall_call] at hops
  rw [asm_call_defs hD hops, asm_callDefOps_vregs] at hk
  exact hk

section Segs
variable {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
  {bl : List BLow}
  (hd : Dominated f) (hs : LowerScope f) (ha : AbiSigsOk f)
  (hb : buildCtx f = .ok (ctx, ranges, st0))
  (hlb : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
    some bl)
  (hlf : LoopFacts f ctx bl)
include hd hs ha hb hlb hlf

/-- **A run segment's killed vregs and uses**: it kills vregs of its range; it reads vregs of
CLIF values, or of its rule's range that it does not kill. -/
theorem seg_ok (hK : KillRunsHyp) (hX : TryDefsExact) {lo mid hi : Nat} {c : List MInst}
    (h : Seg f bl lo mid hi c) :
    ctx.valDef.size ≤ lo ∧ lo ≤ mid ∧ (∀ m ∈ c, ∀ k ∈ unstored m, lo ≤ k ∧ k < hi) ∧
      ∀ m ∈ c, ∀ u ∈ useVregs m,
        u < ctx.valDef.size ∨ (mid ≤ u ∧ u < hi ∧ ∀ m' ∈ c, u ∉ unstored m') := by
  obtain ⟨hS, hT, hY⟩ := hK f ctx ranges st0 hd hs ha hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  obtain ⟨hord, -⟩ := driver_ord hlb
  have hN : st0.nextVreg = ctx.valDef.size := hcf.size.1
  obtain ⟨bi, B, L, hB, hL, hc⟩ := h
  obtain ⟨-, hcs, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
  rcases hc with ⟨j, sl, hsl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, hmid, rfl⟩
  · -- a statement
    have hj : j < B.body.length := by
      rw [← (hspec bi B L hB hL).1]; exact (List.getElem?_eq_some_iff.mp hsl).1
    obtain ⟨stm, hstm⟩ : ∃ stm, B.body[j]? = some stm := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨info, hinf, hic, -⟩ := hcf.stmt bi B j stm hB hstm
    obtain ⟨tr, hrun⟩ := hcs j sl hsl
    rw [hstart bi L hL] at hrun
    have hge : ctx.valDef.size ≤ sl.st.nextVreg := hN ▸ ((hord bi L hL).stmt j sl hsl).1
    obtain ⟨hk, -⟩ := hS _ info stm.inst _ _ _ _ hinf hic hge hrun
    obtain ⟨h1, h2⟩ := asm_runKill hk (hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl))
    refine ⟨hge, Nat.le_refl _, h1, fun m hm u hu => ?_⟩
    rcases (h2 m hm u hu).1 with h3 | h3
    · exact .inl h3
    · exact .inr ⟨h3.1, h3.2, (h2 m hm u hu).2⟩
  · -- the terminator
    have hph := hcf.term bi B hB
    rw [← hstart bi L hL] at hph
    have hti := (Array.getElem?_eq_some_iff.mp hph).1
    have hge : ctx.valDef.size ≤ L.tst.nextVreg := hN ▸ (hord bi L hL).term.1
    obtain ⟨hn, hy⟩ := lowTerm_spec hterm
    cases ht : B.term.isTry with
    | false =>
      obtain ⟨htl, hdat, out, tr, hc⟩ := hn ht
      have hk := hT _ _ _ _ _ _ _ _ hti hph ht hdat hge hc
      obtain ⟨h1, h2⟩ := asm_runKill hk htst
      rw [htl] at hmid ⊢
      simp only at hmid
      subst hmid
      refine ⟨hge, Nat.le_refl _, h1, fun m hm u hu => ?_⟩
      rcases (h2 m hm u hu).1 with h3 | h3
      · exact .inl h3
      · exact .inr ⟨h3.1, h3.2, (h2 m hm u hu).2⟩
    | true =>
      obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := isTry_with ht
      obtain ⟨T, hT', hdat, hex, -, hreg, hinfo, out, tr, hc⟩ := hy et het
      have hBt : ∃ B' ∈ f.blocks, B'.term = B.term := ⟨B, List.mem_of_getElem? hB, rfl⟩
      obtain ⟨hk, -⟩ := hY _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het hBt hdat hex hge hreg hc
      have hdefs := hX f ctx ranges st0 hd hs ha hb _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het hBt hdat
        hex hge hreg hc
      obtain ⟨h1, h2⟩ := asm_runKill hk rfl
      obtain ⟨-, -, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc hex) hreg
      have hmono : T.st1.nextVreg ≤ L.tst'.nextVreg := (runTerm_mono hc).1
      rw [hT'] at hmid ⊢
      simp only at hmid
      subst hmid
      obtain ⟨cl, hcl⟩ := hlf.tryLast bi B L T hB hL hT'
      rw [← back_toList] at hcl
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hcl
      have hD := hdefs (.call cl) (by rw [hys]; simp) cl rfl
      have hcode : fixTry (some T) L.tst'.emitted.toList = ys ++ [.tryCall cl T.info] := by
        show tryFix T.info _ = _
        rw [hys, tryFix_append]
      rw [hcode]
      have hys' : ∀ m ∈ ys, m ∈ L.tst'.emitted.toList := fun m hm => by
        rw [hys]; exact List.mem_append_left _ hm
      have hcm : MInst.call cl ∈ L.tst'.emitted.toList := by rw [hys]; simp
      -- what the `tryCall` kills: the results, below `mid`
      have htk : ∀ k ∈ unstored (.tryCall cl T.info), L.tst.nextVreg ≤ k ∧ k < T.st1.nextVreg := by
        intro k hk'
        have := asm_unstored_tryCall hD hk'
        rw [asm_outDefs_vregs] at this
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp this
        rw [List.mem_range] at hj
        omega
      refine ⟨hge, by omega, fun m hm k hk' => ?_, fun m hm u hu => ?_⟩
      · rcases List.mem_append.mp hm with hm | hm
        · have := h1 m (hys' m hm) k hk'
          omega
        · rw [List.mem_singleton] at hm
          subst hm
          have := htk k hk'
          omega
      · have hu' : ∃ m0 ∈ L.tst'.emitted.toList, u ∈ useVregs m0 := by
          rcases List.mem_append.mp hm with hm | hm
          · exact ⟨m, hys' m hm, hu⟩
          · rw [List.mem_singleton] at hm
            subst hm
            exact ⟨_, hcm, by rw [← asm_useVregs_tryCall]; exact hu⟩
        obtain ⟨m0, hm0, hu0⟩ := hu'
        obtain ⟨h3, h4⟩ := h2 m0 hm0 u hu0
        rcases h3 with h3 | h3
        · exact .inl h3
        · refine .inr ⟨h3.1, h3.2, fun m' hm' hum => ?_⟩
          rcases List.mem_append.mp hm' with hm' | hm'
          · exact h4 m' (hys' m' hm') hum
          · rw [List.mem_singleton] at hm'
            subst hm'
            have := htk u hum
            omega

end Segs


/-! ## The alias renaming -/

/-- `lowerFunction`'s alias renaming of the recorded lowering `bl`. -/
abbrev asmR (f : Clif.Function) (bl : List BLow) : Reg → Reg :=
  lowerFunction.resolve (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1)

/-- Its vreg renaming. -/
abbrev asmG (f : Clif.Function) (bl : List BLow) : Nat → Nat :=
  chaseF (fun n => ((aliasArr (aliasOf f bl))[n]?).join) ((aliasArr (aliasOf f bl)).size + 1)

theorem asm_ren (f : Clif.Function) (bl : List BLow) : VRenaming (asmR f bl) (asmG f bl) :=
  ⟨resolve_vreg _ _, fun r hr => by
    cases r with
    | vreg n c => exact absurd rfl (hr n c)
    | _ => rfl⟩

/-- The renaming maps a vreg to itself or to an alias target. -/
theorem asm_gn_cases (f : Clif.Function) (bl : List BLow) (x : Nat) :
    asmG f bl x = x ∨ ∃ p ∈ aliasOf f bl, asmG f bl x = p.2 := by
  rcases asm_chase (fun n => ((aliasArr (aliasOf f bl))[n]?).join) ((aliasArr (aliasOf f bl)).size + 1) x
    with h | ⟨m, hm⟩
  · exact .inl h
  · exact .inr ⟨(m, _), (faithful_arr _).some m _ hm, rfl⟩

/-- The entry block's argument setup kills and reads nothing. -/
theorem asm_pre {f : Clif.Function} {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn)
    {bi : Nat} {i : MInst} (h : i ∈ pre f R bi) : unstored i = [] ∧ useVregs i = [] := by
  unfold pre at h
  split at h
  · simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨asm_unstored_nil rfl rfl, asm_args_uses _⟩
    · simp only [entryLoads, List.mem_filterMap] at h
      obtain ⟨q, -, hq⟩ := h
      unfold entryLoadOf at hq
      split at hq
      · cases hq
        rw [hg.vreg]
        exact ⟨asm_unstored_nil rfl rfl, asm_load _ _ _ _⟩
      · cases hq
  · simp at h

section Insts
variable {f : Clif.Function} {vc : VCode} {bl : List BLow}
  (hvb : vc.blocks = vcBlocksOf f bl)
include hvb

/-- **An instruction of `lowerFunction`'s VCode** kills and reads nothing, or is the renaming of
an instruction of a run segment. -/
theorem vb_inst_cases {vb : VBlock} (hvb' : vb ∈ vc.blocks.toList) {i : MInst}
    (hi : i ∈ vb.insts.toList) :
    (unstored i = [] ∧ useVregs i = []) ∨
      ∃ lo mid hi c m, Seg f bl lo mid hi c ∧ m ∈ c ∧ i = m.mapRegs (asmR f bl) := by
  have hg := asm_ren f bl
  rw [hvb] at hvb'
  rcases mem_vcBlocksOf' hvb' with ⟨bi, B, L, hB, hL, rfl⟩ | ⟨B, L, e, -, he, rfl⟩
  · have hi' : i ∈ ((rawBlock f bl bi B).insts.map (MInst.mapRegs (asmR f bl))).toList := hi
    rw [rawBlock_insts] at hi'
    simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at hi'
    rcases hi' with (hpre | ⟨sg, ⟨j, -, rfl⟩, hm⟩) | htseg
    · exact .inl (asm_pre hg hpre)
    · unfold seg at hm
      rw [hB, hL] at hm
      simp only at hm
      split at hm
      · rename_i stm sl hstm hsl
        simp only [List.mem_map, List.mem_append] at hm
        obtain ⟨m, hm, rfl⟩ := hm
        rcases hm with hm | hm
        · exact .inr ⟨_, _, _, _, m, ⟨bi, B, L, hB, hL, .inl ⟨j, sl, hsl, rfl, rfl, rfl, rfl⟩⟩, hm, rfl⟩
        · simp only [extraOf, List.mem_filterMap] at hm
          obtain ⟨q, -, hq⟩ := hm
          split at hq
          · cases hq
          · rename_i out hout' _
            cases hq
            have hout : ∀ n c, out ≠ .vreg n c := fun n c e => hout' n c e
            have e : (MInst.mov .size64 (.vreg q.1 .int) out).mapRegs (asmR f bl) =
                .mov .size64 (.vreg (asmG f bl q.1) .int) out := by
              show MInst.mov .size64 (asmR f bl (.vreg q.1 .int)) (asmR f bl out) = _
              rw [hg.vreg, hg.real out hout]
            rw [e]
            exact .inl ⟨asm_unstored_nil rfl rfl, asm_mov_uses _ _ _ hout⟩
          · cases hq
      · simp at hm
    · unfold tseg at htseg
      split at htseg
      · rename_i L' hL'
        rw [hL] at hL'
        cases hL'
        simp only [List.mem_map] at htseg
        obtain ⟨m, hm, rfl⟩ := htseg
        exact .inr ⟨_, _, _, _, m, ⟨bi, B, L, hB, hL, .inr ⟨rfl, rfl, rfl, rfl⟩⟩, hm, rfl⟩
      · simp at htseg
  · obtain ⟨tl, hie⟩ := edgeBlocks_insts he
    simp only [fixBlock, hie] at hi
    simp at hi
    subst hi
    exact .inl (asm_jump tl)

end Insts


/-- Vregs at or above the CLIF values' are not renamed. -/
theorem asm_fix {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (bl : List BLow) (hb : buildCtx f = .ok (ctx, ranges, st0)) {n : Nat} (hn : ctx.valDef.size ≤ n) : asmG f bl n = n := by
  have hcf := ctxFacts_of hb
  refine resolve_fix (aliasOf f bl) (fun o hmo => ?_)
  have hv := (aliasOf_keys f bl).subset (List.mem_map_of_mem (f := (·.1)) hmo)
  have hlt := (hcf.vals n hv).1
  rw [hcf.size.1] at hlt
  exact absurd hlt (Nat.not_lt.mpr hn)

theorem asm_disj {f : Clif.Function} {ctx : Ctx} {st0 : LState} {bl : List BLow}
    (hlb : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
      some bl) {lo mid hi lo' mid' hi' x : Nat} {c c' : List MInst}
    (h : Seg f bl lo mid hi c) (h' : Seg f bl lo' mid' hi' c') (h1 : lo ≤ x) (h2 : x < hi)
    (h1' : lo' ≤ x) (h2' : x < hi') : c = c' := by
  obtain ⟨hO1, hO2⟩ := driver_ord hlb
  exact seg_disj hO1 hO2 h h' h1 h2 h1' h2'

/-! ## Killed vregs and uses of the assembled VCode -/

section Assemble
variable {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
  {bl : List BLow} {vc : VCode}
  (hd : Dominated f) (hs : LowerScope f) (ha : AbiSigsOk f)
  (hb : buildCtx f = .ok (ctx, ranges, st0))
  (hlb : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
    some bl)
  (hlf : LoopFacts f ctx bl) (hvb : vc.blocks = vcBlocksOf f bl)
  (hK : KillRunsHyp) (hX : TryDefsExact)
include hd hs ha hb hlb hlf hvb hK hX

/-- **A killed vreg** is killed by an instruction of a run segment, inside the segment's range. -/
theorem killed_seg {k : Nat} (hk : k ∈ killedOf vc) :
    ∃ lo mid hi c m, Seg f bl lo mid hi c ∧ m ∈ c ∧ k ∈ unstored m ∧ lo ≤ k ∧ k < hi := by
  simp only [killedOf, List.mem_flatMap] at hk
  obtain ⟨vb, hvb', i, hi, hki⟩ := hk
  rcases vb_inst_cases hvb hvb' hi with ⟨h0, -⟩ | ⟨lo, mid, hi', c, m, hseg, hm, rfl⟩
  · rw [h0] at hki; cases hki
  · obtain ⟨k0, hk0, rfl⟩ := asm_unstored_mapRegs (asm_ren f bl) hki
    obtain ⟨hlo, -, hkill, -⟩ := seg_ok hd hs ha hb hlb hlf hK hX hseg
    obtain ⟨h1, h2⟩ := hkill m hm k0 hk0
    rw [asm_fix bl hb (by omega)]
    exact ⟨lo, mid, hi', c, m, hseg, hm, hk0, h1, h2⟩

/-- **A use** is a renamed CLIF value's vreg, or a vreg of a run segment's rule that the
segment does not kill. -/
theorem use_src {vb : VBlock} (hvb' : vb ∈ vc.blocks.toList) {i : MInst} (hi : i ∈ vb.insts.toList)
    {u : Nat} (hu : u ∈ useVregs i) :
    (∃ x, x < ctx.valDef.size ∧ u = asmG f bl x) ∨
      ∃ lo mid hi c, Seg f bl lo mid hi c ∧ mid ≤ u ∧ u < hi ∧ ∀ m' ∈ c, u ∉ unstored m' := by
  rcases vb_inst_cases hvb hvb' hi with ⟨-, h0⟩ | ⟨lo, mid, hi', c, m, hseg, hm, rfl⟩
  · rw [h0] at hu; cases hu
  · obtain ⟨u0, hu0, rfl⟩ := asm_useVregs_mapRegs (asm_ren f bl) hu
    obtain ⟨hlo, hlm, -, huse⟩ := seg_ok hd hs ha hb hlb hlf hK hX hseg
    rcases huse m hm u0 hu0 with h1 | ⟨h1, h2, h3⟩
    · exact .inl ⟨u0, h1, rfl⟩
    · rw [asm_fix bl hb (by omega : ctx.valDef.size ≤ u0)]
      exact .inr ⟨lo, mid, hi', c, hseg, h1, h2, h3⟩

omit hlf hvb hX in
/-- **An alias target**, a statement's result register, is a CLIF value's vreg or a vreg of the
statement's segment that the segment does not kill. -/
theorem alias_ok {p : Nat × Nat} (hp : p ∈ aliasOf f bl) :
    p.2 < ctx.valDef.size ∨
      ∃ lo hi c, Seg f bl lo lo hi c ∧ lo ≤ p.2 ∧ p.2 < hi ∧ ∀ m ∈ c, p.2 ∉ unstored m := by
  obtain ⟨hS, -, -⟩ := hK f ctx ranges st0 hd hs ha hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  obtain ⟨hord, -⟩ := driver_ord hlb
  have hN : st0.nextVreg = ctx.valDef.size := hcf.size.1
  obtain ⟨bi, B, L, j, stm, sl, hB, hL, hstm, hsl, hr, rs, c, hrs, hrse⟩ := mem_aliasOf hp
  obtain ⟨-, hcs, -⟩ := hspec bi B L hB hL
  obtain ⟨info, hinf, hic, hres⟩ := hcf.stmt bi B j stm hB hstm
  obtain ⟨tr, hrun⟩ := hcs j sl hsl
  rw [hstart bi L hL] at hrun
  have hge : ctx.valDef.size ≤ sl.st.nextVreg := hN ▸ ((hord bi L hL).stmt j sl hsl).1
  obtain ⟨-, hout⟩ := hS _ info stm.inst _ _ _ _ hinf hic hge hrun
  have hne : info.results ≠ [] := by
    rw [hres]; intro h0; rw [h0] at hr; cases hr
  have he := hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)
  obtain ⟨h1, h2⟩ := hout hne _ rfl rs hrs p.2 c (by rw [hrse]; simp)
  have hes : emittedSince sl.st sl.st' = sl.st'.emitted.toList := by
    simp [emittedSince, he]
  rw [hes] at h2
  rcases h1 with h1 | h1
  · exact .inl h1
  · exact .inr ⟨_, _, _, ⟨bi, B, L, hB, hL, .inl ⟨j, sl, hsl, rfl, rfl, rfl, rfl⟩⟩, h1.1, h1.2,
      fun m hm hpm => h2 (asm_mem_killedL hm hpm)⟩

/-- **A renamed CLIF value's vreg is never killed.** -/
theorem val_nk {x : Nat} (hx : x < ctx.valDef.size) : asmG f bl x ∉ killedOf vc := by
  intro hk
  obtain ⟨lo, mid, hi, c, m, hseg, hm, hkm, h1, h2⟩ :=
    killed_seg hd hs ha hb hlb hlf hvb hK hX hk
  have hlo := (seg_ok hd hs ha hb hlb hlf hK hX hseg).1
  rcases asm_gn_cases f bl x with e | ⟨p, hp, e⟩
  · rw [e] at h1; omega
  · rw [e] at h1 h2 hkm
    rcases alias_ok hd hs ha hb hlb hK hp with h3 | ⟨lo', hi', c', hseg', h3, h4, h5⟩
    · omega
    · have := asm_disj hlb hseg hseg' h1 h2 h3 h4
      subst this
      exact h5 m hm hkm

/-- **Part 1 of `killFreeB`**: no instruction reads a killed vreg. -/
theorem uses_nk {vb : VBlock} (hvb' : vb ∈ vc.blocks.toList) {i : MInst} (hi : i ∈ vb.insts.toList)
    {u : Nat} (hu : u ∈ useVregs i) : u ∉ killedOf vc := by
  rcases use_src hd hs ha hb hlb hlf hvb hK hX hvb' hi hu with ⟨x, hx, rfl⟩ |
      ⟨lo, mid, hi', c, hseg, h1, h2, h3⟩
  · exact val_nk hd hs ha hb hlb hlf hvb hK hX hx
  · intro hk
    obtain ⟨lo', mid', hi'', c', m, hseg', hm, hkm, h1', h2'⟩ :=
      killed_seg hd hs ha hb hlb hlf hvb hK hX hk
    have hlm := (seg_ok hd hs ha hb hlb hlf hK hX hseg).2.1
    have := asm_disj hlb hseg hseg' (by omega) h2 h1' h2'
    subst this
    exact h3 m hm hkm

/-! ## A `try_call`'s block -/

omit hvb in
/-- **A `try_call`'s terminator segment**: the rule's code with its call replaced by the
`tryCall`, whose defs are the result vregs `[lo, lo + max n 2)`, in order; the rule's other
instructions kill only vregs from `T.st1` on. -/
theorem try_facts {bi : Nat} {B : Clif.Block} {L : BLow} {et : Clif.ExnTable}
    (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L) (het : IsTryWith B.term et) :
    ∃ T ys cl, L.tl = some T ∧
      fixTry L.tl L.tst'.emitted.toList = ys ++ [.tryCall cl T.info] ∧
      cl.defs = callDefs (outDefs L.tst.nextVreg (max (sigRets T.sig).length 2)) ∧
      (∀ m ∈ ys, ∀ k ∈ unstored m, T.st1.nextVreg ≤ k) ∧
      T.regs = ((List.range (sigRets T.sig).length).map
        (fun j => Reg.vreg (L.tst.nextVreg + j) .int),
        [.vreg L.tst.nextVreg .int, .vreg (L.tst.nextVreg + 1) .int]) ∧
      T.st1.nextVreg = L.tst.nextVreg + max (sigRets T.sig).length 2 ∧
      T.st1.nextVreg ≤ L.tst'.nextVreg ∧ ctx.valDef.size ≤ L.tst.nextVreg ∧
      tryInfoOf T.sig T.items L.targets = some T.info ∧
      L.targets.length = et.dests.length ∧ L.targets.Nodup := by
  obtain ⟨-, -, hY⟩ := hK f ctx ranges st0 hd hs ha hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  obtain ⟨hord, -⟩ := driver_ord hlb
  have hN : st0.nextVreg = ctx.valDef.size := hcf.size.1
  obtain ⟨-, -, -, nl0, nl', hterm⟩ := hspec bi B L hB hL
  have hph := hcf.term bi B hB
  rw [← hstart bi L hL] at hph
  have hti := (Array.getElem?_eq_some_iff.mp hph).1
  have hge : ctx.valDef.size ≤ L.tst.nextVreg := hN ▸ (hord bi L hL).term.1
  obtain ⟨-, hy⟩ := lowTerm_spec hterm
  obtain ⟨T, hT', hdat, hex, htt, hreg, hinfo, out, tr, hc⟩ := hy et het
  have hBt : ∃ B' ∈ f.blocks, B'.term = B.term := ⟨B, List.mem_of_getElem? hB, rfl⟩
  obtain ⟨hk, -⟩ := hY _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het hBt hdat hex hge hreg hc
  have hdefs := hX f ctx ranges st0 hd hs ha hb _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het hBt hdat
    hex hge hreg hc
  obtain ⟨h1, -⟩ := asm_runKill hk rfl
  obtain ⟨-, htrs, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc hex) hreg
  have hmono : T.st1.nextVreg ≤ L.tst'.nextVreg := (runTerm_mono hc).1
  obtain ⟨cl, hcl⟩ := hlf.tryLast bi B L T hB hL hT'
  rw [← back_toList] at hcl
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hcl
  have hD := hdefs (.call cl) (by rw [hys]; simp) cl rfl
  have hcode : fixTry L.tl L.tst'.emitted.toList = ys ++ [.tryCall cl T.info] := by
    rw [hT']
    show tryFix T.info _ = _
    rw [hys, tryFix_append]
  refine ⟨T, ys, cl, hT', hcode, hD, fun m hm k hkm => ?_, htrs, hst1, hmono, hge, hinfo,
    by rw [(tryTargets_spec htt).1, List.length_range'],
    by rw [(tryTargets_spec htt).1]; exact List.nodup_range'⟩
  exact (h1 m (by rw [hys]; exact List.mem_append_left _ hm) k hkm).1

end Assemble

/-! ## `VCode.cfg` of the lowered VCode -/

/-- The successors of a block are its terminator's targets (labels are indices). -/
theorem asm_succs {vc : VCode} (hv : LowOk vc) {ss ps : Array (Array Nat)}
    (hc : vc.cfg = .ok (ss, ps)) {b : Nat} {vb : VBlock} {t : MInst} {sb : Array Nat}
    (hb : vc.blocks[b]? = some vb) (ht : vb.insts.back? = some t) (hsb : ss[b]? = some sb) :
    sb.toList = t.targets := by
  obtain ⟨t0, ts, ht0, -, hts, hsz, hl⟩ := (Prep.cfg_spec hc).blk b vb hb
  rw [ht] at ht0
  cases ht0
  rw [hsb] at hts
  cases hts
  apply List.ext_getElem?
  intro j
  by_cases hj : j < t.targets.length
  · obtain ⟨l, hlj⟩ : ∃ l, t.targets[j]? = some l := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨kk, hkk, hlab⟩ := hl j l hlj
    obtain ⟨hk, hlabel⟩ := Prep.lab_some hlab
    have := hv.labels kk _ (Array.getElem?_eq_getElem hk)
    rw [hlabel] at this
    subst this
    rw [hlj, Array.getElem?_toList, hkk]
  · rw [List.getElem?_eq_none (l := t.targets) (by omega),
      List.getElem?_eq_none (l := sb.toList) (by simp; omega)]


theorem asm_idxOf {l : List Nat} (hn : l.Nodup) {k x : Nat} (h : l[k]? = some x) :
    List.idxOf? x l = some k := by
  obtain ⟨hk, e⟩ := List.getElem?_eq_some_iff.mp h
  refine List.idxOf?_eq_some_iff.mpr ⟨hk, e, fun j hj ej => ?_⟩
  have := hn.eq_of_getElem_eq (Nat.lt_trans hj hk) hk (by rw [ej, e])
  omega

theorem asm_filter_map_rn (gn : Nat → Nat) (ops : Array Operand) (k : OpKind) :
    (ops.map (rnOp gn)).toList.filter (·.kind == k) =
      (ops.toList.filter (·.kind == k)).map (rnOp gn) := by
  rw [Array.toList_map, List.filter_map]; rfl

theorem asm_callDefOps_rn (gn : Nat → Nat) (D : List (Reg × Nat)) (h : ∀ q ∈ D, gn q.2 = q.2) :
    (callDefOps D).map (rnOp gn) = callDefOps D := by
  unfold callDefOps
  rw [List.map_map]
  apply List.map_congr_left
  intro q hq
  simp [rnOp, h q hq]

theorem asm_valueReg_lt {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hb : buildCtx f = .ok (ctx, ranges, st0)) {v : Nat} {r : Reg}
    (h : ctx.valueReg? v = some r) : v < ctx.valDef.size := by
  have hcf := ctxFacts_of hb
  simp only [Ctx.valueReg?] at h
  cases hh : ctx.valReg[v]? with
  | none => rw [hh] at h; cases h
  | some _ => rw [← hcf.size.2.1]; exact (Array.getElem?_eq_some_iff.mp hh).1

/-! ## Branch arguments -/

section Edges
variable {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
  {bl : List BLow} {vc : VCode}
  (hd : Dominated f) (hs : LowerScope f) (ha : AbiSigsOk f)
  (hb : buildCtx f = .ok (ctx, ranges, st0))
  (hlb : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
    some bl)
  (hlf : LoopFacts f ctx bl) (hvb : vc.blocks = vcBlocksOf f bl)
  (hK : KillRunsHyp) (hX : TryDefsExact)
  (H : Low f vc ctx st0 bl (asmR f bl)) (hv : LowOk vc)
include hd hs ha hb hlb hlf hvb hK hX H hv

/-- **A `try_call`'s edge block** passes a value's vreg (never killed) or a result vreg, which
its entry stores store when killed (the edge block kills nothing). -/
theorem try_edge_ok {succs preds : Array (Array Nat)} (hc : vc.cfg = .ok (succs, preds))
    {bi : Nat} {B : Clif.Block} {L : BLow} {et : Clif.ExnTable}
    (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L) (het : IsTryWith B.term et)
    {e : VBlock} (he : e ∈ edgeBlocks f B L) {a : Reg}
    (ha' : a ∈ (fixBlock (asmR f bl) e).branchArgs.toList) :
    (!(killedOf vc).contains a.homeNum ||
      ((entryStored vc succs preds e.label).contains a.homeNum &&
        (fixBlock (asmR f bl) e).insts.toList.all fun i => !(unstored i).contains a.homeNum)) =
      true := by
  have hg := asm_ren f bl
  have he0 := he
  obtain ⟨T, ys, cl, hT, hcode, hD, hys, hregs, hst1, hmono, hge, hinfo, htlen, htnd⟩ :=
    try_facts hd hs ha hb hlb hlf hK hX hB hL het
  rw [shape_edgeBlocks_try het hT] at he
  obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp he
  simp only [edgeOfTry] at hpe
  obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.mp hpe
  obtain ⟨k, hk, hpk⟩ := List.getElem_of_mem hp
  have hzk : (et.dests.zip L.targets)[k]? = some p := by rw [List.getElem?_eq_getElem hk, hpk]
  obtain ⟨hdk, htk⟩ := List.getElem?_zip_eq_some.mp hzk
  obtain ⟨T', hT'', hargs⟩ := hlf.tryArgs bi B L et hB hL het
  rw [hT] at hT''
  cases hT''
  obtain ⟨-, hai⟩ := hargs k p.1 hdk
  simp only [fixBlock, Array.toList_map, List.map_map, List.mem_map,
    Function.comp_def] at ha'
  obtain ⟨ta, hta, rfl⟩ := ha'
  have hok := hai ta hta
  -- a result vreg `lo + i`
  have key : ∀ i, i < max (sigRets T.sig).length 2 →
      (k = et.handlers.length → i < (sigRets T.sig).length) →
      (!(killedOf vc).contains (L.tst.nextVreg + i) ||
        ((entryStored vc succs preds p.2).contains (L.tst.nextVreg + i) &&
          (#[MInst.jump tl].map (MInst.mapRegs (asmR f bl))).toList.all fun i' =>
            !(unstored i').contains (L.tst.nextVreg + i))) = true := by
    intro i hiM hin
    cases hkc : (killedOf vc).contains (L.tst.nextVreg + i)
    · rfl
    have hkm : L.tst.nextVreg + i ∈ killedOf vc := by simpa using hkc
    obtain ⟨lo', mid', hi', c', m, hseg', hm, hkm', h1', h2'⟩ :=
      killed_seg hd hs ha hb hlb hlf hvb hK hX hkm
    have hsegT : Seg f bl L.tst.nextVreg T.st1.nextVreg L.tst'.nextVreg
        (ys ++ [.tryCall cl T.info]) :=
      ⟨bi, B, L, hB, hL, .inr ⟨rfl, rfl, by rw [hT], by rw [hcode]⟩⟩
    have := asm_disj hlb hseg' hsegT h1' h2' (by omega) (by omega)
    subst this
    have hm' : m = .tryCall cl T.info := by
      rcases List.mem_append.mp hm with hm | hm
      · have := hys m hm _ hkm'; omega
      · simpa using hm
    subst hm'
    obtain ⟨ops, hops, -⟩ := asm_unstored_sub hkm'
    have hvbt := H.raw_at hB
    have hlast : (fixTry L.tl L.tst'.emitted.toList).getLast? = some (.tryCall cl T.info) := by
      rw [hcode]; simp
    have hback := raw_back_of (RR := asmR f bl) (f := f) (B := B) hL hlast
    obtain ⟨c', hc'⟩ : ∃ c', (MInst.tryCall cl T.info).mapRegs (asmR f bl) = .tryCall c' T.info :=
      ⟨_, rfl⟩
    rw [hc'] at hback
    have hops' : (MInst.tryCall c' T.info).operands = .ok (ops.map (rnOp (asmG f bl))) := by
      rw [← hc', operands_mapRegs hg, hops]; rfl
    have hfD : ∀ q ∈ outDefs L.tst.nextVreg (max (sigRets T.sig).length 2),
        asmG f bl q.2 = q.2 := by
      intro q hq
      simp only [outDefs, List.mem_map, List.mem_range] at hq
      obtain ⟨j, -, rfl⟩ := hq
      exact asm_fix bl hb (by simp only; omega)
    have hD0 : ops.toList.filter (·.kind == .def) =
        callDefOps (outDefs L.tst.nextVreg (max (sigRets T.sig).length 2)) := by
      rw [operands_tryCall_call] at hops
      exact asm_call_defs hD hops
    have hD' : (ops.map (rnOp (asmG f bl))).toList.filter (·.kind == .def) =
        callDefOps (outDefs L.tst.nextVreg (max (sigRets T.sig).length 2)) := by
      rw [asm_filter_map_rn, hD0, asm_callDefOps_rn _ _ hfD]
    have hte := asm_termEdge_try hback hops' hD' k
    -- the CFG
    have hbl : bi < vc.blocks.size := (Array.getElem?_eq_some_iff.mp hvbt).1
    obtain ⟨ss, hss⟩ := cfg_succs_some hc hbl
    have hsst := asm_succs hv hc hvbt hback hss
    rw [tryInfo_targets hinfo c'] at hsst
    obtain ⟨-, hat⟩ := H.edge_at hB hL he0
    have hsz : p.2 < vc.blocks.size := (Array.getElem?_eq_some_iff.mp hat).1
    have hidx : List.idxOf? p.2 ss.toList = some k := by rw [hsst]; exact asm_idxOf htnd htk
    have hj0 : ss[k]? = some p.2 := by rw [← Array.getElem?_toList, hsst]; exact htk
    have htk' : (MInst.tryCall c' T.info).targets[k]? = some p.2 := by
      rw [tryInfo_targets hinfo c']; exact htk
    have hu : ∀ (q : Nat) (sq : Array Nat) (j : Nat), succs[q]? = some sq → sq[j]? = some p.2 →
        q = bi ∧ j = k := by
      intro q sq j hq hj
      have hql : q < vc.blocks.size := by
        rw [← (Prep.cfg_spec hc).size]; exact (Array.getElem?_eq_some_iff.mp hq).1
      obtain ⟨t', ht', -⟩ := cfg_last hc (Array.getElem?_eq_getElem hql)
      have hsq := asm_succs hv hc (Array.getElem?_eq_getElem hql) ht' hq
      have htj : t'.targets[j]? = some p.2 := by rw [← hsq, Array.getElem?_toList]; exact hj
      exact hv.tryUniq bi _ c' T.info k p.2 hvbt hback htk' q _ t' j
        (Array.getElem?_eq_getElem hql) ht' htj
    have hpreds : preds[p.2]? = some #[bi] := preds_one hc hsz hss hj0 hu
    -- the stored vregs
    have hhl : T.info.handlers.length = et.handlers.length := by
      unfold tryInfoOf at hinfo
      split at hinfo
      · cases hinfo
      · rename_i hlen
        rw [← Option.some.inj hinfo]
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
        simp only [List.length_map, List.length_zip]
        have : et.dests.length = et.handlers.length + 1 := by simp [Clif.ExnTable.dests]
        omega
    have hrets : T.info.rets = (sigRets T.sig).length := by
      unfold tryInfoOf at hinfo
      split at hinfo
      · cases hinfo
      · rw [← Option.some.inj hinfo]
    have hmem : L.tst.nextVreg + i ∈ (termEdgeDefs (fixBlock (asmR f bl) (rawBlock f bl bi B)) k).map
        (·.1.vreg) := by
      rw [hte, asm_outDefs_vregs]
      split
      · rename_i hkh
        rw [hrets]
        have hin' := hin (by rw [← hhl]; exact hkh)
        rw [← List.map_take, List.take_range, List.mem_map]
        exact ⟨i, List.mem_range.mpr (by omega), rfl⟩
      · exact List.mem_map.mpr ⟨i, List.mem_range.mpr hiM, rfl⟩
    have hes : (entryStored vc succs preds p.2).contains (L.tst.nextVreg + i) = true := by
      rw [entryStored_one hpreds, hvbt, hss]
      simp only
      rw [hidx]
      simpa using hmem
    have hall : ((#[MInst.jump tl].map (MInst.mapRegs (asmR f bl))).toList.all fun i' =>
        !(unstored i').contains (L.tst.nextVreg + i)) = true := by
      simp [MInst.mapRegs, (asm_jump tl).1]
    rw [hes, hall]
    rfl
  have hfixR : ∀ i, (asmR f bl (.vreg (L.tst.nextVreg + i) .int)).homeNum = L.tst.nextVreg + i := by
    intro i
    rw [hg.vreg, asm_fix bl hb (by omega)]
    rfl
  cases ta with
  | val v =>
    have hvlt : v < ctx.valDef.size := by
      have hcf := ctxFacts_of hb
      simp only [Ctx.valueReg?] at hok
      cases hh : ctx.valReg[v]? with
      | none => rw [hh] at hok; cases hok
      | some _ => rw [← hcf.size.2.1]; exact (Array.getElem?_eq_some_iff.mp hh).1
    have hnk := val_nk hd hs ha hb hlb hlf hvb hK hX hvlt
    have e : (killedOf vc).contains (asmR f bl (tryEdgeArg T.regs.1 T.regs.2 (.val v))).homeNum =
        false := by
      show (killedOf vc).contains (asmR f bl (.vreg v .int)).homeNum = false
      rw [hg.vreg]
      simpa [Reg.homeNum] using hnk
    rw [e]
    rfl
  | ret i =>
    obtain ⟨hkh, hil⟩ := hok
    rw [hregs] at hil
    simp only [List.length_map, List.length_range] at hil
    have e : tryEdgeArg T.regs.1 T.regs.2 (.ret i) = .vreg (L.tst.nextVreg + i) .int := by
      simp [tryEdgeArg, hregs, hil]
    rw [e, hfixR]
    exact key i (by omega) (fun _ => hil)
  | exn i =>
    obtain ⟨hkh, hil⟩ := hok
    rw [hregs] at hil
    simp only [List.length_cons, List.length_nil] at hil
    have e : tryEdgeArg T.regs.1 T.regs.2 (.exn i) = .vreg (L.tst.nextVreg + i) .int := by
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp [tryEdgeArg, hregs]
    rw [e, hfixR]
    exact key i (by omega) (fun h => absurd h hkh)


/-- **A block's branch arguments** meet `killFreeB`'s second condition. -/
theorem args_ok {succs preds : Array (Array Nat)} (hc : vc.cfg = .ok (succs, preds)) {b : Nat}
    {vb : VBlock} (hvbb : vc.blocks[b]? = some vb) {a : Reg} (ha' : a ∈ vb.branchArgs.toList) :
    (!(killedOf vc).contains a.homeNum ||
      ((entryStored vc succs preds b).contains a.homeNum &&
        vb.insts.toList.all fun i => !(unstored i).contains a.homeNum)) = true := by
  have hg := asm_ren f bl
  -- a value's vreg
  have val : ∀ y, ctx.valueReg? y = some (.vreg y .int) → a = asmR f bl (.vreg y .int) →
      (!(killedOf vc).contains a.homeNum ||
        ((entryStored vc succs preds b).contains a.homeNum &&
          vb.insts.toList.all fun i => !(unstored i).contains a.homeNum)) = true := by
    intro y hy e
    have hnk := val_nk hd hs ha hb hlb hlf hvb hK hX (asm_valueReg_lt hb hy)
    have : (killedOf vc).contains a.homeNum = false := by
      rw [e, hg.vreg]; simpa [Reg.homeNum] using hnk
    rw [this]; rfl
  rcases H.cases hvbb with ⟨B, L, -, hB, hL, rfl⟩ | ⟨bi, B, L, e, hB, hL, he, hel, -, rfl⟩
  · have hBm := List.mem_of_getElem? hB
    simp only [fixBlock, rawBlock] at ha'
    split at ha'
    · rename_i bc hj
      simp only [Array.toList_map, List.map_map, List.mem_map,
        Function.comp_def] at ha'
      obtain ⟨y, hy, rfl⟩ := ha'
      obtain ⟨-, -, -, hvals⟩ := hlf.args B hBm bc (by rw [hj]; simp [dests])
      exact val y (hvals y hy) rfl
    · simp at ha'
  · subst hel
    rcases try_or B.term with ht | ⟨et, het⟩
    · by_cases hj : ∃ bc, B.term = .jump bc
      · obtain ⟨bc, hj⟩ := hj
        rw [shape_edgeBlocks_jump hj] at he
        cases he
      · have hj' : ∀ bc, B.term ≠ .jump bc := fun bc e => hj ⟨bc, e⟩
        have he' := he
        rw [shape_edgeBlocks_other ht hj'] at he'
        obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp he'
        simp only [edgeOfBc] at hqe
        split at hqe
        · cases hqe
        obtain ⟨tl, -, rfl⟩ := Option.map_eq_some_iff.mp hqe
        have hbc : q.1 ∈ dests B.term := (List.of_mem_zip hq).1
        simp only [fixBlock, Array.toList_map, List.map_map, List.mem_map,
          Function.comp_def] at ha'
        obtain ⟨y, hy, rfl⟩ := ha'
        obtain ⟨-, -, -, hvals⟩ := hlf.args B (List.mem_of_getElem? hB) q.1 hbc
        exact val y (hvals y hy) rfl
    · exact try_edge_ok hd hs ha hb hlb hlf hvb hK hX H hv hc hB hL het he ha'

end Edges

/-! ## The theorem -/

/-- **`lowerFunction`'s VCode passes `killFreeB`** on in-scope input, given the killed-vreg
facts of the ISLE runs (`KillRunsHyp`) and the exact defs of a `try_call`'s call
(`TryDefsExact`). -/
theorem killFreeB_lower (hK : KillRunsHyp) (hX : TryDefsExact) {f : Clif.Function} {vc : VCode}
    (hd : Dominated f) (hs : LowerScope f) (ha : AbiSigsOk f) (har : ArityOk f)
    (hl : lowerFunction f = .ok vc) : killFreeB vc = true := by
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, hlf⟩ := lowerFunction_run hl
  have H : Low f vc ctx st0 bl (asmR f bl) := by
    have hlb' := hlb
    rw [lowBlocks_eq] at hlb'
    cases hr : lowB f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length with
    | none => rw [hr] at hlb'; cases hlb'
    | some r =>
      rw [hr] at hlb'
      obtain ⟨bl', stE, nlE⟩ := r
      cases hlb'
      exact ⟨⟨ranges, hb⟩, ⟨stE, nlE, hr⟩, by rw [hvb]; simp [vcBlocksOf], ⟨_, asm_ren f bl'⟩,
        hlf, (lowBlocks_spec hlb).1⟩
  have hv := lowOk_of hd hs har hl
  unfold killFreeB
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · refine List.all_eq_true.mpr fun vb hvb' => List.all_eq_true.mpr fun i hi =>
      List.all_eq_true.mpr fun u hu => ?_
    have := uses_nk hd hs ha hb hlb hlf hvb hK hX hvb' hi hu
    simpa using this
  · split
    · rfl
    · rename_i succs preds hc
      refine List.all_eq_true.mpr fun b _ => ?_
      split
      · rfl
      · rename_i vb hvbb
        exact List.all_eq_true.mpr fun a ha' =>
          args_ok hd hs ha hb hlb hlf hvb hK hX H hv hc hvbb ha'

end Backend.Proof.Kill
