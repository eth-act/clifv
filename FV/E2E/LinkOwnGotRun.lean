import FV.E2E.LinkOwnCallsShape
import FV.Backend.Proof.KillAssemble
import FV.Backend.Proof.KillDriver

/-! # The GOT vreg of a direct call (`GotRunHyp`)

`gotRunHyp_of`: `GotRunHyp` (`LinkOwnCallsShape`) from two smaller program-independent facts:

* `SegRangeHyp`, about every run segment of the recorded lowering (`Kill.Seg`): its
  instructions define only vregs of the segment's range `[lo, hi)`, and a call through a vreg
  calls a CLIF value's vreg or one of the range (M4's `LowerInstOk.defs`/`LowerTermOk.defs`/
  `LowerTryOk.shape`; `Kill.RunKill`'s uses);
* `GotLocalHyp`, about the code `ms` of the direct call's own run: only the GOT load defines `t`,
  every call through `t` in `ms` follows the GOT load, and `t` is no result register of the
  statement.

The driver part is proven: every instruction of `lowerFunction`'s VCode is an entry-block
`Args`/load or a `mov` of `extraOf` (defining renamed CLIF values), an edge block's `jump`, or the
renaming of an instruction of a run segment (`blk_cases`, with its position in the block); fresh
vregs are not renamed (`Kill.asm_fix`), run segments have disjoint ranges (`Kill.asm_disj`), and
no alias renames a CLIF value to `t` (`alias_ne`: alias targets are result registers, which are
CLIF values or vregs of their statement's range, `Kill.killRunsHyp`).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Kill

/-! ## The hypotheses -/

/-- **The ranges of the run segments** (program-independent): every instruction of a run
segment defines only vregs of its range, and a call through a vreg calls a CLIF value's vreg or a
vreg of the range. -/
def SegRangeHyp : Prop :=
  ∀ (p : Clif.Program) (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat))
    (st0 : LState) (bl : List BLow), InSubset p f → Dominated f → LowerScope f →
    buildCtx f = .ok (ctx, ranges, st0) →
    lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
      some bl →
    ∀ (lo mid hi : Nat) (c : List MInst), Seg f bl lo mid hi c → ∀ m ∈ c,
      (∀ d ∈ vdefs m, lo ≤ d ∧ d < hi) ∧
      (∀ (ci : CallInfo) (d : Nat), (m = .call ci ∨ ∃ ti, m = .tryCall ci ti) →
        ci.dest = .reg (.vreg d .int) → d < ctx.valDef.size ∨ (lo ≤ d ∧ d < hi))

/-- **The direct call's own run** (program-independent; the premises of `GotRunHyp`): in its
code `ms`, only the GOT load defines `t`, every call through `t` follows the GOT load, and `t` is
no result register of the statement. -/
def GotLocalHyp : Prop :=
  ∀ (p : Clif.Program) (f : Clif.Function) (vc : VCode), InSubset p f → Dominated f →
    LowerScope f → lowerFunction f = .ok vc →
    ∀ (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState) (bl : List BLow),
      buildCtx f = .ok (ctx, ranges, st0) →
      lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
        some bl →
      ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (ms : List MInst) (c : CallInfo) (t : Nat)
        (n : String), f.blocks[bi]? = some B → bl[bi]? = some L →
        ((∃ (j : Nat) (stm : Clif.Stmt) (sl : SLow) (fn : Clif.FnRef) (args : List Nat),
            B.body[j]? = some stm ∧ L.sl[j]? = some sl ∧
            stm.inst = Clif.Inst.call fn args ∧ sl.st'.emitted.toList = ms) ∨
          (∃ T fn args et, B.term = .tryCall fn args et ∧ L.tl = some T ∧
            L.tst'.emitted.toList = ms)) →
        ctx.valDef.size ≤ t → MInst.loadExtNameGot (.vreg t .int) n ∈ ms →
        MInst.call c ∈ ms → c.dest = .reg (.vreg t .int) →
        (∀ m ∈ ms, t ∈ vdefs m → m = .loadExtNameGot (.vreg t .int) n) ∧
        (∀ (k : Nat) (ci : CallInfo),
          (ms[k]? = some (.call ci) ∨ ∃ ti, ms[k]? = some (.tryCall ci ti)) →
          ci.dest = .reg (.vreg t .int) →
          ∃ k' < k, ms[k']? = some (.loadExtNameGot (.vreg t .int) n)) ∧
        (∀ (j : Nat) (sl : SLow), L.sl[j]? = some sl → sl.st'.emitted.toList = ms →
          ∀ cl, [Reg.vreg t cl] ∉ sl.rss)

/-! ## Instruction facts -/

theorem gotDefB_of {t : Nat} {n : String} {i : MInst}
    (h : t ∉ vdefs i ∨ i = .loadExtNameGot (.vreg t .int) n) : gotDefB t n i = true := by
  unfold gotDefB
  cases hops : i.operands with
  | error e => rfl
  | ok ops =>
    simp only
    rcases h with h | h
    · have : (ops.any fun o => o.isDef && o.vreg == t) = false := by
        rw [Array.any_eq_false]
        intro k hk
        simp only [Bool.and_eq_true, beq_iff_eq, not_and]
        intro hd hv
        apply h
        unfold vdefs
        rw [hops]
        exact List.mem_map.mpr ⟨ops[k], List.mem_filter.mpr
          ⟨Array.mem_toList_iff.mpr (Array.getElem_mem hk), hd⟩, hv⟩
      simp [this]
    · simp [h]

theorem vdefs_mapRegs {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn) (m : MInst)
    {d : Nat} (h : d ∈ vdefs (m.mapRegs R)) : ∃ d0 ∈ vdefs m, d = gn d0 := by
  unfold vdefs at h ⊢
  rw [operands_mapRegs hg] at h
  cases hm : m.operands with
  | error e => rw [hm] at h; cases h
  | ok ops =>
    rw [hm] at h
    simp only [Except.map, Array.toList_map, List.filter_map, List.map_map,
      List.mem_map, List.mem_filter, Function.comp_def] at h
    obtain ⟨o, ⟨ho, hdef⟩, rfl⟩ := h
    exact ⟨o.vreg, List.mem_map.mpr ⟨o, List.mem_filter.mpr ⟨ho, hdef⟩, rfl⟩, rfl⟩

theorem vdefs_got (t : Nat) (n : String) :
    vdefs (.loadExtNameGot (.vreg t .int) n) = [t] := rfl

theorem vdefs_jump (l : Label) : vdefs (.jump l) = [] := rfl

theorem vdefs_tryCall (c : CallInfo) (ti : TryInfo) : vdefs (.tryCall c ti) = vdefs (.call c) := by
  unfold vdefs; rw [operands_tryCall_call]

theorem mov_defs (r : Nat) (out : Reg) (hout : ∀ n c, out ≠ .vreg n c) :
    ∀ d ∈ vdefs (.mov .size64 (.vreg r .int) out), d = r := by
  unfold vdefs
  rw [operands_eq]
  simp only [MInst.visitOperands, StateT.run_bind]
  have h1 : (collectOp OpSpec.def_ (Reg.vreg r .int)).run #[] =
      .ok (.vreg r .int, #[⟨r, .int, OpSpec.def_.kind, OpSpec.def_.pos, OpSpec.def_.con⟩]) := rfl
  rw [h1, Driver.except_ok_bind]
  cases h2 : (collectOp OpSpec.use out).run
      #[⟨r, .int, OpSpec.def_.kind, OpSpec.def_.pos, OpSpec.def_.con⟩] with
  | error e => intro d hd; cases hd
  | ok p =>
    obtain ⟨a, s'⟩ := p
    have := asm_collect_real hout h2
    subst this
    intro d hd
    simp [bind, Except.bind, pure, Except.pure, StateT.run, StateT.pure] at hd
    obtain ⟨o, ⟨rfl, -⟩, rfl⟩ := hd
    rfl

/-- The renaming of a call through a vreg calls through a renamed vreg. -/
theorem callMap_dest_inv {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn) {c : CallInfo}
    {t : Nat} (h : (callMap R c).dest = .reg (.vreg t .int)) :
    ∃ d, c.dest = .reg (.vreg d .int) ∧ gn d = t := by
  cases hc : c.dest with
  | sym s => simp [callMap, hc] at h
  | reg r =>
    simp only [callMap, hc, CallDest.reg.injEq] at h
    cases r with
    | vreg d cl =>
      rw [hg.vreg] at h
      cases h
      exact ⟨d, rfl, rfl⟩
    | _ => rw [hg.real _ (fun _ _ e => by cases e)] at h; cases h

/-! ## `tryFix` -/

theorem tryFix_get {info : TryInfo} {ms : List MInst} {k : Nat} {m : MInst}
    (h : (tryFix info ms)[k]? = some m) :
    ms[k]? = some m ∨ ∃ cl, ms[k]? = some (.call cl) ∧ m = .tryCall cl info := by
  unfold tryFix at h
  split at h
  · rename_i cl hlast
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [List.dropLast_concat] at h
    by_cases hk : k < ys.length
    · left
      rw [List.getElem?_append_left hk] at h ⊢
      exact h
    · right
      have hlt := (List.getElem?_eq_some_iff.mp h).1
      simp only [List.length_append, List.length_singleton] at hlt
      have hk0 : k = ys.length := by omega
      subst hk0
      refine ⟨cl, by simp, ?_⟩
      rw [List.getElem?_append_right (Nat.le_refl _)] at h
      simp at h
      exact h.symm
  · left; exact h

theorem tryFix_of_get {info : TryInfo} {ms : List MInst} {k : Nat} {m : MInst}
    (h : ms[k]? = some m) (hm : ∀ cl, m ≠ .call cl) : (tryFix info ms)[k]? = some m := by
  unfold tryFix
  split
  · rename_i cl hlast
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [List.dropLast_concat]
    by_cases hk : k < ys.length
    · rw [List.getElem?_append_left hk] at h ⊢
      exact h
    · have hlt := (List.getElem?_eq_some_iff.mp h).1
      simp only [List.length_append, List.length_singleton] at hlt
      have hk0 : k = ys.length := by omega
      subst hk0
      simp at h
      exact absurd h.symm (hm cl)
  · exact h

theorem tryFix_mem {info : TryInfo} {ms : List MInst} {m : MInst} (h : m ∈ tryFix info ms) :
    m ∈ ms ∨ ∃ cl, MInst.call cl ∈ ms ∧ m = .tryCall cl info := by
  obtain ⟨k, hk⟩ := List.getElem?_of_mem h
  rcases tryFix_get hk with h1 | ⟨cl, h1, rfl⟩
  · exact .inl (List.mem_of_getElem? h1)
  · exact .inr ⟨cl, List.mem_of_getElem? h1, rfl⟩

/-! ## Positions in a block -/

/-- An index of `A ++ S.flatten ++ C` is in `A`, or in one of the lists of `S` or in `C`, placed
at an offset `o`. -/
theorem idx_split {α : Type} : ∀ (S : List (List α)) (A C : List α) (k : Nat) (x : α),
    (A ++ S.flatten ++ C)[k]? = some x →
    A[k]? = some x ∨
    (∃ (j : Nat) (s : List α) (o : Nat), S[j]? = some s ∧ o ≤ k ∧ s[k - o]? = some x ∧
      ∀ i < s.length, (A ++ S.flatten ++ C)[o + i]? = s[i]?) ∨
    (∃ o, o ≤ k ∧ C[k - o]? = some x ∧ ∀ i < C.length, (A ++ S.flatten ++ C)[o + i]? = C[i]?)
  | [], A, C, k, x, h => by
    simp only [List.flatten_nil, List.append_nil] at h ⊢
    by_cases hk : k < A.length
    · left; rwa [List.getElem?_append_left hk] at h
    · right; right
      refine ⟨A.length, by omega, ?_, fun i hi => ?_⟩
      · rwa [List.getElem?_append_right (by omega)] at h
      · rw [List.getElem?_append_right (by omega)]; simp
  | s :: S, A, C, k, x, h => by
    have e : A ++ (s :: S).flatten ++ C = (A ++ s) ++ S.flatten ++ C := by simp
    rw [e] at h ⊢
    rcases idx_split S (A ++ s) C k x h with h1 | ⟨j, s', o, hs', ho, hx, hall⟩ |
      ⟨o, ho, hx, hall⟩
    · by_cases hk : k < A.length
      · left; rwa [List.getElem?_append_left hk] at h1
      · right; left
        refine ⟨0, s, A.length, rfl, by omega, ?_, fun i hi => ?_⟩
        · rwa [List.getElem?_append_right (by omega)] at h1
        · rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by omega),
            Nat.add_sub_cancel_left, List.getElem?_append_left hi]
    · right; left; exact ⟨j + 1, s', o, hs', ho, hx, hall⟩
    · right; right; exact ⟨o, ho, hx, hall⟩

/-! ## Ranges -/

section Ord
variable {v : Nat} {bl : List BLow}
  (hO1 : ∀ (bi : Nat) (L : BLow), bl[bi]? = some L → BlockOrd v L)
  (hO2 : ∀ (bi bi' : Nat) (L L' : BLow), bi < bi' → bl[bi]? = some L → bl[bi']? = some L' →
    BlockOrd L.tst'.nextVreg L')

include hO1 hO2 in
/-- Two statements whose ranges share a vreg are one statement. -/
theorem stmt_ident {bi bi' j j' x : Nat} {L L' : BLow} {sl sl' : SLow}
    (hL : bl[bi]? = some L) (hsl : L.sl[j]? = some sl) (hL' : bl[bi']? = some L')
    (hsl' : L'.sl[j']? = some sl') (h1 : sl.st.nextVreg ≤ x) (h2 : x < sl.st'.nextVreg)
    (h1' : sl'.st.nextVreg ≤ x) (h2' : x < sl'.st'.nextVreg) : bi = bi' ∧ j = j' := by
  rcases Nat.lt_trichotomy bi bi' with hlt | rfl | hlt
  · have := segIn_hi hO1 (⟨hL, .inl ⟨j, sl, hsl, rfl, rfl, rfl, rfl⟩⟩ :
      SegIn bl bi L sl.st.nextVreg sl.st.nextVreg sl.st'.nextVreg sl.st'.emitted.toList)
    have := segIn_lo hO2 hlt hL (⟨hL', .inl ⟨j', sl', hsl', rfl, rfl, rfl, rfl⟩⟩ :
      SegIn bl bi' L' sl'.st.nextVreg sl'.st.nextVreg sl'.st'.nextVreg sl'.st'.emitted.toList)
    omega
  · rw [hL] at hL'
    cases hL'
    refine ⟨rfl, ?_⟩
    have hB := hO1 bi L hL
    rcases Nat.lt_trichotomy j j' with hj | rfl | hj
    · have := (hB.stmt j sl hsl).2.2.2 j' sl' hj hsl'
      omega
    · rfl
    · have := (hB.stmt j' sl' hsl').2.2.2 j sl hj hsl
      omega
  · have := segIn_hi hO1 (⟨hL', .inl ⟨j', sl', hsl', rfl, rfl, rfl, rfl⟩⟩ :
      SegIn bl bi' L' sl'.st.nextVreg sl'.st.nextVreg sl'.st'.nextVreg sl'.st'.emitted.toList)
    have := segIn_lo hO2 hlt hL' (⟨hL, .inl ⟨j, sl, hsl, rfl, rfl, rfl, rfl⟩⟩ :
      SegIn bl bi L sl.st.nextVreg sl.st.nextVreg sl.st'.nextVreg sl.st'.emitted.toList)
    omega

include hO1 hO2 in
/-- A statement's and a terminator's ranges share no vreg. -/
theorem stmt_term {bi bi' j x : Nat} {L L' : BLow} {sl : SLow}
    (hL : bl[bi]? = some L) (hsl : L.sl[j]? = some sl) (hL' : bl[bi']? = some L')
    (h1 : sl.st.nextVreg ≤ x) (h2 : x < sl.st'.nextVreg)
    (h1' : L'.tst.nextVreg ≤ x) (h2' : x < L'.tst'.nextVreg) : False := by
  rcases Nat.lt_trichotomy bi bi' with hlt | rfl | hlt
  · have := segIn_hi hO1 (⟨hL, .inl ⟨j, sl, hsl, rfl, rfl, rfl, rfl⟩⟩ :
      SegIn bl bi L sl.st.nextVreg sl.st.nextVreg sl.st'.nextVreg sl.st'.emitted.toList)
    have := (hO2 bi bi' L L' hlt hL hL').term.1
    omega
  · rw [hL] at hL'
    cases hL'
    have := ((hO1 bi L hL).stmt j sl hsl).2.2.1
    omega
  · have := (hO2 bi' bi L' L hlt hL' hL).stmt j sl hsl
    have := (hO1 bi' L' hL').term
    omega

include hO1 in
theorem seg_lo {f : Clif.Function} {lo mid hi : Nat} {c : List MInst}
    (h : Seg f bl lo mid hi c) : v ≤ lo := by
  obtain ⟨bi, B, L, -, hL, ⟨j, sl, hsl, rfl, -, -, -⟩ | ⟨rfl, -, -, -⟩⟩ := h
  · exact ((hO1 bi L hL).stmt j sl hsl).1
  · exact (hO1 bi L hL).term.1

end Ord

/-! ## The instructions of `lowerFunction`'s VCode -/

theorem mem_valueDefs {f : Clif.Function} {B : Clif.Block} (hB : B ∈ f.blocks) {x : Nat}
    (hx : x ∈ B.params.map (·.1) ∨ x ∈ B.body.flatMap (·.results)) : x ∈ valueDefs f :=
  List.mem_flatMap.mpr ⟨B, hB, List.mem_append.mpr hx⟩

/-- The entry block's `Args` and loads define CLIF values (before the renaming). -/
theorem pre_defs {f : Clif.Function} {bi : Nat} {i : MInst} (h : i ∈ pre f id bi) :
    ∀ d ∈ vdefs i, d ∈ valueDefs f := by
  unfold pre at h
  split at h
  · rename_i B hB
    have hBm : B ∈ f.blocks := List.mem_of_getElem? hB
    have hpar : ∀ q ∈ entryParams f B, q.1.1.1 ∈ valueDefs f := by
      intro q hq
      have h1 := (List.of_mem_zip hq).1
      have h2 := (List.of_mem_zip h1).1
      exact mem_valueDefs hBm (.inl (List.mem_map.mpr ⟨_, h2, rfl⟩))
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · let ns : List (Nat × Reg) := (entryParams f B).filterMap fun q => match q.1.2 with
        | .reg p => some (q.1.1.1, p)
        | .stack _ => none
      have e : entryRegs f id B = argPairs ns := by
        simp only [entryRegs, argPairs, ns, List.map_filterMap]
        congr 1
        funext q
        unfold entryRegOf
        split <;> simp_all
      intro d hd
      rw [e] at hd
      unfold vdefs at hd
      rw [operands_args] at hd
      simp only [argOps, List.map_map, List.filter_map, List.mem_map, List.mem_filter,
        Function.comp_def] at hd
      obtain ⟨q, ⟨hq, -⟩, rfl⟩ := hd
      obtain ⟨q', hq', hq''⟩ := List.mem_filterMap.mp hq
      split at hq''
      · cases hq''; exact hpar q' hq'
      · cases hq''
    · simp only [entryLoads, List.mem_filterMap] at h
      obtain ⟨q, hq, hq'⟩ := h
      unfold entryLoadOf at hq'
      split at hq'
      · rename_i off _
        cases hq'
        intro d hd
        have hd' : d ∈ [q.1.1.1] := hd
        rw [List.mem_singleton] at hd'
        rw [hd']
        exact hpar q hq
      · cases hq'
  · simp at h

/-- The entry block's `Args` and loads are no calls. -/
theorem pre_not_call {f : Clif.Function} {bi : Nat} {i : MInst} (h : i ∈ pre f id bi) :
    (∀ c, i ≠ .call c) ∧ ∀ c ti, i ≠ .tryCall c ti := by
  unfold pre at h
  split at h
  · simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h)⟩
    · simp only [entryLoads, List.mem_filterMap] at h
      obtain ⟨q, -, hq⟩ := h
      unfold entryLoadOf at hq
      split at hq
      · cases hq; exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h)⟩
      · cases hq
  · simp at h

/-- A raw block of the recorded lowering is (renamed) a block of the VCode. -/
theorem raw_mem {f : Clif.Function} {bl : List BLow} {bi : Nat} {B : Clif.Block} {L : BLow}
    (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L) :
    fixBlock (asmR f bl) (rawBlock f bl bi B) ∈ (vcBlocksOf f bl).toList := by
  simp only [vcBlocksOf, List.toList_toArray, List.mem_map, List.mem_append]
  refine ⟨rawBlock f bl bi B, .inl ⟨((B, L), bi), ?_, rfl⟩, rfl⟩
  rw [List.mem_zipIdx_iff_getElem?]
  simp [List.getElem?_zip_eq_some, hB, hL]

/-- **The instructions of `lowerFunction`'s VCode, with their positions**: an entry-block
`Args`/load or a `mov` of `extraOf` (renamed), an edge block's `jump`, or the renaming of the
instruction at index `k - o` of a run segment placed at offset `o` of the block. -/
theorem blk_cases {f : Clif.Function} {vc : VCode} {bl : List BLow}
    (hvb : vc.blocks = vcBlocksOf f bl) {vb : VBlock} (hvb' : vb ∈ vc.blocks.toList) {k : Nat}
    {i : MInst} (hi : vb.insts[k]? = some i) :
    (∃ bi i0, i0 ∈ pre f id bi ∧ i = i0.mapRegs (asmR f bl)) ∨
    (∃ r out, r ∈ valueDefs f ∧ (∀ n c, out ≠ .vreg n c) ∧
      i = .mov .size64 (.vreg (asmG f bl r) .int) out) ∨
    (∃ l, i = .jump l) ∨
    (∃ lo mid hi c m o, Seg f bl lo mid hi c ∧ o ≤ k ∧ c[k - o]? = some m ∧
      i = m.mapRegs (asmR f bl) ∧
      ∀ p m', c[p]? = some m' → vb.insts[o + p]? = some (m'.mapRegs (asmR f bl))) := by
  have hg := asm_ren f bl
  rw [hvb] at hvb'
  rcases Backend.Proof.Spill.mem_vcBlocksOf' hvb' with ⟨bi, B, L, hB, hL, rfl⟩ |
    ⟨B, L, e, -, he, rfl⟩
  · have hW : (fixBlock (asmR f bl) (rawBlock f bl bi B)).insts.toList =
        pre f (asmR f bl) bi ++
          ((List.range B.body.length).map (seg f (asmR f bl) bl bi)).flatten ++
          tseg (asmR f bl) bl bi :=
      rawBlock_insts f (asmR f bl) bl bi B
    have hget : ∀ x, (fixBlock (asmR f bl) (rawBlock f bl bi B)).insts[x]? =
        (pre f (asmR f bl) bi ++
          ((List.range B.body.length).map (seg f (asmR f bl) bl bi)).flatten ++
          tseg (asmR f bl) bl bi)[x]? := fun x => by rw [← Array.getElem?_toList, hW]
    rw [hget] at hi
    rcases idx_split _ _ _ k i hi with h1 | ⟨j, s, o, hs, ho, hx, hall⟩ | ⟨o, ho, hx, hall⟩
    · left
      have hm := List.mem_of_getElem? h1
      rw [← pre_map] at hm
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hm
      exact ⟨bi, i0, hi0, rfl⟩
    · have hj : j < B.body.length := by
        refine (Nat.lt_or_ge j B.body.length).resolve_right fun hj => ?_
        simp [show ¬ j < B.body.length by omega] at hs
      have hs' : s = seg f (asmR f bl) bl bi j := by
        simp [hj] at hs
        exact hs.symm
      subst hs'
      cases hstm : B.body[j]? with
      | none => simp [seg, hB, hL, hstm] at hx
      | some stm =>
        cases hsl : L.sl[j]? with
        | none => simp [seg, hB, hL, hstm, hsl] at hx
        | some sl =>
          simp only [seg, hB, hL, hstm, hsl] at hx hall
          rw [List.getElem?_map] at hx
          by_cases hp : k - o < sl.st'.emitted.toList.length
          · rw [List.getElem?_append_left hp] at hx
            obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hx
            right; right; right
            refine ⟨_, _, _, _, m, o,
              ⟨bi, B, L, hB, hL, .inl ⟨j, sl, hsl, rfl, rfl, rfl, rfl⟩⟩, ho, hm, rfl,
              fun p m' hp' => ?_⟩
            have hpl : p < sl.st'.emitted.toList.length := (List.getElem?_eq_some_iff.mp hp').1
            rw [hget, hall p (by rw [List.length_map, List.length_append]; omega),
              List.getElem?_map, List.getElem?_append_left hpl, hp']
            rfl
          · rw [List.getElem?_append_right (by omega)] at hx
            obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hx
            have hmem := List.mem_of_getElem? hm
            simp only [extraOf, List.mem_filterMap] at hmem
            obtain ⟨q, hq, hq'⟩ := hmem
            split at hq'
            · cases hq'
            · rename_i out hout' _
              cases hq'
              have hout : ∀ n c, out ≠ .vreg n c := fun n c e => hout' n c e
              right; left
              refine ⟨q.1, out, mem_valueDefs (List.mem_of_getElem? hB)
                (.inr (List.mem_flatMap.mpr ⟨stm, List.mem_of_getElem? hstm,
                  (List.of_mem_zip hq).1⟩)), hout, ?_⟩
              show MInst.mov .size64 (asmR f bl (.vreg q.1 .int)) (asmR f bl out) = _
              rw [hg.vreg, hg.real out hout]
            · cases hq'
    · simp only [tseg, hL] at hx hall
      rw [List.getElem?_map] at hx
      obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hx
      right; right; right
      refine ⟨_, _, _, _, m, o, ⟨bi, B, L, hB, hL, .inr ⟨rfl, rfl, rfl, rfl⟩⟩, ho, hm, rfl,
        fun p m' hp' => ?_⟩
      have hpl := (List.getElem?_eq_some_iff.mp hp').1
      rw [hget]
      simp only [tseg, hL]
      rw [hall p (by rw [List.length_map]; omega), List.getElem?_map, hp']
      rfl
  · obtain ⟨tl, hie⟩ := edgeBlocks_insts he
    have hm : i ∈ (fixBlock (asmR f bl) e).insts.toList :=
      Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)
    simp only [fixBlock, hie] at hm
    simp at hm
    exact .inr (.inr (.inl ⟨tl, hm⟩))

/-- **No alias renames a CLIF value to `t`**, a vreg of no statement's results that is no CLIF
value: an alias target is a statement's result register, a CLIF value's vreg or a vreg of the
statement's range (`Kill.killRunsHyp`'s `OutKill`). -/
theorem alias_ne {p : Clif.Program} {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} {bl : List BLow} (hsub : InSubset p f) (hd : Dominated f) (hs : LowerScope f)
    (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hlb : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl) {t : Nat} (ht : ctx.valDef.size ≤ t)
    (hno : ∀ (bi : Nat) (L : BLow) (j : Nat) (sl : SLow), bl[bi]? = some L → L.sl[j]? = some sl →
      sl.st.nextVreg ≤ t → t < sl.st'.nextVreg → ∀ cl, [Reg.vreg t cl] ∉ sl.rss) :
    ∀ q ∈ aliasOf f bl, q.2 ≠ t := by
  intro q hq he
  have ha := abiSigsOk_of_inSubset hsub
  obtain ⟨hS, -, -⟩ := killRunsHyp f ctx ranges st0 hd hs ha hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  obtain ⟨hord, -⟩ := driver_ord hlb
  have hN : st0.nextVreg = ctx.valDef.size := hcf.size.1
  obtain ⟨bi, B, L, j, stm, sl, hB, hL, hstm, hsl, hr, rs, c, hrs, hrse⟩ := mem_aliasOf hq
  obtain ⟨-, hcs, -⟩ := hspec bi B L hB hL
  obtain ⟨info, hinf, hic, hres⟩ := hcf.stmt bi B j stm hB hstm
  obtain ⟨tr, hrun⟩ := hcs j sl hsl
  rw [hstart bi L hL] at hrun
  have hge : ctx.valDef.size ≤ sl.st.nextVreg := hN ▸ ((hord bi L hL).stmt j sl hsl).1
  obtain ⟨-, hout⟩ := hS _ info stm.inst _ _ _ _ hinf hic hge hrun
  have hne : info.results ≠ [] := by
    rw [hres]; intro h0; rw [h0] at hr; cases hr
  obtain ⟨h1, -⟩ := hout hne _ rfl rs hrs q.2 c (by rw [hrse]; simp)
  rcases h1 with h1 | h1
  · omega
  · apply hno bi L j sl hL hsl (he ▸ h1.1) (he ▸ h1.2) c
    rw [← he, ← hrse]
    exact hrs

/-! ## The theorem -/

/-- **`GotRunHyp` from the run segments' ranges and the direct call's own run.** -/
theorem gotRunHyp_of (hS : SegRangeHyp) (hLoc : GotLocalHyp) : GotRunHyp := by
  intro p f vc hsub hd hs hl ctx ranges st0 bl hbc hlb bi0 B0 L0 ms c t n hB0 hL0 hsrc ht hgl
    hcm hdst
  obtain ⟨hD1, hOrd1, hRss⟩ := hLoc p f vc hsub hd hs hl ctx ranges st0 bl hbc hlb bi0 B0 L0 ms
    c t n hB0 hL0 hsrc ht hgl hcm hdst
  have hR := hS p f ctx ranges st0 bl hsub hd hs hbc hlb
  obtain ⟨ctx', ranges', st0', bl', hbc', hlb', hvb, -, -⟩ := lowerFunction_run hl
  rw [hbc] at hbc'
  cases hbc'
  rw [hlb] at hlb'
  cases hlb'
  have hcf := ctxFacts_of hbc
  have hN : st0.nextVreg = ctx.valDef.size := hcf.size.1
  obtain ⟨hO1, hO2⟩ := driver_ord hlb
  have hg := asm_ren f bl
  have hfix : ∀ x, ctx.valDef.size ≤ x → asmG f bl x = x := fun x hx => asm_fix bl hbc hx
  have hval : ∀ x ∈ valueDefs f, x < ctx.valDef.size := fun x hx => hN ▸ (hcf.vals x hx).1
  have hgot_ren : (MInst.loadExtNameGot (.vreg t .int) n).mapRegs (asmR f bl) =
      .loadExtNameGot (.vreg t .int) n := by
    show MInst.loadExtNameGot (asmR f bl (.vreg t .int)) n = _
    rw [hg.vreg, hfix t ht]
  -- the direct call's segment
  obtain ⟨lo0, mid0, hi0, c0, hSeg0, hGc0, hD0, hO0, hrng, hvbG⟩ :
      ∃ lo0 mid0 hi0 c0, Seg f bl lo0 mid0 hi0 c0 ∧
        MInst.loadExtNameGot (.vreg t .int) n ∈ c0 ∧
        (∀ m ∈ c0, t ∈ vdefs m → m = .loadExtNameGot (.vreg t .int) n) ∧
        (∀ (k : Nat) (ci : CallInfo),
          (c0[k]? = some (.call ci) ∨ ∃ ti, c0[k]? = some (.tryCall ci ti)) →
          ci.dest = .reg (.vreg t .int) →
          ∃ k' < k, c0[k']? = some (.loadExtNameGot (.vreg t .int) n)) ∧
        (∀ (bi : Nat) (L : BLow) (j : Nat) (sl : SLow), bl[bi]? = some L → L.sl[j]? = some sl →
          sl.st.nextVreg ≤ t → t < sl.st'.nextVreg → lo0 ≤ t → t < hi0 →
          ∀ cl, [Reg.vreg t cl] ∉ sl.rss) ∧
        ∃ vb ∈ vc.blocks.toList, MInst.loadExtNameGot (.vreg t .int) n ∈ vb.insts.toList := by
    have hvb0 : fixBlock (asmR f bl) (rawBlock f bl bi0 B0) ∈ vc.blocks.toList := by
      rw [hvb]; exact raw_mem hB0 hL0
    have hW : (fixBlock (asmR f bl) (rawBlock f bl bi0 B0)).insts.toList =
        pre f (asmR f bl) bi0 ++
          ((List.range B0.body.length).map (seg f (asmR f bl) bl bi0)).flatten ++
          tseg (asmR f bl) bl bi0 :=
      rawBlock_insts f (asmR f bl) bl bi0 B0
    rcases hsrc with ⟨j0, stm0, sl0, fn, args, hstm0, hsl0, hin0, hms0⟩ |
      ⟨T, fn, args, et, hte, hT, hms0⟩
    · refine ⟨_, _, _, _, ⟨bi0, B0, L0, hB0, hL0, .inl ⟨j0, sl0, hsl0, rfl, rfl, rfl, rfl⟩⟩,
        ?_, ?_, ?_, ?_, _, hvb0, ?_⟩
      · rw [hms0]; exact hgl
      · rw [hms0]; exact hD1
      · rw [hms0]; exact hOrd1
      · intro bi L j sl hL hsl h1 h2 h3 h4 cl
        obtain ⟨rfl, rfl⟩ := stmt_ident hO1 hO2 hL hsl hL0 hsl0 h1 h2 h3 h4
        obtain rfl : L = L0 := Option.some.inj (hL.symm.trans hL0)
        obtain rfl : sl = sl0 := Option.some.inj (hsl.symm.trans hsl0)
        exact hRss _ _ hsl0 hms0 cl
      · rw [hW]
        refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr
          ⟨seg f (asmR f bl) bl bi0 j0, List.mem_map.mpr
            ⟨j0, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hstm0).1, rfl⟩, ?_⟩))
        simp only [seg, hB0, hL0, hstm0, hsl0]
        exact List.mem_map.mpr ⟨_, List.mem_append_left _ (hms0 ▸ hgl), hgot_ren⟩
    · have hfx : fixTry L0.tl L0.tst'.emitted.toList = tryFix T.info ms := by
        rw [hT, hms0]; rfl
      have hGc : MInst.loadExtNameGot (.vreg t .int) n ∈ tryFix T.info ms := by
        obtain ⟨k, hk⟩ := List.getElem?_of_mem hgl
        exact List.mem_of_getElem? (tryFix_of_get hk (fun _ h => by cases h))
      refine ⟨_, _, _, _, ⟨bi0, B0, L0, hB0, hL0, .inr ⟨rfl, rfl, rfl, rfl⟩⟩, ?_, ?_, ?_, ?_, _,
        hvb0, ?_⟩
      · rw [hfx]; exact hGc
      · rw [hfx]
        intro m hm htm
        rcases tryFix_mem hm with hm | ⟨cl, hcl, rfl⟩
        · exact hD1 m hm htm
        · rw [vdefs_tryCall] at htm
          cases hD1 _ hcl htm
      · rw [hfx]
        intro k ci hk hdst'
        have hk' : ms[k]? = some (.call ci) ∨ ∃ ti, ms[k]? = some (.tryCall ci ti) := by
          rcases hk with hk | ⟨ti, hk⟩
          · rcases tryFix_get hk with h | ⟨cl, h, he⟩
            · exact .inl h
            · cases he
          · rcases tryFix_get hk with h | ⟨cl, h, he⟩
            · exact .inr ⟨ti, h⟩
            · cases he; exact .inl h
        obtain ⟨k', hk'', hg'⟩ := hOrd1 k ci hk' hdst'
        exact ⟨k', hk'', tryFix_of_get hg' (fun _ h => by cases h)⟩
      · intro bi L j sl hL hsl h1 h2 h3 h4
        exact (stmt_term hO1 hO2 hL hsl hL0 h1 h2 h3 h4).elim
      · rw [hW]
        refine List.mem_append_right _ ?_
        simp only [tseg, hL0, hfx]
        exact List.mem_map.mpr ⟨_, hGc, hgot_ren⟩
  -- `t` is in the segment's range
  have htr : lo0 ≤ t ∧ t < hi0 :=
    (hR lo0 mid0 hi0 c0 hSeg0 _ hGc0).1 t (by rw [vdefs_got]; exact List.mem_singleton_self t)
  -- no CLIF value is renamed to `t`
  have hal : ∀ q ∈ aliasOf f bl, q.2 ≠ t := alias_ne hsub hd hs hbc hlb ht
    (fun bi L j sl hL hsl h1 h2 => hrng bi L j sl hL hsl h1 h2 htr.1 htr.2)
  have hgv : ∀ x, x < ctx.valDef.size → asmG f bl x ≠ t := by
    intro x hx he
    rcases asm_gn_cases f bl x with e | ⟨q, hq, e⟩
    · rw [e] at he; omega
    · exact hal q hq (e ▸ he)
  have hslo : ∀ {lo mid hi : Nat} {c' : List MInst}, Seg f bl lo mid hi c' →
      ctx.valDef.size ≤ lo := fun h => hN ▸ seg_lo hO1 h
  -- every instruction defining `t` is the GOT load
  have hdef : ∀ vb ∈ vc.blocks.toList, ∀ (k : Nat) (i : MInst), vb.insts[k]? = some i →
      gotDefB t n i = true := by
    intro vb hvb' k i hi
    apply gotDefB_of
    by_cases hti : t ∈ vdefs i
    · right
      rcases blk_cases hvb hvb' hi with ⟨bi, i0, hi0, rfl⟩ | ⟨r, out, hr, hout, rfl⟩ |
        ⟨l, rfl⟩ | ⟨lo, mid, hi', c', m, o, hseg, -, hm, rfl, -⟩
      · obtain ⟨d0, hd0, he⟩ := vdefs_mapRegs hg i0 hti
        exact absurd he.symm (hgv d0 (hval d0 (pre_defs hi0 d0 hd0)))
      · exact absurd (mov_defs _ out hout t hti).symm (hgv r (hval r hr))
      · rw [vdefs_jump] at hti; cases hti
      · obtain ⟨d0, hd0, he⟩ := vdefs_mapRegs hg m hti
        obtain ⟨h1, h2⟩ := (hR lo mid hi' c' hseg m (List.mem_of_getElem? hm)).1 d0 hd0
        have hlo := hslo hseg
        rw [hfix d0 (by omega)] at he
        subst he
        have hc := asm_disj hlb hseg hSeg0 h1 h2 htr.1 htr.2
        subst hc
        rw [hD0 m (List.mem_of_getElem? hm) hd0, hgot_ren]
    · exact .inl hti
  -- every call through `t` follows the GOT load in its block
  have hsite : ∀ vb ∈ vc.blocks.toList, ∀ k, gotSiteB t n vb k = true := by
    intro vb hvb' k
    have key : ∀ (i : MInst) (ci : CallInfo), vb.insts[k]? = some i →
        (i = .call ci ∨ ∃ ti, i = .tryCall ci ti) → ci.dest = .reg (.vreg t .int) →
        gotBefore t n vb k = true := by
      intro i ci hi hci hdci
      rcases blk_cases hvb hvb' hi with ⟨bi, i0, hi0, rfl⟩ | ⟨r, out, -, -, rfl⟩ |
        ⟨l, rfl⟩ | ⟨lo, mid, hi', c', m, o, hseg, ho, hm, rfl, hall⟩
      · exfalso
        obtain ⟨hn1, hn2⟩ := pre_not_call hi0
        rcases hci with h | ⟨ti, h⟩
        · obtain ⟨c1, rfl, -⟩ := mapRegs_call_inv h
          exact hn1 c1 rfl
        · obtain ⟨c1, rfl, -⟩ := mapRegs_tryCall_inv h
          exact hn2 c1 ti rfl
      · rcases hci with h | ⟨ti, h⟩ <;> cases h
      · rcases hci with h | ⟨ti, h⟩ <;> cases h
      · obtain ⟨c1, hm1, hc1⟩ : ∃ c1, (m = .call c1 ∨ ∃ ti, m = .tryCall c1 ti) ∧
            ci = callMap (asmR f bl) c1 := by
          rcases hci with h | ⟨ti, h⟩
          · obtain ⟨c1, rfl, rfl⟩ := mapRegs_call_inv h
            exact ⟨c1, .inl rfl, rfl⟩
          · obtain ⟨c1, rfl, rfl⟩ := mapRegs_tryCall_inv h
            exact ⟨c1, .inr ⟨ti, rfl⟩, rfl⟩
        subst hc1
        obtain ⟨d0, hd0, hgd⟩ := callMap_dest_inv hg hdci
        rcases (hR lo mid hi' c' hseg m (List.mem_of_getElem? hm)).2 c1 d0 hm1 hd0 with
          hlt | ⟨h1, h2⟩
        · exact absurd hgd (hgv d0 hlt)
        · have hlo := hslo hseg
          rw [hfix d0 (by omega)] at hgd
          subst hgd
          have hc := asm_disj hlb hseg hSeg0 h1 h2 htr.1 htr.2
          subst hc
          have hk1 : c'[k - o]? = some (.call c1) ∨ ∃ ti, c'[k - o]? = some (.tryCall c1 ti) := by
            rcases hm1 with rfl | ⟨ti, rfl⟩
            · exact .inl hm
            · exact .inr ⟨ti, hm⟩
          obtain ⟨k', hk', hgk⟩ := hO0 (k - o) c1 hk1 hd0
          have hpos := hall k' _ hgk
          rw [hgot_ren] at hpos
          simp only [gotBefore, List.any_eq_true, List.mem_range, decide_eq_true_eq]
          exact ⟨o + k', by omega, hpos⟩
    unfold gotSiteB
    cases hi : vb.insts[k]? with
    | none => rfl
    | some i =>
      cases i with
      | call ci =>
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
        by_cases hdc : ci.dest = .reg (.vreg t .int)
        · exact .inr (key _ ci hi (.inl rfl) hdc)
        · exact .inl hdc
      | tryCall ci ti =>
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
        by_cases hdc : ci.dest = .reg (.vreg t .int)
        · exact .inr (key _ ci hi (.inr ⟨ti, rfl⟩) hdc)
        · exact .inl hdc
      | _ => rfl
  -- the GOT symbol
  have hsym : gotSym vc t = some n := by
    unfold gotSym
    obtain ⟨vbG, hvbG, hGG⟩ := hvbG
    refine findSome_eq (fun x hx m hm => ?_)
      ⟨MInst.loadExtNameGot (.vreg t .int) n, ?_, by simp⟩
    · simp only [List.mem_flatMap, Array.mem_toList_iff] at hx
      obtain ⟨vb', hvb', hx⟩ := hx
      obtain ⟨k', hk'⟩ := Array.getElem?_of_mem hx
      have hdx := hdef vb' (Array.mem_toList_iff.mpr hvb') k' x hk'
      split at hm
      · rename_i t' n'
        split at hm
        · rename_i htt
          subst htt
          cases hm
          obtain ⟨ops, hops, ho⟩ := operands_got t' m
          simp only [gotDefB, hops, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
            at hdx
          rcases hdx with hdx | hdx
          · obtain ⟨o, hom, hod, hov⟩ := ho
            obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hom
            have := Array.any_eq_false.mp hdx i' (by simpa using hi')
            simp only [Array.getElem_toList] at hod hov
            exact absurd this (by simp [hod, hov])
          · cases hdx; rfl
        · cases hm
      · cases hm
    · simp only [List.mem_flatMap, Array.mem_toList_iff]
      exact ⟨vbG, Array.mem_toList_iff.mp hvbG, Array.mem_toList_iff.mp hGG⟩
  have hgb : gotB vc t n = true := by
    simp only [gotB]
    refine (array_all_iff _ _).2 fun q vb hq => ?_
    have hvbm : vb ∈ vc.blocks.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hq)
    simp only [Bool.and_eq_true]
    exact ⟨(array_all_iff _ _).2 fun k i hi => hdef vb hvbm k i hi,
      List.all_eq_true.2 fun k _ => hsite vb hvbm k⟩
  unfold gotOf
  rw [hsym]
  simp [hgb]

end E2E.LinkCheck
