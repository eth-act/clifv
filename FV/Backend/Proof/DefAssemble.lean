import FV.Backend.Proof.DefAssembleBase
import FV.Backend.Proof.KillTryDefs
import FV.Backend.Proof.KillDriver
import FV.Backend.Proof.SpillCtlPipe
import FV.Backend.Proof.EntryParams

/-!
# Definite assignment of `lowerFunction`'s VCode from the run facts

`lowerDefined_of_runs`: under the run facts `DefRunsHyp`, `lowerFunction`'s VCode on in-scope
input with the signature's entry parameters (`entryParamsB`) has definedness sets with nothing
defined on entry. By `Spill.defined_of_paths` it suffices that every use is defined on every path
of the CFG that reaches it (`UsesDefined`) and that every edge into a block with parameters
passes an argument for each (`ParamArgs`, from `LowOk`).

The path invariant (`Inv`): on entry to the code of CLIF block `bi`, the vregs of the values
available there (`availIn`, renamed) and, but for the entry block, its parameters are defined
(`GoodC`); on entry to an edge block of `bi`, what is defined at the end of `bi`'s code
(`EndDef`: the renamed values available at the end of `bi`, and a `try_call`'s result vregs).
Inside a block (`avail_def`, `uses_def`, `end_def`): the entry block's parameters are defined by
its argument setup, a statement's results by its run (`OutDef`: a reached value's vreg, the alias
renaming makes them equal, or a fresh vreg its run defines), and a run's uses are reached values,
available where it stands, or fresh vregs an earlier instruction of the run defines (`RunDef`,
`SegDef`; for a `try_call` also after the call becomes the `tryCall`).
-/

namespace Backend.Proof.DefRun

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Kill

/-! ## Lists -/

theorem idx_app {α : Type} {l1 l2 : List α} {k : Nat} {x : α} (h : (l1 ++ l2)[k]? = some x) :
    (k < l1.length ∧ l1[k]? = some x ∧ (l1 ++ l2).take k = l1.take k) ∨
    (l1.length ≤ k ∧ l2[k - l1.length]? = some x ∧
      (l1 ++ l2).take k = l1 ++ l2.take (k - l1.length)) := by
  by_cases hk : k < l1.length
  · left
    refine ⟨hk, by rwa [List.getElem?_append_left hk] at h, ?_⟩
    rw [List.take_append, Nat.sub_eq_zero_of_le (Nat.le_of_lt hk)]
    simp
  · right
    have hk' : l1.length ≤ k := Nat.le_of_not_lt hk
    refine ⟨hk', by rwa [List.getElem?_append_right hk'] at h, ?_⟩
    rw [List.take_append, List.take_of_length_le hk']

theorem flat_idx {α : Type} (g : Nat → List α) : ∀ (n k : Nat) (x : α),
    (((List.range n).map g).flatten)[k]? = some x →
    ∃ j, j < n ∧ ∃ k', (g j)[k']? = some x ∧
      ((List.range n).map g).flatten.take k = ((List.range j).map g).flatten ++ (g j).take k'
  | 0, k, x, h => by simp at h
  | n + 1, k, x, h => by
    rw [List.range_succ, List.map_append, List.flatten_append] at h ⊢
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil] at h ⊢
    rcases idx_app h with ⟨-, h1, e⟩ | ⟨-, h1, e⟩
    · obtain ⟨j, hj, k', h2, e'⟩ := flat_idx g n k x h1
      exact ⟨j, by omega, k', h2, by rw [e, e']⟩
    · exact ⟨n, by omega, _, h1, e⟩

theorem mem_flat_le {α : Type} (g : Nat → List α) {j j' : Nat} (h : j ≤ j') {x : α}
    (hx : x ∈ ((List.range j).map g).flatten) : x ∈ ((List.range j').map g).flatten := by
  simp only [List.mem_flatten, List.mem_map, List.mem_range] at hx ⊢
  obtain ⟨l, ⟨i, hi, rfl⟩, hx⟩ := hx
  exact ⟨g i, ⟨i, by omega, rfl⟩, hx⟩

theorem mem_flat_seg {α : Type} (g : Nat → List α) {j j' : Nat} (h : j < j') {x : α}
    (hx : x ∈ g j) : x ∈ ((List.range j').map g).flatten := by
  simp only [List.mem_flatten, List.mem_map, List.mem_range]
  exact ⟨g j, ⟨j, h, rfl⟩, hx⟩

theorem mem_take_of {α : Type} {l : List α} {k k' : Nat} {x : α} (hk : k' < k)
    (h : l[k']? = some x) : x ∈ l.take k := by
  apply List.mem_of_getElem? (i := k')
  rw [List.getElem?_take_of_lt hk, h]

/-! ## The uses of a run segment -/

/-- **The uses of a code list `c`**: vregs of CLIF values reached from `S`, or vregs from `lo` on
defined by an earlier instruction of `c`. -/
def SegDef (ctx : Ctx) (S : List Nat) (lo : Nat) (c : List MInst) : Prop :=
  ∀ (k : Nat) (m : MInst), c[k]? = some m → ∀ u ∈ useVregs m,
    (u < ctx.valDef.size ∧ Reach ctx S u) ∨
      (lo ≤ u ∧ ∃ k' m', k' < k ∧ c[k']? = some m' ∧ u ∈ defVregs m')

theorem segDef_of_run {ctx : Ctx} {S : List Nat} {s s' : LState} (h : RunDef ctx S s s')
    (he : s.emitted = #[]) : SegDef ctx S s.nextVreg s'.emitted.toList := by
  obtain ⟨ms, hms, hk⟩ := h
  have e : s'.emitted.toList = ms := by rw [hms, he]; simp
  rw [e]
  exact hk

/-- Replacing the last `call` by the `tryCall` keeps `SegDef`. -/
theorem segDef_tryFix {ctx : Ctx} {S : List Nat} {lo : Nat} {ys : List MInst} {cl : CallInfo}
    (info : TryInfo) (h : SegDef ctx S lo (ys ++ [.call cl])) :
    SegDef ctx S lo (ys ++ [.tryCall cl info]) := by
  have keep : ∀ k' m', k' < ys.length → (ys ++ [MInst.call cl])[k']? = some m' →
      (ys ++ [MInst.tryCall cl info])[k']? = some m' := by
    intro k' m' hk' hm'
    rw [List.getElem?_append_left hk'] at hm' ⊢
    exact hm'
  intro k x hx u hu
  rcases idx_app hx with ⟨hk, hx1, -⟩ | ⟨hk, hx1, -⟩
  · rcases h k x (by rw [List.getElem?_append_left hk]; exact hx1) u hu with h1 |
        ⟨h1, k', m', hk', hm', hd⟩
    · exact .inl h1
    · exact .inr ⟨h1, k', m', hk', keep k' m' (by omega) hm', hd⟩
  · have hk0 : k - ys.length = 0 := by
      cases h' : k - ys.length with
      | zero => rfl
      | succ n => rw [h'] at hx1; simp at hx1
    rw [hk0] at hx1
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx1
    subst hx1
    rw [asm_useVregs_tryCall] at hu
    rcases h k (.call cl) (by rw [List.getElem?_append_right hk, hk0]; rfl) u hu with h1 |
        ⟨h1, k', m', hk', hm', hd⟩
    · exact .inl h1
    · exact .inr ⟨h1, k', m', hk', keep k' m' (by omega) hm', hd⟩

/-! ## Definedness inside a CLIF block's code -/

/-- **Defined on entry to CLIF block `bi`'s code**: the renamed values available on entry and,
but for the entry block, the parameters. -/
def GoodC (f : Clif.Function) (ctx : Ctx) (bl : List BLow) (bi v : Nat) : Prop :=
  (∃ y ∈ (availIn f ctx).getD bi [], v = asmG f bl y) ∨
    (bi ≠ 0 ∧ ∃ B, f.blocks[bi]? = some B ∧ v ∈ B.params.map (·.1))

/-- **Defined at the end of CLIF block `bi`'s code**: the renamed values available there, and a
`try_call`'s result vregs. -/
def EndDef (f : Clif.Function) (ctx : Ctx) (bl : List BLow) (bi v : Nat) : Prop :=
  (∃ B, f.blocks[bi]? = some B ∧ ∃ y ∈ availOf f (availIn f ctx) bi B.body.length,
      v = asmG f bl y) ∨
    (∃ B L T et, f.blocks[bi]? = some B ∧ bl[bi]? = some L ∧ IsTryWith B.term et ∧
      L.tl = some T ∧ ∃ i, i < max (sigRets T.sig).length 2 ∧ v = L.tst.nextVreg + i)

/-- The code of CLIF block `bi` before statement `j`. -/
abbrev pfx (f : Clif.Function) (bl : List BLow) (bi j : Nat) : List MInst :=
  pre f (asmR f bl) bi ++ ((List.range j).map (seg f (asmR f bl) bl bi)).flatten

/-- The code of CLIF block `bi` (`B`). -/
abbrev codeOf (f : Clif.Function) (bl : List BLow) (bi : Nat) (B : Clif.Block) : List MInst :=
  pfx f bl bi B.body.length ++ tseg (asmR f bl) bl bi

theorem pfx_mono (f : Clif.Function) (bl : List BLow) (bi : Nat) {j j' : Nat} (h : j ≤ j')
    {m : MInst} (hm : m ∈ pfx f bl bi j) : m ∈ pfx f bl bi j' := by
  rcases List.mem_append.mp hm with hm | hm
  · exact List.mem_append_left _ hm
  · exact List.mem_append_right _ (mem_flat_le _ h hm)

/-- **The entry block's parameters** are defined by its argument setup (`entryParamsB`: one per
parameter of the signature). -/
theorem pre_param {f : Clif.Function} {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn)
    {B : Clif.Block} (hB : f.blocks[0]? = some B) (hen : entryParamsB f = true)
    (hE : (locsOf f.sig).length = f.sig.params.length ∧ ∃ bytes, sigParamBytes f.sig = .ok bytes)
    {y : Nat} (hy : y ∈ B.params.map (·.1)) : ∃ m ∈ pre f R 0, isDefV m (gn y) = true := by
  obtain ⟨hloc, bytes, hby⟩ := hE
  have hpre : pre f R 0 = .args (entryRegs f R B) :: entryLoads f R B := by simp [pre, hB]
  rw [hpre]
  have hlen : B.params.length = f.sig.params.length := by
    unfold entryParamsB at hen
    cases hbl : f.blocks with
    | nil => rw [hbl] at hB; simp at hB
    | cons B0 Bs =>
      rw [hbl] at hen hB
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hB
      subst hB
      simpa using hen
  have hbl := sigParamBytes_length hby
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
  obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
  have hi1 : i < (locsOf f.sig).length := by omega
  have hi2 : i < bytes.length := by omega
  have hq : ((B.params[i], (locsOf f.sig)[i]), bytes[i]) ∈ entryParams f B := by
    simp only [entryParams, hby]
    exact List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr
      ⟨List.getElem?_zip_eq_some.mpr ⟨List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi1⟩,
       List.getElem?_eq_getElem hi2⟩)
  rw [hpi] at hq
  cases hl : (locsOf f.sig)[i] with
  | reg r =>
    rw [hl] at hq
    have hv : ∀ q ∈ entryRegs f R B, ∃ n c, q.1 = Reg.vreg n c := by
      intro q hq'
      obtain ⟨q0, -, hq0⟩ := List.mem_filterMap.mp hq'
      unfold entryRegOf at hq0
      split at hq0
      · cases hq0; exact ⟨_, _, hg.vreg _ _⟩
      · cases hq0
    have hm : (Reg.vreg (gn p.1) .int, r) ∈ entryRegs f R B :=
      List.mem_filterMap.mpr ⟨_, hq, by simp [entryRegOf, hg.vreg]⟩
    exact ⟨_, List.mem_cons_self, isDefV_args hv hm⟩
  | stack off =>
    rw [hl] at hq
    have hm : MInst.load (loadOpOfBytes bytes[i]) (.vreg (gn p.1) .int) (.fpOffset (16 + off))
        trustedFlags ∈ entryLoads f R B :=
      List.mem_filterMap.mpr ⟨_, hq, by simp [entryLoadOf, hg.vreg]⟩
    exact ⟨_, List.mem_cons_of_mem _ hm, isDefV_load _ _ _ _⟩

section Block
variable {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
  {bl : List BLow} (hb : buildCtx f = .ok (ctx, ranges, st0))

include hb in
/-- A renamed `SegDef` segment: its uses are defined, given the reached values' vregs. -/
theorem segDef_ren {S : List Nat} {lo : Nat} {c : List MInst} (h : SegDef ctx S lo c)
    (hlo : ctx.valDef.size ≤ lo) {A : Nat → Bool} {Pf : List MInst}
    (hS : ∀ u, u < ctx.valDef.size → Reach ctx S u → DefBy A Pf (asmG f bl u)) {k : Nat}
    {x : MInst} (hx : (c.map (MInst.mapRegs (asmR f bl)))[k]? = some x) {u : Nat}
    (hu : u ∈ useVregs x) :
    DefBy A (Pf ++ (c.map (MInst.mapRegs (asmR f bl))).take k) u := by
  rw [List.getElem?_map] at hx
  cases hx0 : c[k]? with
  | none => rw [hx0] at hx; cases hx
  | some x0 =>
    rw [hx0] at hx
    obtain rfl : x0.mapRegs (asmR f bl) = x := by simpa using hx
    obtain ⟨u0, hu0, rfl⟩ := asm_useVregs_mapRegs (asm_ren f bl) hu
    rcases h k x0 hx0 u0 hu0 with ⟨h1, h2⟩ | ⟨h1, k', m', hk', hm', hd⟩
    · exact (hS u0 h1 h2).mono fun m hm => List.mem_append_left _ hm
    · have e := asm_fix bl hb (Nat.le_trans hlo h1)
      refine .inl ⟨m'.mapRegs (asmR f bl), List.mem_append_right _ (mem_take_of hk' ?_), ?_⟩
      · rw [List.getElem?_map, hm']; rfl
      · have := defVregs_mapRegs (asm_ren f bl) hd
        exact isDefV_iff.mpr this

variable (hd : Dominated f) (hs : LowerScope f) (ha : AbiSigsOk f)
  (hlb : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
    some bl)
  (hlf : LoopFacts f ctx bl) (hR : DefRunsHyp)
include hb hd hs ha hlb hlf hR

/-- **A statement's segment**: the renamed run code, whose uses meet `SegDef`; each result is
aliased to a reached value's vreg or to a fresh vreg its run defines. -/
theorem stmt_facts {bi j : Nat} {B : Clif.Block} {L : BLow} {stm : Clif.Stmt} {sl : SLow}
    (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L) (hstm : B.body[j]? = some stm)
    (hsl : L.sl[j]? = some sl) :
    ctx.valDef.size ≤ sl.st.nextVreg ∧
      SegDef ctx (instArgs stm.inst) sl.st.nextVreg sl.st'.emitted.toList ∧
      seg f (asmR f bl) bl bi j = sl.st'.emitted.toList.map (MInst.mapRegs (asmR f bl)) ∧
      ∀ y ∈ stm.results, ∃ n, (y, n) ∈ aliasOf f bl ∧
        ((n < ctx.valDef.size ∧ Reach ctx (instArgs stm.inst) n) ∨
          (sl.st.nextVreg ≤ n ∧ ∃ m ∈ sl.st'.emitted.toList, n ∈ defVregs m)) := by
  obtain ⟨hS, -, -⟩ := hR f ctx ranges st0 hd hs ha hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  obtain ⟨hord, -⟩ := driver_ord hlb
  have hN : st0.nextVreg = ctx.valDef.size := hcf.size.1
  obtain ⟨-, hcs, -, -, -, -⟩ := hspec bi B L hB hL
  obtain ⟨info, hinf, hic, hres⟩ := hcf.stmt bi B j stm hB hstm
  obtain ⟨tr, hrun⟩ := hcs j sl hsl
  rw [hstart bi L hL] at hrun
  have hge : ctx.valDef.size ≤ sl.st.nextVreg := hN ▸ ((hord bi L hL).stmt j sl hsl).1
  have he : sl.st.emitted = #[] :=
    hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)
  obtain ⟨hk, hout⟩ := hS _ info stm.inst _ _ _ _ hinf hic hge hrun
  obtain ⟨hlen, hone⟩ := hlf.results bi B L hB hL j stm sl hstm hsl
  have hvr : stm.results ≠ [] → ∀ rs ∈ sl.rss, ∀ r ∈ rs, ∃ n c, r = Reg.vreg n c ∧
      ((n < ctx.valDef.size ∧ Reach ctx (instArgs stm.inst) n) ∨
        (sl.st.nextVreg ≤ n ∧ ∃ m ∈ sl.st'.emitted.toList, n ∈ defVregs m)) := by
    intro hne rs hrs r hr
    have := hout (by rw [hres]; exact hne) _ rfl rs hrs r hr
    simpa [emittedSince, he] using this
  have hx : extraOf stm.results sl.rss = [] := by
    unfold extraOf
    refine List.filterMap_eq_nil_iff.mpr fun q hq => ?_
    have hne : stm.results ≠ [] := by intro h0; rw [h0] at hq; simp at hq
    obtain ⟨x, hx⟩ := hone q.1 q.2 hq
    obtain ⟨n, c, e, -⟩ := hvr hne q.2 (List.of_mem_zip hq).2 x (by rw [hx]; simp)
    obtain ⟨r, rs⟩ := q
    simp only at hx
    subst hx e
    rfl
  refine ⟨hge, segDef_of_run hk he, by simp only [seg, hB, hL, hstm, hsl, hx, List.append_nil],
    fun y hy => ?_⟩
  have hne : stm.results ≠ [] := by intro h0; rw [h0] at hy; cases hy
  obtain ⟨i, hi, hyi⟩ := List.getElem_of_mem hy
  have hl' : sl.rss.length = stm.results.length := by
    rcases hlen with h | h
    · exact h
    · exact absurd h hne
  have hz : (stm.results.zip sl.rss)[i]? = some (y, sl.rss[i]'(by omega)) :=
    List.getElem?_zip_eq_some.mpr ⟨by rw [List.getElem?_eq_getElem hi, hyi],
      List.getElem?_eq_getElem _⟩
  have hzm := List.mem_of_getElem? hz
  obtain ⟨x, hx1⟩ := hone _ _ hzm
  obtain ⟨n, c, rfl, hn⟩ := hvr hne _ (List.getElem_mem _) x (by rw [hx1]; simp)
  refine ⟨n, ?_, hn⟩
  unfold aliasOf
  refine List.mem_flatMap.mpr ⟨(B, L), List.mem_of_getElem?
    ((List.getElem?_zip_eq_some (z := (B, L))).mpr ⟨hB, hL⟩), ?_⟩
  refine List.mem_flatMap.mpr ⟨(stm, sl), List.mem_of_getElem?
    ((List.getElem?_zip_eq_some (z := (stm, sl))).mpr ⟨hstm, hsl⟩), ?_⟩
  rw [hx1] at hzm
  exact List.mem_filterMap.mpr ⟨_, hzm, rfl⟩

/-- **The terminator's segment**: the renamed code of a list meeting `SegDef` for values
available at the end of the block. -/
theorem term_facts {bi : Nat} {B : Clif.Block} {L : BLow} (hB : f.blocks[bi]? = some B)
    (hL : bl[bi]? = some L) :
    ∃ c S lo, tseg (asmR f bl) bl bi = c.map (MInst.mapRegs (asmR f bl)) ∧ SegDef ctx S lo c ∧
      ctx.valDef.size ≤ lo ∧ ∀ y ∈ S, y ∈ availOf f (availIn f ctx) bi B.body.length := by
  obtain ⟨-, hT, hY⟩ := hR f ctx ranges st0 hd hs ha hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  obtain ⟨hord, -⟩ := driver_ord hlb
  have hN : st0.nextVreg = ctx.valDef.size := hcf.size.1
  obtain ⟨-, -, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
  have hph := hcf.term bi B hB
  rw [← hstart bi L hL] at hph
  have hti := (Array.getElem?_eq_some_iff.mp hph).1
  have hge : ctx.valDef.size ≤ L.tst.nextVreg := hN ▸ (hord bi L hL).term.1
  have hBt : ∃ B' ∈ f.blocks, B'.term = B.term := ⟨B, List.mem_of_getElem? hB, rfl⟩
  have hav := (hd.uses ctx ranges st0 hb bi B hB).2
  obtain ⟨hn, hy⟩ := lowTerm_spec hterm
  have htseg : tseg (asmR f bl) bl bi =
      (fixTry L.tl L.tst'.emitted.toList).map (MInst.mapRegs (asmR f bl)) := by
    simp only [tseg, hL]
  cases ht : B.term.isTry with
  | false =>
    obtain ⟨htl, hdat, out, tr, hc⟩ := hn ht
    have hk := hT _ _ _ _ _ _ _ _ hti hph ht hBt hdat hge hc
    exact ⟨L.tst'.emitted.toList, _, _, by rw [htseg, htl]; rfl, segDef_of_run hk htst, hge, hav⟩
  | true =>
    obtain ⟨et, het⟩ := isTry_with ht
    obtain ⟨T, hT', hdat, hex, -, hreg, hinfo, out, tr, hc⟩ := hy et het
    have hk := hY _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het hBt hdat hex hge hreg hc
    obtain ⟨-, -, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc hex) hreg
    obtain ⟨cl, hcl⟩ := hlf.tryLast bi B L T hB hL hT'
    rw [← back_toList] at hcl
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hcl
    have hsd := segDef_of_run hk rfl
    rw [hys] at hsd
    have e : abiTerm f B.term = B.term := by
      rcases het with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] <;> rfl
    rw [e] at hav
    refine ⟨ys ++ [.tryCall cl T.info], _, T.st1.nextVreg, ?_, segDef_tryFix T.info hsd,
      by omega, hav⟩
    rw [htseg, hT']
    show (tryFix T.info _).map _ = _
    rw [hys, tryFix_append]

omit hb hd hs ha hlb hlf hR in
/-- The code of CLIF block `bi` in `vc`. -/
theorem raw_insts (bi : Nat) (B : Clif.Block) :
    (fixBlock (asmR f bl) (rawBlock f bl bi B)).insts.toList = codeOf f bl bi B :=
  rawBlock_insts f (asmR f bl) bl bi B

/-- **The values available before statement `j`** have their vregs defined there. -/
theorem avail_def (hen : entryParamsB f = true)
    (hE : (locsOf f.sig).length = f.sig.params.length ∧ ∃ bytes, sigParamBytes f.sig = .ok bytes)
    {A : Nat → Bool} {bi : Nat} {B : Clif.Block} {L : BLow} (hB : f.blocks[bi]? = some B)
    (hL : bl[bi]? = some L) (hA : ∀ v, GoodC f ctx bl bi v → A v = true) :
    ∀ j, j ≤ B.body.length → ∀ y ∈ availOf f (availIn f ctx) bi j,
      DefBy A (pfx f bl bi j) (asmG f bl y) := by
  intro j
  induction j with
  | zero =>
    intro _ y hy
    rcases avail_zero hB hy with hp | hi
    · by_cases h0 : bi = 0
      · subst h0
        obtain ⟨m, hm, hdm⟩ := pre_param (asm_ren f bl) hB hen hE hp
        exact .inl ⟨m, List.mem_append_left _ hm, hdm⟩
      · rw [asmG_par hd hB hp]
        exact .inr (hA _ (.inr ⟨h0, B, hB, hp⟩))
    · exact .inr (hA _ (.inl ⟨y, hi, rfl⟩))
  | succ j ih =>
    intro hj y hy
    obtain ⟨stm, hstm⟩ : ∃ stm, B.body[j]? = some stm := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hsl_len : L.sl.length = B.body.length := ((lowBlocks_spec hlb).2 bi B L hB hL).1
    obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hpf : ∀ m ∈ pfx f bl bi j, m ∈ pfx f bl bi (j + 1) :=
      fun m hm => pfx_mono f bl bi (Nat.le_succ j) hm
    rcases avail_succ hB hstm hy with hr | hy'
    · obtain ⟨hge, -, hseg, hres⟩ := stmt_facts hb hd hs ha hlb hlf hR hB hL hstm hsl
      obtain ⟨n, hal, hn⟩ := hres y hr
      rw [show asmG f bl y = asmG f bl n from asmG_alias hd hs hb hlb hal]
      rcases hn with ⟨h1, h2⟩ | ⟨h1, m, hm, hdm⟩
      · exact (ih (by omega) n (reach_avail hd hb
          (fun z hz => (hd.uses ctx ranges st0 hb bi B hB).1 j stm hstm z hz) h2)).mono hpf
      · have e := asm_fix bl hb (show ctx.valDef.size ≤ n by omega)
        rw [e]
        refine .inl ⟨m.mapRegs (asmR f bl),
          List.mem_append_right _ (mem_flat_seg _ (Nat.lt_succ_self j) ?_), ?_⟩
        · rw [hseg]; exact List.mem_map_of_mem hm
        · have := defVregs_mapRegs (asm_ren f bl) hdm
          rw [e] at this
          exact isDefV_iff.mpr this
    · exact (ih (by omega) y hy').mono hpf

/-- **Every use of CLIF block `bi`'s code** is defined where it is read. -/
theorem uses_def (hen : entryParamsB f = true)
    (hE : (locsOf f.sig).length = f.sig.params.length ∧ ∃ bytes, sigParamBytes f.sig = .ok bytes)
    {A : Nat → Bool} {bi : Nat} {B : Clif.Block} {L : BLow} (hB : f.blocks[bi]? = some B)
    (hL : bl[bi]? = some L) (hA : ∀ v, GoodC f ctx bl bi v → A v = true) {k : Nat} {i : MInst}
    (hi : (codeOf f bl bi B)[k]? = some i) {u : Nat} (hu : u ∈ useVregs i) :
    DefBy A ((codeOf f bl bi B).take k) u := by
  have hav := avail_def hb hd hs ha hlb hlf hR hen hE hB hL hA
  have hsl_len : L.sl.length = B.body.length := ((lowBlocks_spec hlb).2 bi B L hB hL).1
  rcases idx_app hi with ⟨-, hi1, e1⟩ | ⟨-, hi1, e1⟩
  · rw [e1]
    rcases idx_app hi1 with ⟨-, hi2, -⟩ | ⟨-, hi2, e2⟩
    · rw [(asm_pre (asm_ren f bl) (List.mem_of_getElem? hi2)).2] at hu
      cases hu
    · rw [e2]
      obtain ⟨j, hj, k', hk', e3⟩ := flat_idx _ _ _ _ hi2
      rw [e3, ← List.append_assoc]
      obtain ⟨stm, hstm⟩ : ∃ stm, B.body[j]? = some stm := ⟨_, List.getElem?_eq_getElem hj⟩
      obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨hge, hsd, hseg, -⟩ := stmt_facts hb hd hs ha hlb hlf hR hB hL hstm hsl
      rw [hseg] at hk' ⊢
      exact segDef_ren hb hsd hge (fun u _ hu2 => hav j (by omega) u (reach_avail hd hb
        (fun z hz => (hd.uses ctx ranges st0 hb bi B hB).1 j stm hstm z hz) hu2)) hk' hu
  · rw [e1]
    obtain ⟨c, S, lo, htseg, hsd, hlo, hS⟩ := term_facts hb hd hs ha hlb hlf hR hB hL
    rw [htseg] at hi1 ⊢
    exact segDef_ren hb hsd hlo
      (fun u _ hu2 => hav _ (Nat.le_refl _) u (reach_avail hd hb hS hu2)) hi1 hu

/-- **What is defined at the end of CLIF block `bi`'s code** (`EndDef`) is defined by its code. -/
theorem end_def (hen : entryParamsB f = true)
    (hE : (locsOf f.sig).length = f.sig.params.length ∧ ∃ bytes, sigParamBytes f.sig = .ok bytes)
    {vc : VCode} (hl : lowerFunction f = .ok vc) (H : Low f vc ctx st0 bl (asmR f bl))
    {A : Nat → Bool} {bi : Nat} {B : Clif.Block} {L : BLow} (hB : f.blocks[bi]? = some B)
    (hL : bl[bi]? = some L) (hA : ∀ v, GoodC f ctx bl bi v → A v = true) {v : Nat}
    (hv : EndDef f ctx bl bi v) : DefBy A (codeOf f bl bi B) v := by
  rcases hv with ⟨B', hB', y, hy, rfl⟩ | ⟨B', L', T, et, hB', hL', het, hT, i, hi, rfl⟩
  · rw [hB] at hB'; cases hB'
    exact (avail_def hb hd hs ha hlb hlf hR hen hE hB hL hA _ (Nat.le_refl _) y hy).mono
      fun m hm => List.mem_append_left _ hm
  · rw [hB] at hB'; cases hB'
    rw [hL] at hL'; cases hL'
    obtain ⟨T', ys, cl, hT', hcode, hD, -, -, -, -, hge, -⟩ :=
      try_facts hd hs ha hb hlb hlf killRunsHyp tryDefsExact hB hL het
    rw [hT] at hT'; cases hT'
    have hx : (MInst.tryCall cl T.info).mapRegs (asmR f bl) ∈ codeOf f bl bi B := by
      refine List.mem_append_right _ ?_
      simp only [tseg, hL, hcode, List.map_append, List.map_cons, List.map_nil]
      exact List.mem_append_right _ List.mem_cons_self
    have hvb : fixBlock (asmR f bl) (rawBlock f bl bi B) ∈ vc.blocks.toList :=
      List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact H.raw_at hB)
    obtain ⟨ops, hops, -⟩ := ctlSpillHyp_of iselCtlHyp hd hs ha hl _ hvb _
      (by rw [raw_insts]; exact hx) rfl
    obtain ⟨ops0, hops0⟩ : ∃ ops0, (MInst.tryCall cl T.info).operands = .ok ops0 := by
      rw [operands_mapRegs (asm_ren f bl)] at hops
      cases h0 : (MInst.tryCall cl T.info).operands with
      | error e => simp [h0, Except.map] at hops
      | ok ops0 => exact ⟨ops0, rfl⟩
    have hq : (Reg.x i, L.tst.nextVreg + i) ∈
        outDefs L.tst.nextVreg (max (sigRets T.sig).length 2) :=
      List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
    have h2 := defVregs_mapRegs (asm_ren f bl) (isDefV_tryCall hD hops0 hq)
    rw [asm_fix bl hb (show ctx.valDef.size ≤ L.tst.nextVreg + i by omega)] at h2
    exact .inl ⟨_, hx, isDefV_iff.mpr h2⟩

end Block

end Backend.Proof.DefRun
