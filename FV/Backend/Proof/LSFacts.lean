import FV.Backend.Proof.LSFn
import FV.Backend.Proof.LSSeg

/-!
# The validator's conditions as facts (V4b-3, #275)

`planFacts_of_structOk`: a plan of `Fn.make vc` that passes `Ctx.structOk` meets `PlanFacts`,
the propositional form of the validator's conditions that the proof of the builder uses:
segments start at births (`birthOk`), edges deliver the vregs live at a block's start
(`edgeOk`), uses and defs are covered, registers are of their vreg's class, two vregs sharing a
register (`inter`) or a home (`homes`) never cover one position, fixed-operand claims and
clobbers exclude the other vregs. `regFree_sound`: a register `regFree` reports is `Excl`
(holds no vreg over the range) and misses the taken ranges.
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan

deriving instance ReflBEq, LawfulBEq for RegClass
deriving instance ReflBEq, LawfulBEq for Reg

/-- **The validator's conditions** (`Ctx.structOk`) as facts about the plan of context `c`. -/
structure PlanFacts (vc : VCode) (c : LinearScan.Ctx) : Prop where
  birth : ∀ v < c.fn.nv, ∀ (s e : Nat), (s, e) ∈ (c.pl.segs.getD v #[]).toList →
    s ≤ e ∧ c.birthOk v s = true
  edge : ∀ v < c.fn.nv, ∀ t < vc.blocks.size, c.pl.cov v (pos (c.fn.start.getD t 0) 0) = true →
    ∀ b ∈ (c.fn.preds.getD t #[]).toList, c.edgeOk v t b = true
  use : ∀ (g : Nat) (os : Array Operand), c.fn.ops[g]? = some os → ∀ o ∈ os.toList, o.kind = .use →
    c.pl.covI o.vreg (pos g 0) (pos g (opSlot o)) = true
  def_ : ∀ (g : Nat) (os : Array Operand), c.fn.ops[g]? = some os → ∀ o ∈ os.toList, o.kind = .def →
    c.pl.covI o.vreg (pos g (opSlot o)) (pos g 3) = true
  regs : ∀ (v : Nat) (r : Reg), c.pl.regOf v = some r → r ∈ pool (c.fn.clsOf v)
  occ : ∀ i, SegsOk (c.occ.getD i #[])
  inter : ∀ (v w : Nat) (r : Reg) (p : Nat), c.pl.regOf v = some r → c.pl.regOf w = some r → c.pl.cov v p = true →
    c.pl.cov w p = true → v = w
  homes : ∀ (v w p : Nat), v < c.fn.nv → w < c.fn.nv → c.pl.regOf v = none → c.pl.regOf w = none →
    c.pl.home.getD v 0 = c.pl.home.getD w 0 → c.fn.clsOf v = c.fn.clsOf w →
    c.pl.cov v p = true → c.pl.cov w p = true → v = w
  homeLt : ∀ v < c.fn.nv, c.pl.regOf v = none → ∀ p, c.pl.cov v p = true →
    c.pl.home.getD v 0 < c.pl.nslots
  claim : ∀ (g : Nat) (os : Array Operand), c.fn.ops[g]? = some os → ∀ o ∈ os.toList, ∀ p, o.con = .fixed p →
    (regIdx p).isSome ∧ ∀ w, c.pl.regOf w = some p → ∀ q, (opRange g o true).1 ≤ q →
      q ≤ (opRange g o true).2 → c.pl.cov w q = true → w = o.vreg
  clob : ∀ (g : Nat) (i : MInst), c.fn.insts[g]? = some i → ∀ r ∈ i.clobbers, ∀ w, c.pl.regOf w = some r →
    c.pl.cov w (pos g 3) = false
  retsClob : ∀ (g : Nat) (us : List (Reg × Reg)), c.fn.insts[g]? = some (.rets us) →
    ∀ r ∈ calleeSaved, ∀ w, c.pl.regOf w = some r → c.pl.cov w (pos g 3) = false
  defUse : ∀ (g : Nat) (os : Array Operand), c.fn.ops[g]? = some os → ∀ o ∈ os.toList, o.kind = .def →
    (c.pl.regOf o.vreg).isSome → ∀ o' ∈ os.toList, o'.kind = .use → o'.vreg = o.vreg →
      o.pos = .late ∧ o'.pos = .early

/-! ## Helpers -/

private theorem lt_of_getElem? {α : Type} {a : Array α} {i : Nat} {x : α} (h : a[i]? = some x) :
    i < a.size :=
  (Array.getElem?_eq_some_iff.mp h).1

private theorem getD_of_getElem? {α : Type} {a : Array α} {i : Nat} {x d : α} (h : a[i]? = some x) :
    a.getD i d = x := by
  simp [Array.getD_eq_getD_getElem?, h]

private theorem lt_of_regOf {pl : LinearScan.Plan} {v : Nat} {r : Reg} (h : pl.regOf v = some r) :
    v < pl.reg.size := by
  unfold Plan.regOf Array.getD at h
  split at h
  · assumption
  · cases h

private theorem has_of {g : LinearScan.Seg} {p : Nat} (h1 : g.s ≤ p) (h2 : p ≤ g.e) : g.has p := And.intro h1 h2

private theorem disj_getD {a : Array (Array LinearScan.Seg)} (h : a.all disjointSorted = true) (i : Nat) :
    disjointSorted (a.getD i #[]) = true := by
  rw [Array.all_eq_true_iff_forall_mem] at h
  unfold Array.getD
  split
  · exact h _ (Array.getElem_mem _)
  · rfl

private theorem structOk_parts {c : LinearScan.Ctx} (h : c.structOk = true) :
    c.segsOk = true ∧ c.usesOk = true ∧ c.regsOk = true ∧ c.occ.all disjointSorted = true ∧
      c.homesOk = true ∧ c.claimsOk = true ∧ c.defUseOk = true := by
  simp only [LinearScan.Ctx.structOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

private theorem segsOk_spec {c : LinearScan.Ctx} (h : c.segsOk = true) {v : Nat} (hv : v < c.fn.nv)
    {s e : Nat} (hs : (s, e) ∈ (c.pl.segs.getD v #[]).toList) :
    s ≤ e ∧ c.birthOk v s = true ∧
      ∀ t ∈ c.fn.blocksIn s e, ∀ b ∈ (c.fn.preds.getD t #[]).toList, c.edgeOk v t b = true := by
  simp only [LinearScan.Ctx.segsOk, List.all_eq_true, List.mem_range,
    Array.all_eq_true_iff_forall_mem] at h
  have h' := h v hv (s, e) (by simpa using hs)
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Array.all_eq_true_iff_forall_mem] at h'
  obtain ⟨⟨h1, h2⟩, h3⟩ := h'
  exact ⟨h1, h2, fun t ht b hb => h3 t ht b (by simpa using hb)⟩

private theorem regsOk_spec {c : LinearScan.Ctx} (h : c.regsOk = true) :
    c.pl.reg.size ≤ c.fn.nv ∧ ∀ v r, c.pl.regOf v = some r → r ∈ pool (c.fn.clsOf v) := by
  simp only [LinearScan.Ctx.regsOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  refine ⟨h.1, fun v r hr => ?_⟩
  have h' := h.2 v (lt_of_regOf hr)
  simp only [hr] at h'
  simpa using h'

/-- The arrays of `occ` are `SegsOk`. -/
private theorem occ_segsOk {c : LinearScan.Ctx} (hc : c.occ = c.pl.occ) (hs : c.segsOk = true)
    (hr : c.regsOk = true) (ho : c.occ.all disjointSorted = true) (i : Nat) :
    SegsOk (c.occ.getD i #[]) := by
  refine ⟨disj_getD ho i, fun g hg => ?_⟩
  rw [hc] at hg
  obtain ⟨r, hr', -, hm⟩ := occ_mem hg
  exact (segsOk_spec hs (Nat.lt_of_lt_of_le (lt_of_regOf hr') (regsOk_spec hr).1) hm).1

private theorem homesOk_spec {c : LinearScan.Ctx} (h : c.homesOk = true) :
    (∀ v < c.fn.nv, c.pl.regOf v = none → ∀ p, c.pl.cov v p = true →
      c.pl.home.getD v 0 < c.pl.nslots) ∧ (c.pl.homeOcc c.fn).all disjointSorted = true := by
  simp only [LinearScan.Ctx.homesOk, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq] at h
  refine ⟨fun v hv hr p hp => ?_, h.2⟩
  obtain ⟨s, e, hm, -, -⟩ := cov_iff.mp hp
  rcases h.1 v hv with (h' | h') | h'
  · simp [hr] at h'
  · rw [Array.isEmpty_iff] at h'
    rw [h'] at hm
    simp at hm
  · exact h'

/-- The arrays of `homeOcc` are `SegsOk`. -/
private theorem homeOcc_segsOk {c : LinearScan.Ctx} (hs : c.segsOk = true) (hh : c.homesOk = true)
    (i : Nat) : SegsOk ((c.pl.homeOcc c.fn).getD i #[]) :=
  ⟨disj_getD (homesOk_spec hh).2 i, fun _ hg =>
    (segsOk_spec hs (homeOcc_mem hg).1 (homeOcc_mem hg).2.2.2).1⟩

/-! ## Completeness of `Fn.blocksIn` -/

section
variable {vc : VCode} {fn : Fn}

private theorem pos_mono (hf : FnOk vc fn) {b b' : Nat} (h : b ≤ b') (hb' : b' ≤ fn.nblocks) :
    pos (fn.start.getD b 0) 0 ≤ pos (fn.start.getD b' 0) 0 := by
  have := hf.start_mono h (by rw [← hf.nblocks]; exact hb')
  simp only [pos]
  omega

private theorem firstBlockIn_le_hi (fn : Fn) (x lo hi : Nat) (h : lo ≤ hi) :
    fn.firstBlockIn x lo hi ≤ hi := by
  rw [Fn.firstBlockIn]
  dsimp only
  split
  · split
    · exact firstBlockIn_le_hi fn x _ _ (by omega)
    · have := firstBlockIn_le_hi fn x lo ((lo + hi) / 2) (by omega)
      omega
  · exact h
termination_by hi - lo

private theorem firstBlockIn_le (hf : FnOk vc fn) (x lo hi t : Nat) (h1 : lo ≤ t) (h2 : t < hi)
    (h3 : hi ≤ fn.nblocks) (h4 : x ≤ pos (fn.start.getD t 0) 0) : fn.firstBlockIn x lo hi ≤ t := by
  rw [Fn.firstBlockIn]
  dsimp only
  split
  · split
    · rename_i hm
      have hlt : (lo + hi) / 2 < t := by
        rcases Nat.lt_or_ge ((lo + hi) / 2) t with h | h
        · exact h
        · have := pos_mono hf (b := t) (b' := (lo + hi) / 2) h (by omega)
          omega
      exact firstBlockIn_le hf x _ _ t (by omega) h2 h3 h4
    · by_cases ht : t < (lo + hi) / 2
      · exact firstBlockIn_le hf x lo _ t h1 ht (by omega) h4
      · have := firstBlockIn_le_hi fn x lo ((lo + hi) / 2) (by omega)
        omega
  · omega
termination_by hi - lo

private theorem mem_blocksUpTo (hf : FnOk vc fn) (e b t : Nat) (h1 : b ≤ t) (h2 : t < fn.nblocks)
    (h3 : pos (fn.start.getD t 0) 0 ≤ e) : t ∈ fn.blocksUpTo e b := by
  have hb : pos (fn.start.getD b 0) 0 ≤ e := Nat.le_trans (pos_mono hf h1 (by omega)) h3
  rw [Fn.blocksUpTo]
  simp only [show b < fn.nblocks by omega, hb, ↓reduceIte]
  rcases Nat.eq_or_lt_of_le h1 with h | h
  · subst h
    exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (mem_blocksUpTo hf e (b + 1) t h h2 h3)
termination_by fn.nblocks - b

/-- `Fn.blocksIn s e` lists every block whose start position is in `[s, e]`. -/
private theorem mem_blocksIn (hf : FnOk vc fn) {s e t : Nat} (ht : t < fn.nblocks)
    (hs : s ≤ pos (fn.start.getD t 0) 0) (he : pos (fn.start.getD t 0) 0 ≤ e) :
    t ∈ fn.blocksIn s e :=
  mem_blocksUpTo hf e _ t (firstBlockIn_le hf s 0 _ t (Nat.zero_le _) ht (Nat.le_refl _) hs) ht he

end

/-! ## The facts -/

private theorem usesOk_spec {c : LinearScan.Ctx} (h : c.usesOk = true) {g : Nat} {os : Array Operand}
    (hg : c.fn.ops[g]? = some os) {o : Operand} (ho : o ∈ os.toList) :
    (o.kind = .use → c.pl.covI o.vreg (pos g 0) (pos g (opSlot o)) = true) ∧
      (o.kind = .def → c.pl.covI o.vreg (pos g (opSlot o)) (pos g 3) = true) := by
  simp only [LinearScan.Ctx.usesOk, List.all_eq_true, List.mem_range,
    Array.all_eq_true_iff_forall_mem] at h
  have h' := h g (lt_of_getElem? hg)
  rw [getD_of_getElem? hg] at h'
  have h'' := h' o (by simpa using ho)
  constructor <;> intro hk <;> simpa [hk] using h''

private theorem claimsOk_spec {c : LinearScan.Ctx} (h : c.claimsOk = true) {g : Nat}
    (hg : g < c.fn.ops.size) :
    (∀ o ∈ (c.fn.ops.getD g #[]).toList, ∀ p, o.con = .fixed p → ∃ i, regIdx p = some i ∧
      meetsOther (c.occ.getD i #[]) (opRange g o true).1 (opRange g o true).2 o.vreg = false) ∧
    ∀ r ∈ (c.fn.insts.getD g default).clobbers ++
      (if c.fn.insts.getD g default matches .rets _ then calleeSaved else []), ∀ i, regIdx r = some i →
      segFree (c.occ.getD i #[]) (pos g 3) (pos g 3) = true := by
  simp only [LinearScan.Ctx.claimsOk, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨h1, h2⟩ := h g hg
  refine ⟨fun o ho p hp => ?_, fun r hr i hi => ?_⟩
  · have h' := h1 o (by simpa using ho)
    simp only [hp] at h'
    cases hi : regIdx p with
    | none => simp [hi] at h'
    | some i => exact ⟨i, rfl, by simpa [hi] using h'⟩
  · have h' := h2 r hr
    simpa [hi] using h'

private theorem defUseOk_spec {c : LinearScan.Ctx} (h : c.defUseOk = true) {g : Nat}
    {os : Array Operand} (hg : c.fn.ops[g]? = some os) {o : Operand} (ho : o ∈ os.toList)
    (hk : o.kind = .def) (hr : (c.pl.regOf o.vreg).isSome) {o' : Operand} (ho' : o' ∈ os.toList)
    (hk' : o'.kind = .use) (hv : o'.vreg = o.vreg) : o.pos = .late ∧ o'.pos = .early := by
  simp only [LinearScan.Ctx.defUseOk, List.all_eq_true, List.mem_range,
    Array.all_eq_true_iff_forall_mem] at h
  have h' := h g (lt_of_getElem? hg)
  rw [getD_of_getElem? hg] at h'
  have h'' := h' o (by simpa using ho)
  have hn : (c.pl.regOf o.vreg).isNone = false := by
    cases h0 : c.pl.regOf o.vreg <;> simp_all
  simp only [hk, hn, bne_self_eq_false, Bool.false_or, Array.all_eq_true_iff_forall_mem] at h''
  have h3 := h'' o' (by simpa using ho')
  simpa [hk', hv] using h3

/-- A pool register is allocatable, of the pool's class and has an index. -/
private theorem pool_all : ∀ c, ∀ r ∈ pool c,
    r.allocatable = true ∧ r.realClass? = some c ∧ (regIdx r).isSome = true := by
  intro c
  cases c <;> decide

private theorem scratchOrder_all : ∀ c, ∀ r ∈ scratchOrder c,
    r.allocatable = true ∧ r.realClass? = some c ∧ (regIdx r).isSome = true := by
  intro c
  cases c <;> decide

/-- A register in the pool of a class is allocatable and of that class. -/
theorem pool_ok {c : RegClass} {r : Reg} (h : r ∈ pool c) :
    r.allocatable = true ∧ r.realClass? = some c ∧ (regIdx r).isSome :=
  pool_all c r h

/-- A scratch register is allocatable and of its class. -/
theorem scratchOrder_ok {c : RegClass} {r : Reg} (h : r ∈ scratchOrder c) :
    r.allocatable = true ∧ r.realClass? = some c ∧ (regIdx r).isSome :=
  scratchOrder_all c r h

/-- An index of a register of the plan. -/
private theorem regIdx_of_regOf {c : LinearScan.Ctx} (hr : c.regsOk = true) {v : Nat} {r : Reg}
    (h : c.pl.regOf v = some r) : ∃ i, regIdx r = some i := by
  have := (pool_ok ((regsOk_spec hr).2 v r h)).2.2
  cases hi : regIdx r with
  | none => simp [hi] at this
  | some i => exact ⟨i, rfl⟩

/-- `planFacts_of_structOk` for any context whose `occ` is its plan's. -/
private theorem planFacts_of {vc : VCode} {c : LinearScan.Ctx} (hf : FnOk vc c.fn)
    (hc : c.occ = c.pl.occ) (h : c.structOk = true) : PlanFacts vc c := by
  obtain ⟨hs, hu, hr, ho, hh, hcl, hd⟩ := structOk_parts h
  have hocc := occ_segsOk hc hs hr ho
  have hclob : ∀ g, g < c.fn.ops.size → ∀ r ∈ (c.fn.insts.getD g default).clobbers ++
      (if c.fn.insts.getD g default matches .rets _ then calleeSaved else []), ∀ w,
      c.pl.regOf w = some r → c.pl.cov w (pos g 3) = false := by
    intro g hg' r hrm w hw
    obtain ⟨k, hk⟩ := regIdx_of_regOf hr hw
    have hfree := (claimsOk_spec hcl hg').2 r hrm k hk
    cases hq : c.pl.cov w (pos g 3) with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨s, e, hms, h1, h2⟩ := cov_iff.mp hq
      have g1 := mem_occ hw hk hms
      rw [← hc] at g1
      exact segFree_sound (hocc k) hfree _ g1 _ (Nat.le_refl _) (Nat.le_refl _) (has_of h1 h2)
  refine
    { birth := fun v hv s e hm => ⟨(segsOk_spec hs hv hm).1, (segsOk_spec hs hv hm).2.1⟩
      edge := ?_
      use := fun g os hg o ho hk => (usesOk_spec hu hg ho).1 hk
      def_ := fun g os hg o ho hk => (usesOk_spec hu hg ho).2 hk
      regs := (regsOk_spec hr).2
      occ := hocc
      inter := ?_
      homes := ?_
      homeLt := (homesOk_spec hh).1
      claim := ?_
      clob := fun g i hg r hrm w hw => hclob g (by rw [hf.ops_size]; exact lt_of_getElem? hg) r
        (by rw [getD_of_getElem? hg]; exact List.mem_append_left _ hrm) w hw
      retsClob := fun g us hg r hrm w hw => hclob g (by rw [hf.ops_size]; exact lt_of_getElem? hg) r
        (by rw [getD_of_getElem? hg]; exact List.mem_append_right _ (by simpa using hrm)) w hw
      defUse := fun g os hg o ho hk hreg o' ho' hk' hv => defUseOk_spec hd hg ho hk hreg ho' hk' hv }
  · intro v hv t ht hcov b hb
    obtain ⟨s, e, hm, h1, h2⟩ := cov_iff.mp hcov
    exact (segsOk_spec hs hv hm).2.2 t
      (mem_blocksIn hf (by rw [hf.nblocks]; exact ht) h1 h2) b hb
  · intro v w r p hv hw hpv hpw
    obtain ⟨i, hi⟩ := regIdx_of_regOf hr hv
    obtain ⟨s, e, hm, h1, h2⟩ := cov_iff.mp hpv
    obtain ⟨s', e', hm', h1', h2'⟩ := cov_iff.mp hpw
    have g1 := mem_occ hv hi hm
    have g2 := mem_occ hw hi hm'
    rw [← hc] at g1 g2
    have := (hocc i).unique g1 g2 (has_of h1 h2) (has_of h1' h2')
    exact congrArg LinearScan.Seg.v this
  · intro v w p hv hw hrv hrw hhome hcls hpv hpw
    obtain ⟨s, e, hm, h1, h2⟩ := cov_iff.mp hpv
    obtain ⟨s', e', hm', h1', h2'⟩ := cov_iff.mp hpw
    have g1 := mem_homeOcc hv hrv ((homesOk_spec hh).1 v hv hrv p hpv) hm
    have g2 := mem_homeOcc hw hrw ((homesOk_spec hh).1 w hw hrw p hpw) hm'
    have hidx : homeIdx c.fn c.pl v = homeIdx c.fn c.pl w := by simp [homeIdx, hhome, hcls]
    rw [hidx] at g1
    have := (homeOcc_segsOk hs hh _).unique g1 g2 (has_of h1 h2) (has_of h1' h2')
    exact congrArg LinearScan.Seg.v this
  · intro g os hg o ho p hp
    have hg' := lt_of_getElem? hg
    obtain ⟨i, hi, hm⟩ := (claimsOk_spec hcl hg').1 o (by rw [getD_of_getElem? hg]; exact ho) p hp
    refine ⟨by simp [hi], fun w hw q hq1 hq2 hq => ?_⟩
    obtain ⟨s, e, hms, h1, h2⟩ := cov_iff.mp hq
    have g1 := mem_occ hw hi hms
    rw [← hc] at g1
    exact meetsOther_false (hocc i) hm _ g1 q hq1 hq2 (has_of h1 h2)

theorem planFacts_of_structOk {vc : VCode} {fn : Fn} {pl : LinearScan.Plan} (hf : FnOk vc fn)
    (h : (LinearScan.Ctx.ofPlan fn pl).structOk = true) : PlanFacts vc (LinearScan.Ctx.ofPlan fn pl) :=
  planFacts_of hf rfl h

/-- `x` holds no vreg other than `u` over the positions `[s, e]`. -/
def Excl (pl : LinearScan.Plan) (x : Reg) (s e : Nat) (u : Option Nat) : Prop :=
  ∀ w, pl.regOf w = some x → ∀ q, s ≤ q → q ≤ e → pl.cov w q = true → u = some w

/-- A register `regFree` reports free holds no vreg over the range and misses `taken`. -/
theorem regFree_sound {vc : VCode} {c : LinearScan.Ctx} (hpf : PlanFacts vc c) (hc : c.occ = c.pl.occ)
    {taken : List (Reg × Nat × Nat)} {x : Reg} {s e : Nat}
    (h : regFree c.occ taken x s e = true) :
    Excl c.pl x s e none ∧ (regIdx x).isSome ∧ ∀ y ∈ taken, y.1 = x → y.2.2 < s ∨ e < y.2.1 := by
  unfold regFree at h
  cases hi : regIdx x with
  | none => simp [hi] at h
  | some i =>
    simp only [hi, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at h
    obtain ⟨hfree, ht⟩ := h
    refine ⟨fun w hw q h1 h2 hq => ?_, rfl, fun y hy hyx => ?_⟩
    · exfalso
      obtain ⟨s', e', hms, h3, h4⟩ := cov_iff.mp hq
      have g1 := mem_occ hw hi hms
      rw [← hc] at g1
      exact segFree_sound (hpf.occ i) hfree _ g1 q h1 h2 (has_of h3 h4)
    · obtain ⟨r', s', e'⟩ := y
      have := ht _ hy
      simp only at hyx
      subst hyx
      dsimp only at this ⊢
      simp only [beq_self_eq_true, decide_eq_true_eq, true_and] at this
      omega

end Backend.Proof.LS
