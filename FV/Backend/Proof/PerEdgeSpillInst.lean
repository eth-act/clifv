import FV.Backend.Proof.PerEdgeSpillCopy
import FV.Backend.Proof.SpillStep4Inst

namespace Backend.Proof.PerEdgeSpill
open Backend Backend.Proof.Spill
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Availability invariant for the actual dense indexed homes and actual
checker-state size. Classes remain an internal VCode obligation. -/
structure GoodAt (vc : VCode) (edges : Array (Array (Array Reg))) (A : Nat → Bool) (a : AState) : Prop where
  size : a.size = stateSizeAt vc edges
  home : ∀ v c n,A v = true → vc.classes[v]? = some c →
    homeLookup (spillHomesAt vc edges) (spillHomeKeyAt v c) = some n → Sym.vreg v ∈ a.get (.stack n c)
  save : ∀ r ∈ calleeSaved,Sym.entry r ∈ a.get (.save r)

private theorem home_eq {h : SpillHomesAt} {v n : Nat} {cl : RegClass}
    (found : homeLookup h (spillHomeKeyAt v cl) = some n) : spillHomeAt h v cl = .stack n cl := by
  unfold homeLookup at found
  simp only [spillHomeAt,found,Option.getD_some]
private theorem home_lt {vc : VCode} {edges : Array (Array (Array Reg))} {key n : Nat}
    (found : homeLookup (spillHomesAt vc edges) key = some n) : n < (spillHomesAt vc edges).size :=
  (spillHomesAt_spec vc edges).valid.1 key n found
private theorem home_inj {vc : VCode} {edges : Array (Array (Array Reg))} {v w n : Nat} {c d : RegClass}
    (left : homeLookup (spillHomesAt vc edges) (spillHomeKeyAt v c) = some n)
    (right : homeLookup (spillHomesAt vc edges) (spillHomeKeyAt w d) = some n) : (v,c) = (w,d) := by
  have same := (spillHomesAt_spec vc edges).valid.2 _ _ _ left right
  obtain ⟨rfl,rfl⟩ := spillHomeKeyAt_injective same
  rfl
private theorem home_index_lt {vc : VCode} {edges : Array (Array (Array Reg))} {n v : Nat} {c : RegClass}
    (found : homeLookup (spillHomesAt vc edges) (spillHomeKeyAt v c) = some n) :
    ∃ i,(Loc.stack n c).index = some i ∧ i < stateSizeAt vc edges := by
  have bound := home_lt found
  cases c <;> exact ⟨_,rfl,by unfold stateSizeAt; omega⟩

private def loadMovesAt (hm : SpillHomesAt) (ops : Array Operand) (clob : List Reg) : List (Loc × Loc) :=
  ((ops.zip (spillLocs ops clob)).toList.filter (·.1.kind == .use)).map
    fun (o, l) => (spillHomeAt hm o.vreg o.cls, l)

/-- **The loads**: each use's location then holds its home's symbols; every location that is
not a register is unchanged. -/
private theorem loadsAt_run (c : CheckCtx) (w : String) {hm : SpillHomesAt} {ops : Array Operand} {clob : List Reg}
    (hok : OpsOk ops clob)
    (hslot : ∀ o ∈ ops.toList, o.kind = .use → (homeLookup hm (spillHomeKeyAt o.vreg o.cls)).getD 0 < c.rf.spillSlots)
    {a : AState} (hsz : 64 ≤ a.size) :
    ∃ a', runMoves c w (loadMovesAt hm ops clob) a = .ok a' ∧ a'.size = a.size ∧
      (∀ o l, (o, l) ∈ (ops.zip (spillLocs ops clob)).toList → o.kind = .use →
        a'.get l = a.get (spillHomeAt hm o.vreg o.cls)) ∧
      ∀ l, l.isReg = false → a'.get l = a.get l := by
  have mem : ∀ m ∈ loadMovesAt hm ops clob, ∃ o, (o, m.2) ∈ (ops.zip (spillLocs ops clob)).toList ∧
      o.kind = .use ∧ m.1 = spillHomeAt hm o.vreg o.cls := by
    intro m hm'
    simp only [loadMovesAt, List.mem_map, List.mem_filter] at hm'
    obtain ⟨⟨o, l⟩, ⟨hx, hk⟩, rfl⟩ := hm'
    exact ⟨o, hx, by simpa using hk, rfl⟩
  obtain ⟨a', hrun, hsz', hget, hkeep⟩ := runMoves_spec c w (loadMovesAt hm ops clob) a
    (fun m hm' => by
      obtain ⟨o, hx, hk, h1⟩ := mem m hm'
      obtain ⟨r, hr, ha, hc⟩ := spill_reg hok hx
      obtain ⟨j, hj, -⟩ := mem_spillPairs hx
      rw [h1, hr]
      exact checkMove_load c w (hslot o (List.mem_of_getElem? hj) hk) ha hc)
    (fun m hm' => by
      obtain ⟨o, hx, -, -⟩ := mem m hm'
      obtain ⟨r, hr, ha, -⟩ := spill_reg hok hx
      exact ⟨r, hr, ha⟩)
    (fun m hm' => by obtain ⟨o, -, -, h1⟩ := mem m hm'; rw [h1]; rfl)
    (fun m hm' m' hm'' he => by
      obtain ⟨o, hx, hk, h1⟩ := mem m hm'
      obtain ⟨o', hx', hk', h1'⟩ := mem m' hm''
      rw [he] at hx
      obtain ⟨e1, e2⟩ := spill_useEq hok hx hx' hk hk'
      rw [h1, h1', e1, e2])
    hsz
  refine ⟨a', hrun, hsz', fun o l hx hk => ?_, fun l hl => hkeep l fun m hm' he => ?_⟩
  · have hmem : (spillHomeAt hm o.vreg o.cls, l) ∈ loadMovesAt hm ops clob := by
      simp only [loadMovesAt, List.mem_map, List.mem_filter]
      exact ⟨(o, l), ⟨hx, by simpa using hk⟩, rfl⟩
    exact hget _ hmem
  · obtain ⟨o, hx, -, -⟩ := mem m hm'
    obtain ⟨r, hr, -, -⟩ := spill_reg hok hx
    rw [← he, hr] at hl
    cases hl

private def storeMovesAt (h : SpillHomesAt) (i : MInst) (ops : Array Operand) : List (Loc × Loc) :=
  (keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList).map
    fun x => (x.2,spillHomeAt h x.1.vreg x.1.cls)
private theorem spillInstAt_eq {h : SpillHomesAt} {k : Nat} {i : MInst} {ops : Array Operand}
    (hops : i.operands = .ok ops) :
    spillInstAt h k i = restoresOf i ++ (loadMovesAt h ops i.clobbers).map mv ++
      [.op k (spillLocs ops i.clobbers)] ++ (if i.isTerminator then [] else (storeMovesAt h i ops).map mv) := by
  unfold spillInstAt
  rw [hops]
  simp only [loadMovesAt,storeMovesAt,List.map_map]
  rfl

section
variable {c : CheckCtx} {vc : VCode} {edges : Array (Array (Array Reg))}

private theorem restoresAt_runs (hsv : c.rf.saved = calleeSaved) {vb : VBlock} {k : Nat}
    (hkn : k ≠ vb.insts.size) {i : MInst} {A : Nat → Bool} {a : AState} (hg : GoodAt vc edges A a) :
    Runs c vb k (restoresOf i) a fun k' a1 => k' = k ∧ GoodAt vc edges A a1 ∧
      (∀ us, i = .rets us → ∀ r ∈ calleeSaved, Sym.entry r ∈ a1.get (.reg r)) := by
  by_cases hr : ∃ us, i = .rets us
  · obtain ⟨us, rfl⟩ := hr
    show Runs c vb k spillRestores a _
    rw [spillRestores_eq]
    refine (Runs.moves hkn _ a
      (fun m hm => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
        exact (checkMove_saves c hsv _ hr).2)
      (fun m hm m' hm' => by
        obtain ⟨r, -, rfl⟩ := List.mem_map.mp hm
        obtain ⟨r', -, rfl⟩ := List.mem_map.mp hm'
        simp)
      (by
        rw [List.map_map]
        exact nodup_map_of_inj (g := id) (by simpa using calleeSaved_nodup)
          fun x _ y _ h => by simpa using h)
      (fun m hm => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
        obtain ⟨i, h1, h2⟩ := reg_index (calleeSaved_ok r hr).1
        exact ⟨i, h1, by rw [hg.size]; unfold stateSizeAt; omega⟩)).mono
      fun k' a1 ⟨e1, e2, e3, e4⟩ => ⟨e1, ⟨by rw [e2, hg.size],
        fun v c n hv hc hn => by rw [e4 _ (by simp)]; exact hg.home v c n hv hc hn,
        fun r hr => by rw [e4 _ (by simp)]; exact hg.save r hr⟩,
        fun _ _ r hr => by rw [e3 (Loc.save r, Loc.reg r) (List.mem_map_of_mem hr)]; exact hg.save r hr⟩
  · rw [restoresOf_other fun us h => hr ⟨us, h⟩]
    exact Runs.nil ⟨rfl, hg, fun us h => absurd ⟨us, h⟩ hr⟩

/-- Dense-home instruction proof: restores, operand loads, transfer and kept-result stores preserve the actual availability invariant. -/
private theorem instAt_core (hsl : c.rf.spillSlots = (spillHomesAt vc edges).size + maxArgsAt edges)
    (hsv : c.rf.saved = calleeSaved) {vb : VBlock} {k : Nat} {i : MInst} {ops : Array Operand}
    (hk : k < vb.insts.size) (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops)
    (hok : OpsOk ops i.clobbers)
    (hrets : ∀ us, i = .rets us → ∀ o ∈ ops.toList, ∃ p, o.con = .fixed p ∧ p ∉ calleeSaved)
    (hterm : k + 1 = vb.insts.size → i.isTerminator = true)
    (hmem : ∀ o ∈ ops.toList, vc.classes[o.vreg]? = some o.cls ∧
      ∃ n, homeLookup (spillHomesAt vc edges) (spillHomeKeyAt o.vreg o.cls) = some n)
    {A : Nat → Bool} (huse : ∀ o ∈ ops.toList, o.kind = .use → A o.vreg = true)
    {a : AState} (hg : GoodAt vc edges A a) :
    Runs c vb k (spillInstAt (spillHomesAt vc edges) k i) a fun k' a' => k' = k + 1 ∧
      GoodAt vc edges (availInst i A) a' ∧
      ∀ x ∈ keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList, Sym.vreg x.1.vreg ∈ a'.get x.2 := by
  have hkn : k ≠ vb.insts.size := by omega
  have h64 : 64 ≤ stateSizeAt vc edges := by unfold stateSizeAt; omega
  have hPf := spillPairs_fst ops i.clobbers
  have hPo : ∀ x ∈ (ops.zip (spillLocs ops i.clobbers)).toList, x.1 ∈ ops.toList := fun x hx =>
    hPf ▸ List.mem_map_of_mem hx
  have hPreg : ∀ x ∈ (ops.zip (spillLocs ops i.clobbers)).toList, ∃ r, x.2 = .reg r ∧
      r.allocatable = true ∧ r.realClass? = some x.1.cls := fun x hx => spill_reg hok hx
  rw [spillInstAt_eq hops]
  -- restores and loads
  have hL : Runs c vb k (restoresOf i ++ (loadMovesAt (spillHomesAt vc edges) ops i.clobbers).map mv) a
      fun k' a2 => k' = k ∧ GoodAt vc edges A a2 ∧
        (∀ x ∈ (ops.zip (spillLocs ops i.clobbers)).toList, x.1.kind = .use →
          Sym.vreg x.1.vreg ∈ a2.get x.2) ∧
        (∀ us, i = .rets us → ∀ r ∈ calleeSaved, Sym.entry r ∈ a2.get (.reg r)) := by
    refine Runs.append (restoresAt_runs hsv hkn hg) fun k1 a1 ⟨hk1, hg1, hret1⟩ => ?_
    subst hk1
    obtain ⟨a2, hrun, hsz2, hget2, hkeep2⟩ := loadsAt_run c s!"block {vb.label}" (hm := spillHomesAt vc edges)
      hok (fun o ho _ => by
        obtain ⟨_, n, hn⟩ := hmem o ho
        rw [hn, Option.getD_some, hsl]
        have := home_lt hn
        omega) (a := a1) (by rw [hg1.size]; exact h64)
    refine (Runs.ofRunMoves hkn _ _ _ hrun).mono fun k' a' ⟨e1, e2⟩ => ?_
    subst e1 e2
    refine ⟨rfl, ⟨by rw [hsz2, hg1.size],
      fun v c n hv hc hn => by rw [hkeep2 _ rfl]; exact hg1.home v c n hv hc hn,
      fun r hr => by rw [hkeep2 _ rfl]; exact hg1.save r hr⟩, fun x hx hu => ?_, fun us hus r hr => ?_⟩
    · obtain ⟨hc, n, hn⟩ := hmem x.1 (hPo x hx)
      rw [hget2 x.1 x.2 hx hu, home_eq hn]
      exact hg1.home _ _ n (huse x.1 (hPo x hx) hu) hc hn
    · rw [runMoves_frame c _ _ _ _ hrun (.reg r) ?_]
      · exact hret1 us hus r hr
      · intro m hm he
        simp only [loadMovesAt, List.mem_map, List.mem_filter] at hm
        obtain ⟨⟨o, l⟩, ⟨hx, -⟩, rfl⟩ := hm
        obtain ⟨p, hp, hpn⟩ := hrets us hus o (hPo _ hx)
        obtain ⟨j, -, hl⟩ := mem_spillPairs hx
        simp only at he
        rw [hl, locOf_fixed hp] at he
        cases he
        exact hpn hr
  -- the instruction
  have hO : Runs c vb k (restoresOf i ++ (loadMovesAt (spillHomesAt vc edges) ops i.clobbers).map mv ++
      [.op k (spillLocs ops i.clobbers)]) a fun k' a3 => k' = k + 1 ∧ a3.size = stateSizeAt vc edges ∧
        (∀ v c n, A v = true → isDefOf ops v = false → vc.classes[v]? = some c →
          homeLookup (spillHomesAt vc edges) (spillHomeKeyAt v c) = some n → Sym.vreg v ∈ a3.get (.stack n c)) ∧
        (∀ r ∈ calleeSaved, Sym.entry r ∈ a3.get (.save r)) ∧
        (∀ x ∈ keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList,
          Sym.vreg x.1.vreg ∈ a3.get x.2) := by
    refine Runs.append hL fun k2 a2 ⟨hk2, hg2, huse2, hret2⟩ => ?_
    subst hk2
    have hnr : ∀ l, l.isReg = false → ∀ x ∈ (ops.zip (spillLocs ops i.clobbers)).toList,
        x.1.kind = .def → x.2 ≠ l := by
      intro l hl x hx _ he
      obtain ⟨r, hr, -⟩ := hPreg x hx
      rw [← he, hr] at hl
      cases hl
    have hnc : ∀ l, l.isReg = false → ∀ r ∈ i.clobbers, Loc.reg r ≠ l := by
      intro l hl r _ he
      rw [← he] at hl
      cases hl
    refine Runs.op hkn hi hops (stepOp_of (checkStatic_spill c _ hok) ?_ ?_ ?_) ⟨rfl, ?_, ?_, ?_, ?_⟩
    · intro p hp
      have := mem_atPos.mp hp
      exact huse2 p this.1 this.2.1
    · apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      have := mem_atPos.mp hx
      have := hok.useEarly x.1 (hPo x this.1) this.2.1
      rw [(mem_atPos.mp hx).2.2] at this
      cases this
    · by_cases hr : ∃ us, i = .rets us
      · obtain ⟨us, rfl⟩ := hr
        apply retCheck_rets
        intro r hr'
        refine transferOp_keep (fun x hx _ he => ?_) (fun r' h => by simp [MInst.clobbers] at h)
          (hret2 us rfl r hr') (fun _ _ _ he => by cases he)
        obtain ⟨p, hp, hpn⟩ := hrets us rfl x.1 (hPo x hx)
        obtain ⟨j, -, hl⟩ := mem_spillPairs hx
        rw [hl, locOf_fixed hp] at he
        cases he
        exact hpn hr'
      · exact retCheck_other (fun us h => hr ⟨us, h⟩) _
    · rw [size_transferOp, hg2.size]
    · intro v c n hv hnd hc hn
      refine transferOp_keep (hnr _ rfl) (hnc _ rfl) (hg2.home v c n hv hc hn) fun x hx hd he => ?_
      injection he with he
      rw [he, isDefOf_of (hPo x hx) hd] at hnd
      cases hnd
    · intro r hr
      exact transferOp_keep (hnr _ rfl) (hnc _ rfl) (hg2.save r hr) fun _ _ _ he => by cases he
    · intro x hx
      rw [transferOp_kept hok (by rw [hg2.size]; exact h64) hx]
      exact List.mem_singleton_self _
  -- the stores
  refine Runs.append hO fun k3 a3 ⟨hk3, hsz3, hh3, hs3, hkept3⟩ => ?_
  subst hk3
  have availEq := availInst_eq hops A
  by_cases ht : i.isTerminator = true
  · simp only [ht, ↓reduceIte]
    refine Runs.nil ⟨rfl, ⟨hsz3, fun v c n hv hc hn => ?_, hs3⟩, hkept3⟩
    rw [availEq, storedDefs_eq] at hv
    simp only [ht, ↓reduceIte] at hv
    cases hd : isDefOf ops v
    · rw [hd] at hv; exact hh3 v c n (by simpa using hv) hd hc hn
    · rw [hd] at hv; simp at hv
  · have ht' : i.isTerminator = false := by simpa using ht
    simp only [ht', Bool.false_eq_true, ↓reduceIte]
    have hk1 : k + 1 ≠ vb.insts.size := fun h => ht (hterm h)
    have hmemS : ∀ m ∈ storeMovesAt (spillHomesAt vc edges) i ops, ∃ x ∈ keptPairs i
        (ops.zip (spillLocs ops i.clobbers)).toList, ∃ n, m = (x.2, .stack n x.1.cls) ∧
        homeLookup (spillHomesAt vc edges) (spillHomeKeyAt x.1.vreg x.1.cls) = some n := by
      intro m hm
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
      obtain ⟨-, n, hn⟩ := hmem x.1 (hPo x (mem_keptPairs hx).1)
      exact ⟨x, hx, n, by rw [home_eq hn], hn⟩
    refine (Runs.moves hk1 (storeMovesAt (spillHomesAt vc edges) i ops) a3 (fun m hm => ?_)
      (fun m hm m' hm' he => ?_) ?_ (fun m hm => ?_)).mono fun k' a4 ⟨e1, e2, e3, e4⟩ => ?_
    · obtain ⟨x, hx, n, rfl, hn⟩ := hmemS m hm
      obtain ⟨r, hr, ha, hcl⟩ := hPreg x (mem_keptPairs hx).1
      rw [hr]
      exact checkMove_store c _ (by rw [hsl]; have := home_lt hn; omega) ha hcl
    · obtain ⟨x, hx, n, rfl, hn⟩ := hmemS m hm
      obtain ⟨x', hx', n', rfl, hn'⟩ := hmemS m' hm'
      obtain ⟨r, hr, -⟩ := hPreg x (mem_keptPairs hx).1
      simp only at he
      rw [hr] at he
      cases he
    · unfold storeMovesAt
      rw [List.map_map]
      refine nodup_map_of_inj (keptPairs_vregs_nodup hok) fun x hx y hy he => ?_
      obtain ⟨-, n, hn⟩ := hmem x.1 (hPo x (mem_keptPairs hx).1)
      obtain ⟨-, n', hn'⟩ := hmem y.1 (hPo y (mem_keptPairs hy).1)
      simp only [Function.comp, home_eq hn, home_eq hn'] at he
      injection he with e1 e2
      rw [← e1, ← e2] at hn'
      have := home_inj hn hn'
      injection this
    · obtain ⟨x, hx, n, rfl, hn⟩ := hmemS m hm
      obtain ⟨j, h1, h2⟩ := home_index_lt hn
      exact ⟨j, h1, by rw [hsz3]; exact h2⟩
    · have hnotS : ∀ l, (∀ n c, l ≠ .stack n c) → ∀ m ∈ storeMovesAt (spillHomesAt vc edges) i ops, m.2 ≠ l := by
        intro l hl m hm he
        obtain ⟨x, hx, n, rfl, hn⟩ := hmemS m hm
        exact hl n _ he.symm
      refine ⟨e1, ⟨by rw [e2, hsz3], fun v c n hv hc hn => ?_,
        fun r hr => by rw [e4 _ (hnotS _ fun _ _ he => by cases he)]; exact hs3 r hr⟩,
        fun x hx => ?_⟩
      · rw [availEq] at hv
        cases hd : isDefOf ops v
        · rw [hd] at hv
          rw [e4 _ fun m hm he => ?_]
          · exact hh3 v c n (by simpa using hv) hd hc hn
          · obtain ⟨x, hx, n', rfl, hn'⟩ := hmemS m hm
            simp only at he
            injection he with e1 e2
            subst e1 e2
            have := home_inj hn' hn
            injection this with ev
            rw [← ev, isDefOf_of (hPo x (mem_keptPairs hx).1) (mem_keptPairs hx).2] at hd
            cases hd
        · rw [hd] at hv
          simp only [storedDefs_eq, ht', Bool.false_eq_true, ↓reduceIte] at hv
          obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp hv)
          rw [← spillPairs_fst ops i.clobbers, ← keptPairs_fst] at ho
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ho
          obtain ⟨hcx, nx, hnx⟩ := hmem x.1 (hPo x (mem_keptPairs hx).1)
          rw [hc] at hcx
          cases hcx
          rw [hn] at hnx
          cases hnx
          have hmx : (x.2, Loc.stack n x.1.cls) ∈ storeMovesAt (spillHomesAt vc edges) i ops :=
            List.mem_map.mpr ⟨x, hx, by rw [home_eq hn]⟩
          rw [e3 _ hmx]
          exact hkept3 x hx
      · obtain ⟨r, hr, -⟩ := hPreg x (mem_keptPairs hx).1
        rw [e4 _ (hnotS _ fun _ _ he => by rw [hr] at he; cases he)]
        exact hkept3 x hx

end

/-- Each actual indexed spill instruction passes the checker and re-establishes
the dense-home availability invariant. Real code membership derives all home
lookups/bounds/injectivity internally. Static operand/class and available-use
facts remain internal obligations, not additional source input filters. -/
theorem spillInstAt_runs {vc : VCode} {edges : Array (Array (Array Reg))} {c : CheckCtx}
    (slots : c.rf.spillSlots = (spillHomesAt vc edges).size + maxArgsAt edges)
    (saved : c.rf.saved = calleeSaved)
    {b k : Nat} {vb : VBlock} {i : MInst} {ops : Array Operand}
    (block : vc.blocks[b]? = some vb) (instruction : vb.insts[k]? = some i)
    (operands : i.operands = .ok ops) (static : OpsOk ops i.clobbers)
    (returns : ∀ us,i = .rets us → ∀ o ∈ ops.toList,∃ p,o.con = .fixed p ∧ p ∉ calleeSaved)
    (last : k + 1 = vb.insts.size → i.isTerminator = true)
    (classes : ∀ o ∈ ops.toList,vc.classes[o.vreg]? = some o.cls)
    {A : Nat → Bool} (uses : ∀ o ∈ ops.toList,o.kind = .use → A o.vreg = true)
    {a : AState} (good : GoodAt vc edges A a) :
    Runs c vb k (spillInstAt (spillHomesAt vc edges) k i) a fun k' a' =>
      k' = k + 1 ∧ GoodAt vc edges (availInst i A) a' ∧
      ∀ x ∈ keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList,Sym.vreg x.1.vreg ∈ a'.get x.2 := by
  exact instAt_core slots saved (Array.getElem?_eq_some_iff.mp instruction).1 instruction operands static returns last
    (fun o ho => ⟨classes o ho,(spillHomesAt_spec vc edges).code b vb block _ (mem_blockVregs_op instruction operands ho)⟩) uses good

end Backend.Proof.PerEdgeSpill
