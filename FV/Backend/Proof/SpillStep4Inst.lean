import FV.Backend.Proof.SpillStep4Run
import FV.Backend.Proof.SpillStep4Homes
import FV.Backend.Proof.SpillStep4Cfg

/-!
# One spilled instruction re-establishes the availability invariant (V4 (a), step 4)

`Good vc A a`: the checker's abstract state `a` (of the spill allocation's size `stN vc`) has the
home of every vreg available in `A` holding it, and every save slot its callee-saved register's
entry value. `inst_runs`: the items of one instruction (`spillInst`: the restores in front of a
`Rets`, the loads of its uses, the instruction, the stores of its kept defs) pass the checker
from a `Good` state whose availability covers the uses, and reach a `Good` state for
`availInst`, with every kept def's register holding its vreg.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof

/-! ## The frame of the spill allocation -/

/-- `spillAlloc`'s number of argument temporaries. -/
def maxArgs (vc : VCode) : Nat := vc.blocks.foldl (fun m b => max m b.branchArgs.size) 0

theorem spillAlloc_slots (vc : VCode) :
    (spillAlloc vc).spillSlots = (spillHomes vc).size + maxArgs vc := by
  unfold spillAlloc; split <;> rfl

theorem spillAlloc_saved (vc : VCode) : (spillAlloc vc).saved = calleeSaved := by
  unfold spillAlloc; split <;> rfl

/-- The size of the abstract states of the spill allocation. -/
def stN (vc : VCode) : Nat := 128 + 2 * ((spillHomes vc).size + maxArgs vc)

theorem spillHome_eq {vc : VCode} {v n : Nat} {c : RegClass}
    (h : (spillHomes vc)[(v, c)]? = some n) : spillHome (spillHomes vc) v c = .stack n c := by
  simp [spillHome, Std.HashMap.getD_eq_getD_getElem?, h]

theorem stack_index_lt {vc : VCode} {n : Nat} {c : RegClass}
    (hn : n < (spillHomes vc).size + maxArgs vc) :
    ∃ i, (Loc.stack n c).index = some i ∧ i < stN vc := by
  cases c <;> exact ⟨_, rfl, by unfold stN; omega⟩

theorem home_index_lt {vc : VCode} {v n : Nat} {c : RegClass}
    (h : (spillHomes vc)[(v, c)]? = some n) :
    ∃ i, (Loc.stack n c).index = some i ∧ i < stN vc :=
  stack_index_lt (by have := spillHomes_lt vc h; omega)

theorem reg_index_lt {vc : VCode} {r : Reg} (h : r.allocatable = true) :
    ∃ i, (Loc.reg r).index = some i ∧ i < stN vc := by
  obtain ⟨i, h1, h2⟩ := reg_index h
  exact ⟨i, h1, by unfold stN; omega⟩

theorem calleeSaved_ok : ∀ r ∈ calleeSaved, r.allocatable = true ∧ r.realClass?.isSome = true := by
  decide

theorem calleeSaved_nodup : calleeSaved.Nodup := by decide

theorem checkMove_saves (c : CheckCtx) (hs : c.rf.saved = calleeSaved) (w : String) {r : Reg}
    (hr : r ∈ calleeSaved) :
    c.checkMove w (.reg r) (.save r) = .ok () ∧ c.checkMove w (.save r) (.reg r) = .ok () := by
  obtain ⟨ha, hc⟩ := calleeSaved_ok r hr
  obtain ⟨cls, hcls⟩ := Option.isSome_iff_exists.mp hc
  constructor <;>
    simp [CheckCtx.checkMove, CheckCtx.locOk, Loc.cls?, hcls, ha, hs, hr, ensure, Loc.isReg] <;> rfl

theorem nodup_map_of_inj {α β γ : Type} {f : α → β} {g : α → γ} {l : List α}
    (h : (l.map g).Nodup) (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → g x = g y) : (l.map f).Nodup := by
  rw [List.Nodup, List.pairwise_map] at h ⊢
  exact h.imp_of_mem fun hx hy hne he => hne (hinj _ hx _ hy he)

/-! ## The invariant -/

/-- **The availability invariant**: the home of every vreg available in `A` holds it, every save
slot holds its register's entry value. -/
structure Good (vc : VCode) (A : Nat → Bool) (a : AState) : Prop where
  size : a.size = stN vc
  home : ∀ v c n, A v = true → vc.classes[v]? = some c → (spillHomes vc)[(v, c)]? = some n →
    Sym.vreg v ∈ a.get (.stack n c)
  save : ∀ r ∈ calleeSaved, Sym.entry r ∈ a.get (.save r)

/-! ## Kept defs -/

theorem spillPairs_fst (ops : Array Operand) (clob : List Reg) :
    (ops.zip (spillLocs ops clob)).toList.map Prod.fst = ops.toList := by
  rw [pairs_eq, List.map_map]; exact List.zipIdx_map_fst 0 _

/-- The def operands an instruction keeps (`MInst.keptDefs`). -/
def keptOps (i : MInst) (ops : List Operand) : List Operand :=
  match i.keptDefs with
  | none => ops.filter (·.kind == .def)
  | some n => (ops.filter (·.kind == .def)).take n

theorem keptPairs_fst (i : MInst) (P : List (Operand × Loc)) :
    (keptPairs i P).map Prod.fst = keptOps i (P.map Prod.fst) := by
  have : (P.filter (·.1.kind == .def)).map Prod.fst = (P.map Prod.fst).filter (·.kind == .def) := by
    rw [List.filter_map]; rfl
  unfold keptPairs keptOps
  cases hk : i.keptDefs <;> simp only [List.map_take, this]

theorem storedDefs_eq (i : MInst) (ops : Array Operand) :
    storedDefs i ops = if i.isTerminator then [] else (keptOps i ops.toList).map (·.vreg) := by
  unfold storedDefs keptOps
  cases hk : i.keptDefs <;> rfl

theorem mem_keptOps {i : MInst} {ops : List Operand} {o : Operand} (h : o ∈ keptOps i ops) :
    o ∈ ops ∧ o.kind = .def := by
  unfold keptOps at h
  split at h
  · have := List.mem_filter.mp h; exact ⟨this.1, by simpa using this.2⟩
  · have := List.mem_filter.mp (List.mem_of_mem_take h); exact ⟨this.1, by simpa using this.2⟩

theorem mem_keptPairs {i : MInst} {P : List (Operand × Loc)} {x : Operand × Loc}
    (h : x ∈ keptPairs i P) : x ∈ P ∧ x.1.kind = .def := by
  unfold keptPairs at h
  split at h
  · have := List.mem_filter.mp h; exact ⟨this.1, by simpa using this.2⟩
  · have := List.mem_filter.mp (List.mem_of_mem_take h); exact ⟨this.1, by simpa using this.2⟩

theorem keptPairs_vregs_nodup {ops : Array Operand} {i : MInst} (h : OpsOk ops i.clobbers) :
    ((keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList).map (·.1.vreg)).Nodup := by
  have hd := spill_defVregs_nodup h
  unfold keptPairs
  split
  · exact hd
  · rw [List.map_take]; exact hd.sublist (List.take_sublist _ _)

/-- Is `v` a def of the operands `ops`? -/
def isDefOf (ops : Array Operand) (v : Nat) : Bool := (ops.toList.filter (·.kind == .def)).any (·.vreg == v)

theorem isDefOf_of {ops : Array Operand} {o : Operand} (ho : o ∈ ops.toList) (hd : o.kind = .def) :
    isDefOf ops o.vreg = true :=
  List.any_eq_true.mpr ⟨o, List.mem_filter.mpr ⟨ho, by simp [hd]⟩, by simp⟩

theorem availInst_eq {i : MInst} {ops : Array Operand} (hops : i.operands = .ok ops)
    (A : Nat → Bool) (v : Nat) :
    availInst i A v = if isDefOf ops v then (storedDefs i ops).contains v else A v := by
  unfold availInst isDefOf; rw [hops]

/-! ## The items of one instruction -/

/-- The restores in front of a `Rets`. -/
def restoresOf (i : MInst) : List RItem :=
  match i with
  | .rets _ => spillRestores
  | _ => []

/-- The stores of the kept defs. -/
def storeMoves (h : Homes) (i : MInst) (ops : Array Operand) : List (Loc × Loc) :=
  (keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList).map
    fun x => (x.2, spillHome h x.1.vreg x.1.cls)

theorem spillInst_eq {h : Homes} {k : Nat} {i : MInst} {ops : Array Operand}
    (hops : i.operands = .ok ops) :
    spillInst h k i = restoresOf i ++ (loadMoves h ops i.clobbers).map mv ++
      [.op k (spillLocs ops i.clobbers)] ++
      (if i.isTerminator then [] else (storeMoves h i ops).map mv) := by
  simp only [spillInst, hops, loadMoves, storeMoves, List.map_map]
  congr 1 <;> (try split) <;> rfl

theorem restoresOf_other {i : MInst} (h : ∀ us, i ≠ .rets us) : restoresOf i = [] := by
  unfold restoresOf
  split
  · exact absurd rfl (h _)
  · rfl

theorem spillRestores_eq : spillRestores = (calleeSaved.map fun r => (Loc.save r, Loc.reg r)).map mv := by
  simp [spillRestores, List.map_map, mv]

theorem spillSaves_eq : spillSaves = (calleeSaved.map fun r => (Loc.reg r, Loc.save r)).map mv := by
  simp [spillSaves, List.map_map, mv]

section
variable {c : CheckCtx} {vc : VCode}

/-- **The restores in front of a `Rets`** leave the callee-saved registers holding their entry
values, and keep `Good`. -/
theorem restores_runs (hsv : c.rf.saved = calleeSaved) {vb : VBlock} {k : Nat}
    (hkn : k ≠ vb.insts.size) {i : MInst} {A : Nat → Bool} {a : AState} (hg : Good vc A a) :
    Runs c vb k (restoresOf i) a fun k' a1 => k' = k ∧ Good vc A a1 ∧
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
        exact ⟨i, h1, by rw [hg.size]; unfold stN; omega⟩)).mono
      fun k' a1 ⟨e1, e2, e3, e4⟩ => ⟨e1, ⟨by rw [e2, hg.size],
        fun v c n hv hc hn => by rw [e4 _ (by simp)]; exact hg.home v c n hv hc hn,
        fun r hr => by rw [e4 _ (by simp)]; exact hg.save r hr⟩,
        fun _ _ r hr => by rw [e3 (Loc.save r, Loc.reg r) (List.mem_map_of_mem hr)]; exact hg.save r hr⟩
  · rw [restoresOf_other fun us h => hr ⟨us, h⟩]
    exact Runs.nil ⟨rfl, hg, fun us h => absurd ⟨us, h⟩ hr⟩

/-- **One instruction** (`spillInst`): from a `Good` state whose availability covers the uses, the
items pass the checker and reach a `Good` state for `availInst`, every kept def's register
holding its vreg. -/
theorem inst_runs (hsl : c.rf.spillSlots = (spillHomes vc).size + maxArgs vc)
    (hsv : c.rf.saved = calleeSaved) {vb : VBlock} {k : Nat} {i : MInst} {ops : Array Operand}
    (hk : k < vb.insts.size) (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops)
    (hok : OpsOk ops i.clobbers)
    (hrets : ∀ us, i = .rets us → ∀ o ∈ ops.toList, ∃ p, o.con = .fixed p ∧ p ∉ calleeSaved)
    (hterm : k + 1 = vb.insts.size → i.isTerminator = true)
    (hmem : ∀ o ∈ ops.toList, vc.classes[o.vreg]? = some o.cls ∧
      ∃ n, (spillHomes vc)[(o.vreg, o.cls)]? = some n)
    {A : Nat → Bool} (huse : ∀ o ∈ ops.toList, o.kind = .use → A o.vreg = true)
    {a : AState} (hg : Good vc A a) :
    Runs c vb k (spillInst (spillHomes vc) k i) a fun k' a' => k' = k + 1 ∧
      Good vc (availInst i A) a' ∧
      ∀ x ∈ keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList, Sym.vreg x.1.vreg ∈ a'.get x.2 := by
  have hkn : k ≠ vb.insts.size := by omega
  have h64 : 64 ≤ stN vc := by unfold stN; omega
  have hPf := spillPairs_fst ops i.clobbers
  have hPo : ∀ x ∈ (ops.zip (spillLocs ops i.clobbers)).toList, x.1 ∈ ops.toList := fun x hx =>
    hPf ▸ List.mem_map_of_mem hx
  have hPreg : ∀ x ∈ (ops.zip (spillLocs ops i.clobbers)).toList, ∃ r, x.2 = .reg r ∧
      r.allocatable = true ∧ r.realClass? = some x.1.cls := fun x hx => spill_reg hok hx
  rw [spillInst_eq hops]
  -- restores and loads
  have hL : Runs c vb k (restoresOf i ++ (loadMoves (spillHomes vc) ops i.clobbers).map mv) a
      fun k' a2 => k' = k ∧ Good vc A a2 ∧
        (∀ x ∈ (ops.zip (spillLocs ops i.clobbers)).toList, x.1.kind = .use →
          Sym.vreg x.1.vreg ∈ a2.get x.2) ∧
        (∀ us, i = .rets us → ∀ r ∈ calleeSaved, Sym.entry r ∈ a2.get (.reg r)) := by
    refine Runs.append (restores_runs hsv hkn hg) fun k1 a1 ⟨hk1, hg1, hret1⟩ => ?_
    subst hk1
    obtain ⟨a2, hrun, hsz2, hget2, hkeep2⟩ := loads_run c s!"block {vb.label}" (hm := spillHomes vc)
      hok (fun o ho _ => by
        obtain ⟨_, n, hn⟩ := hmem o ho
        rw [Std.HashMap.getD_eq_getD_getElem?, hn, Option.getD_some, hsl]
        have := spillHomes_lt vc hn
        omega) (a := a1) (by rw [hg1.size]; exact h64)
    refine (Runs.ofRunMoves hkn _ _ _ hrun).mono fun k' a' ⟨e1, e2⟩ => ?_
    subst e1 e2
    refine ⟨rfl, ⟨by rw [hsz2, hg1.size],
      fun v c n hv hc hn => by rw [hkeep2 _ rfl]; exact hg1.home v c n hv hc hn,
      fun r hr => by rw [hkeep2 _ rfl]; exact hg1.save r hr⟩, fun x hx hu => ?_, fun us hus r hr => ?_⟩
    · obtain ⟨hc, n, hn⟩ := hmem x.1 (hPo x hx)
      rw [hget2 x.1 x.2 hx hu, spillHome_eq hn]
      exact hg1.home _ _ n (huse x.1 (hPo x hx) hu) hc hn
    · rw [runMoves_frame c _ _ _ _ hrun (.reg r) ?_]
      · exact hret1 us hus r hr
      · intro m hm he
        simp only [loadMoves, List.mem_map, List.mem_filter] at hm
        obtain ⟨⟨o, l⟩, ⟨hx, -⟩, rfl⟩ := hm
        obtain ⟨p, hp, hpn⟩ := hrets us hus o (hPo _ hx)
        obtain ⟨j, -, hl⟩ := mem_spillPairs hx
        simp only at he
        rw [hl, locOf_fixed hp] at he
        cases he
        exact hpn hr
  -- the instruction
  have hO : Runs c vb k (restoresOf i ++ (loadMoves (spillHomes vc) ops i.clobbers).map mv ++
      [.op k (spillLocs ops i.clobbers)]) a fun k' a3 => k' = k + 1 ∧ a3.size = stN vc ∧
        (∀ v c n, A v = true → isDefOf ops v = false → vc.classes[v]? = some c →
          (spillHomes vc)[(v, c)]? = some n → Sym.vreg v ∈ a3.get (.stack n c)) ∧
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
    have hmemS : ∀ m ∈ storeMoves (spillHomes vc) i ops, ∃ x ∈ keptPairs i
        (ops.zip (spillLocs ops i.clobbers)).toList, ∃ n, m = (x.2, .stack n x.1.cls) ∧
        (spillHomes vc)[(x.1.vreg, x.1.cls)]? = some n := by
      intro m hm
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
      obtain ⟨-, n, hn⟩ := hmem x.1 (hPo x (mem_keptPairs hx).1)
      exact ⟨x, hx, n, by rw [spillHome_eq hn], hn⟩
    refine (Runs.moves hk1 (storeMoves (spillHomes vc) i ops) a3 (fun m hm => ?_)
      (fun m hm m' hm' he => ?_) ?_ (fun m hm => ?_)).mono fun k' a4 ⟨e1, e2, e3, e4⟩ => ?_
    · obtain ⟨x, hx, n, rfl, hn⟩ := hmemS m hm
      obtain ⟨r, hr, ha, hcl⟩ := hPreg x (mem_keptPairs hx).1
      rw [hr]
      exact checkMove_store c _ (by rw [hsl]; have := spillHomes_lt vc hn; omega) ha hcl
    · obtain ⟨x, hx, n, rfl, hn⟩ := hmemS m hm
      obtain ⟨x', hx', n', rfl, hn'⟩ := hmemS m' hm'
      obtain ⟨r, hr, -⟩ := hPreg x (mem_keptPairs hx).1
      simp only at he
      rw [hr] at he
      cases he
    · unfold storeMoves
      rw [List.map_map]
      refine nodup_map_of_inj (keptPairs_vregs_nodup hok) fun x hx y hy he => ?_
      obtain ⟨-, n, hn⟩ := hmem x.1 (hPo x (mem_keptPairs hx).1)
      obtain ⟨-, n', hn'⟩ := hmem y.1 (hPo y (mem_keptPairs hy).1)
      simp only [Function.comp, spillHome_eq hn, spillHome_eq hn'] at he
      injection he with e1 e2
      rw [← e1, ← e2] at hn'
      have := spillHomes_inj vc hn hn'
      injection this
    · obtain ⟨x, hx, n, rfl, hn⟩ := hmemS m hm
      obtain ⟨j, h1, h2⟩ := home_index_lt hn
      exact ⟨j, h1, by rw [hsz3]; exact h2⟩
    · have hnotS : ∀ l, (∀ n c, l ≠ .stack n c) → ∀ m ∈ storeMoves (spillHomes vc) i ops, m.2 ≠ l := by
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
            have := spillHomes_inj vc hn' hn
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
          have hmx : (x.2, Loc.stack n x.1.cls) ∈ storeMoves (spillHomes vc) i ops :=
            List.mem_map.mpr ⟨x, hx, by rw [spillHome_eq hn]⟩
          rw [e3 _ hmx]
          exact hkept3 x hx
      · obtain ⟨r, hr, -⟩ := hPreg x (mem_keptPairs hx).1
        rw [e4 _ (hnotS _ fun _ _ he => by rw [hr] at he; cases he)]
        exact hkept3 x hx

end

end Backend.Proof.Spill
