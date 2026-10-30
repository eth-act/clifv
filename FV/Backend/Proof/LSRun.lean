import FV.Backend.Proof.LSInst
import FV.Backend.Proof.LSMoves
import FV.Backend.Proof.LSBuild
import FV.Backend.Proof.SpillStep4State

/-!
# The checker accepts the Lean allocator's validated plans (V4b-3, #275): states and invariants

The in-states of an allocation `rf = Ctx.build c` of a validated plan (`inState`): on entry to
block `s`, the location of every vreg live there (`Plan.cov` at the block's start) and available
(`SpillAvail`'s `D s`, or a result of the only predecessor's `try_call`: `entryStored`) holds it —
a `try_call` result still in its fixed register (`entryLoc`) —, every callee-saved register the
allocation saves is in its save slot (on entry to block 0: in the register), the others in their
register (`mem_inState`, `inState_vreg`, …). Along a block (`Good`): at instruction `g`, every
vreg live at `pos g 0` and available is in its location; after an instruction (`Post`) the vregs
live across it, its stored defs and a terminator's kept defs are where the successors expect
them, and `good_succ` gives `Good` at the next instruction. `Hyps` collects what the runs assume.
The runs: `inst_runs` (`LSRunInst.lean`), `last_edges` (`LSRunEdge.lean`), `args_runs`
(`LSRunArgs.lean`), `entry_runs`, `inState_entryOk`, `inState_le_entry` (`LSRunEntry.lean`),
`verify_block`, `allocChecked` (`LSRunMain.lean`).
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan Backend.Proof Backend.Proof.Spill
open Backend.LinearScan.Ctx (Parts blockItems)

section
variable (vc : VCode) (c : LinearScan.Ctx) (rf : RFunc) (D : Nat → Nat → Bool)

/-- The checker context of the allocation `rf` of `vc`. -/
def ctxOf : CheckCtx := { vc, succs := c.fn.succs, rf, size := 128 + 2 * rf.spillSlots }

/-- A location the abstract states of `rf`'s checker context represent. -/
def LocValid (l : Loc) : Prop := ∃ i, l.index = some i ∧ i < 128 + 2 * rf.spillSlots

/-- The callee-saved registers' entry values: in the save slot if `rf` saves the register, else
in the register. -/
def CalleeOk (a : AState) : Prop :=
  ∀ r ∈ calleeSaved, (r ∈ rf.saved → Sym.entry r ∈ a.get (.save r)) ∧
    (r ∉ rf.saved → Sym.entry r ∈ a.get (.reg r))

/-- **The invariant along a block** at position `p` (`pos g 0` of instruction `g`) with
availability `A`: every live, available vreg is in its location. -/
structure Good (A : Nat → Bool) (p : Nat) (a : AState) : Prop where
  size : a.size = 128 + 2 * rf.spillSlots
  vregs : ∀ v < c.fn.nv, c.pl.cov v p = true → A v = true → LocValid rf (c.loc v) →
    Sym.vreg v ∈ a.get (c.loc v)
  callee : CalleeOk rf a

/-- What an instruction's items leave (global index `g`, availability `A` before it): the vregs
live across it that it does not define stay in their locations; the defs it stores are in theirs;
the kept defs of a terminator are in their fixed registers. -/
structure Post (g : Nat) (i : MInst) (os : Array Operand) (A : Nat → Bool) (a : AState) : Prop where
  size : a.size = 128 + 2 * rf.spillSlots
  callee : CalleeOk rf a
  thru : ∀ v < c.fn.nv, c.pl.covI v (pos g 0) (pos g 4) = true →
    A v = true → (∀ o ∈ os.toList, o.kind = .def → o.vreg ≠ v) → LocValid rf (c.loc v) →
    Sym.vreg v ∈ a.get (c.loc v)
  stored : ∀ (j : Nat) (o : Operand), os[j]? = some o → o.kind = .def →
    c.store g i.isTerminator (keptIdx i os) j o = true → Sym.vreg o.vreg ∈ a.get (c.loc o.vreg)
  results : i.isTerminator = true → ∀ (j : Nat) (o : Operand) (p : Reg), os[j]? = some o →
    o.kind = .def → j ∈ keptIdx i os → o.con = .fixed p → Sym.vreg o.vreg ∈ a.get (.reg p)

/-- The location of `v` on entry to block `s`: a live result of its only predecessor's `try_call`
is still in its fixed register (the entry moves move it). -/
def entryLoc (s v : Nat) : Loc :=
  match ((entryPairs vc c.fn.succs c.fn.preds s).map (·.1)).find? (·.vreg == v) with
  | some o => match o.con with
    | .fixed p => .reg p
    | _ => c.loc v
  | none => c.loc v

/-- The content of each location in the in-state of block `s`. -/
def inContent (s : Nat) (l : Loc) : List Sym :=
  ((List.range c.fn.nv).filter fun v => c.pl.cov v (pos (c.fn.start.getD s 0) 0) &&
      (D s v || (entryStored vc c.fn.succs c.fn.preds s).contains v) && entryLoc vc c s v == l).map
    .vreg ++
  match l with
  | .reg r => if r ∈ calleeSaved ∧ (s = 0 ∨ r ∉ rf.saved) then [.entry r] else []
  | .save r => if s ≠ 0 ∧ r ∈ rf.saved then [.entry r] else []
  | .stack _ _ => []

/-- **The in-state of block `s`.** -/
def inState (s : Nat) : AState := mkState (128 + 2 * rf.spillSlots) (inContent vc c rf D s)

/-- The in-states of all blocks. -/
def insOf : Array (Option AState) :=
  Array.ofFn (n := vc.blocks.size) fun b => some (inState vc c rf D b)

end

/-- What the runs assume: the function view, the validated plan's facts, the builder's output
facts, the in-scope local facts and availability sets, and the instruction step. -/
structure Hyps (vc : VCode) (c : LinearScan.Ctx) (rf : RFunc) (D : Nat → Nat → Bool) : Prop where
  fn : FnOk vc c.fn
  plan : PlanFacts vc c
  occ : c.occ = c.pl.occ
  build : BuildFacts vc c rf
  loc : SpillLocalOk vc
  avail : SpillAvail vc D
  inst : ∀ (g : Nat) (i : MInst) (os : Array Operand) (io : IOut), c.fn.insts[g]? = some i →
    c.fn.ops[g]? = some os → OpsOk os i.clobbers → (∀ o ∈ os.toList, c.fn.clsOf o.vreg = o.cls) →
    c.inst g = .ok io → InstFacts c g i os io

/-! ## Positions and births -/

theorem pos_div (g sl : Nat) (h : sl < 5) : pos g sl / 5 = g ∧ pos g sl % 5 = sl := by
  unfold pos; omega

/-- What a birth at `pos g sl` is. -/
theorem birthOk_pos {c : LinearScan.Ctx} {v g sl : Nat} (hsl : sl < 5)
    (h : c.birthOk v (pos g sl) = true) :
    (sl = 0 → c.fn.isStart g = true) ∧ (sl = 1 → c.fn.paramAt g v = true) ∧
    (sl ≠ 0 → sl ≠ 1 → ∃ o ∈ (c.fn.ops.getD g #[]).toList, o.kind = .def ∧ o.vreg = v ∧
      opSlot o = sl) := by
  obtain ⟨h1, h2⟩ := pos_div g sl hsl
  unfold LinearScan.Ctx.birthOk at h
  simp only [h1, h2] at h
  refine ⟨fun e => by subst e; exact h, fun e => by subst e; exact h, fun h0 h1' => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, sl = n + 2 := ⟨sl - 2, by omega⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h⟩ := h
  rw [← Array.any_toList, List.any_eq_true] at h
  obtain ⟨o, ho, he⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq] at he
  exact ⟨o, ho, he.1.1, he.1.2, he.2⟩

/-- A covered position lies in a segment that starts at a birth. -/
theorem cov_seg {vc : VCode} {c : LinearScan.Ctx} (hpf : PlanFacts vc c) {v p : Nat}
    (hv : v < c.fn.nv) (h : c.pl.cov v p = true) :
    ∃ s e, (s, e) ∈ (c.pl.segs.getD v #[]).toList ∧ s ≤ p ∧ p ≤ e ∧ c.birthOk v s = true := by
  obtain ⟨s, e, hm, h1, h2⟩ := cov_iff.mp h
  exact ⟨s, e, hm, h1, h2, (hpf.birth v hv s e hm).2⟩

/-- A position covered with no birth between `q` and it is covered from `q` on. -/
theorem covI_of_nobirth {vc : VCode} {c : LinearScan.Ctx} (hpf : PlanFacts vc c) {v p q : Nat}
    (hv : v < c.fn.nv) (h : c.pl.cov v p = true) (_hqp : q ≤ p)
    (hnb : ∀ s, q < s → s ≤ p → c.birthOk v s = false) : c.pl.covI v q p = true := by
  obtain ⟨s, e, hm, h1, h2, hb⟩ := cov_seg hpf hv h
  refine covI_iff.mpr ⟨s, e, hm, ?_, h2⟩
  rcases Nat.lt_or_ge q s with hlt | hle
  · have := hnb s hlt h1
    rw [hb] at this; cases this
  · exact hle

theorem covI_mono {c : LinearScan.Ctx} {v p q p' q' : Nat} (h : c.pl.covI v p q = true)
    (hp : p ≤ p') (hq : q' ≤ q) : c.pl.covI v p' q' = true := by
  obtain ⟨s, e, hm, h1, h2⟩ := covI_iff.mp h
  exact covI_iff.mpr ⟨s, e, hm, by omega, by omega⟩

theorem cov_of_covI {c : LinearScan.Ctx} {v p q r : Nat} (h : c.pl.covI v p q = true)
    (h1 : p ≤ r) (h2 : r ≤ q) : c.pl.cov v r = true := by
  obtain ⟨s, e, hm, h1', h2'⟩ := covI_iff.mp h
  exact cov_iff.mpr ⟨s, e, hm, by omega, by omega⟩

section
variable {vc : VCode} {fn : Fn} (hf : FnOk vc fn)
include hf

theorem FnOk.blkGetD {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {k : Nat}
    (hk : k < vb.insts.size) : fn.blk.getD (fn.start.getD b 0 + k) 0 = b := by
  obtain ⟨-, hblk, -⟩ := hf.inst b vb k _ hvb (Array.getElem?_eq_getElem hk)
  rw [Array.getD_eq_getD_getElem?, hblk, Option.getD_some]

theorem FnOk.startSucc {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) :
    fn.start.getD (b + 1) 0 = fn.start.getD b 0 + vb.insts.size := by
  rw [Array.getD_eq_getD_getElem?, hf.start_succ b vb hvb, Option.getD_some]

/-- Inside a block, no instruction but the first starts it. -/
theorem FnOk.notStart {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {k : Nat}
    (hk : k < vb.insts.size) (hk0 : k ≠ 0) : fn.isStart (fn.start.getD b 0 + k) = false := by
  unfold Fn.isStart
  rw [hf.blkGetD hvb hk]
  simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  right; omega

/-- Only the last instruction of a block writes parameters. -/
theorem FnOk.notParamAt {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {k : Nat}
    (hk : k + 1 < vb.insts.size) (v : Nat) : fn.paramAt (fn.start.getD b 0 + k) v = false := by
  have hb := hf.blkGetD hvb (k := k) (by omega)
  have hs := hf.startSucc hvb
  have hne : (fn.start.getD b 0 + k + 1 == fn.start.getD (b + 1) 0) = false := by
    rw [hs, beq_eq_false_iff_ne]; omega
  simp only [Fn.paramAt, hb, hne, Bool.and_false, Bool.false_and]

end

/-- The operand view of instruction `k` of block `b` at its global index. -/
theorem FnOk.opsGetD {vc : VCode} {fn : Fn} (hf : FnOk vc fn) {b : Nat} {vb : VBlock}
    (hvb : vc.blocks[b]? = some vb) {k : Nat} {i : MInst} (hi : vb.insts[k]? = some i)
    {os : Array Operand} (hos : i.operands = .ok os) :
    fn.ops[fn.start.getD b 0 + k]? = some os ∧ fn.ops.getD (fn.start.getD b 0 + k) #[] = os ∧
      fn.insts[fn.start.getD b 0 + k]? = some i := by
  obtain ⟨hgi, -, ops', hops', hgo⟩ := hf.inst b vb k i hvb hi
  rw [hos] at hops'
  cases hops'
  exact ⟨hgo, by rw [Array.getD_eq_getD_getElem?, hgo, Option.getD_some], hgi⟩

/-- No birth at the next instruction's start inside a block. -/
theorem nobirth_next {vc : VCode} {c : LinearScan.Ctx} (hf : FnOk vc c.fn) {b : Nat}
    {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {k : Nat} (hk : k + 1 < vb.insts.size)
    (v : Nat) : c.birthOk v (pos (c.fn.start.getD b 0 + k) 0 + 5) = false := by
  have he : pos (c.fn.start.getD b 0 + k) 0 + 5 = pos (c.fn.start.getD b 0 + (k + 1)) 0 := by
    unfold pos; omega
  rw [he, Bool.eq_false_iff]
  intro h
  have := (birthOk_pos (by omega) h).1 rfl
  rw [hf.notStart hvb hk (by omega)] at this
  cases this

/-- No birth inside an instruction that is not its block's last, of a vreg it does not define. -/
theorem nobirth_inside {vc : VCode} {c : LinearScan.Ctx} (hf : FnOk vc c.fn) {b : Nat}
    {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {k : Nat} {i : MInst}
    (hi : vb.insts[k]? = some i) {os : Array Operand} (hos : i.operands = .ok os)
    (hk : k + 1 < vb.insts.size) {v : Nat} (hd : isDefOf os v = false) :
    ∀ s, pos (c.fn.start.getD b 0 + k) 0 < s → s ≤ pos (c.fn.start.getD b 0 + k) 0 + 5 →
      c.birthOk v s = false := by
  intro s h1 h2
  by_cases h5 : s = pos (c.fn.start.getD b 0 + k) 0 + 5
  · subst h5; exact nobirth_next hf hvb hk v
  rw [Bool.eq_false_iff]
  intro hb
  obtain ⟨sl, hsl, rfl⟩ : ∃ sl, sl < 5 ∧ s = pos (c.fn.start.getD b 0 + k) sl :=
    ⟨s - 5 * (c.fn.start.getD b 0 + k), by unfold pos at *; omega, by unfold pos at *; omega⟩
  obtain ⟨-, hb1, hb2⟩ := birthOk_pos hsl hb
  have hsl0 : sl ≠ 0 := by unfold pos at h1; omega
  by_cases hsl1 : sl = 1
  · subst hsl1
    have := hb1 rfl
    rw [hf.notParamAt hvb hk v] at this
    cases this
  obtain ⟨o, ho, hk', hv, -⟩ := hb2 hsl0 hsl1
  rw [(hf.opsGetD hvb hi hos).2.1] at ho
  have := isDefOf_of ho hk'
  rw [hv, hd] at this
  cases this

/-- A kept def (`keptOps`) is the operand at a kept index (`keptIdx`). -/
theorem keptOps_idx {i : MInst} {os : Array Operand} {o : Operand}
    (h : o ∈ keptOps i os.toList) : ∃ j, os[j]? = some o ∧ j ∈ keptIdx i os := by
  have hP : (os.toList.zipIdx.filter (·.1.kind == .def)).map (·.1) = os.toList.filter (·.kind == .def) := by
    conv => rhs; rw [← List.zipIdx_map_fst 0 os.toList]
    rw [List.filter_map]; rfl
  have key : ∀ (L : List (Operand × Nat)), (∀ x ∈ L, os[x.2]? = some x.1) → o ∈ L.map (·.1) →
      ∃ j, os[j]? = some o ∧ j ∈ L.map (·.2) := by
    intro L hL ho
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ho
    exact ⟨x.2, hL x hx, List.mem_map_of_mem hx⟩
  have hz : ∀ x ∈ os.toList.zipIdx.filter (·.1.kind == .def), os[x.2]? = some x.1 := by
    intro x hx
    have := List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hx).1
    simpa [Array.getElem?_toList] using this
  unfold keptOps at h
  unfold keptIdx
  split at h <;> rename_i hkd <;> simp only [hkd]
  · exact key _ hz (by rw [hP]; exact h)
  · rename_i n
    rw [← List.map_take]
    exact key _ (fun x hx => hz x (List.mem_of_mem_take hx)) (by rw [List.map_take, hP]; exact h)

/-! ## Checker helpers -/

theorem mem_of_get {α : Type} {a : Array α} {j : Nat} {x : α} (h : a[j]? = some x) :
    x ∈ a.toList :=
  List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact h)

theorem zip_get {α β : Type} {a : Array α} {b : Array β} {x : α × β}
    (h : x ∈ (a.zip b).toList) : ∃ j : Nat, a[j]? = some x.1 ∧ b[j]? = some x.2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
  have hj' : (a.zip b)[j]? = some x := by rw [← Array.getElem?_toList]; exact hj
  exact ⟨j, (Array.getElem?_zip_eq_some.mp hj').1, (Array.getElem?_zip_eq_some.mp hj').2⟩

theorem get_zip {α β : Type} {a : Array α} {b : Array β} {j : Nat} {x : α} {y : β}
    (ha : a[j]? = some x) (hb : b[j]? = some y) : (x, y) ∈ (a.zip b).toList :=
  mem_of_get (a := a.zip b) (j := j) (Array.getElem?_zip_eq_some.mpr ⟨ha, hb⟩)

theorem loc_cls {vc : VCode} {c : LinearScan.Ctx} (hpf : PlanFacts vc c) {v : Nat}
    {cl : RegClass} (h : c.fn.clsOf v = cl) : LocCls (c.loc v) cl := by
  unfold LinearScan.Ctx.loc Fn.loc
  cases hr : c.pl.regOf v with
  | some r =>
    obtain ⟨h1, h2, -⟩ := pool_ok (hpf.regs v r hr)
    exact .inl ⟨r, rfl, h1, h ▸ h2⟩
  | none => exact .inr ⟨_, by rw [h]⟩

theorem loc_reg {c : LinearScan.Ctx} {v : Nat} {r : Reg} (h : c.loc v = .reg r) :
    c.pl.regOf v = some r := by
  unfold LinearScan.Ctx.loc Fn.loc at h
  cases hr : c.pl.regOf v with
  | some r' => rw [hr] at h; cases h; rfl
  | none => rw [hr] at h; cases h

theorem locValid_of_cls {rf : RFunc} {l : Loc} {cl : RegClass} (h : LocCls l cl)
    (hs : ∀ s c', l = .stack s c' → s < rf.spillSlots) : LocValid rf l := by
  rcases h with ⟨r, rfl, ha, -⟩ | ⟨s, rfl⟩
  · obtain ⟨i, hi, hlt⟩ := reg_index ha
    exact ⟨i, hi, by omega⟩
  · have := hs s cl rfl
    cases cl
    · exact ⟨128 + 2 * s, rfl, by omega⟩
    · exact ⟨129 + 2 * s, rfl, by omega⟩

theorem checkMove_ok {cc : CheckCtx} {w : String} {src dst : Loc} {cl : RegClass}
    (hs : LocCls src cl) (hd : LocCls dst cl)
    (hss : ∀ s c', src = .stack s c' → s < cc.rf.spillSlots)
    (hds : ∀ s c', dst = .stack s c' → s < cc.rf.spillSlots)
    (hreg : src.isReg = true ∨ dst.isReg = true) : cc.checkMove w src dst = .ok () := by
  rcases hs with ⟨r, rfl, ha, hc⟩ | ⟨s, rfl⟩ <;> rcases hd with ⟨r', rfl, ha', hc'⟩ | ⟨s', rfl⟩
  · simp [CheckCtx.checkMove, CheckCtx.locOk, Loc.cls?, ha, hc, ha', hc', ensure, Loc.isReg]; rfl
  · have := hds s' cl rfl
    simp [CheckCtx.checkMove, CheckCtx.locOk, Loc.cls?, ha, hc, this, ensure, Loc.isReg]; rfl
  · have := hss s cl rfl
    simp [CheckCtx.checkMove, CheckCtx.locOk, Loc.cls?, ha', hc', this, ensure, Loc.isReg]; rfl
  · simp [Loc.isReg] at hreg

theorem calleeSaved_ok' : ∀ r ∈ calleeSaved, r.allocatable = true ∧ r.realClass?.isSome = true := by
  decide

theorem calleeSaved_ok (r : Reg) (h : r ∈ calleeSaved) :
    r.allocatable = true ∧ ∃ cl, r.realClass? = some cl := by
  obtain ⟨h1, h2⟩ := calleeSaved_ok' r h
  exact ⟨h1, Option.isSome_iff_exists.mp h2⟩

theorem checkMove_restore {cc : CheckCtx} {w : String} {r : Reg} (hr : r ∈ cc.rf.saved)
    (hc : r ∈ calleeSaved) : cc.checkMove w (.save r) (.reg r) = .ok () := by
  obtain ⟨ha, cl, hcl⟩ := calleeSaved_ok r hc
  simp [CheckCtx.checkMove, CheckCtx.locOk, Loc.cls?, hcl, ha, hr, hc, ensure, Loc.isReg]; rfl

theorem checkMove_save {cc : CheckCtx} {w : String} {r : Reg} (hr : r ∈ cc.rf.saved)
    (hc : r ∈ calleeSaved) : cc.checkMove w (.reg r) (.save r) = .ok () := by
  obtain ⟨ha, cl, hcl⟩ := calleeSaved_ok r hc
  simp [CheckCtx.checkMove, CheckCtx.locOk, Loc.cls?, hcl, ha, hr, hc, ensure, Loc.isReg]; rfl

theorem mv_eq : LinearScan.mv = Spill.mv := rfl

theorem restoresOf_eq (L : List Reg) :
    restoresOf L = (L.map fun r => (Loc.save r, Loc.reg r)).map Spill.mv := by
  simp [restoresOf, Spill.mv]

theorem savesOf_eq (L : List Reg) :
    savesOf L = (L.map fun r => (Loc.reg r, Loc.save r)).map Spill.mv := by
  simp [savesOf, Spill.mv]

/-- What the static checks give the transfer: def locations distinct and not clobbered. -/
theorem checkStatic_defs {cc : CheckCtx} {w : String} {ops : Array Operand} {allocs : Array Loc}
    {clob : List Reg} (h : cc.checkStatic w ops allocs clob = .ok ()) :
    (((ops.zip allocs).toList.filter (·.1.kind == .def)).map (·.2)).Nodup ∧
    ∀ d ∈ (ops.zip allocs).toList, d.1.kind = .def → ∀ r ∈ clob, Loc.reg r ≠ d.2 := by
  unfold CheckCtx.checkStatic at h
  obtain ⟨_, h⟩ := Except.seq_ok h
  dsimp only at h
  obtain ⟨_, h⟩ := Except.seq_ok h
  obtain ⟨h3, h⟩ := Except.seq_ok h
  obtain ⟨h4, _⟩ := Except.seq_ok h
  refine ⟨by simpa using ensure_ok h3, fun d hd hk r hr e => ?_⟩
  have hd' : d ∈ (ops.zip allocs).toList.filter (·.1.kind == .def) :=
    List.mem_filter.mpr ⟨hd, by simp [hk]⟩
  have := ensure_ok (forM_ok h4 d hd')
  have hmem : d.2 ∈ defConflicts ((ops.zip allocs).toList.filter (·.1.kind == .use))
      (clob.map Loc.reg) d.1.pos := by
    cases d.1.pos <;> simp only [defConflicts, List.mem_append, List.mem_map] <;>
      exact .inr ⟨r, hr, e⟩
  simp at this
  exact this (by simpa using hmem)

/-- A kept def's location holds exactly its vreg after the transfer (the static checks pass). -/
theorem transferOp_kept' {i : MInst} {P : List (Operand × Loc)} {a : AState}
    (hsz : 64 ≤ a.size)
    (hDl : ((P.filter (·.1.kind == .def)).map (·.2)).Nodup)
    (hDv : ((P.filter (·.1.kind == .def)).map (·.1.vreg)).Nodup)
    (hreg : ∀ x ∈ P, ∃ i, x.2.index = some i ∧ i < 64)
    (hnotclob : ∀ x ∈ P, x.1.kind = .def → ∀ r ∈ i.clobbers, Loc.reg r ≠ x.2)
    {o : Operand} {l : Loc} (hk : (o, l) ∈ keptPairs i P) :
    (transferOp i P a).get l = [.vreg o.vreg] := by
  have hD : (o, l) ∈ P.filter (·.1.kind == .def) := by
    unfold keptPairs at hk
    split at hk
    · exact hk
    · exact List.mem_of_mem_take hk
  have hDP := (List.mem_filter.mp hD)
  have injL : ∀ x ∈ P.filter (·.1.kind == .def), x.2 = l → x = (o, l) :=
    fun x hx he => inj_of_nodup_map hDl hx hD he
  have injV : ∀ x ∈ P.filter (·.1.kind == .def), x.1.vreg = o.vreg → x = (o, l) :=
    fun x hx he => inj_of_nodup_map hDv hx hD he
  have subE := atPos_sublist P .early
  have subL := atPos_sublist P .late
  have hnc : ∀ r ∈ i.clobbers, Loc.reg r ≠ l := hnotclob _ hDP.1 (by simpa using hDP.2)
  have hA3 : (defineAll (clobberAll (defineAll a (atPos P .def .early)) i.clobbers)
      (atPos P .def .late)).get l = [.vreg o.vreg] := by
    have bnd : ∀ (b : AState), 64 ≤ b.size → ∀ ds : List (Operand × Loc), ds.Sublist P →
        ∀ x ∈ ds, ∃ i, x.2.index = some i ∧ i < b.size := by
      intro b hb ds hs x hx
      obtain ⟨i, h1, h2⟩ := hreg x (hs.subset hx)
      exact ⟨i, h1, by omega⟩
    rcases hpos : o.pos
    · have hE : (o, l) ∈ atPos P .def .early := mem_atPos.mpr ⟨hDP.1, by simpa using hDP.2, hpos⟩
      have h1 := defineAll_get_mem (atPos P .def .early) a ((subE.map _).nodup hDl)
        ((subE.map _).nodup hDv) (bnd a hsz _ (subE.trans List.filter_sublist)) (o, l) hE
      have h2 := clobberAll_get_other i.clobbers (defineAll a (atPos P .def .early)) l hnc
      rw [defineAll_get_other, h2, h1]
      · simp only [List.filter_cons, List.filter_nil]
        have : ((atPos P .def .late).any fun x => Sym.vreg o.vreg == .vreg x.1.vreg) = false := by
          rw [Bool.eq_false_iff]
          intro hany
          obtain ⟨x, hx, hxe⟩ := List.any_eq_true.mp hany
          simp at hxe
          have := injV x (subL.subset hx) hxe.symm
          rw [this] at hx
          rw [(mem_atPos.mp hx).2.2] at hpos; cases hpos
        simp [this]
      · intro x hx he
        have := injL x (subL.subset hx) he
        rw [this] at hx
        rw [(mem_atPos.mp hx).2.2] at hpos; cases hpos
    · have hLt : (o, l) ∈ atPos P .def .late := mem_atPos.mpr ⟨hDP.1, by simpa using hDP.2, hpos⟩
      have hb : 64 ≤ (clobberAll (defineAll a (atPos P .def .early)) i.clobbers).size := by
        rw [size_clobberAll, size_defineAll]; exact hsz
      exact defineAll_get_mem _ _ ((subL.map _).nodup hDl) ((subL.map _).nodup hDv)
        (bnd _ hb _ (subL.trans List.filter_sublist)) (o, l) hLt
  unfold transferOp
  split
  · exact hA3
  · rename_i n hn
    rw [forgetDefs_get, hA3]
    simp only [List.filter_cons, List.filter_nil]
    have : (((P.filter (·.1.kind == .def)).drop n).any fun p =>
        p.1.kind == .def && Sym.vreg o.vreg == .vreg p.1.vreg) = false := by
      rw [Bool.eq_false_iff]; intro hany
      obtain ⟨x, hx, hxe⟩ := List.any_eq_true.mp hany
      simp at hxe
      have := injV x (List.mem_of_mem_drop hx) hxe.2.symm
      have hnd : (P.filter (·.1.kind == .def)).Nodup :=
        List.Pairwise.of_map _ (fun a b h e => h (e ▸ rfl)) hDv
      have hk' : (o, l) ∈ (P.filter (·.1.kind == .def)).take n := by
        unfold keptPairs at hk; rw [hn] at hk; exact hk
      rw [← List.take_append_drop n (P.filter (·.1.kind == .def))] at hnd
      rw [this] at hx
      exact (List.nodup_append.mp hnd).2.2 _ hk' _ hx rfl
    simp [this]

theorem clobberAll_entry : ∀ (clob : List Reg) (a : AState) (r : Reg),
    Sym.entry r ∈ a.get (.reg r) → Sym.entry r ∈ (clobberAll a clob).get (.reg r)
  | [], _, _, h => h
  | r' :: clob, a, r, h => by
    simp only [clobberAll, List.foldl_cons]
    apply clobberAll_entry clob
    by_cases he : r' = r
    · subst he
      rcases hidx : (Loc.reg r').index with _ | i
      · simp only [AState.put, hidx]; exact h
      · by_cases hlt : i < a.size
        · rw [get_put_self hidx hlt]; simp [h]
        · exfalso
          simp [AState.get, hidx, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega : a.size ≤ i)] at h
    · rw [get_put_ne (fun e => he (by injection e))]
      exact h

/-- The entry value of a callee-saved register survives a transfer that defines nothing there. -/
theorem transferOp_entry {i : MInst} {P : List (Operand × Loc)} {a : AState} {r : Reg}
    (h : Sym.entry r ∈ a.get (.reg r)) (hd : ∀ x ∈ P, x.1.kind = .def → x.2 ≠ .reg r) :
    Sym.entry r ∈ (transferOp i P a).get (.reg r) := by
  have hpos : ∀ p, ∀ x ∈ atPos P .def p, x.2 ≠ .reg r := fun p x hx =>
    hd x (mem_atPos.mp hx).1 (mem_atPos.mp hx).2.1
  have h1 := defineAll_get_other (atPos P .def .early) a (.reg r) (hpos _)
  have hm : Sym.entry r ∈ (defineAll (clobberAll (defineAll a (atPos P .def .early)) i.clobbers)
      (atPos P .def .late)).get (.reg r) := by
    rw [defineAll_get_other _ _ _ (hpos _)]
    simp only [List.mem_filter]
    refine ⟨clobberAll_entry _ _ _ ?_, by simp⟩
    rw [h1]; simp only [List.mem_filter]; exact ⟨h, by simp⟩
  unfold transferOp
  split
  · exact hm
  · rw [forgetDefs_get]; simp only [List.mem_filter]; exact ⟨hm, by simp⟩

/-- A kept index pairs its operand with its location. -/
theorem keptIdx_pair {i : MInst} {os : Array Operand} {allocs : Array Loc} {j : Nat} {o : Operand}
    {l : Loc} (hsz : os.size = allocs.size) (hj : j ∈ keptIdx i os) (ho : os[j]? = some o)
    (hl : allocs[j]? = some l) : (o, l) ∈ keptPairs i (os.zip allocs).toList := by
  let f : Operand × Nat → Operand × Loc := fun x => (x.1, allocs[x.2]?.getD (.reg .sp))
  have hP : (os.zip allocs).toList = os.toList.zipIdx.map f := by
    apply List.ext_getElem
    · simp [hsz]
    · intro n h1 h2
      have hn : n < allocs.size := by simp at h1; omega
      simp [f, Array.getElem?_eq_getElem hn]
  have hD : (os.zip allocs).toList.filter (·.1.kind == .def) =
      (os.toList.zipIdx.filter (·.1.kind == .def)).map f := by
    rw [hP, List.filter_map]; rfl
  have hfj : ∀ x ∈ os.toList.zipIdx, x.2 = j → f x = (o, l) := by
    intro x hx he
    have := List.mem_zipIdx_iff_getElem?.mp hx
    rw [he, Array.getElem?_toList, ho] at this
    rcases x with ⟨xo, xj⟩
    simp only at he this
    subst he
    simp [f, ← Option.some.inj this, hl]
  unfold keptIdx at hj
  unfold keptPairs
  split at hj <;> rename_i hkd <;> simp only [hkd]
  · rw [hD]
    obtain ⟨x, hx, he⟩ := List.mem_map.mp hj
    rw [← hfj x (List.mem_filter.mp hx).1 he]
    exact List.mem_map_of_mem hx
  · rw [hD, ← List.map_take]
    rw [← List.map_take] at hj
    obtain ⟨x, hx, he⟩ := List.mem_map.mp hj
    rw [← hfj x (List.mem_filter.mp (List.mem_of_mem_take hx)).1 he]
    exact List.mem_map_of_mem hx

/-! ## The in-states -/

section
variable {vc : VCode} {c : LinearScan.Ctx} {rf : RFunc} {D : Nat → Nat → Bool}

theorem size_inState (s : Nat) : (inState vc c rf D s).size = 128 + 2 * rf.spillSlots :=
  size_mkState _ _

theorem insOf_get {b : Nat} (hb : b < vc.blocks.size) :
    (insOf vc c rf D)[b]? = some (some (inState vc c rf D b)) := by
  simp [insOf, hb]

/-- What the in-state of block `s` holds: a live, available vreg in its entry location, the
entry value of a callee-saved register in the register (block 0, or not saved) or in its save
slot (other blocks, saved). -/
theorem mem_inState {s : Nat} {l : Loc} {x : Sym} (h : x ∈ (inState vc c rf D s).get l) :
    LocValid rf l ∧
    ((∃ v, x = .vreg v ∧ v < c.fn.nv ∧ c.pl.cov v (pos (c.fn.start.getD s 0) 0) = true ∧
        (D s v || (entryStored vc c.fn.succs c.fn.preds s).contains v) = true ∧
        entryLoc vc c s v = l) ∨
      ∃ r, x = .entry r ∧ ((l = .reg r ∧ r ∈ calleeSaved ∧ (s = 0 ∨ r ∉ rf.saved)) ∨
        (l = .save r ∧ s ≠ 0 ∧ r ∈ rf.saved))) := by
  obtain ⟨hm, i, hi, hlt⟩ := mem_get_mkState h
  refine ⟨⟨i, hi, hlt⟩, ?_⟩
  simp only [inContent, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
    Bool.and_eq_true, beq_iff_eq] at hm
  rcases hm with ⟨v, ⟨hv, ⟨hc, hd⟩, he⟩, rfl⟩ | hm
  · exact .inl ⟨v, rfl, hv, hc, hd, he⟩
  · right
    cases l with
    | reg r =>
      dsimp only at hm
      split at hm
      · next hc => exact ⟨r, List.mem_singleton.mp hm, .inl ⟨rfl, hc.1, hc.2⟩⟩
      · cases hm
    | save r =>
      dsimp only at hm
      split at hm
      · next hc => exact ⟨r, List.mem_singleton.mp hm, .inr ⟨rfl, hc.1, hc.2⟩⟩
      · cases hm
    | stack _ _ => cases hm

/-- A live, available vreg is in its entry location in the in-state (if that location is
represented). -/
theorem inState_vreg {s v : Nat} (hv : v < c.fn.nv)
    (hc : c.pl.cov v (pos (c.fn.start.getD s 0) 0) = true)
    (hd : (D s v || (entryStored vc c.fn.succs c.fn.preds s).contains v) = true)
    (hl : LocValid rf (entryLoc vc c s v)) :
    Sym.vreg v ∈ (inState vc c rf D s).get (entryLoc vc c s v) := by
  obtain ⟨i, hi, hlt⟩ := hl
  rw [inState, get_mkState hi hlt]
  simp only [inContent, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
    Bool.and_eq_true, beq_iff_eq]
  exact .inl ⟨v, ⟨hv, ⟨hc, hd⟩, rfl⟩, rfl⟩

/-- The entry value of a callee-saved register is in the register in the in-state of block 0
and, if the register is not saved, of every block. -/
theorem inState_entryReg {s : Nat} {r : Reg} (hr : r ∈ calleeSaved) (h : s = 0 ∨ r ∉ rf.saved) :
    Sym.entry r ∈ (inState vc c rf D s).get (.reg r) := by
  obtain ⟨i, hi, hlt⟩ := reg_index (calleeSaved_ok r hr).1
  rw [inState, get_mkState hi (by omega)]
  simp only [inContent, List.mem_append]
  exact .inr (by split <;> simp_all)

/-- The entry value of a saved callee-saved register is in its save slot in the in-state of
every block but 0. -/
theorem inState_entrySave {s : Nat} {r : Reg} (hr : r ∈ calleeSaved) (hs : s ≠ 0)
    (h : r ∈ rf.saved) : Sym.entry r ∈ (inState vc c rf D s).get (.save r) := by
  obtain ⟨i, hi, hlt⟩ := save_index hr
  rw [inState, get_mkState hi (by omega)]
  simp only [inContent, List.mem_append]
  exact .inr (by split <;> simp_all)

/-- The entry location of `v` is its location unless an entry pair of `s` (a def of the only
predecessor's terminator) carries `v` in a fixed register. -/
theorem entryLoc_cases (s v : Nat) :
    entryLoc vc c s v = c.loc v ∨ ∃ y ∈ entryPairs vc c.fn.succs c.fn.preds s, y.1.vreg = v ∧
      ∃ p, y.1.con = .fixed p ∧ entryLoc vc c s v = .reg p := by
  unfold entryLoc
  cases hf : ((entryPairs vc c.fn.succs c.fn.preds s).map (·.1)).find? (·.vreg == v) with
  | none => exact .inl rfl
  | some o =>
    have hv : o.vreg = v := by simpa using List.find?_some hf
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
    simp only
    cases hcon : y.1.con with
    | fixed p => exact .inr ⟨y, hy, hv, p, hcon, rfl⟩
    | _ => exact .inl rfl

theorem entryLoc_none {s v : Nat} (h : ∀ y ∈ entryPairs vc c.fn.succs c.fn.preds s, y.1.vreg ≠ v) :
    entryLoc vc c s v = c.loc v := by
  rcases entryLoc_cases (vc := vc) (c := c) s v with h' | ⟨y, hy, hv, -⟩
  · exact h'
  · exact absurd hv (h y hy)

end

section
variable {vc : VCode} {c : LinearScan.Ctx} {rf : RFunc} {D : Nat → Nat → Bool}
  (H : Hyps vc c rf D)
include H

/-- Within a block, `Post` gives `Good` at the next instruction. -/
theorem good_succ {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {k : Nat}
    (hk : k + 1 < vb.insts.size) {i : MInst} (hi : vb.insts[k]? = some i) {os : Array Operand}
    (hos : i.operands = .ok os) {A : Nat → Bool} {a : AState}
    (hpost : Post c rf (c.fn.start.getD b 0 + k) i os A a) :
    Good c rf (availInst i A) (pos (c.fn.start.getD b 0 + k + 1) 0) a := by
  have hf := H.fn
  have hpf := H.plan
  refine ⟨hpost.size, fun v hv hcov hA hloc => ?_, hpost.callee⟩
  have hp5 : pos (c.fn.start.getD b 0 + k + 1) 0 = pos (c.fn.start.getD b 0 + k) 0 + 5 := by
    unfold pos; omega
  rw [hp5] at hcov
  rw [availInst_eq hos] at hA
  cases hd : isDefOf os v
  · rw [hd] at hA
    simp only [Bool.false_eq_true, ite_false] at hA
    have hI := covI_of_nobirth hpf hv hcov (by omega) (nobirth_inside hf hvb hi hos hk hd)
    refine hpost.thru v hv (covI_mono hI (Nat.le_refl _) (by unfold pos; omega)) hA (fun o ho hk' he => ?_) hloc
    have := isDefOf_of ho hk'
    rw [he, hd] at this
    cases this
  · rw [hd] at hA
    simp only [ite_true, storedDefs_eq] at hA
    split at hA
    · simp at hA
    rename_i hnt
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp hA)
    obtain ⟨j, hj, hjk⟩ := keptOps_idx ho
    have hdef := (mem_keptOps ho).2
    have h4 : c.pl.cov o.vreg (pos (c.fn.start.getD b 0 + k) 4) = true := by
      have := covI_of_nobirth hpf hv hcov (q := pos (c.fn.start.getD b 0 + k) 4)
        (by unfold pos; omega) (fun s h1 h2 => by
          have : s = pos (c.fn.start.getD b 0 + k) 0 + 5 := by unfold pos at *; omega
          subst this; exact nobirth_next hf hvb hk _)
      exact cov_of_covI this (Nat.le_refl _) (by unfold pos; omega)
    refine hpost.stored j o hj hdef ?_
    simp only [LinearScan.Ctx.store, hnt, Bool.not_false, Bool.true_and, Bool.and_eq_true,
      List.contains_iff_mem]
    exact ⟨hjk, h4⟩

end

end Backend.Proof.LS
