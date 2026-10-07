import FV.Backend.Proof.DefRuns

/-!
# Definite assignment of `lowerFunction`'s VCode: instruction and availability facts

The pieces `DefAssemble` assembles: `DefBy` (some instruction of a list defines a vreg, or it is
defined at the list's start; `defAt` is `DefBy` on a prefix of the block), the defs of the
renamed instructions and of the driver's own instructions (the entry block's `Args` and
parameter loads, a `try_call`'s `tryCall`), and the CLIF values a run reaches (`Reach`), which
are available (`Dominated`) where the run's instruction stands.
-/

namespace Backend.Proof.DefRun

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Kill

/-! ## Definedness after a list of instructions -/

/-- `v` is defined after the instructions `l`, from definedness `A` before them. -/
def DefBy (A : Nat → Bool) (l : List MInst) (v : Nat) : Prop :=
  (∃ m ∈ l, isDefV m v = true) ∨ A v = true

theorem DefBy.mono {A : Nat → Bool} {l l' : List MInst} {v : Nat} (h : DefBy A l v)
    (hs : ∀ m ∈ l, m ∈ l') : DefBy A l' v :=
  h.imp_left fun ⟨m, hm, hd⟩ => ⟨m, hs m hm, hd⟩

theorem defAt_of_defBy {insts : Array MInst} {A : Nat → Bool} {k v : Nat}
    (h : DefBy A (insts.toList.take k) v) : defAt insts A k v = true := by
  rw [defAt_eq]
  rcases h with ⟨m, hm, hd⟩ | h
  · rw [Bool.or_eq_true, List.any_eq_true]
    exact .inl ⟨m, hm, hd⟩
  · rw [h, Bool.or_true]

theorem isDefV_iff {m : MInst} {v : Nat} : isDefV m v = true ↔ v ∈ defVregs m := by
  unfold isDefV defVregs
  cases m.operands with
  | error e => simp
  | ok ops =>
    simp only [List.any_eq_true, List.mem_map, List.mem_filter, beq_iff_eq]

/-- A renamed instruction defines the renamed defs. -/
theorem defVregs_mapRegs {g : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming g gn) {m : MInst}
    {v : Nat} (h : v ∈ defVregs m) : gn v ∈ defVregs (m.mapRegs g) := by
  unfold defVregs at h ⊢
  rw [operands_mapRegs hg]
  cases hm : m.operands with
  | error e => rw [hm] at h; cases h
  | ok ops =>
    rw [hm] at h
    simp only [Except.map]
    rw [asm_filter_rn]
    exact List.mem_map_of_mem h

/-- A use operand's vreg is a use vreg. -/
theorem mem_useVregs {i : MInst} {ops : Array Operand} (h : i.operands = .ok ops) {o : Operand}
    (ho : o ∈ ops.toList) (hk : o.kind = .use) : o.vreg ∈ useVregs i := by
  unfold useVregs
  rw [h]
  exact List.mem_map_of_mem (List.mem_filter.mpr ⟨ho, by simp [hk]⟩)

/-! ## The driver's own instructions -/

theorem isDefV_load (op : LoadOp) (n : Nat) (o : Int) (fl : Clif.MemFlags) :
    isDefV (.load op (.vreg n .int) (.fpOffset o) fl) n = true := by
  unfold isDefV
  obtain ⟨k, p, c, h, hk⟩ : ∃ k p c, (MInst.load op (.vreg n .int) (.fpOffset o) fl).operands =
      .ok #[⟨n, .int, k, p, c⟩] ∧ k = .def := ⟨_, _, _, rfl, rfl⟩
  rw [h]; subst hk; simp

theorem mapM_fixedDef_vregs : ∀ (l : List (Reg × Reg)) (s : Array Operand),
    (∀ q ∈ l, ∃ n c, q.1 = .vreg n c) →
    ∃ a s', (l.mapM (fun (x : Reg × Reg) => do
        let r ← collectOp (OpSpec.fixedDef x.2) x.1; pure (r, x.2))).run s = .ok (a, s') ∧
      (∀ o ∈ s.toList, o ∈ s'.toList) ∧
      ∀ q ∈ l, ∀ n c, q.1 = .vreg n c → ∃ o ∈ s'.toList, o.kind = .def ∧ o.vreg = n
  | [], s, _ => ⟨[], s, rfl, fun _ h => h, fun _ h => by cases h⟩
  | q :: l, s, hv => by
    obtain ⟨n0, c0, hq⟩ := hv q List.mem_cons_self
    obtain ⟨a, s', hrun, hkeep, hdef⟩ := mapM_fixedDef_vregs l
      (s.push ⟨n0, c0, (OpSpec.fixedDef q.2).kind, (OpSpec.fixedDef q.2).pos,
        (OpSpec.fixedDef q.2).con⟩)
      (fun q' hq' => hv q' (List.mem_cons_of_mem _ hq'))
    have h1 : (collectOp (OpSpec.fixedDef q.2) q.1).run s = .ok (q.1, s.push ⟨n0, c0,
        (OpSpec.fixedDef q.2).kind, (OpSpec.fixedDef q.2).pos, (OpSpec.fixedDef q.2).con⟩) := by
      rw [hq]; rfl
    refine ⟨(q.1, q.2) :: a, s', ?_, fun o ho => hkeep o (by simp [ho]), fun q' hq' n c hn => ?_⟩
    · simp only [List.mapM_cons, StateT.run_bind]
      rw [h1, Driver.except_ok_bind, StateT.run_pure, Driver.except_pure, Driver.except_ok_bind,
        hrun, Driver.except_ok_bind]
      rfl
    · rcases List.mem_cons.mp hq' with rfl | hq'
      · rw [hq] at hn
        cases hn
        exact ⟨⟨_, c0, (OpSpec.fixedDef q'.2).kind, (OpSpec.fixedDef q'.2).pos,
          (OpSpec.fixedDef q'.2).con⟩, hkeep _ (by simp), rfl, rfl⟩
      · exact hdef q' hq' n c hn

/-- An `Args` defines the vregs of its pairs. -/
theorem isDefV_args {ps : List (Reg × Reg)} (hv : ∀ q ∈ ps, ∃ n c, q.1 = .vreg n c) {n : Nat}
    {c : RegClass} {p : Reg} (hq : (Reg.vreg n c, p) ∈ ps) : isDefV (.args ps) n = true := by
  obtain ⟨a, s', hrun, -, hdef⟩ := mapM_fixedDef_vregs ps #[] hv
  obtain ⟨o, ho, hk, hn⟩ := hdef _ hq n c rfl
  unfold isDefV
  rw [operands_eq]
  simp only [MInst.visitOperands, StateT.run_bind]
  rw [hrun, Driver.except_ok_bind, StateT.run_pure, Driver.except_pure, Driver.except_ok_bind]
  simp only [Driver.except_pure]
  rw [List.any_eq_true]
  exact ⟨o, List.mem_filter.mpr ⟨ho, by simp [hk]⟩, by simp [hn]⟩

/-- A `tryCall` whose call has defs `callDefs D` defines `D`'s vregs. -/
theorem isDefV_tryCall {c : CallInfo} {ti : TryInfo} {D : List (Reg × Nat)}
    (hD : c.defs = callDefs D) {ops : Array Operand}
    (hops : (MInst.tryCall c ti).operands = .ok ops) {q : Reg × Nat} (hq : q ∈ D) :
    q.2 ∈ defVregs (.tryCall c ti) := by
  unfold defVregs
  rw [hops]
  rw [operands_tryCall_call] at hops
  simp only
  rw [asm_call_defs hD hops, asm_callDefOps_vregs]
  exact List.mem_map_of_mem hq

/-! ## Available values -/

section Avail
variable {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
  (hd : Dominated f) (hb : buildCtx f = .ok (ctx, ranges, st0))
include hd hb

/-- **The values a run reaches from available values are available.** -/
theorem reach_avail {bi j : Nat} {S : List Nat}
    (hS : ∀ y ∈ S, y ∈ availOf f (availIn f ctx) bi j) {y : Nat} (h : Reach ctx S y) :
    y ∈ availOf f (availIn f ctx) bi j := by
  induction h with
  | seed hy => exact hS _ hy
  | dep _ hd' hi hc hy ih => exact avail_step hd hb ih hd' hi hc hy

end Avail

/-- At the block's start: a parameter or an entry value. -/
theorem avail_zero {f : Clif.Function} {In : Array (List Clif.ValueId)} {bi : Nat} {B : Clif.Block}
    (hB : f.blocks[bi]? = some B) {x : Nat} (h : x ∈ availOf f In bi 0) :
    x ∈ B.params.map (·.1) ∨ x ∈ In.getD bi [] := by
  rcases ((mem_av hB).mp h).1 with h | h | ⟨k, s, hk, -⟩
  · exact .inl h
  · exact .inr h
  · omega

/-- After statement `j`: available before it, or one of its results. -/
theorem avail_succ {f : Clif.Function} {In : Array (List Clif.ValueId)} {bi : Nat} {B : Clif.Block}
    (hB : f.blocks[bi]? = some B) {j : Nat} {stm : Clif.Stmt} (hs : B.body[j]? = some stm) {x : Nat}
    (h : x ∈ availOf f In bi (j + 1)) : x ∈ stm.results ∨ x ∈ availOf f In bi j := by
  by_cases hx : x ∈ stm.results
  · exact .inl hx
  · right
    obtain ⟨hm, hn⟩ := (mem_av hB).mp h
    refine (mem_av hB).mpr ⟨?_, fun ⟨k, s, hk, hs', hxk⟩ => ?_⟩
    · rcases hm with h | h | ⟨k, s, hk, hs', hxk⟩
      · exact .inl h
      · exact .inr (.inl h)
      · by_cases hkj : k = j
        · subst hkj; rw [hs] at hs'; cases hs'; exact absurd hxk hx
        · exact .inr (.inr ⟨k, s, by omega, hs', hxk⟩)
    · by_cases hkj : k = j
      · subst hkj; rw [hs] at hs'; cases hs'; exact hx hxk
      · exact hn ⟨k, s, by omega, hs', hxk⟩

/-- A value available at the entry of a successor `tl` of block `bi` is available at `bi`'s end. -/
theorem avail_out {f : Clif.Function} {ctx : Ctx} {bi tl : Nat} {B : Clif.Block}
    (hB : f.blocks[bi]? = some B) (htl : tl ∈ succIdx f bi) {x : Nat}
    (hx : x ∈ (availIn f ctx).getD tl []) : x ∈ availOf f (availIn f ctx) bi B.body.length := by
  refine (mem_av hB).mpr ⟨?_, fun ⟨k, s, hk, hs, _⟩ => ?_⟩
  rotate_left
  · have := (List.getElem?_eq_some_iff.mp hs).1; omega
  rcases (inFix_fixOk (gn := id)).out tl x hx bi htl with h | h | h
  · rw [parsOf_of hB] at h; exact .inl h
  · obtain ⟨B', k, s, hB', hs, hxs⟩ := mem_defsOf.mp h
    rw [hB] at hB'; cases hB'
    exact .inr (.inr ⟨k, s, (List.getElem?_eq_some_iff.mp hs).1, hs, hxs⟩)
  · exact .inr (.inl h)

/-- A parameter is available everywhere in its block. -/
theorem avail_par {f : Clif.Function} {In : Array (List Clif.ValueId)} (hssa : (valueDefs f).Nodup)
    {bi : Nat} {B : Clif.Block} (hB : f.blocks[bi]? = some B) {j x : Nat}
    (hx : x ∈ B.params.map (·.1)) : x ∈ availOf f In bi j :=
  (mem_av hB).mpr ⟨.inl hx, fun ⟨_, _, _, hs, hxs⟩ => par_not_res hssa hB hx hB hs hxs⟩

/-! ## The alias renaming -/

section Alias
variable {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
  {bl : List BLow} (hd : Dominated f) (hs : LowerScope f) (hb : buildCtx f = .ok (ctx, ranges, st0))
  (hlb : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
    some bl)
include hd hs hb hlb

/-- **The renaming is constant along an alias.** -/
theorem asmG_alias {p : Nat × Nat} (hp : p ∈ aliasOf f bl) : asmG f bl p.1 = asmG f bl p.2 := by
  obtain ⟨hu, hk, hwf⟩ := alias_facts hd hs hb hlb
  have e : ∀ n, asmG f bl n = gnAt (gnTable st0.nextVreg (aliasOf f bl)) n := by
    intro n
    have := congrFun (resolve_eq hu hk hwf) (.vreg n .int)
    rw [resolve_vreg] at this
    simpa [renOf] using this
  rw [e, e]
  exact gn_step hu hk hwf p hp

omit hs hb hlb in
/-- A parameter is not renamed. -/
theorem asmG_par {bi : Nat} {B : Clif.Block} (hB : f.blocks[bi]? = some B) {x : Nat}
    (hx : x ∈ B.params.map (·.1)) : asmG f bl x = x := by
  refine resolve_fix (aliasOf f bl) (fun o hmo => ?_)
  obtain ⟨bi', B', L, j, stm, sl, hB', -, hs', -, hr, -⟩ := mem_aliasOf hmo
  exact par_not_res hd.ssa hB hx hB' hs' hr

end Alias

end Backend.Proof.DefRun
