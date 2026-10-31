import FV.Backend.Proof.SpillCtlPipe
import FV.Backend.Proof.SpillCtlFormsT
import FV.Backend.Proof.LowerLoopCtxT
import FV.Backend.Proof.LowerDecide
import FV.Compile.StoreTyped
import FV.Compile.SelectTyped

/-!
# Control shapes of the typed lowering (S11 #35)

The typed lowering emits the control forms of the integer one (`CtlShape`) and, from
`gen_return`, a `Rets` whose pairs have either class (`argPairsC`): an int vreg in x0..x7, an
`f32`/`f64` vreg in v0..v7 (`retRegsC`).

* `CtlShapeT N m`: `CtlShape N m`, or such a `Rets` of distinct return registers;
  `spillInstOk_of_ctlShapeT`: it meets `SpillInstOk` (`spillInstOk_retsC`).
* `CtlSinceT`: `CtlSince` with `CtlShapeT`.
* `rets_shapeT`: `gen_return`'s `Rets` of vregs has its shape.
* `IselCtlHypT`: `IselCtlHyp` over the typed scope (`LowerScopeT`, with the typed coverage
  analysis' input conditions: `dominatedB`, class-checked `store`s and `select`s), with
  `CtlSinceT`; its terminator clause is restricted to `f`'s terminators.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Driver

/-- **The control shapes of the typed lowering.** A `Rets` pins vregs to distinct registers of
their classes: x0..x7/v0..v7 for the declared returns, x8 for an `sret` function's struct
pointer (`ArgRegC`; #587, Cranelift's `gen_return` returns `sret_reg` in x8). -/
def CtlShapeT (N : Nat) (m : MInst) : Prop :=
  CtlShape N m ∨ ∃ ns : List (Nat × RegClass × Reg), m = .rets (argPairsC ns) ∧
    (∀ q ∈ ns, ArgRegC q.2.1 q.2.2) ∧ (ns.map (·.2.2)).Nodup

theorem CtlShape.toT {N : Nat} {m : MInst} (h : CtlShape N m) : CtlShapeT N m := .inl h

/-- **Every typed control shape meets `SpillInstOk`.** -/
theorem spillInstOk_of_ctlShapeT {N : Nat} {m : MInst} (h : CtlShapeT N m) : SpillInstOk m := by
  rcases h with h | ⟨ns, rfl, hr, hnd⟩
  · exact spillInstOk_of_ctlShape h
  · exact spillInstOk_retsC hr hnd

/-- Every control form emitted from `s` to `s'` has its typed shape. -/
def CtlSinceT (N : Nat) (s s' : LState) : Prop :=
  ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ ∀ m ∈ ms, m.isCtl = true → CtlShapeT N m

theorem CtlSince.toT {N : Nat} {s s' : LState} (h : CtlSince N s s') : CtlSinceT N s s' :=
  let ⟨ms, h1, h2⟩ := h
  ⟨ms, h1, fun m hm hc => (h2 m hm hc).toT⟩

/-! ## `gen_return`'s `Rets` -/

/-- The registers `retRegsC` assigns from `x nx`/`v nv` on: distinct return registers of their
classes, at or above `x nx`/`v nv`. -/
theorem retRegsC_pairs : ∀ (rs : List Reg) (nx nv : Nat) (ps : List Reg),
    (∀ r ∈ rs, ∃ n c, r = .vreg n c) → retRegsC (rs.map Reg.homeCls) nx nv = some ps →
    ∃ ns : List (Nat × RegClass × Reg), rs.zip ps = argPairsC ns ∧
      (∀ q ∈ ns, RetRegC q.2.1 q.2.2 ∧ (∀ k, q.2.2 = .x k → nx ≤ k) ∧ (∀ k, q.2.2 = .v k → nv ≤ k)) ∧
      (ns.map (·.2.2)).Nodup
  | [], _, _, ps, _, h => by
    simp only [List.map_nil, retRegsC, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, by simp, List.nodup_nil⟩
  | r :: rs, nx, nv, ps, hv, h => by
    obtain ⟨n, c, rfl⟩ := hv r List.mem_cons_self
    have hv' : ∀ r ∈ rs, ∃ n c, r = .vreg n c := fun r hr => hv r (List.mem_cons_of_mem _ hr)
    cases c with
    | int =>
      simp only [List.map_cons, Reg.homeCls, retRegsC] at h
      split at h
      · rename_i hx
        obtain ⟨ps', hps', rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨ns, hz, hns, hnd⟩ := retRegsC_pairs rs (nx + 1) nv ps' hv' hps'
        refine ⟨(n, .int, .x nx) :: ns, by simp [argPairsC, hz], ?_, ?_⟩
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨.inl ⟨rfl, nx, hx, rfl⟩, fun k hk => by cases hk; exact Nat.le_refl _,
              fun k hk => by cases hk⟩
          · obtain ⟨h1, h2, h3⟩ := hns q hq
            exact ⟨h1, fun k hk => Nat.le_of_succ_le (h2 k hk), h3⟩
        · refine List.nodup_cons.mpr ⟨fun hm => ?_, hnd⟩
          obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
          have := (hns q hq).2.1 nx he
          omega
      · cases h
    | float =>
      simp only [List.map_cons, Reg.homeCls, retRegsC] at h
      split at h
      · rename_i hx
        obtain ⟨ps', hps', rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨ns, hz, hns, hnd⟩ := retRegsC_pairs rs nx (nv + 1) ps' hv' hps'
        refine ⟨(n, .float, .v nv) :: ns, by simp [argPairsC, hz], ?_, ?_⟩
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨.inr ⟨rfl, nv, hx, rfl⟩, fun k hk => (by cases hk),
              fun k hk => (by cases hk; exact Nat.le_refl _)⟩
          · obtain ⟨h1, h2, h3⟩ := hns q hq
            exact ⟨h1, h2, fun k hk => Nat.le_of_succ_le (h3 k hk)⟩
        · refine List.nodup_cons.mpr ⟨fun hm => ?_, hnd⟩
          obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
          have := (hns q hq).2.2 nv he
          omega
      · cases h

/-- **`gen_return`'s `Rets` of vregs** has its typed control shape. -/
theorem rets_shapeT (N : Nat) {rs ps : List Reg} (hv : ∀ r ∈ rs, ∃ n c, r = .vreg n c)
    (hps : retRegsC (rs.map Reg.homeCls) 0 0 = some ps) : CtlShapeT N (.rets (rs.zip ps)) := by
  obtain ⟨ns, hz, hns, hnd⟩ := retRegsC_pairs rs 0 0 ps hv hps
  exact .inr ⟨ns, by rw [hz], fun q hq => retRegC_argRegC (hns q hq).1, hnd⟩

/-! ## The typed ISLE inversion -/

/-- **`IselCtlHyp` over the typed scope**: every ISLE run of the driver, on `LowerScopeT`
input with class-checked `store`s and `select`s and an integer-classed `sret` struct pointer
(the value `gen_return` returns in x8; the entry block's typing `EntryClassOk` gives it,
`sretRet_valClass_int`), emits only control forms of the typed shapes `CtlShapeT`. Its
terminator clause is restricted to `f`'s terminators. -/
def IselCtlHypT : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState),
    dominatedB f = true → LowerScopeT f → Compile.storeTypedB f = true →
    Compile.selectTypedB f = true → AbiSigsOk f → buildCtx f = .ok (ctx, ranges, st0) →
    (∀ y ∈ sretRet f, valClassOf ctx y = .int) →
    (∀ ii info inst s out s' tr, ctx.insts[ii]? = some info → info.clif = some inst →
      ctx.valDef.size ≤ s.nextVreg →
      runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr) → CtlSinceT ctx.valDef.size s s') ∧
    (∀ ti t data targets s out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → t.isTry = false → (∃ B ∈ f.blocks, B.term = t) →
      termData (abiTerm f t) = .ok data → ctx.valDef.size ≤ s.nextVreg →
      termCallF ctx ti data t targets s = .ok (out, s', tr) → CtlSinceT ctx.valDef.size s s') ∧
    (∀ ti t et data sig items lo trs st1 targets out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → IsTryWith t et → (∃ B ∈ f.blocks, B.term = t) →
      tryCallData f t = .ok data → exnTableOpnd f et = .ok (sig, items) →
      ctx.valDef.size ≤ lo.nextVreg → tryRegsOf sig lo = some (trs, st1) →
      tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (out, s', tr) →
      CtlSinceT ctx.valDef.size { st1 with emitted := #[] } s')

/-- **The typed ISLE inversion of one function** (`IselCtlHypT`'s conclusion for `f`): every ISLE
run of the driver in `buildCtx f`'s context emits only control forms of the typed shapes, when the
`sret` struct pointer `gen_return` returns in x8 has an integer vreg (as in `IselCtlHypT`). -/
def IselCtlOn (f : Clif.Function) : Prop :=
  ∀ (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState), buildCtx f = .ok (ctx, ranges, st0) →
    (∀ y ∈ sretRet f, valClassOf ctx y = .int) →
    (∀ ii info inst s out s' tr, ctx.insts[ii]? = some info → info.clif = some inst →
      ctx.valDef.size ≤ s.nextVreg →
      runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr) → CtlSinceT ctx.valDef.size s s') ∧
    (∀ ti t data targets s out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → t.isTry = false → (∃ B ∈ f.blocks, B.term = t) →
      termData (abiTerm f t) = .ok data → ctx.valDef.size ≤ s.nextVreg →
      termCallF ctx ti data t targets s = .ok (out, s', tr) → CtlSinceT ctx.valDef.size s s') ∧
    (∀ ti t et data sig items lo trs st1 targets out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → IsTryWith t et → (∃ B ∈ f.blocks, B.term = t) →
      tryCallData f t = .ok data → exnTableOpnd f et = .ok (sig, items) →
      ctx.valDef.size ≤ lo.nextVreg → tryRegsOf sig lo = some (trs, st1) →
      tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (out, s', tr) →
      CtlSinceT ctx.valDef.size { st1 with emitted := #[] } s')

/-- `IselCtlHypT` gives `IselCtlOn` of a typed-scope function. -/
theorem IselCtlHypT.on (hI : IselCtlHypT) {f : Clif.Function} (hdom : dominatedB f = true)
    (hs : LowerScopeT f) (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (ha : AbiSigsOk f) : IselCtlOn f :=
  fun ctx ranges st0 hb => hI f ctx ranges st0 hdom hs hst hsel ha hb

end Backend.Proof.Spill
