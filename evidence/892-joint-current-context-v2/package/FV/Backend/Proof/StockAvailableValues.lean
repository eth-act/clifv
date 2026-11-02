import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.LowerCertBase

/-! Guard the live-value relation at each source statement boundary. A frame can
retain stale values from an earlier loop iteration; these need not be held before
their current definition executes. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program

/-- Passing a statement adds only its results to source availability. -/
theorem available_before_of_after_not_result {f : Clif.Function}
    {In : Array (List Clif.ValueId)} {bi j y : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (after : y ∈ availOf f In bi (j + 1)) (other : y ∉ stm.results) :
    y ∈ availOf f In bi j := by
  obtain ⟨present, future⟩ := (mem_av block).mp after
  refine (mem_av block).mpr ⟨?_, ?_⟩
  · rcases present with param | entry | ⟨k, s, earlier, lookup, member⟩
    · exact Or.inl param
    · exact Or.inr (Or.inl entry)
    · by_cases equal : k = j
      · subst k
        have same := Option.some.inj (lookup.symm.trans statement)
        subst s
        exact False.elim (other member)
      · exact Or.inr (Or.inr ⟨k, s, by omega, lookup, member⟩)
  · intro ⟨k, s, later, lookup, member⟩
    by_cases equal : k = j
    · subst k
      have same := Option.some.inj (lookup.symm.trans statement)
      subst s
      exact other member
    · exact future ⟨k, s, by omega, lookup, member⟩

/-- The new result need not have been held before execution, even when its old
source-frame slot is populated. Other required values come from the old set. -/
theorem ValuesHeld.resolvedResult_change_needed {before after : Nat → Prop} {ctx : Ctx}
    {fr : Clif.Frame} {ρ ρ' : Nat → CV} {gn : Nat → Nat} {x n d lo hi : Nat}
    {v : Clif.Val} {ms : List MInst} {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (held : ValuesHeld before ctx fr (fun k => ρ (gn k)))
    (previous : ∀ y, after y → y ≠ x → before y)
    (mapped : ctx.valueReg? x = some (.vreg n .int)) (resolved : gn n = d)
    (value : VHolds v (ρ' d))
    (outside : ∀ y m, after y → y ≠ x → ctx.valueReg? y = some (.vreg m .int) →
      (fr.regs y).isSome = true → gn m < lo ∨ hi ≤ gn m)
    (defs : ∀ mi ∈ ms, ∀ e ∈ vdefs mi, lo ≤ e ∧ e < hi)
    (executed : PRun F isem ms ρ ρ') :
    ValuesHeld after ctx (withValue fr x v) (fun k => ρ' (gn k)) := by
  intro y required val lookup
  by_cases equal : y = x
  · subst y
    simp only [withValue, eq_self, ite_true] at lookup
    cases lookup
    exact ⟨n, mapped, by change VHolds v (ρ' (gn n)); rw [resolved]; exact value⟩
  · simp only [withValue, ite_eq_right equal] at lookup
    obtain ⟨m, map, old⟩ := held y (previous y required equal) val lookup
    obtain ⟨w', run, _⟩ := executed Arm.ArmState.default
    have preserved : ρ' (gn m) = ρ (gn m) := seqRun_fall_frame (by
      intro mi member defined
      have := outside y m required equal map (by rw [lookup]; rfl)
      have := defs mi member _ defined
      omega) run
    exact ⟨m, map, by change VHolds val (ρ' (gn m)); rw [preserved]; exact old⟩

/-- Before/after availability discharges the changing-set premise. -/
theorem ValuesHeld.resolvedResult_available {f : Clif.Function}
    {In : Array (List Clif.ValueId)} {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    {needed : Nat → Prop} {ctx : Ctx} {fr : Clif.Frame} {ρ ρ' : Nat → CV}
    {gn : Nat → Nat} {x n d lo hi : Nat} {v : Clif.Val} {ms : List MInst}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (results : stm.results = [x])
    (held : ValuesHeld (fun y => needed y ∧ y ∈ availOf f In bi j) ctx fr (fun k => ρ (gn k)))
    (mapped : ctx.valueReg? x = some (.vreg n .int)) (resolved : gn n = d)
    (value : VHolds v (ρ' d))
    (outside : ∀ y m, needed y → y ∈ availOf f In bi j →
      ctx.valueReg? y = some (.vreg m .int) → (fr.regs y).isSome = true →
      gn m < lo ∨ hi ≤ gn m)
    (defs : ∀ mi ∈ ms, ∀ e ∈ vdefs mi, lo ≤ e ∧ e < hi)
    (executed : PRun F isem ms ρ ρ') :
    ValuesHeld (fun y => needed y ∧ y ∈ availOf f In bi (j + 1)) ctx
      (withValue fr x v) (fun k => ρ' (gn k)) := by
  have previous : ∀ y, needed y ∧ y ∈ availOf f In bi (j + 1) → y ≠ x →
      needed y ∧ y ∈ availOf f In bi j := by
    intro y required other
    exact ⟨required.1, available_before_of_after_not_result block statement required.2
      (by simpa only [results, List.mem_singleton] using other)⟩
  exact held.resolvedResult_change_needed previous mapped resolved value
    (fun y m required other map hv => outside y m required.1
      (previous y required other).2 map hv) defs executed

private theorem available_alias_renaming (a : Array (Option Nat)) :
    VRenaming (Backend.lowerFunction.resolve a (a.size + 1)) (aliasNum a) := by
  refine ⟨fun n c => resolve_vreg a _ n c, ?_⟩
  intro r hr
  cases r with
  | vreg n c => exact False.elim (hr n c rfl)
  | _ => simp [Backend.lowerFunction.resolve]

private theorem available_alias_fresh {a : Array (Option Nat)} {lo n : Nat}
    (ha : a.size ≤ lo) (hn : lo ≤ n) : aliasNum a n = n := by
  apply chaseF_none
  rw [Array.getElem?_eq_none (by omega)]
  rfl

private theorem available_renamed_defs (a : Array (Option Nat)) (m : MInst) :
    vdefs (m.mapRegs (Backend.lowerFunction.resolve a (a.size + 1))) =
      (vdefs m).map (aliasNum a) := by
  unfold vdefs
  rw [operands_mapRegs (available_alias_renaming a)]
  cases hm : m.operands with
  | error e => rfl
  | ok ops =>
    simp only [Except.map, Array.toList_map]
    rw [filter_map_rn _ Operand.isDef (fun _ => rfl)]
    simp only [List.map_map]
    rfl

/-- Actual constant selection, binding and execution with source availability guards. -/
theorem stock_iconst_available_resolved {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : MappedCtxInv f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hic : info.clif = some inst)
    {cfg : Config} (hc : cfg.checkOverlap = false)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (hR : Refines F isem)
    (hsem : ∀ aliases i, isem (i.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1))) = isem i)
    {m n : Nat} (hm : 2 ≤ m) (hn : 50 ≤ n)
    {st s1 st' : State} {tr tr1 tr' : Array RuleId} {env' : Isle.Interp.Env V} {out : V}
    (hmatch : (matchRule p (Stock.sem ctx) cfg m rule_lower_53 [.inst ii]).run (st, tr) =
      .ok (some env', s1, tr1))
    (heval : (evalExpr p (Stock.sem ctx) cfg n rule_lower_53.rhs env').run (s1, tr1) =
      .ok (some out, st', tr')) {x a : Nat}
    {In : Array (List Clif.ValueId)} {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (results : stm.results = [x])
    (hres : info.results = [x]) (hmap : ctx.valueReg? x = some (.vreg a .int)) :
    ∃ (ty : Clif.Ty) (imm : BitVec ty.width) (ms : List MInst) (d : Nat) (bound : State),
      inst = .iconst ty imm ∧ out = .regsVec [[.vreg d .int]] ∧
      bindResults ctx (info.results.zip [[.vreg d .int]]) st' = .ok (bound, #[]) ∧
      bound = { st' with alias := aliasStep st'.alias (a, d) } ∧
      CodeShape st.base bound.base ms d st.base.nextVreg ∧
      ∀ aliases, aliases.size ≤ st.base.nextVreg → ∀ ρ, ∃ ρ',
        PRun F isem (ms.map (·.mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size + 1)))) ρ ρ' ∧
        VHolds ⟨ty, imm⟩ (ρ' d) ∧
        ∀ (needed : Nat → Prop) (fr : Clif.Frame),
          ValuesHeld (fun y => needed y ∧ y ∈ availOf f In bi j) ctx fr (fun k => ρ (aliasNum aliases k)) →
          aliasNum aliases a = d →
          (∀ y b, needed y → y ∈ availOf f In bi j → ctx.valueReg? y = some (.vreg b .int) →
            (fr.regs y).isSome = true →
              aliasNum aliases b < st.base.nextVreg ∨ bound.base.nextVreg ≤ aliasNum aliases b) →
          ValuesHeld (fun y => needed y ∧ y ∈ availOf f In bi (j + 1)) ctx (withValue fr x ⟨ty, imm⟩)
            (fun k => ρ' (aliasNum aliases k)) := by
  obtain ⟨ty, imm, ms, d, bound, hinst, hout, hb, hbound, hshape, hrun⟩ :=
    stock_iconst_resolved hp hctx hi hic hc hR hsem hm hn hmatch heval hres hmap
  refine ⟨ty, imm, ms, d, bound, hinst, hout, hb, hbound, hshape, ?_⟩
  intro aliases ha ρ
  obtain ⟨ρ', run, value, _⟩ := hrun aliases ha ρ
  have defs : ∀ mi ∈ ms.map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1))),
      ∀ e ∈ vdefs mi, st.base.nextVreg ≤ e ∧ e < bound.base.nextVreg := by
    intro mi member e defined
    obtain ⟨raw, rawMem, rfl⟩ := List.mem_map.mp member
    rw [available_renamed_defs] at defined
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp defined
    rw [available_alias_fresh ha (hshape.defs raw rawMem r hr).1]
    exact hshape.defs raw rawMem r hr
  refine ⟨ρ', run, value, ?_⟩
  intro needed fr held resolved outside
  exact held.resolvedResult_available block statement results hmap resolved value outside defs run

attribute [local semireducible] Isle.Aarch64.program

private def exampleFunction : Clif.Function :=
  (fun {f : Clif.Function} {ctx : Ctx} (_ : MappedCtxInv f ctx) => f)
    buildCtx_mappedInv_witness.2.2.1
private def exampleCtx : Ctx :=
  (fun {f : Clif.Function} {ctx : Ctx} (_ : MappedCtxInv f ctx) => ctx)
    buildCtx_mappedInv_witness.2.2.1
private def exampleBlock : Clif.Block := exampleFunction.blocks[0]!
private def exampleFrame : Clif.Frame := {
  func := exampleFunction
  regs := fun x => if x = 2 then some (.ofInt .i8 77)
    else if x = 7 then some (.ofInt .i64 11) else none
  slots := [], body := exampleBlock.body, term := exampleBlock.term }
private def exampleRegs (n : Nat) : CV := if n = 192 then 11 else 0
private def exampleAliases : Array (Option Nat) := aliasStep #[] (193, 194)
private theorem exampleAliasFacts : exampleAliases.size ≤ 194 ∧
    aliasNum exampleAliases 193 = 194 ∧ aliasNum exampleAliases 192 = 192 := by
  decide +kernel
private theorem exampleBefore : ∀ y, y ∈ availOf exampleFunction #[] 0 0 ↔ y = 7 := by
  intro y
  change y ∈ ([7] : List Nat) ↔ y = 7
  exact List.mem_singleton
private theorem exampleHeld :
    ValuesHeld (fun y => True ∧ y ∈ availOf exampleFunction #[] 0 0)
      exampleCtx exampleFrame (fun k => exampleRegs (aliasNum exampleAliases k)) := by
  intro y required val lookup
  have equal := (exampleBefore y).mp required.2
  subst y
  change some (Clif.Val.ofInt .i64 11) = some val at lookup
  cases lookup
  refine ⟨192, rfl, ?_⟩
  change VHolds (Clif.Val.ofInt .i64 11) (exampleRegs (aliasNum exampleAliases 192))
  rw [exampleAliasFacts.2.2]
  change VHolds (Clif.Val.ofInt .i64 11) 11
  unfold VHolds
  decide +kernel

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A real selected constant replaces stale source value77 with9 without requiring
77 in the machine beforehand. Its source-available parameter stays11. This
inhabits the selection, binding, execution and changing-availability premises. -/
theorem stock_available_values_witness :
    ∃ (ms : List MInst) (ρ' : Nat → CV),
      exampleFrame.regs 2 = some (.ofInt .i8 77) ∧
      (2 : Nat) ∉ availOf exampleFunction #[] 0 0 ∧
      (2 : Nat) ∈ availOf exampleFunction #[] 0 1 ∧
      (7 : Nat) ∈ availOf exampleFunction #[] 0 0 ∧
      ¬ VHolds (.ofInt .i8 77) (exampleRegs (aliasNum exampleAliases 193)) ∧
      PRun (fun _ => True) ispec (ms.map (·.mapRegs
        (Backend.lowerFunction.resolve exampleAliases (exampleAliases.size + 1)))) exampleRegs ρ' ∧
      VHolds (.ofInt .i8 9) (ρ' 194) ∧
      ValuesHeld (fun y => True ∧ y ∈ availOf exampleFunction #[] 0 1) exampleCtx
        (withValue exampleFrame 2 (.ofInt .i8 9)) (fun k => ρ' (aliasNum exampleAliases k)) := by
  have ctx : MappedCtxInv exampleFunction exampleCtx := buildCtx_mappedInv_witness.2.2.1
  have selected : (matchRule program (Stock.sem exampleCtx) {} 2 rule_lower_53 [.inst 0]).run
      (sinkState, #[]) = .ok (some (env2 (.ty (.int 8)) (.int 9)), sinkState, #[]) := by
    rfl
  obtain ⟨next, trace, evaluated⟩ := stock_iconst_rhs_nine_large data_program exampleCtx sinkState
  have refines : Refines (fun _ => True) ispec :=
    fun _ _ _ _ w' _ h => ⟨w', h, SameWorld.refl _ _⟩
  have semantics : ∀ aliases i, ispec (i.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1))) = ispec i := by
    intro aliases i
    funext us w
    exact ispec_mapRegs (available_alias_renaming aliases) us w i
  obtain ⟨ty, imm, ms, d, bound, inst, out, _, _, _, run⟩ :=
    stock_iconst_available_resolved data_program ctx (ii := 0)
      (info := exampleCtx.insts[0]!) (inst := .iconst .i8 9) rfl rfl rfl refines semantics
      (by decide) (by decide) selected evaluated (In := #[]) (bi := 0) (j := 0)
      (b := exampleBlock) (stm := ⟨[2], .iconst .i8 9⟩) rfl rfl rfl rfl rfl
  cases inst
  cases out
  obtain ⟨ρ', executed, value, held⟩ := run exampleAliases exampleAliasFacts.1 exampleRegs
  have held' := held (fun _ => True) exampleFrame exampleHeld exampleAliasFacts.2.1 (by
    intro y m _ available mapped _
    have equal := (exampleBefore y).mp available
    subst y
    change some (Reg.vreg 192 .int) = some (Reg.vreg m .int) at mapped
    cases mapped
    rw [exampleAliasFacts.2.2]
    exact Or.inl (by decide))
  have parameterAfter : (7 : Nat) ∈ availOf exampleFunction #[] 0 1 := by decide +kernel
  have parameterBefore := available_before_of_after_not_result (bi := 0) (j := 0)
    (b := exampleBlock) (stm := ⟨[2], .iconst .i8 9⟩) rfl rfl parameterAfter (by decide)
  exact ⟨ms, ρ', rfl, by rw [exampleBefore]; decide, by decide +kernel, parameterBefore,
    by rw [exampleAliasFacts.2.1]; change ¬ VHolds (.ofInt .i8 77) 0; unfold VHolds; decide +kernel, executed, value, held'⟩

end Backend.Stock.Proof
