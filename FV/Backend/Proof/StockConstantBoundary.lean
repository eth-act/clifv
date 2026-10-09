import FV.Backend.Proof.StockBoundaryValues
import FV.Backend.Proof.StockEmissionSemantics

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 4096

private def withoutResult (fr : Clif.Frame) (x : Nat) : Clif.Frame :=
  { fr with regs := fun y => if y = x then none else fr.regs y }

private theorem after_withoutResult (fr : Clif.Frame) (x : Nat) (v : Clif.Val) :
    withValue (withoutResult fr x) x v = withValue fr x v := by
  change { fr with regs := fun y => if y = x then some v else
    if y = x then none else fr.regs y } = { fr with regs := fun y => if y = x then some v else fr.regs y }
  congr 1
  funext y
  by_cases same : y = x <;> simp [same]

/-- The actual selected constant and binder transfer between source-boundary
need sets. The result being overwritten need not already agree with the machine;
other values needed afterwards must have been available before. The original
same-demand theorem remains available, and no source frame is cleared at runtime. -/
theorem stock_iconst_resolved_boundaries {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (hctx : MappedCtxInv f ctx)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst}
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
        ∀ (before after : Nat → Prop) (fr : Clif.Frame),
          ValuesHeld before ctx fr (fun k => ρ (aliasNum aliases k)) →
          (∀ y, after y → y ≠ x → before y) →
          aliasNum aliases a = d →
          (∀ y b, after y → y ≠ x → ctx.valueReg? y = some (.vreg b .int) →
            (fr.regs y).isSome = true →
              aliasNum aliases b < st.base.nextVreg ∨ bound.base.nextVreg ≤ aliasNum aliases b) →
          ValuesHeld after ctx (withValue fr x ⟨ty, imm⟩)
            (fun k => ρ' (aliasNum aliases k)) := by
  obtain ⟨ty, imm, ms, d, bound, original, output, binding, boundEq, shape, transfer⟩ :=
    stock_iconst_resolved hp hctx hi hic hc hR hsem hm hn hmatch heval hres hmap
  refine ⟨ty, imm, ms, d, bound, original, output, binding, boundEq, shape, ?_⟩
  intro aliases capacity ρ
  obtain ⟨ρ', run, value, install⟩ := transfer aliases capacity ρ
  refine ⟨ρ', run, value, ?_⟩
  intro before after fr held available result outside
  have reduced : ValuesHeld after ctx (withoutResult fr x)
      (fun k => ρ (aliasNum aliases k)) := by
    intro y needed val lookup
    by_cases same : y = x
    · simp [withoutResult, same] at lookup
    · have original : fr.regs y = some val := by simpa [withoutResult, same] using lookup
      exact held y (available y needed same) val original
  have post := install after (withoutResult fr x) reduced result (by
    intro y b needed other mapped present
    exact outside y b needed other mapped (by simpa [withoutResult, other] using present))
  simpa only [after_withoutResult] using post

private def boundaryAliases : Array (Option Nat) := aliasStep #[] (193, 194)
private theorem boundary_capacity : boundaryAliases.size ≤ sinkState.base.nextVreg ∧
    aliasNum boundaryAliases 193 = 194 := by decide
private theorem boundary_refines : Refines (fun _ => True) ispec :=
  fun _ _ _ _ world _ run => ⟨world, run, SameWorld.refl _ _⟩
private theorem boundary_renaming : ∀ aliases i, ispec (i.mapRegs
    (Backend.lowerFunction.resolve aliases (aliases.size + 1))) = ispec i := by
  intro aliases i
  funext us world
  have vren : VRenaming (Backend.lowerFunction.resolve aliases (aliases.size + 1))
      (aliasNum aliases) := by
    refine ⟨fun n c => resolve_vreg aliases _ n c, ?_⟩
    intro r nonvirtual
    cases r with
    | vreg n c => exact False.elim (nonvirtual n c rfl)
    | _ => simp [Backend.lowerFunction.resolve]
  exact ispec_mapRegs vren us world i

/-- Actual exported constant selection and its binder run with a chosen stale
source result. The incoming post-boundary relation is false, but resolved code
establishes the new result without assuming the stale value was held beforehand. -/
theorem stock_iconst_resolved_boundaries_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (info : IInfo) (fr : Clif.Frame)
      (st' bound : State) (tr' : Array RuleId) (ms : List MInst) (ρ' : Nat → CV),
      MappedCtxInv f ctx ∧ ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      fr.regs 2 = some (.ofInt .i8 64) ∧
      ¬ValuesHeld (fun y => y = 2) ctx fr (fun _ => (0 : CV)) ∧
      (matchRule program (Stock.sem ctx) {} 2 rule_lower_53 [.inst 0]).run (sinkState, #[]) =
        .ok (some (env2 (.ty (.int 8)) (.int 9)), sinkState, #[]) ∧
      (evalExpr program (Stock.sem ctx) {} 2003 rule_lower_53.rhs
        (env2 (.ty (.int 8)) (.int 9))).run (sinkState, #[]) =
        .ok (some (.regsVec [[.vreg 194 .int]]), st', tr') ∧
      bindResults ctx (info.results.zip [[.vreg 194 .int]]) st' = .ok (bound, #[]) ∧
      PRun (fun _ => True) ispec (ms.map (·.mapRegs
        (Backend.lowerFunction.resolve boundaryAliases (boundaryAliases.size + 1)))) (fun _ => 0) ρ' ∧
      VHolds (Clif.Val.ofInt .i8 9) (ρ' 194) ∧
      ValuesHeld (fun y => y = 2) ctx (withValue fr 2 (.ofInt .i8 9))
        (fun k => ρ' (aliasNum boundaryAliases k)) := by
  obtain ⟨f, ctx, info, st', tr', hctx, mapped, source, original, results, matched, evaluated, _⟩ :=
    stock_iconst_ok_witness
  let fr : Clif.Frame := {
    func := f, regs := fun y => if y = 2 then some (.ofInt .i8 64) else none,
    slots := [], body := [⟨[2], .iconst .i8 9⟩], term := .ret [2] }
  obtain ⟨ty, imm, ms, d, bound, inst, out, binding, _, _, transfer⟩ :=
    stock_iconst_resolved_boundaries data_program hctx source original rfl
      boundary_refines boundary_renaming (by decide) (by decide) matched evaluated results mapped
  cases out
  cases inst
  obtain ⟨ρ', run, value, install⟩ := transfer boundaryAliases boundary_capacity.1 (fun _ => 0)
  refine ⟨f, ctx, info, fr, st', bound, tr', ms, ρ', hctx, mapped, rfl, ?_, matched,
    evaluated, binding, run, value, ?_⟩
  · intro held
    have impossible := held.read (x := 2) (n := 193) (v := .ofInt .i8 64) rfl rfl mapped
    exact (by unfold VHolds; decide : ¬VHolds (Clif.Val.ofInt .i8 64) (0 : CV)) impossible
  · apply install (fun _ => False) (fun y => y = 2) fr (fun _ impossible => False.elim impossible)
      (fun _ same other => False.elim (other same)) boundary_capacity.2
    intro y b same other
    exact False.elim (other same)

end Backend.Stock.Proof
