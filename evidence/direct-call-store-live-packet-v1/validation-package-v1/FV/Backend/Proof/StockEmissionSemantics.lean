import FV.Backend.Proof.StockScanSemantics
import FV.Backend.Proof.StockConstantRoot

/-! Connect actual selected constant roots and output binding to the forward
source/machine transfer used by backward scan composition. Final alias and
noninterference facts are internal driver invariants, not source restrictions. -/

namespace Backend.Stock.Proof

open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 4096
attribute [local irreducible] Isle.Aarch64.program

/-- The real selected constant path installs precisely one alias in the incoming
array. Matching and RHS evaluation retain the other scheduling fields. -/
theorem stock_iconst_emission_alias {p : Program} (hp : Data p) {ctx : Ctx}
    {ii : Nat} {info : IInfo} (hi : ctx.insts[ii]? = some info)
    {x a d : Nat} (hres : info.results = [x])
    (hmap : ctx.valueReg? x = some (.vreg a .int))
    {cfg : Config} (hc : cfg.checkOverlap = false) {m n : Nat}
    {st matched next : State} {tr tr1 tr2 : Array RuleId} {env : Isle.Interp.Env V}
    (hmatch : (matchRule p (Stock.sem ctx) cfg m rule_lower_53 [.inst ii]).run (st, tr) =
      .ok (some env, matched, tr1))
    (heval : (evalExpr p (Stock.sem ctx) cfg n rule_lower_53.rhs env).run (matched, tr1) =
      .ok (some (.regsVec [[.vreg d .int]]), next, tr2)) {trace : List RuleId}
    (hroot : Stock.runTerm ctx "lower" [.inst ii] st =
      .ok (some (.regsVec [[.vreg d .int]]), next, trace)) :
    ∃ emission, emitInstruction ctx ii st = .ok emission ∧
      emission.state = { st with base := next.base, alias := aliasStep st.alias (a, d) } ∧
      emission.code = next.base.emitted ∧ emission.results = [[.vreg d .int]] := by
  have hfull : next = { st with base := next.base } := by
    rw [stock_iconst_rhs_frame hp ctx hc heval, stock_iconst_match_frame hp ctx hc hmatch]
  let bound : State := { next with alias := aliasStep next.alias (a, d) }
  have hb : bindResults ctx (info.results.zip [[.vreg d .int]]) next = .ok (bound, #[]) := by
    rw [hres]
    exact bindResults_virtual ctx next [(x, a, d)] (by
      intro q hq
      have he := List.mem_singleton.mp hq
      subst q
      exact hmap)
  rw [hres] at hb
  let emission : Emission := ⟨bound, next.base.emitted, [[.vreg d .int]], trace⟩
  have hemit : emitInstruction ctx ii st = .ok emission := by
    have hinfo : ctx.insts[ii]! = info := by simp only [getElem!_def, hi]
    unfold emitInstruction
    rw [hinfo, hroot]
    simp only [bind, Except.bind, hres, List.length_cons, List.length_nil,
      bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false, hb,
      pure, Except.pure, Array.append_empty]
    rfl
  refine ⟨emission, hemit, ?_, rfl, rfl⟩
  change { next with alias := aliasStep next.alias (a, d) } = _
  rw [hfull]

/-- A fresh constant binding gives the actual post-emission array its required
size bound and result resolution. No supplied final resolver is needed here. -/
theorem stock_iconst_emission_alias_fresh {st : State} {emission : Emission}
    {a d lo : Nat} (ha : emission.state.alias = aliasStep st.alias (a, d))
    (hs : st.alias.size ≤ lo) (hkey : a < lo) (hfresh : lo ≤ d) :
    emission.state.alias.size ≤ lo ∧ aliasNum emission.state.alias a = d := by
  have hsize : (aliasStep st.alias (a, d)).size ≤ lo := by
    unfold aliasStep
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    split
    · simp only [Array.size_append, Array.size_replicate]; omega
    · exact hs
  refine ⟨by rw [ha]; exact hsize, ?_⟩
  rw [ha]
  unfold aliasNum
  have htarget : ((aliasStep st.alias (a, d))[d]?).join = none := by
    rw [aliasStep_get]
    simp only [show d ≠ a from by omega, ite_false,
      Array.getElem?_eq_none (by omega : st.alias.size ≤ d), Option.join_none]
  have hsource : ((aliasStep st.alias (a, d))[a]?).join = some d := by
    rw [aliasStep_get]
    simp only [ite_true]
  rw [chaseF, hsource]
  exact chaseF_none htarget _

/-- A selected constant's actual named root and result binder produce the real
emitted fragment, and discharge its forward source/machine transfer. The final
resolver and other live values are supplied by the whole-driver invariant. -/
theorem stock_iconst_emission_fall_refines {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (hctx : MappedCtxInv f ctx)
    {ii block : Nat} {info : IInfo} {inst : Clif.Inst}
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
      .ok (some out, st', tr'))
    {trace : List RuleId}
    (hroot : Stock.runTerm ctx "lower" [.inst ii] st = .ok (some out, st', trace))
    (hempty : st.base.emitted = #[]) {x a : Nat}
    (hres : info.results = [x]) (hmap : ctx.valueReg? x = some (.vreg a .int)) :
    ∃ (ty : Clif.Ty) (imm : BitVec ty.width) (d : Nat) (emission : Emission),
      inst = .iconst ty imm ∧ out = .regsVec [[.vreg d .int]] ∧ emission.results = [[.vreg d .int]] ∧
      emitInstruction ctx ii st = .ok emission ∧
      emission.state.demand = st.demand ∧
      ∀ (aliases : Array (Option Nat)), aliases.size ≤ st.base.nextVreg →
        aliasNum aliases a = d →
        (∀ y b, Demanded st y → y ≠ x → ctx.valueReg? y = some (.vreg b .int) →
          aliasNum aliases b < st.base.nextVreg ∨ emission.state.base.nextVreg ≤ aliasNum aliases b) →
        ∀ (env : Clif.Env) (cp : Clif.Program) (MR : Clif.Mem → Arm.ArmState → Prop),
        (∀ cm w w', SameWorld F w' w → MR cm w → MR cm w') →
        ScanFallRefines (SourceInstResult env cp ctx) isem aliases
          (fun q s ρ w => MR s.2 w ∧ ValuesHeld (Demanded q) ctx s.1
            (fun k => ρ (aliasNum aliases k)))
          ⟨ii, st, emission.scan block ii st⟩ := by
  obtain ⟨ty, imm, ms, d, bound, hinst, hout, hb, hbound, hshape, hrun⟩ :=
    stock_iconst_resolved hp hctx hi hic hc hR hsem hm hn hmatch heval hres hmap
  have hinfo : ctx.insts[ii]! = info := by simp only [getElem!_def, hi]
  let emission : Emission := ⟨bound, ms.toArray, [[.vreg d .int]], trace⟩
  have hcode : bound.base.emitted = ms.toArray := by
    rw [hshape.emitted, hempty, Array.empty_append]
  have hemit : emitInstruction ctx ii st = .ok emission := by
    unfold emitInstruction
    rw [hinfo, hroot, hout]
    rw [hres] at hb
    simp only [bind, Except.bind, hres, List.length_cons, List.length_nil,
      bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false, hb,
      pure, Except.pure, Array.append_empty, hcode]
    rfl
  have hfull : st' = { st with base := st'.base } := by
    rw [stock_iconst_rhs_frame hp ctx hc heval, stock_iconst_match_frame hp ctx hc hmatch]
  have hmono : emission.state.demand = st.demand := by
    change bound.demand = st.demand
    rw [hbound, hfull]
  refine ⟨ty, imm, d, emission, hinst, hout, rfl, hemit, hmono, ?_⟩
  intro aliases ha hresult houtside env cp MR hMR s s' hsource ρ w hrel
  obtain ⟨info', inst', vals, regs, rest, hi', hic', _, he, hs, hfr⟩ := hsource
  have hei : info' = info := Option.some.inj (hi'.symm.trans hi)
  subst info'
  have hei : inst' = inst := Option.some.inj (hic'.symm.trans hic)
  subst inst'
  rw [hinst] at he
  simp only [instOutcome, Clif.evalInst, pure] at he
  have heq := Clif.Res.ok.inj he
  obtain ⟨hvals, hmem⟩ := Prod.mk.inj heq
  rw [← hvals] at hs
  rw [hres] at hs
  simp only [Clif.Regs.setMany_cons, Clif.Regs.setMany_nil, Option.some.injEq] at hs
  subst regs
  have hheld : ValuesHeld (Demanded st) ctx s.1 (fun k => ρ (aliasNum aliases k)) := by
    simpa only [ValuesHeld, Demanded, Emission.scan, hmono] using hrel.2
  obtain ⟨ρ', hr, hv, hinstall⟩ := hrun aliases ha ρ
  obtain ⟨w', hexec, hworld⟩ := hr w
  have hpost := hinstall (Demanded st) s.1 hheld hresult
    (fun y b hy hne hb _ => houtside y b hy hne hb)
  refine ⟨ρ', w', ?_, ?_, ?_⟩
  · simpa only [emission, Emission.scan, List.toList_toArray] using hexec
  · rw [← hmem]
    exact hMR _ _ _ hworld hrel.1
  · rw [hfr]
    change ValuesHeld (Demanded st) ctx (withValue s.1 x ⟨ty, imm⟩)
      (fun k => ρ' (aliasNum aliases k))
    exact hpost

private def constantInput : State := { sinkState with demand := #[0, 0, 1] }
private def constantBefore : State := scanState constantInput 0
private def constantAliases : Array (Option Nat) := aliasStep #[] (193, 194)

private theorem constant_aliases :
    constantAliases.size ≤ constantBefore.base.nextVreg ∧
      aliasNum constantAliases 193 = 194 := by decide

private theorem constant_demanded (y : Nat) : Demanded constantBefore y ↔ y = 2 := by
  rw [Demanded, constantBefore, scanState_demands]
  change (#[0, 0, 1] : Array Nat)[y]! ≠ 0 ↔ y = 2
  match y with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | y + 3 =>
    have ho : (#[0, 0, 1] : Array Nat)[y + 3]? = none :=
      Array.getElem?_eq_none (by change 3 ≤ y + 3; omega)
    simp only [getElem!_def, ho]
    simp

private theorem self_refines : Refines (fun _ => True) ispec :=
  fun _ _ _ _ w' _ h => ⟨w', h, SameWorld.refl _ _⟩

private theorem resolver_sem : ∀ aliases i, ispec (i.mapRegs
    (Backend.lowerFunction.resolve aliases (aliases.size + 1))) = ispec i := by
  intro aliases i
  funext us w
  have hg : VRenaming (Backend.lowerFunction.resolve aliases (aliases.size + 1))
      (aliasNum aliases) := by
    refine ⟨fun n c => resolve_vreg aliases _ n c, ?_⟩
    intro r hr
    cases r with
    | vreg n c => exact False.elim (hr n c rfl)
    | _ => simp [Backend.lowerFunction.resolve]
  exact ispec_mapRegs hg us w i

private def aliasBefore : State :=
  { constantBefore with alias := aliasStep #[] (191, 192) }

private theorem alias_emission :
    ∃ (f : Clif.Function) (ctx : Ctx) (emission : Emission),
      MappedCtxInv f ctx ∧ ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      emitInstruction ctx 0 aliasBefore = .ok emission ∧
      emission.state.alias = aliasStep aliasBefore.alias (193, 194) ∧
      emission.state.demand = aliasBefore.demand ∧ emission.state.sunk = aliasBefore.sunk := by
  obtain ⟨f, ctx, info, hc, hi, hic, hres, hmap, hselected⟩ := stock_statement_selectedConstant
  obtain ⟨next, trace, hroot, heval, hmatch⟩ := hselected aliasBefore
  obtain ⟨emission, hemit, hf, hcode, hresults⟩ :=
    stock_iconst_emission_alias data_program hi hres hmap rfl hmatch heval hroot
  refine ⟨f, ctx, emission, hc, hmap, hemit, ?_, ?_, ?_⟩ <;> rw [hf] <;> rfl

/-- Actual generated selection preserves a pre-existing alias and installs the
mapped constant result without changing demand or sinking state. -/
theorem stock_iconst_emission_alias_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (emission : Emission),
      MappedCtxInv f ctx ∧ ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      emitInstruction ctx 0 aliasBefore = .ok emission ∧
      emission.state.alias = aliasStep aliasBefore.alias (193, 194) ∧
      (emission.state.alias[191]?).join = some 192 ∧
      (emission.state.alias[193]?).join = some 194 ∧
      emission.state.demand = aliasBefore.demand ∧ emission.state.sunk = aliasBefore.sunk := by
  obtain ⟨f, ctx, emission, hc, hm, he, ha, hd, hs⟩ := alias_emission
  refine ⟨f, ctx, emission, hc, hm, he, ha, ?_, ?_, hd, hs⟩ <;> rw [ha] <;> rfl

/-- The actual emitter's post-state resolves source result 193 to fresh 194;
its retained older alias still resolves 191 to 192. -/
theorem stock_iconst_emission_alias_fresh_witness :
    ∃ (ctx : Ctx) (emission : Emission),
      emitInstruction ctx 0 aliasBefore = .ok emission ∧
      emission.state.alias.size ≤ aliasBefore.base.nextVreg ∧
      aliasNum emission.state.alias 193 = 194 ∧ aliasNum emission.state.alias 191 = 192 := by
  obtain ⟨f, ctx, emission, hc, hm, he, ha, hd, hs⟩ := alias_emission
  obtain ⟨hsize, hr⟩ := stock_iconst_emission_alias_fresh ha
    (lo := aliasBefore.base.nextVreg) (by decide) (by decide) (by decide)
  refine ⟨ctx, emission, he, hsize, hr, ?_⟩
  rw [ha]
  decide

/-- Actual generated selection, output binding and stock scan execute the
constant's original source statement and install its mapped machine result. -/
theorem stock_iconst_emission_fall_refines_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (emission : Emission)
      (fr fr' : Clif.Frame) (ρ' : Nat → CV) (w' : Arm.ArmState),
      MappedCtxInv f ctx ∧ ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      emitInstruction ctx 0 constantBefore = .ok emission ∧
      scanInstruction ctx 0 0 1 false constantInput =
        .ok (emission.scan 0 0 constantBefore) ∧
      SourceInstResult Clif.Env.empty { funcs := [] } ctx 0
        (fr, Clif.Mem.empty) (fr', Clif.Mem.empty) ∧
      seqRun ispec (emission.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve constantAliases (constantAliases.size + 1))))
        (fun _ => 0) Arm.ArmState.default = some (.fall ρ' w') ∧
      VHolds (Clif.Val.ofInt .i8 9) (ρ' 194) ∧ fr'.regs 2 = some (.ofInt .i8 9) := by
  obtain ⟨f, ctx, info, hctx, hi, hic, hres, hmap, hselected⟩ := stock_statement_selectedConstant
  obtain ⟨next, trace, hroot, heval, hmatch⟩ := hselected constantBefore
  obtain ⟨ty, imm, d, emission, hinst, hout, hresults, hemit, hmono, hlocal⟩ :=
    stock_iconst_emission_fall_refines data_program hctx (block := 0) hi hic rfl
      self_refines resolver_sem (by decide) (by decide) hmatch heval hroot rfl hres hmap
  cases hinst
  change V.regsVec [[.vreg 194 .int]] = .regsVec [[.vreg d .int]] at hout
  cases hout
  have houtside : ∀ y b, Demanded constantBefore y → y ≠ 2 →
      ctx.valueReg? y = some (.vreg b .int) →
      aliasNum constantAliases b < constantBefore.base.nextVreg ∨
        emission.state.base.nextVreg ≤ aliasNum constantAliases b := by
    intro y b hy hne _
    exact False.elim (hne ((constant_demanded y).mp hy))
  have htransfer := hlocal constantAliases constant_aliases.1 constant_aliases.2
    houtside Clif.Env.empty { funcs := [] } (fun _ _ => True) (fun _ _ _ _ _ => trivial)
  let fr : Clif.Frame := {
    func := f
    regs := fun _ => none
    slots := []
    body := [⟨[2], .iconst .i8 9⟩]
    term := .ret [2] }
  let fr' : Clif.Frame := { fr with regs := fr.regs.set 2 (.ofInt .i8 9), body := [] }
  have hsource : SourceInstResult Clif.Env.empty { funcs := [] } ctx 0
      (fr, Clif.Mem.empty) (fr', Clif.Mem.empty) :=
    ⟨info, .iconst .i8 9, [.ofInt .i8 9], fr.regs.set 2 (.ofInt .i8 9), [],
      hi, hic, by simp only [fr, hres], rfl, by rw [hres]; rfl, rfl⟩
  have hstart : ValuesHeld (Demanded emission.state) ctx fr
      (fun k => (0 : CV)) := by
    intro x hx v hv
    cases hv
  obtain ⟨ρ', w', hrun, _, hheld⟩ := htransfer (fr, Clif.Mem.empty) (fr', Clif.Mem.empty)
    hsource (fun _ => 0) Arm.ArmState.default ⟨trivial, hstart⟩
  have hvalue := hheld.read ((constant_demanded 2).mpr rfl)
    (show fr'.regs 2 = some (.ofInt .i8 9) from rfl) hmap
  rw [constant_aliases.2] at hvalue
  have hscan : scanInstruction ctx 0 0 1 false constantInput =
      .ok (emission.scan 0 0 constantBefore) := by
    have hinfo : ctx.insts[0]! = info := by simp only [getElem!_def, hi]
    unfold scanInstruction
    simp only [show constantInput.sunk[0]! = false from rfl, Bool.false_eq_true, ite_false,
      show (0 == 1) = false from rfl, Bool.false_and, hinfo, hic,
      hres, List.any_cons, List.any_nil,
      show (scanState constantInput 0).demand[2]! = 1 from rfl,
      show ((1 : Nat) != 0) = true from rfl, Bool.true_or, Bool.not_true, Bool.and_false,
      show ((scanState constantInput 0).entryColor[0]! == 0) = false from rfl,
      bind, Except.bind, pure, Except.pure]
    change (emitInstruction ctx 0 constantBefore >>= fun e =>
      pure (e.scan 0 0 constantBefore)) = _
    rw [hemit]
    rfl
  exact ⟨f, ctx, emission, fr, fr', ρ', w', hctx, hmap, hemit, hscan, hsource,
    hrun, hvalue, rfl⟩

end Backend.Stock.Proof
