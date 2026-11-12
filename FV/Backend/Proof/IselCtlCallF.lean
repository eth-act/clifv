import FV.Backend.Proof.LowerContractTP
import FV.Backend.Proof.IselTermFactsCallT
import FV.Backend.Proof.IselCtlTermTI
import FV.Backend.Proof.DriverCheckT

/-!
# Family Ctl over typed contexts: `call` with `f32`/`f64` arguments and returns (S11e5 Stage B)

The `call` rules of `lower` (`bl`, rule 1031; GOT + `blr`, rule 1032) on float-capable contexts
for every extern signature the lowering accepts, not only integer ones (`IselCtlCallTI`'s
`CallRulesCorrectTP` assumes integer arguments, `CtxInvT.intOps`, and integer
returns, `CtxT.resTysE`). As Cranelift's aarch64 ABI (`gen_call_args`/`gen_call_output`/
`gen_call_rets`, typed since S11e5a):

* each argument is passed in its value's vreg, of the value's class (`valClassOf`), fixed to the
  location `sigArgLocs` gives its parameter (x0..x7 / v0..v7 with separate counters, an `sret`
  pointer in x8, then the outgoing stack area); a stack-passed argument is stored by
  `stackArgStore` (`str` of its byte size for an int vreg, `str s`/`str d` for a float one), so
  the family assumes the float store forms `MemRefinesFP` beside the integer ones;
* each ABI return gets a fresh vreg of its class (`retClass`), defined by the call from the return
  register `retRegsC` gives it (x0.. / v0.. with separate counters).

The VCode-level callee contract `CallsRefineP` is class-agnostic (`ArgsAt`: the register-passed
arguments held by the uses' values in parameter order, the stack-passed ones in the outgoing
area), so it is unchanged. That a float argument is stored with its own byte size (4 or 8) comes
from the frame's typing (`DFGCons`'s `FrameTyped`: a value of float class has a float type, and
the CLIF call checks the argument types against the parameters).

The contexts are `CallCtxT`: the facts of a float-capable context the call rules use (the
instruction data, the result types, value `x` in vreg `x` of its type's class). `CtxInvT` gives
them (`CtxInvT.toCallCtx`), but `CtxInvT` also types every `call` argument as an integer
(`intArgs`), so the float-argument calls are covered through `CallCtxT`; `callCtxOkB` decides it
(`callCtxOkB_sound`).

Results: `CallRulesCorrectTFP` (`CallRulesCorrectTP` over `CallCtxT`, every extern signature,
with `MemRefinesFP`), `callRulesCorrectTFP_program`; `callRuleOkTP_of_TFP` (the integer-argument
family over `CtxT` is an instance).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## The contexts and the family -/

/-- **The facts of a float-capable lowering context the call rules use**: `CtxInvT`'s instruction
data, result types and class-aware value registers, without its integer typing of operands
(`intArgs`, which lists the arguments of a `call`). -/
structure CallCtxT (f : Clif.Function) (ctx : Ctx) : Prop where
  func : ctx.func = f
  data : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst → instData f inst = .ok info.data
  resTys : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst →
    ∃ tys, inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) = some tys ∧
      info.resTys = tys.map CTy.ofClif ∧ info.results.length = tys.length
  /-- value `x` has vreg `x`, of the class of its type -/
  valueReg : ∀ (x : Nat) (r : Reg), ctx.valueReg? x = some r → r = .vreg x (valClassOf ctx x)

theorem CtxInvT.toCallCtx {f : Clif.Function} {ctx : Ctx} (h : CtxInvT f ctx) : CallCtxT f ctx :=
  ⟨h.func, h.data, h.resTys, h.valueReg⟩

/-- `CallRuleOkTP` over the call facts of float-capable contexts (`CallCtxT`) for calls of any
extern signature. -/
def CallRuleOkTFP (Rd : BitVec 64 → Prop)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (isem : Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (exts : List Clif.ExtFunc) (outB : Nat) (p : Program)
    (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CallCtxT f ctx → ExternsIn f exts →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
  (∀ fn args e, inst = .call fn args → f.extern? fn = some e → SigStackOk e.sig outB) →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOkP Rd Pc isem MR env cp ctx inst info.results st rss st' ms

/-- **The call roots over float-capable contexts, for every extern signature, with pinned
calls**: `CallRulesCorrectTP` with `f32`/`f64` arguments and returns (the float stack-argument
stores under `MemRefinesFP`). -/
def CallRulesCorrectTFP (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → MemRefinesFP Rd F sb isem →
    OutArgsOk F outB MR → CallsRefineP Pc F env exts MR isem →
    ∀ r ∈ p.rulesOf TId.lower, callRootRule r = true →
      CallRuleOkTFP Rd Pc isem MR env cp exts outB p r

/-! ## Typed-context facts -/

/-- The registers of the values of a float-capable context: vreg `x` of `x`'s class. -/
theorem mapM_valueRegC {f : Clif.Function} {ctx : Ctx} (hctx : CallCtxT f ctx) :
    ∀ {xs : List Nat} {rs : List Reg}, xs.mapM ctx.valueReg? = some rs →
      rs = xs.map fun x => Reg.vreg x (valClassOf ctx x)
  | [], rs, h => by simp at h; simp [h]
  | x :: xs, rs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, rs', hrs, rfl⟩ := h
    rw [hctx.valueReg x r hr, mapM_valueRegC hctx hrs]
    rfl

/-- The number of CLIF results of a `call` is its callee's number of returns. -/
theorem call_results_lengthC {f : Clif.Function} {ctx : Ctx} (hctx : CallCtxT f ctx) {ii : Nat}
    {info : IInfo} {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some (.call fn args))
    (hext : f.extern? fn = some ext) : info.results.length = ext.sig.returns.length := by
  obtain ⟨tys, htys, -, hl⟩ := hctx.resTys ii info _ hi hc
  simp only [Clif.Inst.resultTypes, hext, Option.map_some, Option.some.injEq] at htys
  rw [hl, ← htys, List.length_map]

theorem valClass_ofClif_float {t : Clif.Ty} (h : (CTy.ofClif t).valClass = .float) :
    t = .f32 ∨ t = .f64 := by
  cases t <;> simp_all [CTy.ofClif, CTy.valClass, CTy.regClass?]

/-- A value of float class in a typed frame has a float type. -/
theorem float_of_valClassOf {ctx : Ctx} {fr : Clif.Frame} (hft : FrameTyped ctx fr) {x : Nat}
    {v : Clif.Val} (hx : fr.regs x = some v) (hc : valClassOf ctx x = .float) :
    v.ty = .f32 ∨ v.ty = .f64 := by
  unfold valClassOf at hc
  cases ht : ctx.valueType? x with
  | none => rw [ht] at hc; cases hc
  | some t =>
    rw [ht] at hc
    simp only [Option.map_some, Option.getD_some] at hc
    rw [← hft x t v ht hx] at hc
    exact valClass_ofClif_float hc

/-! ## Class-general call operands -/

/-- The register-passed arguments of a call with their classes `cls`. -/
def liftC (cls : Nat → RegClass) (L : List (Nat × Reg)) : List (Nat × RegClass × Reg) :=
  L.map fun q => (q.1, cls q.1, q.2)

theorem liftC_fst (cls : Nat → RegClass) (L : List (Nat × Reg)) :
    (liftC cls L).map (·.1) = L.map (·.1) := by
  simp [liftC]

/-- `(preg, vreg n c)` pairs of a call's defs, of either class. -/
def callDefsC (D : List (Reg × Nat × RegClass)) : List (Reg × Reg) :=
  D.map fun q => (q.1, Reg.vreg q.2.1 q.2.2)

/-- The operands of a call's defs: fixed late defs, of their vregs' classes. -/
def callDefOpsC (D : List (Reg × Nat × RegClass)) : List Operand :=
  D.map fun q => (⟨q.2.1, q.2.2, .def, .late, .fixed q.1⟩ : Operand)

open Driver in
theorem mapM_callDefsC (D : List (Reg × Nat × RegClass)) : ∀ (s : Array Operand),
    ((callDefsC D).mapM
      (fun (x : Reg × Reg) => do let r ← collectOp (OpSpec.fixedDef x.1) x.2; pure (x.1, r))).run s =
      .ok (callDefsC D, s ++ (callDefOpsC D).toArray) := by
  induction D with
  | nil => intro s; simp [callDefsC, callDefOpsC] <;> rfl
  | cons q D ih =>
    intro s
    simp only [callDefsC, callDefOpsC, List.map_cons, List.mapM_cons, StateT.run_bind] at ih ⊢
    have h1 : (collectOp (OpSpec.fixedDef q.1) (Reg.vreg q.2.1 q.2.2)).run s =
        .ok (Reg.vreg q.2.1 q.2.2, s.push ⟨q.2.1, q.2.2, .def, .late, .fixed q.1⟩) := rfl
    rw [h1, except_ok_bind, StateT.run_pure, except_pure, except_ok_bind, ih, except_ok_bind,
      StateT.run_pure, except_pure]
    simp

open Driver in
theorem operands_call_symC (nm : String) (L : List (Nat × RegClass × Reg))
    (D : List (Reg × Nat × RegClass)) :
    (MInst.call ⟨.sym nm, argPairsC L, callDefsC D⟩).operands =
      .ok (retOpsC L ++ callDefOpsC D).toArray := by
  rw [operands_eq]
  simp only [MInst.visitOperands, StateT.run_bind, StateT.run_pure, except_ok_bind, mapM_fixedUseC,
    mapM_callDefsC]
  simp [bind, Except.bind, StateT.run, pure, StateT.pure, Except.pure]

theorem filter_isUse_callDefOpsC (D : List (Reg × Nat × RegClass)) :
    (callDefOpsC D).filter Operand.isUse = [] := by
  rw [List.filter_eq_nil_iff]
  intro o ho
  simp only [callDefOpsC, List.mem_map] at ho
  obtain ⟨q, -, rfl⟩ := ho
  simp [Operand.isUse, Operand.isDef]

theorem filter_isDef_callDefOpsC (D : List (Reg × Nat × RegClass)) :
    (callDefOpsC D).filter Operand.isDef = callDefOpsC D := by
  rw [List.filter_eq_self]
  intro o ho
  simp only [callDefOpsC, List.mem_map] at ho
  obtain ⟨q, -, rfl⟩ := ho
  simp [Operand.isDef]

theorem vuses_callC {V : Type} (L : List (Nat × RegClass × Reg)) (D : List (Reg × Nat × RegClass))
    (ρ : Nat → V) : vuses (retOpsC L ++ callDefOpsC D).toArray ρ = L.map (ρ ·.1) := by
  simp only [vuses, List.toList_toArray, List.filter_append, filter_isUse_retOpsC,
    filter_isUse_callDefOpsC, List.append_nil]
  simp [retOpsC]

theorem defs_callC (L : List (Nat × RegClass × Reg)) (D : List (Reg × Nat × RegClass)) :
    (retOpsC L ++ callDefOpsC D).filter Operand.isDef = callDefOpsC D := by
  simp only [List.filter_append, filter_isDef_retOpsC, filter_isDef_callDefOpsC, List.nil_append]

theorem zip_callDefOpsC_early {V : Type} : ∀ (D : List (Reg × Nat × RegClass)) (outs : List V),
    ((callDefOpsC D).zip outs).filter (·.1.isEarly) = [] ∧
      ((callDefOpsC D).zip outs).filter (·.1.isLate) = (callDefOpsC D).zip outs
  | [], outs => by simp [callDefOpsC]
  | q :: D, [] => by simp [callDefOpsC]
  | q :: D, o :: outs => by
    obtain ⟨h1, h2⟩ := zip_callDefOpsC_early D outs
    simp only [callDefOpsC, List.map_cons, List.zip_cons_cons] at h1 h2 ⊢
    rw [List.filter_cons_of_neg (by simp [Operand.isEarly]), h1,
      List.filter_cons_of_pos (by simp [Operand.isLate]), h2]
    exact ⟨rfl, rfl⟩

theorem vdefUpd_callC {V : Type} (L : List (Nat × RegClass × Reg)) (D : List (Reg × Nat × RegClass))
    (outs : List V) (ρ : Nat → V) :
    vdefUpd (retOpsC L ++ callDefOpsC D).toArray outs ρ = writeV ρ ((callDefOpsC D).zip outs) := by
  simp only [vdefUpd, List.toList_toArray, defs_callC, (zip_callDefOpsC_early D outs).1,
    (zip_callDefOpsC_early D outs).2]
  rfl

theorem vuseNums_call_symC (nm : String) (L : List (Nat × RegClass × Reg))
    (D : List (Reg × Nat × RegClass)) :
    vuseNums (.call ⟨.sym nm, argPairsC L, callDefsC D⟩) = L.map (·.1) := by
  have := vuses_callC L D id
  simp only [vuseNums, operands_call_symC]
  simpa [vuses] using this

theorem vdefs_call_symC (nm : String) (L : List (Nat × RegClass × Reg))
    (D : List (Reg × Nat × RegClass)) :
    vdefs (.call ⟨.sym nm, argPairsC L, callDefsC D⟩) = D.map (·.2.1) := by
  simp only [vdefs, operands_call_symC, List.toList_toArray, defs_callC]
  simp [callDefOpsC]

theorem seqRun_call_symC {isem : Sem} {nm : String} {L : List (Nat × RegClass × Reg)}
    {D : List (Reg × Nat × RegClass)} {ρ : Nat → CV} {w w' : Arm.ArmState} {outs : List CV}
    (h : isem (.call ⟨.sym nm, argPairsC L, callDefsC D⟩) (L.map (ρ ·.1)) w = some (outs, w', .next))
    (hl : outs.length = D.length) :
    seqRun isem [.call ⟨.sym nm, argPairsC L, callDefsC D⟩] ρ w =
      some (.fall (writeV ρ ((callDefOpsC D).zip outs)) w') := by
  simp only [seqRun, operands_call_symC, vuses_callC, h, List.toList_toArray, defs_callC]
  have hl' : outs.length = (callDefOpsC D).length := by simp [callDefOpsC, hl]
  simp only [hl', ↓reduceIte, vdefUpd_callC]
  rfl

open Driver in
theorem operands_call_regC (t : Nat) (L : List (Nat × RegClass × Reg))
    (D : List (Reg × Nat × RegClass)) :
    (MInst.call ⟨.reg (.vreg t .int), argPairsC L, callDefsC D⟩).operands =
      .ok (tgtOp t :: (retOpsC L ++ callDefOpsC D)).toArray := by
  have h1 : ∀ s, (collectOp OpSpec.use (Reg.vreg t .int)).run s =
      .ok (Reg.vreg t .int, s.push (tgtOp t)) := fun _ => rfl
  rw [operands_eq]
  simp only [MInst.visitOperands, StateT.run_bind, StateT.run_pure, except_ok_bind, h1,
    mapM_fixedUseC, mapM_callDefsC]
  simp [bind, Except.bind, StateT.run, pure, StateT.pure, Except.pure]

theorem vuses_call_regC {V : Type} (t : Nat) (L : List (Nat × RegClass × Reg))
    (D : List (Reg × Nat × RegClass)) (ρ : Nat → V) :
    vuses (tgtOp t :: (retOpsC L ++ callDefOpsC D)).toArray ρ = ρ t :: L.map (ρ ·.1) := by
  have := vuses_callC L D ρ
  simp only [vuses, List.toList_toArray] at this ⊢
  rw [List.filter_cons_of_pos (by simp [tgtOp, Operand.isUse])]
  simp only [List.map_cons, this]
  rfl

theorem vdefUpd_call_regC {V : Type} (t : Nat) (L : List (Nat × RegClass × Reg))
    (D : List (Reg × Nat × RegClass)) (outs : List V) (ρ : Nat → V) :
    vdefUpd (tgtOp t :: (retOpsC L ++ callDefOpsC D)).toArray outs ρ =
      writeV ρ ((callDefOpsC D).zip outs) := by
  rw [← vdefUpd_callC L D outs ρ]
  simp only [vdefUpd, List.toList_toArray]
  rw [List.filter_cons_of_neg (by simp [tgtOp, Operand.isDef])]

theorem seqRun_call_regC {isem : Sem} {t : Nat} {L : List (Nat × RegClass × Reg)}
    {D : List (Reg × Nat × RegClass)} {ρ : Nat → CV} {w w' : Arm.ArmState} {outs : List CV}
    (h : isem (.call ⟨.reg (.vreg t .int), argPairsC L, callDefsC D⟩) (ρ t :: L.map (ρ ·.1)) w =
      some (outs, w', .next))
    (hl : outs.length = D.length) :
    seqRun isem [.call ⟨.reg (.vreg t .int), argPairsC L, callDefsC D⟩] ρ w =
      some (.fall (writeV ρ ((callDefOpsC D).zip outs)) w') := by
  simp only [seqRun, operands_call_regC, vuses_call_regC, h, List.toList_toArray]
  rw [List.filter_cons_of_neg (by simp [tgtOp, Operand.isDef]), defs_callC]
  have hl' : outs.length = (callDefOpsC D).length := by simp [callDefOpsC, hl]
  simp only [hl', ↓reduceIte, vdefUpd_call_regC]
  rfl

theorem vuseNums_call_regC (t : Nat) (L : List (Nat × RegClass × Reg))
    (D : List (Reg × Nat × RegClass)) :
    vuseNums (.call ⟨.reg (.vreg t .int), argPairsC L, callDefsC D⟩) = t :: L.map (·.1) := by
  have := vuses_call_regC t L D id
  simp only [vuseNums, operands_call_regC]
  simpa [vuses] using this

theorem vdefs_call_regC (t : Nat) (L : List (Nat × RegClass × Reg))
    (D : List (Reg × Nat × RegClass)) :
    vdefs (.call ⟨.reg (.vreg t .int), argPairsC L, callDefsC D⟩) = D.map (·.2.1) := by
  simp only [vdefs, operands_call_regC, List.toList_toArray]
  rw [List.filter_cons_of_neg (by simp [tgtOp, Operand.isDef]), defs_callC]
  simp [callDefOpsC]

/-! ## The typed outputs -/

/-- The defs of a call whose returns have the classes `cs` and the return registers `ps`: the
`j`-th return register into the fresh vreg `b + j` of class `cs[j]`. -/
def outDefsC (b : Nat) (ps : List Reg) (cs : List RegClass) : List (Reg × Nat × RegClass) :=
  (ps.zip cs.zipIdx).map fun q => (q.1, b + q.2.2, q.2.1)

theorem map_fst_zipIdx {β : Type} : ∀ (cs : List β) (k : Nat), (cs.zipIdx k).map Prod.fst = cs
  | [], _ => rfl
  | c :: cs, k => by simp [List.zipIdx_cons, map_fst_zipIdx cs (k + 1)]

theorem callDefsC_outDefsC (b : Nat) (ps : List Reg) (cs : List RegClass) :
    ps.zip (cs.zipIdx.map fun q => Reg.vreg (b + q.2) q.1) = callDefsC (outDefsC b ps cs) := by
  simp [callDefsC, outDefsC, List.zip_map_right, Function.comp_def]

theorem regsClasses_outRegsC (st : LState) (cs : List RegClass) :
    regsClasses (outRegsC st cs) = cs := by
  simp only [regsClasses, outRegsC, List.map_map, Function.comp_def, List.head?_cons,
    Option.map_some, Option.getD_some, Reg.homeCls]
  rw [show (fun x : RegClass × Nat => x.1) = Prod.fst from rfl, map_fst_zipIdx]

theorem retRegsC_lengthC : ∀ (cs : List RegClass) (nx nv : Nat) {ps : List Reg},
    retRegsC cs nx nv = some ps → ps.length = cs.length
  | [], _, _, ps, h => by simp [retRegsC] at h; subst h; rfl
  | .int :: cs, nx, nv, ps, h => by
    simp only [retRegsC] at h
    split at h
    · obtain ⟨ps', h', rfl⟩ := Option.map_eq_some_iff.mp h
      simp [retRegsC_lengthC cs _ _ h']
    · cases h
  | .float :: cs, nx, nv, ps, h => by
    simp only [retRegsC] at h
    split at h
    · obtain ⟨ps', h', rfl⟩ := Option.map_eq_some_iff.mp h
      simp [retRegsC_lengthC cs _ _ h']
    · cases h

theorem outDefsC_length (b : Nat) {ps : List Reg} {cs : List RegClass}
    (h : ps.length = cs.length) : (outDefsC b ps cs).length = cs.length := by
  simp [outDefsC, h]

theorem outDefsC_vregs (b : Nat) {ps : List Reg} {cs : List RegClass}
    (h : ps.length = cs.length) : (outDefsC b ps cs).map (·.2.1) = (List.range cs.length).map (b + ·) := by
  apply List.ext_getElem (by simp [outDefsC, h])
  intro j h1 h2
  simp [outDefsC]

/-- The call's result vregs hold the extern's results (typed outputs). -/
theorem resultsHeld_callC {fr : Clif.Frame} {ρ : Nat → CV} {st : LState} {rvals : List Clif.Val}
    {outs : List CV} {ps : List Reg} {cs : List RegClass} (hps : ps.length = cs.length)
    (hrN : rvals.length = cs.length) (hro : AllHold rvals outs) :
    ResultsHeld st.nextVreg fr (outRegsC st cs) rvals
      (writeV ρ ((callDefOpsC (outDefsC st.nextVreg ps cs)).zip outs)) := by
  refine ⟨by simp [outRegsC_length, hrN], fun j rs v hrs hvj => ?_⟩
  have hjN : j < cs.length := by
    rcases Nat.lt_or_ge j cs.length with h | h
    · exact h
    · simp [outRegsC, h] at hrs
  obtain ⟨c, hc⟩ : ∃ c, cs[j]? = some c := ⟨cs[j], by simp [hjN]⟩
  have hrs' : rs = [Reg.vreg (st.nextVreg + j) c] := by
    simp only [outRegsC, List.getElem?_map, List.getElem?_zipIdx, hc, Option.map_some,
      Option.some.injEq] at hrs
    rw [← hrs]; simp
  subst hrs'
  refine ⟨st.nextVreg + j, c, rfl, .inl (by omega), ?_⟩
  obtain ⟨x, hx⟩ : ∃ x, outs[j]? = some x :=
    ⟨outs[j]'(by rw [← hro.1, hrN]; exact hjN), by simp⟩
  obtain ⟨p, hp⟩ : ∃ p, ps[j]? = some p := ⟨ps[j]'(by rw [hps]; exact hjN), by simp⟩
  have hk : ((callDefOpsC (outDefsC st.nextVreg ps cs)).zip outs).map (·.1.vreg) =
      (List.range cs.length).map (st.nextVreg + ·) := by
    rw [show (fun q : Operand × CV => q.1.vreg) = Operand.vreg ∘ Prod.fst from rfl, ← List.map_map,
      List.map_fst_zip (by simp [callDefOpsC, outDefsC_length _ hps, ← hro.1, hrN])]
    rw [← outDefsC_vregs st.nextVreg hps]
    simp [callDefOpsC]
  have hnd : (((callDefOpsC (outDefsC st.nextVreg ps cs)).zip outs).map (·.1.vreg)).Nodup := by
    rw [hk]
    exact List.Pairwise.map _ (fun a c h e => h (by omega)) List.nodup_range
  have hget : ((callDefOpsC (outDefsC st.nextVreg ps cs)).zip outs)[j]? =
      some (⟨st.nextVreg + j, c, .def, .late, .fixed p⟩, x) := by
    rw [List.getElem?_zip_eq_some]
    simp [callDefOpsC, outDefsC, hx, hp, hc, List.getElem?_zip_eq_some, List.getElem?_zipIdx]
    exact ⟨_, _, _, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  rw [writeV_nodup_ctl _ ρ j _ x hnd hget]
  exact hro.2 j v x hvj hx

/-- The results of a call with typed outputs (`results_call` with `outRegsC`). -/
theorem results_callC {fr : Clif.Frame} {ρ : Nat → CV} {st : LState} {rvals : List Clif.Val}
    {outs : List CV} {results : List Nat} {s : Clif.Signature} {ps : List Reg}
    (hps : ps.length = (s.returns.map retClass).length)
    (hrN : rvals.length = s.returns.length) (hres : results.length = s.returns.length)
    (hol : outs.length = s.returns.length) (hro : PrefixHold rvals outs) :
    results = [] ∨ ResultsHeld st.nextVreg fr (outRegsC st (s.returns.map retClass)) rvals
      (writeV ρ ((callDefOpsC (outDefsC st.nextVreg ps (s.returns.map retClass))).zip outs)) := by
  cases h0 : s.returns with
  | nil => left; rw [h0] at hres; exact List.eq_nil_of_length_eq_zero hres
  | cons a l =>
    right
    rw [h0] at hps hrN hol
    refine resultsHeld_callC hps (by rw [List.length_map]; exact hrN) ?_
    exact hro.allHold (by rw [hol, hrN])

/-! ## `gen_call_args` with typed arguments -/

/-- The store `gen_call_args` emits for a stack-passed argument (offset, value, byte size) whose
vreg has class `cls value` (`stackArgStore`: `str`/`strb`/`strh` or `str s`/`str d`). -/
def argStoreC (cls : Nat → RegClass) (e : Nat × Nat × Nat) : MInst :=
  stackArgStore (.vreg e.2.1 (cls e.2.1)) e.2.2 (.spOffset e.1)

theorem argRegPairs_mapC (cls : Nat → RegClass) : ∀ (T : List ((ArgLoc × Nat) × Nat)),
    argRegPairs (T.map fun q => ((q.1.1, Reg.vreg q.1.2 (cls q.1.2)), q.2)) =
      argPairsC (liftC cls (regPairsOf T))
  | [] => rfl
  | ((.reg p, x), b) :: T => by
    simp only [List.map_cons, argRegPairs, regPairsOf, List.filterMap_cons] at *
    rw [show argPairsC (liftC cls ((x, p) :: _)) = (Reg.vreg x (cls x), p) :: argPairsC (liftC cls _)
      from rfl]
    congr 1
    exact argRegPairs_mapC cls T
  | ((.stack off, x), b) :: T => by
    simp only [List.map_cons, argRegPairs, regPairsOf, List.filterMap_cons] at *
    exact argRegPairs_mapC cls T

theorem argStores_mapC (cls : Nat → RegClass) : ∀ (T : List ((ArgLoc × Nat) × Nat)),
    argStores (T.map fun q => ((q.1.1, Reg.vreg q.1.2 (cls q.1.2)), q.2)) =
      (stackEnts T).map (argStoreC cls)
  | [] => rfl
  | ((.reg p, x), b) :: T => by
    simp only [List.map_cons, argStores, stackEnts, List.filterMap_cons] at *
    exact argStores_mapC cls T
  | ((.stack off, x), b) :: T => by
    simp only [List.map_cons, argStores, stackEnts, List.filterMap_cons, List.map_cons] at *
    rw [show argStoreC cls (off, x, b) = stackArgStore (.vreg x (cls x)) b (.spOffset off) from rfl]
    congr 1
    exact argStores_mapC cls T

/-- **`gen_call_args`** with arguments in vregs of their classes (any number of parameters): the
register-passed arguments become the call's fixed uses, every stack-passed one a store. -/
theorem ctor_gen_call_args_genC {ctx : Ctx} (st : LState) (s : Clif.Signature) (args : List Nat)
    (cls : Nat → RegClass) {bytes : List Nat} (hb : sigParamBytes s = .ok bytes)
    {locs : List ArgLoc} {S : Nat} (hl : sigArgLocs s = .ok (locs, S)) (v : V) (st' : LState) :
    externCtor ctx T.gen_call_args
      [.op (.sig s), .regsVec ((args.map fun a => Reg.vreg a (cls a)).map fun r => [r])] st =
        .ok (v, st') ↔
      v = .op (.callArgs (argPairsC (liftC cls (regPairsOf ((locs.zip args).zip bytes))))) ∧
        st' = { st with emitted := st.emitted ++
          ((stackEnts ((locs.zip args).zip bytes)).map (argStoreC cls)).toArray } := by
  have : externCtor ctx T.gen_call_args
      [.op (.sig s), .regsVec ((args.map fun a => Reg.vreg a (cls a)).map fun r => [r])] st =
      match sigArgLocs s, ((args.map fun a => Reg.vreg a (cls a)).map fun r => [r]).mapM single? with
      | .ok (locs, _), some rs =>
        let bytes := match sigParamBytes s with | .ok b => b | _ => []
        let r := (((locs.zip rs).zip bytes).foldl argStep (#[], st))
        .ok (.op (.callArgs r.1.toList), r.2)
      | .error e, _ => .unmodeled s!"gen_call_args: {e}"
      | _, none => .unmodeled "gen_call_args: multi-register value" := rfl
  rw [this, hl, hb, mapM_single_map]
  simp only []
  rw [foldl_argStep_gen, zip3_map, argRegPairs_mapC, argStores_mapC]
  simp [eq_comm]

/-! ## The outgoing stack-argument stores of typed arguments -/

theorem operands_argStoreC (cls : Nat → RegClass) (e : Nat × Nat × Nat) :
    (argStoreC cls e).operands = .ok #[⟨e.2.1, cls e.2.1, .use, .early, .reg⟩] := by
  unfold argStoreC stackArgStore
  generalize cls e.2.1 = c
  cases c <;> rfl

theorem vdefs_argStoreC (cls : Nat → RegClass) (e : Nat × Nat × Nat) :
    vdefs (argStoreC cls e) = [] := by
  simp [vdefs, operands_argStoreC, Operand.isDef]

theorem vuseNums_argStoreC (cls : Nat → RegClass) (e : Nat × Nat × Nat) :
    vuseNums (argStoreC cls e) = [e.2.1] := by
  simp [vuseNums, operands_argStoreC, Operand.isUse, Operand.isDef]

theorem seqRun_argStoreC_cons {isem : Sem} {cls : Nat → RegClass} {e : Nat × Nat × Nat}
    {ρ : Nat → CV} {w w1 : Arm.ArmState}
    (h : isem (argStoreC cls e) [ρ e.2.1] w = some ([], w1, .next)) (ms : List MInst) :
    seqRun isem (argStoreC cls e :: ms) ρ w = (seqRun isem ms ρ w1).map SeqEnd.succ := by
  have hv : vuses #[(⟨e.2.1, cls e.2.1, .use, .early, .reg⟩ : Operand)] ρ = [ρ e.2.1] := rfl
  simp only [seqRun, operands_argStoreC, hv, h]
  simp [Operand.isDef, vdefUpd, writeV]

/-- One outgoing store of a typed argument: the low `b` bytes of the argument at `sp + off`
(an integer store, or `str s`/`str d` of a float vreg, `MemRefinesFP`). -/
theorem argStoreC_step {Rd F : BitVec 64 → Prop} {isem : Sem} {sb : Nat}
    {syms : String → Option Nat} (hMem : MemRefinesR Rd F sb syms isem)
    (hFP : MemRefinesFP Rd F sb isem) (cls : Nat → RegClass) {off x b : Nat}
    (hb : b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 8) (hc : cls x = .float → b = 4 ∨ b = 8) (v : CV)
    (w : Arm.ArmState) (hav : Avoids F b (spOf w + BitVec.ofNat 64 off)) :
    ∃ w1, isem (argStoreC cls (off, x, b)) [v] w = some ([], w1, .next) ∧
      SameWorld F w1 (Arm.write_mem_bytes b (spOf w + BitVec.ofNat 64 off)
        ((lo64 v).setWidth (b * 8)) w) := by
  cases hcx : cls x with
  | int =>
    have : argStoreC cls (off, x, b) = argStore (off, x, b) := by
      simp [argStoreC, stackArgStore, hcx, Reg.homeCls, argStore]
    rw [this]
    exact argStore_step hMem hb v w hav
  | float =>
    have hb' := hc hcx
    have hlo : ∀ k, k ≤ 64 → (lo64 v).setWidth k = v.setWidth k := fun k hk => by
      simp only [lo64]; rw [BitVec.setWidth_setWidth_of_le _ hk]
    rcases hb' with rfl | rfl
    · have ha : amodeAddr sb (.spOffset (off : Int)) ScalarSize.size32.bytes [] w =
          some (spOf w + BitVec.ofNat 64 off) := by simp [amodeAddr]
      have : argStoreC cls (off, x, 4) =
          .fpuStore .size32 (.vreg x .float) (.spOffset off) trustedFlags := by
        simp [argStoreC, stackArgStore, hcx, Reg.homeCls]
      rw [this, hlo _ (by decide)]
      exact hFP.2 .size32 x (.spOffset off) trustedFlags v [] w _ (.inl rfl) ha hav
    · have ha : amodeAddr sb (.spOffset (off : Int)) ScalarSize.size64.bytes [] w =
          some (spOf w + BitVec.ofNat 64 off) := by simp [amodeAddr]
      have : argStoreC cls (off, x, 8) =
          .fpuStore .size64 (.vreg x .float) (.spOffset off) trustedFlags := by
        simp [argStoreC, stackArgStore, hcx, Reg.homeCls]
      rw [this, hlo _ (by decide)]
      exact hFP.2 .size64 x (.spOffset off) trustedFlags v [] w _ (.inr rfl) ha hav

/-- **The outgoing stores of typed arguments** (`argStores_run` with `argStoreC`). -/
theorem argStoresC_run {Rd F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {sb : Nat}
    {syms : String → Option Nat} (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem)
    (hFP : MemRefinesFP Rd F sb isem) {outB : Nat} (hout : OutArgsOk F outB MR)
    (cls : Nat → RegClass) (ρ : Nat → CV) :
    ∀ (E : List (Nat × Nat × Nat)) (lo : Nat) (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem)
      (w : Arm.ArmState),
      slotsOk (E.map fun e => (e.1, e.2.2)) lo outB = true →
      (∀ e ∈ E, e.2.2 = 1 ∨ e.2.2 = 2 ∨ e.2.2 = 4 ∨ e.2.2 = 8) →
      (∀ e ∈ E, cls e.2.1 = .float → e.2.2 = 4 ∨ e.2.2 = 8) →
      MR sl cm w →
      ∃ w', seqRun isem (E.map (argStoreC cls)) ρ w = some (.fall ρ w') ∧ MR sl cm w' ∧
        spOf w' = spOf w ∧
        (∀ e ∈ E, Arm.read_mem_bytes e.2.2 (spOf w + BitVec.ofNat 64 e.1) w' =
          (lo64 (ρ e.2.1)).setWidth (e.2.2 * 8)) ∧
        (∀ k, k < lo → k < outB →
          w'.mem (spOf w + BitVec.ofNat 64 k) = w.mem (spOf w + BitVec.ofNat 64 k))
  | [], lo, sl, cm, w, _, _, _, hmr => ⟨w, rfl, hmr, rfl, by simp, fun _ _ _ => rfl⟩
  | (off, x, b) :: E, lo, sl, cm, w, hok, hbs, hcs, hmr => by
    simp only [List.map_cons, slotsOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hlo, hend⟩, hok⟩ := hok
    have hb := hbs (off, x, b) (List.mem_cons_self ..)
    have hbp : 0 < b := by rcases hb with rfl | rfl | rfl | rfl <;> decide
    obtain ⟨h64, hAv, hW⟩ := hout sl cm w hmr
    have hav : Avoids F b (spOf w + BitVec.ofNat 64 off) := fun k hk => by
      rw [add_ofNat_add]; exact hAv (off + k) (by omega)
    obtain ⟨w1, hst, hw1⟩ := argStoreC_step hMem hFP cls (x := x) hb
      (hcs (off, x, b) (List.mem_cons_self ..)) (ρ x) w hav
    have hmr1 : MR sl cm w1 := hMR _ _ _ _ (SameWorld.nf hw1) (hW off b _ hend)
    have hsp1 : spOf w1 = spOf w := by
      simp only [spOf]
      rw [hw1.1 (.GPR 31#5) (by simp [Masked]), Arm.r_of_write_mem_bytes]
    obtain ⟨w', hrun, hmr', hsp', hrd, hfr⟩ := argStoresC_run hMR hMem hFP hout cls ρ E (off + b)
      sl cm w1 hok (fun e he => hbs e (List.mem_cons_of_mem _ he))
      (fun e he => hcs e (List.mem_cons_of_mem _ he)) hmr1
    rw [hsp1] at hrd hfr
    have hw1m : ∀ k, k < outB → w1.mem (spOf w + BitVec.ofNat 64 k) =
        (Arm.write_mem_bytes b (spOf w + BitVec.ofNat 64 off) ((lo64 (ρ x)).setWidth (b * 8)) w).mem
          (spOf w + BitVec.ofNat 64 k) := fun k hk => hw1.2.1 _ (hAv k hk)
    refine ⟨w', ?_, hmr', hsp'.trans hsp1, ?_, ?_⟩
    · rw [List.map_cons, seqRun_argStoreC_cons hst, hrun]; rfl
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · show Arm.read_mem_bytes b (spOf w + BitVec.ofNat 64 off) w' = (lo64 (ρ x)).setWidth (b * 8)
        rw [← Arm.read_mem_bytes_of_write_mem_bytes_same (n := b) (addr := spOf w + BitVec.ofNat 64 off)
          (v := (lo64 (ρ x)).setWidth (b * 8)) (s := w) (by omega)]
        apply read_mem_bytes_congr
        intro k hk
        rw [add_ofNat_add, hfr (off + k) (by omega) (by omega), hw1m (off + k) (by omega)]
      · exact hrd e he
    · intro k hk hko
      rw [hfr k (by omega) hko, hw1m k hko]
      apply writeBytes_mem_ne
      intro j hj e
      rw [add_ofNat_add] at e
      exact add_ofNat_ne (k := k) (k' := off + j) (by omega) (by omega) (by omega) e

/-- An entry of a call's stack-passed arguments is a parameter's (location, value, size). -/
theorem stackEnts_mem_inv : ∀ {locs : List ArgLoc} {args bytes : List Nat} {e : Nat × Nat × Nat},
    e ∈ stackEnts ((locs.zip args).zip bytes) →
    ∃ i : Nat, locs[i]? = some (ArgLoc.stack e.1) ∧ args[i]? = some e.2.1 ∧ bytes[i]? = some e.2.2
  | [], _, _, _, h => by simp [stackEnts] at h
  | _ :: _, [], _, _, h => by simp [stackEnts] at h
  | _ :: _, _ :: _, [], _, h => by simp [stackEnts] at h
  | .reg p :: locs, a :: args, b :: bytes, e, h => by
    simp only [List.zip_cons_cons, stackEnts, List.filterMap_cons] at h
    obtain ⟨i, h1, h2, h3⟩ := stackEnts_mem_inv h
    exact ⟨i + 1, by simpa using h1, by simpa using h2, by simpa using h3⟩
  | .stack o :: locs, a :: args, b :: bytes, e, h => by
    simp only [List.zip_cons_cons, stackEnts, List.filterMap_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨0, rfl, rfl, rfl⟩
    · obtain ⟨i, h1, h2, h3⟩ := stackEnts_mem_inv h
      exact ⟨i + 1, by simpa using h1, by simpa using h2, by simpa using h3⟩

/-- **The typed stores, then the call**: `argsAt_after_stores` for arguments in vregs of the
classes `cls`, a float one being a value of a float type (`hcls`). -/
theorem argsAt_after_storesC {Rd F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {sb : Nat}
    {syms : String → Option Nat} (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem)
    (hFP : MemRefinesFP Rd F sb isem) {outB : Nat} (hout : OutArgsOk F outB MR)
    {s : Clif.Signature} (hso : SigStackOk s outB)
    {bytes : List Nat} (hb : sigParamBytes s = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs s = .ok (locs, S)) {args : List Nat} {vals : List Clif.Val}
    (hty : vals.map (·.ty) = Clif.AbiParam.tys s.params) (hal : args.length = vals.length)
    {ρ : Nat → CV} (cls : Nat → RegClass)
    (hv : ∀ (j : Nat) (v : Clif.Val) (x : Nat), vals[j]? = some v → args[j]? = some x → VHolds v (ρ x))
    (hcls : ∀ (j : Nat) (v : Clif.Val) (x : Nat), vals[j]? = some v → args[j]? = some x →
      cls x = .float → v.ty = .f32 ∨ v.ty = .f64)
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : Arm.ArmState} (hmr : MR sl cm w) :
    ∃ w', seqRun isem ((stackEnts ((locs.zip args).zip bytes)).map (argStoreC cls)) ρ w =
        some (.fall ρ w') ∧ MR sl cm w' ∧
      ∀ w2, SameWorldNF F w2 w' →
        ArgsAt s vals ((regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1)) w2 := by
  have hbm := sigParamBytes_eq_map hb
  have hvl : vals.length = s.params.length := by
    have := congrArg List.length hty; simpa [Clif.AbiParam.tys] using this
  have hbl : args.length = bytes.length := by rw [hbm, List.length_map, hal, hvl]
  have hslots := sigStack_facts hso hb hl
  rw [← stackEnts_proj locs args bytes hbl] at hslots
  -- the byte size of parameter `i` is its value's
  have hbv : ∀ (i : Nat) (v : Clif.Val), vals[i]? = some v → bytes[i]? = some v.ty.bytes := by
    intro i v hvi
    rw [hbm, List.getElem?_map]
    have := congrArg (·[i]?) hty
    simp only [List.getElem?_map, Clif.AbiParam.tys, hvi, Option.map_some] at this
    cases hp : s.params[i]? with
    | none => rw [hp] at this; cases this
    | some p => rw [hp] at this; simp only [Option.map_some, Option.some.injEq] at this ⊢; rw [this]
  obtain ⟨w', hrun, hmr', hsp, hrd, -⟩ := argStoresC_run hMR hMem hFP hout cls ρ _ 0 sl cm w hslots
    (fun e he => by
      obtain ⟨q, hq, he⟩ := List.mem_filterMap.mp he
      obtain ⟨⟨l, x⟩, b⟩ := q
      cases l with
      | reg _ => cases he
      | stack o =>
        cases he
        exact sigParamBytes_bytes hb b (List.of_mem_zip hq).2)
    (fun e he hc => by
      obtain ⟨i, -, hx, hbi⟩ := stackEnts_mem_inv he
      have hilt : i < vals.length := by
        rw [← hal]; exact (List.getElem?_eq_some_iff.mp hx).1
      obtain ⟨v, hvi⟩ : ∃ v, vals[i]? = some v := ⟨vals[i], by simp [hilt]⟩
      rw [hbv i v hvi] at hbi
      have he2 : e.2.2 = v.ty.bytes := Option.some.inj hbi.symm
      rw [he2]
      rcases hcls i v _ hvi hx hc with h | h <;> simp [h, Clif.Ty.bytes, Clif.Ty.width]) hmr
  have hlocs : locsOf s = locs := by simp [locsOf, hl]
  have hAv := (hout sl cm w hmr).2.1
  refine ⟨w', hrun, hmr', fun w2 hw2 => ⟨hvl, ?_, ?_⟩⟩
  · rw [regArgVals, hlocs]
    exact allHold_regPairs locs vals args bytes hal.symm hbl hv
  · intro off v hm
    rw [hlocs] at hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    rw [List.getElem?_zip_eq_some] at hi
    obtain ⟨hli, hvi⟩ := hi
    have hilt : i < vals.length := (List.getElem?_eq_some_iff.mp hvi).1
    obtain ⟨x, hx⟩ : ∃ x, args[i]? = some x := ⟨args[i]'(by omega), by simp⟩
    have hbi := hbv i v hvi
    have hme := mem_stackEnts hli hx hbi
    have hr := hrd _ hme
    simp only at hr
    have hend := (slotsOk_bound _ 0 outB hslots (off, v.ty.bytes)
      (List.mem_map.mpr ⟨_, hme, rfl⟩)).2
    have hsp2 : spOf w2 = spOf w' := hw2.1 (.GPR 31#5) (by simp [Masked]) (fun _ h => by cases h)
    have hr2 : Arm.read_mem_bytes v.ty.bytes (spOf w2 + BitVec.ofNat 64 off) w2 =
        Arm.read_mem_bytes v.ty.bytes (spOf w + BitVec.ofNat 64 off) w' := by
      rw [hsp2, hsp]
      apply read_mem_bytes_congr
      intro k hk
      rw [add_ofNat_add]
      exact hw2.2.1 _ (hAv (off + k) (by simp only at hend; omega))
    rw [hr2, hr]
    have hvx := hv i v x hvi hx
    have hw : v.ty.width ≤ v.ty.bytes * 8 ∧ v.ty.bytes * 8 ≤ 64 := by
      have := sigParamBytes_bytes hb _ (List.mem_of_getElem? hbi)
      cases h : v.ty <;> simp_all [Clif.Ty.bytes, Clif.Ty.width]
    simp only [lo64]
    rw [BitVec.setWidth_setWidth_of_le _ hw.2, BitVec.setWidth_setWidth_of_le _ hw.1]
    exact hvx

/-- The frame's typing makes the classes of a call's argument vregs those of their values: a
float-class argument holds a float value. -/
theorem argClasses_of_frame {ctx : Ctx} {fr : Clif.Frame} (hdfg : DFGCons ctx fr) {args : List Nat}
    {vals : List Clif.Val} (hvals : fr.getMany args = .ok vals) :
    ∀ (j : Nat) (v : Clif.Val) (x : Nat), vals[j]? = some v → args[j]? = some x →
      valClassOf ctx x = .float → v.ty = .f32 ∨ v.ty = .f64 := by
  intro j v x hv hx hc
  exact float_of_valClassOf hdfg.2 ((getMany_ok hvals).2 j x v hx hv) hc

/-! ## `bl` and GOT + `blr` with typed arguments and returns -/

theorem liftC_vals (cls : Nat → RegClass) (L : List (Nat × Reg)) (ρ : Nat → CV) :
    (liftC cls L).map (ρ ·.1) = L.map (ρ ·.1) := by
  simp [liftC]

theorem call_sym_lowerInstOkTF {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefineP Pc F env exts MR isem) {f : Clif.Function} {ctx : Ctx}
    (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S)) {ps : List Reg}
    (hps : ps.length = (ext.sig.returns.map retClass).length)
    {st st' : LState} {results : List Nat} (hres : results.length = ext.sig.returns.length)
    (hst' : st'.nextVreg = st.nextVreg + ext.sig.returns.length) :
    LowerInstOkP Rd Pc isem MR env cp ctx (.call fn args) results st
      (outRegsC st (ext.sig.returns.map retClass)) st'
      ((stackEnts ((locs.zip args).zip bytes)).map (argStoreC (valClassOf ctx)) ++
        [.call ⟨.sym ext.name, argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))),
          callDefsC (outDefsC st.nextVreg ps (ext.sig.returns.map retClass))⟩]) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
      simp [vdefs_argStoreC] at hd
    · simp only [List.mem_singleton] at hm
      subst hm
      rw [vdefs_call_symC, outDefsC_vregs _ hps] at hd
      simp only [List.length_map, List.mem_map, List.mem_range] at hd
      obtain ⟨j, hj, rfl⟩ := hd
      omega
  · intro fr cm ρ w hfr hvh hdfg hmr _ hpin
    split
    · rename_i rvals cm' hO
      obtain ⟨ext', vals, g, hx, hvals, hty, hg, hgo, hrty⟩ := instOutcome_call_ok hO
      have hx0 := hx
      rw [hfr, hfunc, hext] at hx
      cases hx
      have hpc := hpin.1 fn args ext vals g rvals cm' rfl hx0 hvals hg hgo
      have hrN : rvals.length = ext.sig.returns.length := by
        have := congrArg List.length hrty; simpa [Clif.AbiParam.tys] using this
      obtain ⟨hlen, hvx⟩ := getMany_ok hvals
      obtain ⟨w1, hrun1, hmr1, hargs⟩ := argsAt_after_storesC hMR hMem hFP hout hso hb hl hty
        hlen.symm (valClassOf ctx) (fun j v x hv hx => hvh x v (hvx j x v hx hv))
        (argClasses_of_frame hdfg hvals) hmr
      obtain ⟨sym, -, hcall, -⟩ := hCR
      have hdl : (callDefsC (outDefsC st.nextVreg ps (ext.sig.returns.map retClass))).length =
          ext.sig.returns.length := by
        simp [callDefsC, outDefsC_length _ hps]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := hcall ext hin g fr.slots cm w1 (.sym ext.name)
        (argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))))
        (callDefsC (outDefsC st.nextVreg ps (ext.sig.returns.map retClass)))
        _ _ vals rvals cm' hg (.inl ⟨rfl, rfl⟩) hdl (hargs w1 (SameWorldNF.refl F w1)) hmr1 hpc hgo
        hrN
      rw [← liftC_vals (valClassOf ctx)] at hi
      have hol' : outs.length = (outDefsC st.nextVreg ps (ext.sig.returns.map retClass)).length := by
        rw [hol, hdl, outDefsC_length _ hps, List.length_map]
      refine ⟨?_, _, _, seqRun_append_fall' isem hrun1 (seqRun_call_symC hi hol'),
        results_callC hps hrN hres (by rw [hol, hdl]) hro, hmr'⟩
      intro mi hmi u hu
      rcases List.mem_append.mp hmi with hmi | hmi
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmi
        rw [vuseNums_argStoreC, List.mem_singleton] at hu
        subst hu
        exact .inr (usesOk_args hvals _ (map_zip_args (mem_args_of_stackEnts he)))
      · simp only [List.mem_singleton] at hmi
        subst hmi
        rw [vuseNums_call_symC, liftC_fst] at hu
        exact .inr (usesOk_args hvals u (map_zip_args (mem_args_of_regPairs hu)))
    · intro h; simp [explicitTrapInst] at h
    · trivial

theorem call_got_lowerInstOkTF {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefineP Pc F env exts MR isem) {f : Clif.Function}
    {ctx : Ctx} (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hcol : ext.colocated = false)
    (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S)) {ps : List Reg}
    (hps : ps.length = (ext.sig.returns.map retClass).length)
    {st st' : LState} {results : List Nat} (hres : results.length = ext.sig.returns.length)
    (hargs : ∀ x ∈ args, x < st.nextVreg)
    (hst' : st'.nextVreg = st.nextVreg + ext.sig.returns.length + 1) :
    LowerInstOkP Rd Pc isem MR env cp ctx (.call fn args) results st
      (outRegsC st (ext.sig.returns.map retClass)) st'
      ((stackEnts ((locs.zip args).zip bytes)).map (argStoreC (valClassOf ctx)) ++
       [.loadExtNameGot (.vreg (st.nextVreg + ext.sig.returns.length) .int) ext.name,
       .call ⟨.reg (.vreg (st.nextVreg + ext.sig.returns.length) .int),
        argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))),
        callDefsC (outDefsC st.nextVreg ps (ext.sig.returns.map retClass))⟩]) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
      simp [vdefs_argStoreC] at hd
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · rw [vdefs_got_ctl] at hd
        simp only [List.mem_singleton] at hd
        omega
      · rw [vdefs_call_regC, outDefsC_vregs _ hps] at hd
        simp only [List.length_map, List.mem_map, List.mem_range] at hd
        obtain ⟨j, hj, rfl⟩ := hd
        omega
  · intro fr cm ρ w hfr hvh hdfg hmr _ hpin
    split
    · rename_i rvals cm' hO
      obtain ⟨ext', vals, g, hx, hvals, hty, hg, hgo, hrty⟩ := instOutcome_call_ok hO
      have hx0 := hx
      rw [hfr, hfunc, hext] at hx
      cases hx
      have hpc := hpin.1 fn args ext vals g rvals cm' rfl hx0 hvals hg hgo
      have hrN : rvals.length = ext.sig.returns.length := by
        have := congrArg List.length hrty; simpa [Clif.AbiParam.tys] using this
      obtain ⟨hlen, hvx⟩ := getMany_ok hvals
      obtain ⟨w1, hrun1, hmr1, hargsAt⟩ := argsAt_after_storesC hMR hMem hFP hout hso hb hl hty
        hlen.symm (valClassOf ctx) (fun j v x hv hx => hvh x v (hvx j x v hx hv))
        (argClasses_of_frame hdfg hvals) hmr
      obtain ⟨sym, hgot, hcall, -⟩ := hCR
      obtain ⟨w2, hw2, hsw⟩ := hgot (.vreg (st.nextVreg + ext.sig.returns.length) .int) ext.name w1
      have hmr2 := hMR _ _ _ _ hsw hmr1
      have hrun2 := seqRun_got (F := F) (ρ := ρ) hw2
      generalize ht : st.nextVreg + ext.sig.returns.length = t at hrun2 hw2 hsw ⊢
      have hρ1 : ∀ x ∈ args, upd ρ t (ofX (sym ext.name)) x = ρ x := by
        intro x hx
        have := hargs x hx
        simp only [upd]
        rw [if_neg (by omega)]
      have huses : (regPairsOf ((locs.zip args).zip bytes)).map (upd ρ t (ofX (sym ext.name)) ·.1) =
          (regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1) := by
        apply List.map_congr_left
        intro q hq
        exact hρ1 _ (map_zip_args (mem_args_of_regPairs (List.mem_map_of_mem hq)))
      have hdl : (callDefsC (outDefsC st.nextVreg ps (ext.sig.returns.map retClass))).length =
          ext.sig.returns.length := by
        simp [callDefsC, outDefsC_length _ hps]
      have ht1 : upd ρ t (ofX (sym ext.name)) t = ofX (sym ext.name) := by simp [upd]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := hcall ext hin g fr.slots cm w2
        (.reg (.vreg t .int)) (argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))))
        (callDefsC (outDefsC st.nextVreg ps (ext.sig.returns.map retClass)))
        (upd ρ t (ofX (sym ext.name)) t ::
          (regPairsOf ((locs.zip args).zip bytes)).map (upd ρ t (ofX (sym ext.name)) ·.1))
        ((regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1)) vals rvals cm' hg
        (.inr ⟨_, rfl, hcol, by rw [ht1, huses]⟩) hdl (hargsAt w2 hsw) hmr2 hpc hgo hrN
      rw [← liftC_vals (valClassOf ctx)] at hi
      have hol' : outs.length = (outDefsC st.nextVreg ps (ext.sig.returns.map retClass)).length := by
        rw [hol, hdl, outDefsC_length _ hps, List.length_map]
      have hrun3 := seqRun_call_regC hi hol'
      refine ⟨?_, _, _, seqRun_append_fall' isem hrun1
          (seqRun_append_fall' isem (ms1 := [_]) (ms2 := [_]) hrun2 hrun3),
        results_callC hps hrN hres (by rw [hol, hdl]) hro, hmr'⟩
      intro mi hmi u hu
      rcases List.mem_append.mp hmi with hmi | hmi
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmi
        rw [vuseNums_argStoreC, List.mem_singleton] at hu
        subst hu
        exact .inr (usesOk_args hvals _ (map_zip_args (mem_args_of_stackEnts he)))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmi
        rcases hmi with rfl | rfl
        · simp [vuseNums_got_ctl] at hu
        · rw [vuseNums_call_regC, liftC_fst] at hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact .inl (by omega)
          · exact .inr (usesOk_args hvals u (map_zip_args (mem_args_of_regPairs hu)))
    · intro h; simp [explicitTrapInst] at h
    · trivial

set_option maxHeartbeats 5000000 in
/-- **`bl`** (`rule_lower_2508`) over float-capable contexts, any extern signature. -/
theorem call_bl_ruleOkTF {p : Program} (hp : Data p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefineP Pc F env exts MR isem) :
    CallRuleOkTFP Rd Pc isem MR env cp exts outB p rule_lower_2508 := by
  intro f ctx hctx hexts ii info inst hi hcl hstk cfg hc m n st tr env' s1 out st' tr' hm hn
    hvb _ hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have hd := hctx.data ii info inst hi hcl
  cases hp
  ctl_inv [*, rule_lower_2508] at hmatch
  have hinfo := ‹ctx.insts[ii]? = some _›
  rw [hi] at hinfo
  cases hinfo
  rw [← ‹V.data 152 6 _ = info.data›] at hd
  obtain ⟨fn, args, ext, rfl, hext, hfs⟩ := instData_call_inv hd
  simp only [List.cons.injEq, and_true] at hfs
  obtain ⟨rfl, rfl⟩ := hfs
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  have hres := call_results_lengthC hctx hi hcl hext
  simp only [ext_value_list_slice_iff, ext_func_ref_data_iff, hfn] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2508] at heval
  isel_destruct; subst_vars
  simp only [ctor_abi_sig_iff, ctor_gen_call_output_typed, ctor_put_in_regs_vec_iff,
    ctor_gen_call_rets_iff, ctor_try_call_none_iff, ctor_output_vec_iff, regsClasses_outRegsC,
    outRegsC_length,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate] at *
  isel_destruct; subst_vars
  simp only [show (4:Nat) < 10 from by decide, ite_true] at *
  subst_vars
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, regsClasses_outRegsC, outRegsC_single,
    outRegsC_length, Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegC hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_genC _ _ _ (valClassOf ctx) hb hl,
    ctor_gen_call_info_gen _ _ _ _ _ _ _ hl,
    mapM_single_map, Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_info_gen _ _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hps := retRegsC_lengthC _ _ _ ‹retRegsC _ 0 0 = some _›
  simp only [ctor_output_vec_iff] at *
  isel_destruct; subst_vars
  have h638 := ‹ApplyInternal _ _ _ _ 46 638 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h638
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_call] at hmi
  cases hmi
  rw [callDefsC_outDefsC] at hs2
  refine ⟨_, ?_, _, rfl, call_sym_lowerInstOkTF hMR hMem hFP hout hCR hctx.func hext
    (hexts fn _ hext) (hstk fn args _ rfl hext) hb hl hps hres
    (by rw [hs2, hs1]; simp [LState.emit, freshC_nextVreg])⟩
  rw [hs2, hs1]; simp [LState.emit, freshC_emitted]

set_option maxHeartbeats 5000000 in
/-- **GOT + `blr`** (`rule_lower_2518`) over float-capable contexts, any extern signature. -/
theorem call_got_ruleOkTF {p : Program} (hp : Data p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefineP Pc F env exts MR isem) :
    CallRuleOkTFP Rd Pc isem MR env cp exts outB p rule_lower_2518 := by
  intro f ctx hctx hexts ii info inst hi hcl hstk cfg hc m n st tr env' s1 out st' tr' hm hn
    hvb hfirst hmatch heval
  have hnot : ∀ {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc},
      info.data = .data 152 6 [.data 151 8 [], .values args, .op (.funcRef fn)] →
      ctx.func.extern? fn = some ext → ext.colocated = false :=
    fun hd he => call_got_not_colocated hp hi hfirst hd he
  clear hfirst
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kL := fun n (hn : 40 ≤ n) nm d s v s' h => load_ext_name_ok_ctl hp (ctx := ctx) hc (n := n)
    (nm := nm) (d := d) (s := s) (v := v) (s' := s') hn h
  have hd := hctx.data ii info inst hi hcl
  cases hp
  ctl_inv [*, rule_lower_2518] at hmatch
  have hinfo := ‹ctx.insts[ii]? = some _›
  rw [hi] at hinfo
  cases hinfo
  rw [← ‹V.data 152 6 _ = info.data›] at hd
  obtain ⟨fn, args, ext, rfl, hext, hfs⟩ := instData_call_inv hd
  simp only [List.cons.injEq, and_true] at hfs
  obtain ⟨rfl, rfl⟩ := hfs
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  have hcol : ext.colocated = false := hnot ‹V.data 152 6 _ = info.data›.symm hfn
  clear hnot
  have hres := call_results_lengthC hctx hi hcl hext
  simp only [ext_value_list_slice_iff, ext_func_ref_data_iff, hfn] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2518] at heval
  isel_destruct; subst_vars
  simp only [ctor_abi_sig_iff, ctor_gen_call_output_typed, ctor_put_in_regs_vec_iff,
    ctor_gen_call_rets_iff, ctor_try_call_none_iff, ctor_output_vec_iff, ctor_box_external_name_iff,
    regsClasses_outRegsC, outRegsC_length,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate] at *
  isel_destruct; subst_vars
  simp only [show (4:Nat) < 10 from by decide, ite_true] at *
  subst_vars
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, regsClasses_outRegsC, outRegsC_single,
    outRegsC_length, Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hbelow := mapM_valueReg_below hvb ‹List.mapM ctx.valueReg? args = some _›
  have hrs := mapM_valueRegC hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_genC _ _ _ (valClassOf ctx) hb hl, mapM_single_map,
    Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  have h570 := ‹ApplyInternal _ _ _ _ 27 570 _ _ _ _›
  obtain ⟨rfl, hs0⟩ := kL _ (by omega) _ _ _ _ _ h570
  simp only [ctor_gen_call_ind_info_gen _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true,
    ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hps := retRegsC_lengthC _ _ _ ‹retRegsC _ 0 0 = some _›
  simp only [ctor_output_vec_iff] at *
  isel_destruct; subst_vars
  have h639 := ‹ApplyInternal _ _ _ _ 46 639 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h639
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_callInd] at hmi
  cases hmi
  have hfr : ∀ (cs : List RegClass) (e : Array MInst),
      (({ freshC st cs with emitted := e } : LState).fresh .int).1 =
      .vreg (st.nextVreg + cs.length) .int := fun cs e => by
    simp [LState.fresh, freshC_nextVreg]
  rw [hfr, callDefsC_outDefsC] at hs2
  rw [hfr] at hs0
  refine ⟨_, ?_, _, rfl, call_got_lowerInstOkTF hMR hMem hFP hout hCR hctx.func hext
    (hexts fn _ hext) hcol (hstk fn args _ rfl hext) hb hl hps hres hbelow
    (by rw [hs2, hs1, hs0]; simp [LState.emit, LState.fresh, freshC_nextVreg])⟩
  rw [hs2, hs1, hs0]
  simp only [LState.emit, LState.fresh, freshC_emitted]
  rw [← Array.toList_inj]
  simp

/-! ## Assembly -/

/-- **`CallRulesCorrectTFP`**: under the pinned callee contract and the guarded integer and float
memory forms, the `call` rules of `lower` (1031, 1032) are correct over float-capable contexts,
for calls of any extern signature (`f32`/`f64` arguments in v0..v7 or on the stack, `f32`/`f64`
returns from v0..v7). -/
theorem callRulesCorrectTFP_program : CallRulesCorrectTFP program := by
  intro Rd Pc F isem MR env cp exts sb syms outB _ hMR hMem hFP hout hCR r hr hroot
  simp only [callRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
  rcases hroot with h | h
  · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2508 (by rw [h]; rfl)]
    exact call_bl_ruleOkTF data_program hMR hMem hFP hout hCR
  · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2518 (by rw [h]; rfl)]
    exact call_got_ruleOkTF data_program hMR hMem hFP hout hCR

/-- The integer-argument family over typed contexts (`CtxT`) is an instance of the float one (a
rule correct for every extern signature on `CallCtxT` contexts is `CallRuleOkTP`). -/
theorem callRuleOkTP_of_TFP {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {exts : List Clif.ExtFunc} {outB : Nat} {p : Program}
    {r : Rule} (h : CallRuleOkTFP Rd Pc isem MR env cp exts outB p r) :
    CallRuleOkTP Rd Pc isem MR env cp exts outB p r :=
  fun f ctx hctx hexts ii info inst hi hcl _ hstk =>
    h f ctx hctx.inv.toCallCtx hexts ii info inst hi hcl hstk

/-! ## `CallCtxT`, decided -/

open Driver in
/-- **`CallCtxT f ctx`, decided** (`ctxOkT`'s instruction-data, result-type and value-register
checks). -/
def callCtxOkB (f : Clif.Function) (ctx : Ctx) : Bool :=
  decide (ctx.func = f) &&
  ctx.insts.toList.all (fun info => match info.clif with
    | some i =>
      (match instData f i with
        | .ok d => d == info.data
        | .error _ => false) && ctxResTysOk f info i
    | none => true) &&
  (List.range ctx.valReg.size).all (fun x => match ctx.valueReg? x with
    | some r => decide (r = .vreg x (valClassOf ctx x))
    | none => true)

open Driver in
theorem callCtxOkB_sound {f : Clif.Function} {ctx : Ctx} (h : callCtxOkB f ctx = true) :
    CallCtxT f ctx := by
  simp only [callCtxOkB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hfunc, hinsts⟩, hreg⟩ := h
  have hmem : ∀ {ii : Nat} {info : IInfo}, ctx.insts[ii]? = some info → info ∈ ctx.insts.toList :=
    fun hi => by rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hi
  have hinst : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
      info.clif = some inst →
      (instData f inst = .ok info.data) ∧
      (∃ tys, inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) =
          some tys ∧
        info.resTys = tys.map CTy.ofClif ∧ info.results.length = tys.length) := by
    intro ii info inst hi hc
    have := List.all_eq_true.mp hinsts info (hmem hi)
    rw [hc] at this
    simp only [Bool.and_eq_true] at this
    obtain ⟨h1, h2⟩ := this
    refine ⟨?_, ?_⟩
    · cases hd : instData f inst with
      | ok d => rw [hd] at h1; simpa using h1
      | error e => rw [hd] at h1; simp at h1
    · have h2' : ctxResTysOk f info inst = true := h2
      unfold ctxResTysOk at h2'
      cases hty : inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) with
      | none => rw [hty] at h2'; simp at h2'
      | some tys =>
        have h2'' : (decide (info.resTys = tys.map CTy.ofClif) &&
            decide (info.results.length = tys.length)) = true := by
          rw [hty] at h2'; exact h2'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2''
        exact ⟨tys, rfl, h2''.1, h2''.2⟩
  refine ⟨hfunc, fun ii info inst hi hc => (hinst ii info inst hi hc).1,
    fun ii info inst hi hc => (hinst ii info inst hi hc).2, ?_⟩
  intro x r hx
  have := all_range hreg (lt_valReg hx)
  rw [hx] at this
  simpa using this

end Backend.Proof
