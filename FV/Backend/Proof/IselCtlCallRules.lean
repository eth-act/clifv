import FV.Backend.Proof.IselCtlCall
import FV.Backend.Proof.IselFamily
import FV.Backend.Proof.LowerLemmas
import FV.Arm.Memory.MemoryProofs

/-!
# Family Ctl: the `call` rules (rule theorems)

`CallRuleOk` for `rule_lower_2508` (`bl name`, rule id 1031) and `rule_lower_2518`
(`loadExtNameGot t name; blr t`, rule id 1032).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

theorem ofV_loadExtNameGot_ctl (r : Reg) (nm : String) :
    MInst.ofV (.data 58 129 [.reg r, .op (.extName nm)]) = some (.loadExtNameGot r nm) := rfl

set_option maxRecDepth 20000 in
theorem variantNames_Call_fmt : (variantNames 152)[6]? = some "Call" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Call_op : (variantNames 151)[8]? = some "Call" := rfl

/-- A matched `Call (Call) fs` is a `call` of an extern. -/
theorem instData_call_inv {f : Clif.Function} {cl : Clif.Inst} {fs : List V}
    (h : instData f cl = .ok (.data 152 6 (.data 151 8 [] :: fs))) :
    ∃ fn args ext, cl = .call fn args ∧ f.extern? fn = some ext ∧
      fs = [.values args, .op (.funcRef fn)] := by
  obtain ⟨hf, ho⟩ := instData_inv_names h
  rw [variantNames_Call_fmt] at hf
  rw [variantNames_Call_op] at ho
  have hn : instNames cl = ("Call", "Call") :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨fn, args, rfl⟩ : ∃ fn args, cl = .call fn args := by
    cases cl <;> simp [instNames] at hn ⊢
  simp only [instData] at h
  cases he : f.extern? fn with
  | none => rw [he] at h; cases h
  | some ext =>
    rw [he] at h
    simp only at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      injection h3 with _ h4
      exact ⟨fn, args, ext, rfl, he, h4⟩
    · cases h

theorem ctor_gen_call_args_bytes {ctx : Ctx} {st : LState} {s : Clif.Signature}
    {rss : List (List Reg)} {v : V} {st' : LState}
    (h : externCtor ctx T.gen_call_args [.op (.sig s), .regsVec rss] st = .ok (v, st')) :
    ∃ bytes, sigParamBytes s = .ok bytes := by
  have : externCtor ctx T.gen_call_args [.op (.sig s), .regsVec rss] st =
      match sigArgLocs s, rss.mapM single? with
      | .ok (locs, _), some rs =>
        let bytes := match sigParamBytes s with | .ok b => b | _ => []
        let r := (((locs.zip rs).zip bytes).foldl argStep (#[], st))
        .ok (.op (.callArgs r.1.toList), r.2)
      | .error e, _ => .unmodeled s!"gen_call_args: {e}"
      | _, none => .unmodeled "gen_call_args: multi-register value" := rfl
  rw [this] at h
  cases hb : sigParamBytes s with
  | ok b => exact ⟨b, rfl⟩
  | error e =>
    have hl : sigArgLocs s = .error e := by
      have hb' : sigArgs s = .error e := hb
      simp only [sigArgLocs, hb']
      rfl
    rw [hl] at h
    cases rss.mapM single? <;> simp at h

theorem ctor_gen_call_args_locs {ctx : Ctx} {st : LState} {s : Clif.Signature}
    {rss : List (List Reg)} {v : V} {st' : LState}
    (h : externCtor ctx T.gen_call_args [.op (.sig s), .regsVec rss] st = .ok (v, st')) :
    ∃ locs S, sigArgLocs s = .ok (locs, S) := by
  have : externCtor ctx T.gen_call_args [.op (.sig s), .regsVec rss] st =
      match sigArgLocs s, rss.mapM single? with
      | .ok (locs, _), some rs =>
        let bytes := match sigParamBytes s with | .ok b => b | _ => []
        let r := (((locs.zip rs).zip bytes).foldl argStep (#[], st))
        .ok (.op (.callArgs r.1.toList), r.2)
      | .error e, _ => .unmodeled s!"gen_call_args: {e}"
      | _, none => .unmodeled "gen_call_args: multi-register value" := rfl
  rw [this] at h
  cases hl : sigArgLocs s with
  | ok r => exact ⟨r.1, r.2, rfl⟩
  | error e => rw [hl] at h; cases rss.mapM single? <;> simp at h

theorem outRegs_single (st : LState) (n : Nat) :
    (outRegs st n).mapM single? =
      some ((List.range n).map fun j => Reg.vreg (st.nextVreg + j) .int) := by
  rw [show outRegs st n = ((List.range n).map fun j => Reg.vreg (st.nextVreg + j) .int).map
    (fun r => [r]) by simp [outRegs, Function.comp_def]]
  exact mapM_single_map _

theorem outRegs_length (st : LState) (n : Nat) : (outRegs st n).length = n := by
  simp [outRegs]

/-! ## Operand view of `call` -/

/-- `(preg, vreg)` pairs of a call's defs. -/
def callDefs (D : List (Reg × Nat)) : List (Reg × Reg) := D.map fun q => (q.1, Reg.vreg q.2 .int)

/-- The operands of a call's defs: fixed late defs. -/
def callDefOps (D : List (Reg × Nat)) : List Operand :=
  D.map fun q => (⟨q.2, .int, .def, .late, .fixed q.1⟩ : Operand)

open Driver in
theorem mapM_callDefs (D : List (Reg × Nat)) : ∀ (s : Array Operand),
    ((callDefs D).mapM
      (fun (x : Reg × Reg) => do let r ← collectOp (OpSpec.fixedDef x.1) x.2; pure (x.1, r))).run s =
      .ok (callDefs D, s ++ (callDefOps D).toArray) := by
  induction D with
  | nil => intro s; simp [callDefs, callDefOps] <;> rfl
  | cons q D ih =>
    intro s
    simp only [callDefs, callDefOps, List.map_cons, List.mapM_cons, StateT.run_bind] at ih ⊢
    have h1 : (collectOp (OpSpec.fixedDef q.1) (Reg.vreg q.2 .int)).run s =
        .ok (Reg.vreg q.2 .int, s.push ⟨q.2, .int, .def, .late, .fixed q.1⟩) := rfl
    rw [h1, except_ok_bind, StateT.run_pure, except_pure, except_ok_bind, ih, except_ok_bind,
      StateT.run_pure, except_pure]
    simp

open Driver in
theorem operands_call_sym (nm : String) (L : List (Nat × Reg)) (D : List (Reg × Nat)) :
    (MInst.call ⟨.sym nm, retPairs L, callDefs D⟩).operands =
      .ok (retOps L ++ callDefOps D).toArray := by
  rw [operands_eq]
  simp only [MInst.visitOperands, StateT.run_bind, StateT.run_pure, except_ok_bind, mapM_fixedUse,
    mapM_callDefs]
  simp [bind, Except.bind, StateT.run, pure, StateT.pure, Except.pure]

theorem instOutcome_call_ok {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm : Clif.Mem} {fn : Clif.FnRef} {args : List Clif.ValueId} {rvals : List Clif.Val}
    {cm' : Clif.Mem} (h : instOutcome env cp fr cm (.call fn args) = .ok (rvals, cm')) :
    ∃ ext vals g, fr.func.extern? fn = some ext ∧ fr.getMany args = .ok vals ∧
      vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params ∧ env.extern ext.name = some g ∧
      g vals cm = .returned rvals cm' ∧ rvals.map (·.ty) = Clif.AbiParam.tys ext.sig.returns := by
  simp only [instOutcome] at h
  cases he : fr.func.extern? fn with
  | none => simp [he, Clif.Res.ofOption, bind, Clif.Res.bind] at h
  | some ext =>
    cases hv : fr.getMany args with
    | ok vals =>
      by_cases ht : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params
      · simp only [he, hv, Clif.Res.ofOption, bind, Clif.Res.bind, Clif.checkTys, ht, beq_self_eq_true,
          Clif.Res.check_true, pure] at h
        split at h
        · cases h
        · split at h
          · rename_i g hg
            split at h
            · rename_i rv mem' hgo
              split at h
              · rename_i hrt
                cases h
                exact ⟨ext, vals, g, rfl, rfl, ht, hg, hgo, by simpa using hrt⟩
              · cases h
            all_goals cases h
          · cases h
      · simp only [he, hv, Clif.Res.ofOption, bind, Clif.Res.bind, Clif.checkTys] at h
        rw [show (List.map (fun x => x.ty) vals == Clif.AbiParam.tys ext.sig.params) = false from
          by simpa using ht, Clif.Res.check_false] at h
        cases h
    | trap c => simp [he, hv, Clif.Res.ofOption, bind, Clif.Res.bind] at h
    | stuck m => simp [he, hv, Clif.Res.ofOption, bind, Clif.Res.bind] at h

theorem writeV_notMem_ctl {V : Type} : ∀ (dv : List (Operand × V)) (ρ : Nat → V) (y : Nat),
    y ∉ dv.map (·.1.vreg) → writeV ρ dv y = ρ y
  | [], ρ, y, _ => rfl
  | a :: dv, ρ, y, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [writeV_cons, writeV_notMem_ctl dv _ y h.2]
    simp [upd, h.1]

theorem writeV_nodup_ctl {V : Type} : ∀ (dv : List (Operand × V)) (ρ : Nat → V) (j : Nat) (o : Operand)
    (v : V), (dv.map (·.1.vreg)).Nodup → dv[j]? = some (o, v) → writeV ρ dv o.vreg = v
  | [], ρ, j, o, v, _, h => by simp at h
  | a :: dv, ρ, 0, o, v, hn, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [writeV_cons, writeV_notMem_ctl dv _ _ hn.1]
    simp [upd]
  | a :: dv, ρ, j + 1, o, v, hn, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [writeV_cons]
    exact writeV_nodup_ctl dv _ j o v hn.2 h

theorem filter_isUse_callDefOps (D : List (Reg × Nat)) : (callDefOps D).filter Operand.isUse = [] := by
  induction D with
  | nil => rfl
  | cons q D ih => simp only [callDefOps, List.map_cons] at ih ⊢; rw [List.filter_cons_of_neg (by simp [Operand.isUse, Operand.isDef, Operand.isEarly, Operand.isLate]), ih]

theorem filter_isDef_callDefOps (D : List (Reg × Nat)) :
    (callDefOps D).filter Operand.isDef = callDefOps D := by
  induction D with
  | nil => rfl
  | cons q D ih => simp only [callDefOps, List.map_cons] at ih ⊢; rw [List.filter_cons_of_pos (by simp [Operand.isUse, Operand.isDef, Operand.isEarly, Operand.isLate]), ih]

theorem filter_isDef_retOps' (L : List (Nat × Reg)) : (retOps L).filter Operand.isDef = [] := by
  induction L with
  | nil => rfl
  | cons q L ih => simp only [retOps, List.map_cons] at ih ⊢; rw [List.filter_cons_of_neg (by simp [Operand.isUse, Operand.isDef, Operand.isEarly, Operand.isLate]), ih]

theorem vuses_call {V : Type} (L : List (Nat × Reg)) (D : List (Reg × Nat)) (ρ : Nat → V) :
    vuses (retOps L ++ callDefOps D).toArray ρ = L.map (ρ ·.1) := by
  simp only [vuses, List.toList_toArray, List.filter_append, filter_retOps, filter_isUse_callDefOps,
    List.append_nil]
  simp [retOps]

theorem defs_call (L : List (Nat × Reg)) (D : List (Reg × Nat)) :
    (retOps L ++ callDefOps D).filter Operand.isDef = callDefOps D := by
  simp only [List.filter_append, filter_isDef_retOps', filter_isDef_callDefOps,
    List.nil_append]

theorem zip_callDefOps_early {V : Type} : ∀ (D : List (Reg × Nat)) (outs : List V),
    ((callDefOps D).zip outs).filter (·.1.isEarly) = [] ∧
      ((callDefOps D).zip outs).filter (·.1.isLate) = (callDefOps D).zip outs
  | [], outs => by simp [callDefOps]
  | q :: D, [] => by simp [callDefOps]
  | q :: D, o :: outs => by
    obtain ⟨h1, h2⟩ := zip_callDefOps_early D outs
    simp only [callDefOps, List.map_cons, List.zip_cons_cons] at h1 h2 ⊢
    rw [List.filter_cons_of_neg (by simp [Operand.isUse, Operand.isDef, Operand.isEarly, Operand.isLate]), h1, List.filter_cons_of_pos (by simp [Operand.isUse, Operand.isDef, Operand.isEarly, Operand.isLate]), h2]
    exact ⟨rfl, rfl⟩

theorem vdefUpd_call {V : Type} (L : List (Nat × Reg)) (D : List (Reg × Nat)) (outs : List V)
    (ρ : Nat → V) :
    vdefUpd (retOps L ++ callDefOps D).toArray outs ρ = writeV ρ ((callDefOps D).zip outs) := by
  simp only [vdefUpd, List.toList_toArray, defs_call, (zip_callDefOps_early D outs).1,
    (zip_callDefOps_early D outs).2]
  rfl

theorem vuseNums_call_sym (nm : String) (L : List (Nat × Reg)) (D : List (Reg × Nat)) :
    vuseNums (.call ⟨.sym nm, retPairs L, callDefs D⟩) = L.map (·.1) := by
  simp only [vuseNums, operands_call_sym, List.toList_toArray, List.filter_append, filter_retOps,
    filter_isUse_callDefOps, List.append_nil]
  simp [retOps]

theorem vdefs_call_sym (nm : String) (L : List (Nat × Reg)) (D : List (Reg × Nat)) :
    vdefs (.call ⟨.sym nm, retPairs L, callDefs D⟩) = D.map (·.2) := by
  simp only [vdefs, operands_call_sym, List.toList_toArray, defs_call]
  simp [callDefOps]

theorem seqRun_call_sym {isem : Sem} {nm : String} {L : List (Nat × Reg)} {D : List (Reg × Nat)}
    {ρ : Nat → CV} {w w' : Arm.ArmState} {outs : List CV}
    (h : isem (.call ⟨.sym nm, retPairs L, callDefs D⟩) (L.map (ρ ·.1)) w = some (outs, w', .next))
    (hl : outs.length = D.length) :
    seqRun isem [.call ⟨.sym nm, retPairs L, callDefs D⟩] ρ w =
      some (.fall (writeV ρ ((callDefOps D).zip outs)) w') := by
  simp only [seqRun, operands_call_sym, vuses_call, h, List.toList_toArray, defs_call]
  have hl' : outs.length = (callDefOps D).length := by simp [callDefOps, hl]
  simp only [hl', ↓reduceIte, vdefUpd_call]
  rfl

theorem zip_self_ctl {α : Type} : ∀ (l : List α), l.zip l = l.map fun a => (a, a)
  | [] => rfl
  | a :: l => by simp [zip_self_ctl l]

/-- The output registers `outRegs` from a base vreg. -/
def outRegs' (b n : Nat) : List (List Reg) := (List.range n).map fun j => [Reg.vreg (b + j) .int]

/-- The defs of a call with `n` results: `x_j` into vreg `b + j`. -/
def outDefs (b n : Nat) : List (Reg × Nat) := (List.range n).map fun j => (Reg.x j, b + j)

theorem callDefs_outDefs (b n : Nat) :
    (List.map Reg.x (List.range n)).zip (List.map (fun j => Reg.vreg (b + j) .int) (List.range n)) =
      callDefs (outDefs b n) := by
  simp [callDefs, outDefs, List.zip_map_left, List.zip_map_right, Function.comp_def]
  rw [zip_self_ctl]; simp

theorem uses_retPairs (args : List Nat) (L : List Reg) :
    (args.map fun x => Reg.vreg x .int).zip L = retPairs (args.zip L) := by
  simp [retPairs, List.zip_map_left, Prod.map]

theorem allHold_args {fr : Clif.Frame} {ρ : Nat → CV} (hvh : ValsHeld fr ρ) {args : List Nat}
    {vals : List Clif.Val} (hvals : fr.getMany args = .ok vals) : AllHold vals (args.map ρ) := by
  obtain ⟨hlen, hv⟩ := getMany_ok hvals
  refine ⟨by simp [hlen], fun j v x hvj hxj => ?_⟩
  rw [List.getElem?_map] at hxj
  cases hy : args[j]? with
  | none => rw [hy] at hxj; cases hxj
  | some y => rw [hy] at hxj; cases hxj; exact hvh y v (hv j y v hy hvj)

theorem usesOk_args {fr : Clif.Frame} {args : List Nat} {vals : List Clif.Val}
    (hvals : fr.getMany args = .ok vals) : ∀ u ∈ args, (fr.regs u).isSome := by
  obtain ⟨hlen, hv⟩ := getMany_ok hvals
  intro u hu
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
  obtain ⟨v, hv'⟩ : ∃ v, vals[j]? = some v := ⟨vals[j]'(by omega), by simp [hj, hlen]⟩
  rw [hv (j := j) _ v (by simp [hj]) hv']
  rfl

/-- The call's result vregs hold the extern's results. -/
theorem resultsHeld_call {fr : Clif.Frame} {ρ : Nat → CV} {b : Nat} {rvals : List Clif.Val}
    {outs : List CV} (hro : AllHold rvals outs) :
    ResultsHeld b fr (outRegs' b rvals.length) rvals
      (writeV ρ ((callDefOps (outDefs b rvals.length)).zip outs)) := by
  refine ⟨by simp [outRegs'], fun j rs v hrs hvj => ?_⟩
  have hjN : j < rvals.length := by
    rcases Nat.lt_or_ge j rvals.length with h | h
    · exact h
    · simp [outRegs', h] at hrs
  simp only [outRegs', List.getElem?_map, List.getElem?_range hjN, Option.map_some,
    Option.some.injEq] at hrs
  subst hrs
  refine ⟨b + j, .int, rfl, .inl (by omega), ?_⟩
  obtain ⟨x, hx⟩ : ∃ x, outs[j]? = some x :=
    ⟨outs[j]'(by rw [← hro.1]; exact hjN), by simp⟩
  have hk : ((callDefOps (outDefs b rvals.length)).zip outs).map (·.1.vreg) =
      (List.range rvals.length).map (b + ·) := by
    rw [show (fun q : Operand × CV => q.1.vreg) = Operand.vreg ∘ Prod.fst from rfl, ← List.map_map,
      List.map_fst_zip (by simp [callDefOps, outDefs, hro.1])]
    simp [callDefOps, outDefs]
  have hnd : (((callDefOps (outDefs b rvals.length)).zip outs).map (·.1.vreg)).Nodup := by
    rw [hk]
    exact List.Pairwise.map _ (fun a c h e => h (by omega)) List.nodup_range
  have hget : ((callDefOps (outDefs b rvals.length)).zip outs)[j]? =
      some (⟨b + j, .int, .def, .late, .fixed (.x j)⟩, x) := by
    rw [List.getElem?_zip_eq_some]
    simp [callDefOps, outDefs, hx, hjN]
  rw [writeV_nodup_ctl _ ρ j _ x hnd hget]
  exact hro.2 j v x hvj hx

theorem outRegs_eq (st : LState) (n : Nat) : outRegs st n = outRegs' st.nextVreg n := rfl

/-- The results of a call: its defs are one per ABI return (`sigRets`); the first ones hold the
extern's results. An `sret` call without returns has no CLIF result (its def, the returned
struct pointer, is not a CLIF value). -/
theorem results_call {fr : Clif.Frame} {ρ : Nat → CV} {b : Nat} {rvals : List Clif.Val}
    {outs : List CV} {results : List Nat} {s : Clif.Signature}
    (hrN : rvals.length = s.returns.length) (hres : results.length = s.returns.length)
    (hol : outs.length = (sigRets s).length) (hro : PrefixHold rvals outs) :
    results = [] ∨ ResultsHeld b fr (outRegs' b (sigRets s).length) rvals
      (writeV ρ ((callDefOps (outDefs b (sigRets s).length)).zip outs)) := by
  rcases sigRets_cases s with h | ⟨h0, -⟩
  · right
    rw [h, ← hrN]
    exact resultsHeld_call (hro.allHold (by rw [hol, h, hrN]))
  · left
    rw [h0] at hres
    exact List.eq_nil_of_length_eq_zero hres

/-- The number of CLIF results of a `call` is its callee's number of returns (`CtxInv.resTys`). -/
theorem call_results_length {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some (.call fn args))
    (hext : f.extern? fn = some ext) : info.results.length = ext.sig.returns.length := by
  obtain ⟨tys, htys, -, hl⟩ := hctx.resTys ii info _ hi hc
  simp only [Clif.Inst.resultTypes, hext, Option.map_some, Option.some.injEq] at htys
  rw [hl, ← htys, List.length_map]

/-- The CLIF call's facts in the `ok` case, with the lowering's view of the signature. -/
theorem call_ok_facts {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) {fr : Clif.Frame} (hfr : fr.func = ctx.func) {cm cm' : Clif.Mem}
    {rvals : List Clif.Val} (hO : instOutcome env cp fr cm (.call fn args) = .ok (rvals, cm')) :
    ∃ vals g, fr.getMany args = .ok vals ∧ vals.length = ext.sig.params.length ∧
      args.length = ext.sig.params.length ∧ env.extern ext.name = some g ∧
      g vals cm = .returned rvals cm' ∧ rvals.length = ext.sig.returns.length := by
  obtain ⟨ext', vals, g, hx, hvals, hty, hg, hgo, hrty⟩ := instOutcome_call_ok hO
  rw [hfr, hctx.func, hext] at hx
  cases hx
  have hl := congrArg List.length hty
  have hr := congrArg List.length hrty
  simp only [List.length_map, Clif.AbiParam.tys] at hl hr
  exact ⟨vals, g, hvals, hl, (getMany_ok hvals).1 ▸ hl, hg, hgo, hr⟩

/-! ## The outgoing stack-argument stores (agent/stack-tls-proof) -/

theorem storeOpOfBytes_facts {b : Nat} (hb : b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 8) :
    (storeOpOfBytes b).bytes = b ∧ storeOpOfBytes b ≠ .fpuStore128 := by
  rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨rfl, by decide⟩

theorem operands_argStore (e : Nat × Nat × Nat) :
    (argStore e).operands = .ok #[⟨e.2.1, .int, .use, .early, .reg⟩] := rfl

theorem vdefs_argStore (e : Nat × Nat × Nat) : vdefs (argStore e) = [] := rfl

theorem vuseNums_argStore (e : Nat × Nat × Nat) : vuseNums (argStore e) = [e.2.1] := rfl

theorem seqRun_argStore_cons {isem : Sem} {e : Nat × Nat × Nat} {ρ : Nat → CV}
    {w w1 : Arm.ArmState} (h : isem (argStore e) [ρ e.2.1] w = some ([], w1, .next))
    (ms : List MInst) :
    seqRun isem (argStore e :: ms) ρ w = (seqRun isem ms ρ w1).map SeqEnd.succ := by
  have hv : vuses #[(⟨e.2.1, .int, .use, .early, .reg⟩ : Operand)] ρ = [ρ e.2.1] := rfl
  simp only [seqRun, operands_argStore, hv, h]
  simp [Operand.isDef, vdefUpd, writeV]

/-- Byte `k` of the slot at `off` of the area at `a`. -/
theorem add_ofNat_add (a : BitVec 64) (off k : Nat) :
    a + BitVec.ofNat 64 off + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (off + k) := by
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem add_ofNat_ne {a : BitVec 64} {k k' : Nat} (hk : k < 2 ^ 64) (hk' : k' < 2 ^ 64)
    (hne : k ≠ k') : a + BitVec.ofNat 64 k ≠ a + BitVec.ofNat 64 k' := by
  intro e
  have := congrArg BitVec.toNat ((BitVec.add_right_inj a).mp e)
  simp [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk'] at this
  exact hne this

/-- One outgoing store: the low `b` bytes of the argument at `sp + off`. -/
theorem argStore_step {F : BitVec 64 → Prop} {isem : Sem} {sb : Nat}
    {syms : String → Option Nat} (hMem : MemRefines F sb syms isem) {off x b : Nat}
    (hb : b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 8) (v : CV) (w : Arm.ArmState)
    (hav : Avoids F b (spOf w + BitVec.ofNat 64 off)) :
    ∃ w1, isem (argStore (off, x, b)) [v] w = some ([], w1, .next) ∧
      SameWorld F w1 (Arm.write_mem_bytes b (spOf w + BitVec.ofNat 64 off)
        ((lo64 v).setWidth (b * 8)) w) := by
  have ha : amodeAddr sb (.spOffset (off : Int)) b [] w = some (spOf w + BitVec.ofNat 64 off) := by
    simp [amodeAddr]
  rcases hb with rfl | rfl | rfl | rfl <;>
    exact hMem.2.1 _ x (.spOffset (off : Int)) trustedFlags v [] w _ (by simp [storeOpOfBytes]) ha hav

/-- **The outgoing stores** (`gen_call_args`' `spOffset` stores of the stack-passed arguments,
in increasing non-overlapping slots inside the outgoing area): they run, keep the memory relation
and `sp`, and leave each argument's low bytes in its slot (and the area below the first slot
untouched). -/
theorem argStores_run {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {sb : Nat}
    {syms : String → Option Nat} (hMR : MRStable F MR) (hMem : MemRefines F sb syms isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) (ρ : Nat → CV) :
    ∀ (E : List (Nat × Nat × Nat)) (lo : Nat) (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem)
      (w : Arm.ArmState),
      slotsOk (E.map fun e => (e.1, e.2.2)) lo outB = true →
      (∀ e ∈ E, e.2.2 = 1 ∨ e.2.2 = 2 ∨ e.2.2 = 4 ∨ e.2.2 = 8) →
      MR sl cm w →
      ∃ w', seqRun isem (E.map argStore) ρ w = some (.fall ρ w') ∧ MR sl cm w' ∧
        spOf w' = spOf w ∧
        (∀ e ∈ E, Arm.read_mem_bytes e.2.2 (spOf w + BitVec.ofNat 64 e.1) w' =
          (lo64 (ρ e.2.1)).setWidth (e.2.2 * 8)) ∧
        (∀ k, k < lo → k < outB →
          w'.mem (spOf w + BitVec.ofNat 64 k) = w.mem (spOf w + BitVec.ofNat 64 k))
  | [], lo, sl, cm, w, _, _, hmr => ⟨w, rfl, hmr, rfl, by simp, fun _ _ _ => rfl⟩
  | (off, x, b) :: E, lo, sl, cm, w, hok, hbs, hmr => by
    simp only [List.map_cons, slotsOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hlo, hend⟩, hok⟩ := hok
    have hb := hbs (off, x, b) (List.mem_cons_self ..)
    have hbp : 0 < b := by rcases hb with rfl | rfl | rfl | rfl <;> decide
    obtain ⟨h64, hAv, hW⟩ := hout sl cm w hmr
    have hav : Avoids F b (spOf w + BitVec.ofNat 64 off) := fun k hk => by
      rw [add_ofNat_add]; exact hAv (off + k) (by omega)
    obtain ⟨w1, hst, hw1⟩ := argStore_step hMem (x := x) hb (ρ x) w hav
    have hmr1 : MR sl cm w1 := hMR _ _ _ _ (SameWorld.nf hw1) (hW off b _ hend)
    have hsp1 : spOf w1 = spOf w := by
      simp only [spOf]
      rw [hw1.1 (.GPR 31#5) (by simp [Masked]), Arm.r_of_write_mem_bytes]
    obtain ⟨w', hrun, hmr', hsp', hrd, hfr⟩ := argStores_run hMR hMem hout ρ E (off + b) sl cm w1 hok
      (fun e he => hbs e (List.mem_cons_of_mem _ he)) hmr1
    rw [hsp1] at hrd hfr
    -- bytes of the area below `outB` are not frame addresses: `w1` is the write there
    have hw1m : ∀ k, k < outB → w1.mem (spOf w + BitVec.ofNat 64 k) =
        (Arm.write_mem_bytes b (spOf w + BitVec.ofNat 64 off) ((lo64 (ρ x)).setWidth (b * 8)) w).mem
          (spOf w + BitVec.ofNat 64 k) := fun k hk => hw1.2.1 _ (hAv k hk)
    refine ⟨w', ?_, hmr', hsp'.trans hsp1, ?_, ?_⟩
    · rw [List.map_cons, seqRun_argStore_cons hst, hrun]; rfl
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

/-- The (offset, byte size) projection of a call's stack-passed arguments is the signature's
stack slots. -/
theorem stackEnts_proj : ∀ (locs : List ArgLoc) (args bytes : List Nat), args.length = bytes.length →
    (stackEnts ((locs.zip args).zip bytes)).map (fun e => (e.1, e.2.2)) = stackSlots locs bytes
  | [], _, _, _ => by simp [stackEnts, stackSlots]
  | _ :: _, [], [], _ => by simp [stackEnts, stackSlots]
  | _ :: _, [], _ :: _, h => by simp at h
  | _ :: _, _ :: _, [], h => by simp at h
  | .reg p :: locs, a :: args, b :: bytes, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simpa [stackEnts, stackSlots] using stackEnts_proj locs args bytes h
  | .stack o :: locs, a :: args, b :: bytes, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simpa [stackEnts, stackSlots] using stackEnts_proj locs args bytes h

theorem slotsOk_mono : ∀ (L : List (Nat × Nat)) (lo S S' : Nat), S ≤ S' →
    slotsOk L lo S = true → slotsOk L lo S' = true
  | [], _, _, _, _, _ => rfl
  | (o, b) :: L, lo, S, S', hS, h => by
    simp only [slotsOk, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨h.1.1, by omega⟩, slotsOk_mono L _ S S' hS h.2⟩

/-- The entries of a call's stack-passed arguments: the stack-located parameters. -/
theorem mem_stackEnts {locs : List ArgLoc} {args bytes : List Nat} {i off x b : Nat}
    (hl : locs[i]? = some (.stack off)) (ha : args[i]? = some x) (hb : bytes[i]? = some b) :
    (off, x, b) ∈ stackEnts ((locs.zip args).zip bytes) := by
  unfold stackEnts
  refine List.mem_filterMap.mpr ⟨((.stack off, x), b), ?_, rfl⟩
  exact List.mem_iff_getElem?.mpr ⟨i, by simp [List.getElem?_zip_eq_some, hl, ha, hb]⟩

/-- The register-passed arguments of a call are held by their argument values. -/
theorem allHold_regPairs {ρ : Nat → CV} : ∀ (locs : List ArgLoc) (vals : List Clif.Val)
    (args bytes : List Nat), vals.length = args.length → args.length = bytes.length →
    (∀ (j : Nat) (v : Clif.Val) (x : Nat), vals[j]? = some v → args[j]? = some x → VHolds v (ρ x)) →
    AllHold ((locs.zip vals).filterMap fun q => match q.1 with
        | .reg _ => some q.2
        | .stack _ => none)
      ((regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1))
  | [], _, _, _, _, _, _ => ⟨rfl, by simp⟩
  | _ :: _, [], [], [], _, _, _ => ⟨rfl, by simp⟩
  | _ :: _, [], _ :: _, _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, h, _, _ => by simp at h
  | _ :: _, [], [], _ :: _, _, h, _ => by simp at h
  | _ :: _, _ :: _, _ :: _, [], _, h, _ => by simp at h
  | l :: locs, v :: vals, x :: args, b :: bytes, h1, h2, hv => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    have ih := allHold_regPairs locs vals args bytes h1 h2
      (fun (j : Nat) (v' : Clif.Val) (x' : Nat) hv' hx' =>
        hv (j + 1) v' x' (by simpa using hv') (by simpa using hx'))
    cases l with
    | stack o => simpa [regPairsOf] using ih
    | reg p =>
      simp only [List.zip_cons_cons, List.filterMap_cons, regPairsOf, List.map_cons]
      refine ⟨by simp only [regPairsOf] at ih; simpa using ih.1, fun j v' x' hv' hx' => ?_⟩
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hv' hx'
        subst hv' hx'
        exact hv 0 v x rfl rfl
      | succ j => exact ih.2 j v' x' (by simpa using hv') (by simpa [regPairsOf] using hx')

/-- The stack-argument facts of a call of `ext` from `SigStackOk`. -/
theorem sigStack_facts {s : Clif.Signature} {outB : Nat} (hso : SigStackOk s outB)
    {bytes : List Nat} (hb : sigParamBytes s = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs s = .ok (locs, S)) :
    slotsOk (stackSlots locs bytes) 0 outB = true := by
  obtain ⟨hS, hlay⟩ := hso
  have hb' : sigArgs s = .ok bytes := hb
  simp only [stackLayoutOk, hl, hb'] at hlay
  simp only [stackBytes, hl] at hS
  exact slotsOk_mono _ 0 S outB hS hlay

theorem slotsOk_bound : ∀ (L : List (Nat × Nat)) (lo S : Nat), slotsOk L lo S = true →
    ∀ q ∈ L, lo ≤ q.1 ∧ q.1 + q.2 ≤ S
  | [], _, _, _ => by simp
  | (o, b) :: L, lo, S, h => by
    simp only [slotsOk, Bool.and_eq_true, decide_eq_true_eq] at h
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.1
    · have := slotsOk_bound L _ S h.2 q hq; omega

theorem mem_args_of_stackEnts : ∀ {T : List ((ArgLoc × Nat) × Nat)} {e : Nat × Nat × Nat},
    e ∈ stackEnts T → e.2.1 ∈ T.map (·.1.2)
  | [], _, h => by simp [stackEnts] at h
  | ((.reg p, x), b) :: T, e, h => by
    simp only [stackEnts, List.filterMap_cons] at h
    exact List.mem_cons_of_mem _ (mem_args_of_stackEnts h)
  | ((.stack o, x), b) :: T, e, h => by
    simp only [stackEnts, List.filterMap_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_args_of_stackEnts h)

theorem mem_args_of_regPairs : ∀ {T : List ((ArgLoc × Nat) × Nat)} {u : Nat},
    u ∈ (regPairsOf T).map (·.1) → u ∈ T.map (·.1.2)
  | [], _, h => by simp [regPairsOf] at h
  | ((.reg p, x), b) :: T, u, h => by
    simp only [regPairsOf, List.filterMap_cons, List.map_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_args_of_regPairs h)
  | ((.stack o, x), b) :: T, u, h => by
    simp only [regPairsOf, List.filterMap_cons] at h
    exact List.mem_cons_of_mem _ (mem_args_of_regPairs h)

theorem map_zip_args {locs : List ArgLoc} {args bytes : List Nat} {u : Nat}
    (h : u ∈ ((locs.zip args).zip bytes).map (·.1.2)) : u ∈ args := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
  exact (List.of_mem_zip (List.of_mem_zip hq).1).2

/-- The stores, then the call (`bl` or GOT `blr`): what the call clause of `CallsRefine` needs
— the arguments where the ABI puts them (`ArgsAt`) in the world after the stores, and in every
world that agrees with it outside the frame addresses up to the flags (a GOT load before the
call). -/
theorem argsAt_after_stores {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {sb : Nat}
    {syms : String → Option Nat} (hMR : MRStable F MR) (hMem : MemRefines F sb syms isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {s : Clif.Signature} (hso : SigStackOk s outB)
    {bytes : List Nat} (hb : sigParamBytes s = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs s = .ok (locs, S)) {args : List Nat} {vals : List Clif.Val}
    (hty : vals.map (·.ty) = Clif.AbiParam.tys s.params) (hal : args.length = vals.length)
    {ρ : Nat → CV}
    (hv : ∀ (j : Nat) (v : Clif.Val) (x : Nat), vals[j]? = some v → args[j]? = some x → VHolds v (ρ x))
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : Arm.ArmState} (hmr : MR sl cm w) :
    ∃ w', seqRun isem ((stackEnts ((locs.zip args).zip bytes)).map argStore) ρ w =
        some (.fall ρ w') ∧ MR sl cm w' ∧
      ∀ w2, SameWorldNF F w2 w' →
        ArgsAt s vals ((regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1)) w2 := by
  have hbm := sigParamBytes_eq_map hb
  have hvl : vals.length = s.params.length := by
    have := congrArg List.length hty; simpa [Clif.AbiParam.tys] using this
  have hbl : args.length = bytes.length := by rw [hbm, List.length_map, hal, hvl]
  have hslots := sigStack_facts hso hb hl
  rw [← stackEnts_proj locs args bytes hbl] at hslots
  obtain ⟨w', hrun, hmr', hsp, hrd, -⟩ := argStores_run hMR hMem hout ρ _ 0 sl cm w hslots
    (fun e he => by
      obtain ⟨q, hq, he⟩ := List.mem_filterMap.mp he
      obtain ⟨⟨l, x⟩, b⟩ := q
      cases l with
      | reg _ => cases he
      | stack o =>
        cases he
        exact sigArgs_bytes hb b (List.of_mem_zip hq).2) hmr
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
    have hbi : bytes[i]? = some v.ty.bytes := by
      rw [hbm, List.getElem?_map]
      have := congrArg (·[i]?) hty
      simp only [List.getElem?_map, Clif.AbiParam.tys, hvi, Option.map_some] at this
      cases hp : s.params[i]? with
      | none => rw [hp] at this; cases this
      | some p => rw [hp] at this; simp only [Option.map_some, Option.some.injEq] at this ⊢; rw [this]
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
      have := sigArgs_bytes hb _ (List.mem_of_getElem? hbi)
      cases h : v.ty <;> simp_all [Clif.Ty.bytes, Clif.Ty.width]
    simp only [lo64]
    rw [BitVec.setWidth_setWidth_of_le _ hw.2, BitVec.setWidth_setWidth_of_le _ hw.1]
    exact hvx

theorem call_sym_lowerInstOk {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat} (hMR : MRStable F MR)
    (hMem : MemRefines F sb syms isem) {outB : Nat} (hout : OutArgsOk F outB MR)
    {exts : List Clif.ExtFunc} (hCR : CallsRefine F env exts MR isem)
    {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S))
    {st st' : LState} {results : List Nat} (hres : results.length = ext.sig.returns.length)
    (hst' : st'.nextVreg = st.nextVreg + (sigRets ext.sig).length) :
    LowerInstOk isem MR env cp ctx (.call fn args) results st
      (outRegs' st.nextVreg (sigRets ext.sig).length) st'
      ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
        [.call ⟨.sym ext.name, retPairs (regPairsOf ((locs.zip args).zip bytes)),
          callDefs (outDefs st.nextVreg (sigRets ext.sig).length)⟩]) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
      simp [vdefs_argStore] at hd
    · simp only [List.mem_singleton] at hm
      subst hm
      rw [vdefs_call_sym] at hd
      simp only [outDefs, List.map_map, List.mem_map, List.mem_range, Function.comp_def] at hd
      obtain ⟨j, hj, rfl⟩ := hd
      omega
  · intro fr cm ρ w hfr hvh _ hmr
    split
    · rename_i rvals cm' hO
      obtain ⟨ext', vals, g, hx, hvals, hty, hg, hgo, hrty⟩ := instOutcome_call_ok hO
      rw [hfr, hctx.func, hext] at hx
      cases hx
      have hrN : rvals.length = ext.sig.returns.length := by
        have := congrArg List.length hrty; simpa [Clif.AbiParam.tys] using this
      obtain ⟨hlen, hvx⟩ := getMany_ok hvals
      obtain ⟨w1, hrun1, hmr1, hargs⟩ := argsAt_after_stores hMR hMem hout hso hb hl hty hlen.symm
        (fun j v x hv hx => hvh x v (hvx j x v hx hv)) hmr
      obtain ⟨sym, -, hcall, -⟩ := hCR
      have hdl : (callDefs (outDefs st.nextVreg (sigRets ext.sig).length)).length =
          (sigRets ext.sig).length := by simp [callDefs, outDefs]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := hcall ext hin g fr.slots cm w1 (.sym ext.name)
        (retPairs (regPairsOf ((locs.zip args).zip bytes)))
        (callDefs (outDefs st.nextVreg (sigRets ext.sig).length))
        _ _ vals rvals cm' hg (.inl ⟨rfl, rfl⟩) hdl (hargs w1 (SameWorldNF.refl F w1)) hmr1 hgo hrN
      have hol' : outs.length = (outDefs st.nextVreg (sigRets ext.sig).length).length := by
        rw [hol]; simp [callDefs, outDefs]
      refine ⟨?_, _, _, seqRun_append_fall' isem hrun1 (seqRun_call_sym hi hol'),
        results_call hrN hres (by rw [hol, hdl]) hro, hmr'⟩
      intro mi hmi u hu
      rcases List.mem_append.mp hmi with hmi | hmi
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmi
        rw [vuseNums_argStore, List.mem_singleton] at hu
        subst hu
        exact .inr (usesOk_args hvals _ (map_zip_args (mem_args_of_stackEnts he)))
      · simp only [List.mem_singleton] at hmi
        subst hmi
        rw [vuseNums_call_sym] at hu
        exact .inr (usesOk_args hvals u (map_zip_args (mem_args_of_regPairs hu)))
    · intro h; simp [explicitTrapInst] at h
    · trivial


theorem ofV_call (ci : CallInfo) : MInst.ofV (.data 58 109 [.op (.callInfo ci)]) = some (.call ci) :=
  rfl

theorem ofV_callInd (ci : CallInfo) :
    MInst.ofV (.data 58 110 [.op (.callInfo ci)]) = some (.call ci) := rfl

theorem ctor_is_pic_eq {ctx : Ctx} (st : LState) :
    externCtor ctx T.is_pic [] st = .ok (.bool true, st) := rfl

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
theorem call_impl_ok {n : Nat} (hn : 30 ≤ n) {i : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 46 638 [i] s v s') :
    s'.1 = s.1 ∧ v = .data 46 0 [.data 58 109 [i]] := by
  isel_split hp hc h 638
  isel_inv [*, rule_inst_4780] at hm he

include hp hc in
theorem call_ind_impl_ok {n : Nat} (hn : 30 ≤ n) {i : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 46 639 [i] s v s') :
    s'.1 = s.1 ∧ v = .data 46 0 [.data 58 110 [i]] := by
  isel_split hp hc h 639
  isel_inv [*, rule_inst_4786] at hm he

include hp hc in
theorem load_ext_name_got_ok_ctl {n : Nat} (hn : 30 ≤ n) {nm : String} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 571 [.op (.extName nm)] s v s') :
    v = .reg (s.1.fresh .int).1 ∧
      s'.1 = (s.1.fresh .int).2.emit (.loadExtNameGot (s.1.fresh .int).1 nm) := by
  isel_split hp hc h 571
  isel_inv [*, rule_inst_4002] at hm he
  have hof := ‹MInst.ofV _ = some _›
  rw [ofV_loadExtNameGot_ctl] at hof
  cases hof
  rfl

include hp hc in
theorem load_ext_name_ok_ctl {n : Nat} (hn : 40 ≤ n) {nm : String} {d : V} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 570 [.op (.extName nm), .int 0, d] s v s') :
    v = .reg (s.1.fresh .int).1 ∧
      s'.1 = (s.1.fresh .int).2.emit (.loadExtNameGot (s.1.fresh .int).1 nm) := by
  have k := fun n (hn : 30 ≤ n) s v s' h => load_ext_name_got_ok_ctl hp (ctx := ctx) hc (n := n)
    (nm := nm) (s := s) (v := v) (s' := s') hn h
  isel_split hp hc h 570
  · isel_inv [*, rule_inst_3986] at hm he
    simp only [ctor_is_pic_iff] at *
    isel_destruct; subst_vars
    have h571 := ‹ApplyInternal _ _ _ _ 27 571 _ _ _ _›
    exact k _ (by omega) _ _ _ h571
  · isel_inv [*, rule_inst_3991] at hm
    simp [ctor_is_pic_iff] at *
  · isel_inv [*, rule_inst_3996] at hm
    simp [ctor_is_pic_iff] at *
  · obtain ⟨k', s2, h2⟩ := hpre _ (List.mem_cons_self ..)
    revert h2
    isel_eval [*, rule_inst_3986, sem_eq, ctor_is_pic_eq]
    simp

end

/-! ## Rule 1032: `loadExtNameGot t name; blr t` -/

/-- The target register operand of `blr`. -/
def tgtOp (t : Nat) : Operand := ⟨t, .int, .use, .early, .reg⟩

/-- The def operand of `loadExtNameGot`. -/
def gotOp (t : Nat) : Operand := ⟨t, .int, .def, .late, .reg⟩

theorem operands_loadExtNameGot_ctl (t : Nat) (nm : String) :
    (MInst.loadExtNameGot (.vreg t .int) nm).operands = .ok #[gotOp t] := rfl

open Driver in
theorem operands_call_reg (t : Nat) (L : List (Nat × Reg)) (D : List (Reg × Nat)) :
    (MInst.call ⟨.reg (.vreg t .int), retPairs L, callDefs D⟩).operands =
      .ok (tgtOp t :: (retOps L ++ callDefOps D)).toArray := by
  have h1 : ∀ s, (collectOp OpSpec.use (Reg.vreg t .int)).run s =
      .ok (Reg.vreg t .int, s.push (tgtOp t)) := fun _ => rfl
  rw [operands_eq]
  simp only [MInst.visitOperands, StateT.run_bind, StateT.run_pure, except_ok_bind, h1,
    mapM_fixedUse, mapM_callDefs]
  simp [bind, Except.bind, StateT.run, pure, StateT.pure, Except.pure]

theorem vuses_call_reg {V : Type} (t : Nat) (L : List (Nat × Reg)) (D : List (Reg × Nat))
    (ρ : Nat → V) :
    vuses (tgtOp t :: (retOps L ++ callDefOps D)).toArray ρ = ρ t :: L.map (ρ ·.1) := by
  have := vuses_call L D ρ
  simp only [vuses, List.toList_toArray] at this ⊢
  rw [List.filter_cons_of_pos (by simp [tgtOp, Operand.isUse])]
  simp only [List.map_cons, this]
  rfl

theorem vdefUpd_call_reg {V : Type} (t : Nat) (L : List (Nat × Reg)) (D : List (Reg × Nat))
    (outs : List V) (ρ : Nat → V) :
    vdefUpd (tgtOp t :: (retOps L ++ callDefOps D)).toArray outs ρ =
      writeV ρ ((callDefOps D).zip outs) := by
  rw [← vdefUpd_call L D outs ρ]
  simp only [vdefUpd, List.toList_toArray]
  rw [List.filter_cons_of_neg (by simp [tgtOp, Operand.isDef])]

theorem seqRun_call_reg {isem : Sem} {t : Nat} {L : List (Nat × Reg)} {D : List (Reg × Nat)}
    {ρ : Nat → CV} {w w' : Arm.ArmState} {outs : List CV}
    (h : isem (.call ⟨.reg (.vreg t .int), retPairs L, callDefs D⟩) (ρ t :: L.map (ρ ·.1)) w =
      some (outs, w', .next))
    (hl : outs.length = D.length) :
    seqRun isem [.call ⟨.reg (.vreg t .int), retPairs L, callDefs D⟩] ρ w =
      some (.fall (writeV ρ ((callDefOps D).zip outs)) w') := by
  simp only [seqRun, operands_call_reg, vuses_call_reg, h, List.toList_toArray]
  rw [List.filter_cons_of_neg (by simp [tgtOp, Operand.isDef]), defs_call]
  have hl' : outs.length = (callDefOps D).length := by simp [callDefOps, hl]
  simp only [hl', ↓reduceIte, vdefUpd_call_reg]
  rfl

theorem seqRun_got {F : BitVec 64 → Prop} {isem : Sem} {t : Nat} {nm : String} {ρ : Nat → CV}
    {w w' : Arm.ArmState} {x : CV}
    (h : isem (.loadExtNameGot (.vreg t .int) nm) [] w = some ([x], w', .next)) :
    seqRun isem [.loadExtNameGot (.vreg t .int) nm] ρ w = some (.fall (upd ρ t x) w') := by
  simp only [seqRun, operands_loadExtNameGot_ctl]
  have hv : vuses #[gotOp t] ρ = [] := rfl
  rw [hv, h]
  simp [vdefUpd, gotOp, Operand.isDef, Operand.isEarly, Operand.isLate, writeV, SeqEnd.succ]

theorem vuseNums_call_reg (t : Nat) (L : List (Nat × Reg)) (D : List (Reg × Nat)) :
    vuseNums (.call ⟨.reg (.vreg t .int), retPairs L, callDefs D⟩) = t :: L.map (·.1) := by
  have := vuses_call_reg t L D id
  simp only [vuseNums, operands_call_reg]
  simpa [vuses] using this

theorem vdefs_call_reg (t : Nat) (L : List (Nat × Reg)) (D : List (Reg × Nat)) :
    vdefs (.call ⟨.reg (.vreg t .int), retPairs L, callDefs D⟩) = D.map (·.2) := by
  simp only [vdefs, operands_call_reg, List.toList_toArray]
  rw [List.filter_cons_of_neg (by simp [tgtOp, Operand.isDef]), defs_call]
  simp [callDefOps]

theorem vdefs_got_ctl (t : Nat) (nm : String) : vdefs (.loadExtNameGot (.vreg t .int) nm) = [t] := rfl

theorem vuseNums_got_ctl (t : Nat) (nm : String) :
    vuseNums (.loadExtNameGot (.vreg t .int) nm) = [] := rfl

theorem call_got_lowerInstOk {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat} (hMR : MRStable F MR)
    (hMem : MemRefines F sb syms isem) {outB : Nat} (hout : OutArgsOk F outB MR)
    {exts : List Clif.ExtFunc} (hCR : CallsRefine F env exts MR isem) {f : Clif.Function}
    {ctx : Ctx} (hctx : CtxInv f ctx) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S))
    {st st' : LState} {results : List Nat} (hres : results.length = ext.sig.returns.length)
    (hargs : ∀ x ∈ args, x < st.nextVreg)
    (hst' : st'.nextVreg = st.nextVreg + (sigRets ext.sig).length + 1) :
    LowerInstOk isem MR env cp ctx (.call fn args) results st
      (outRegs' st.nextVreg (sigRets ext.sig).length) st'
      ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
       [.loadExtNameGot (.vreg (st.nextVreg + (sigRets ext.sig).length) .int) ext.name,
       .call ⟨.reg (.vreg (st.nextVreg + (sigRets ext.sig).length) .int),
        retPairs (regPairsOf ((locs.zip args).zip bytes)),
        callDefs (outDefs st.nextVreg (sigRets ext.sig).length)⟩]) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
      simp [vdefs_argStore] at hd
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · rw [vdefs_got_ctl] at hd
        simp only [List.mem_singleton] at hd
        omega
      · rw [vdefs_call_reg] at hd
        simp only [outDefs, List.map_map, List.mem_map, List.mem_range, Function.comp_def] at hd
        obtain ⟨j, hj, rfl⟩ := hd
        omega
  · intro fr cm ρ w hfr hvh _ hmr
    split
    · rename_i rvals cm' hO
      obtain ⟨ext', vals, g, hx, hvals, hty, hg, hgo, hrty⟩ := instOutcome_call_ok hO
      rw [hfr, hctx.func, hext] at hx
      cases hx
      have hrN : rvals.length = ext.sig.returns.length := by
        have := congrArg List.length hrty; simpa [Clif.AbiParam.tys] using this
      obtain ⟨hlen, hvx⟩ := getMany_ok hvals
      obtain ⟨w1, hrun1, hmr1, hargsAt⟩ := argsAt_after_stores hMR hMem hout hso hb hl hty
        hlen.symm (fun j v x hv hx => hvh x v (hvx j x v hx hv)) hmr
      obtain ⟨sym, hgot, hcall, -⟩ := hCR
      obtain ⟨w2, hw2, hsw⟩ := hgot (.vreg (st.nextVreg + (sigRets ext.sig).length) .int) ext.name w1
      have hmr2 := hMR _ _ _ _ hsw hmr1
      have hrun2 := seqRun_got (F := F) (ρ := ρ) hw2
      generalize ht : st.nextVreg + (sigRets ext.sig).length = t at hrun2 hw2 hsw ⊢
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
      have hdl : (callDefs (outDefs st.nextVreg (sigRets ext.sig).length)).length =
          (sigRets ext.sig).length := by simp [callDefs, outDefs]
      have ht1 : upd ρ t (ofX (sym ext.name)) t = ofX (sym ext.name) := by simp [upd]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := hcall ext hin g fr.slots cm w2
        (.reg (.vreg t .int)) (retPairs (regPairsOf ((locs.zip args).zip bytes)))
        (callDefs (outDefs st.nextVreg (sigRets ext.sig).length))
        (upd ρ t (ofX (sym ext.name)) t ::
          (regPairsOf ((locs.zip args).zip bytes)).map (upd ρ t (ofX (sym ext.name)) ·.1))
        ((regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1)) vals rvals cm' hg
        (.inr ⟨_, rfl, by rw [ht1, huses]⟩) hdl (hargsAt w2 hsw) hmr2 hgo hrN
      have hol' : outs.length = (outDefs st.nextVreg (sigRets ext.sig).length).length := by
        rw [hol]; simp [callDefs, outDefs]
      have hrun3 := seqRun_call_reg hi hol'
      refine ⟨?_, _, _, seqRun_append_fall' isem hrun1
          (seqRun_append_fall' isem (ms1 := [_]) (ms2 := [_]) hrun2 hrun3),
        results_call hrN hres (by rw [hol, hdl]) hro, hmr'⟩
      intro mi hmi u hu
      rcases List.mem_append.mp hmi with hmi | hmi
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmi
        rw [vuseNums_argStore, List.mem_singleton] at hu
        subst hu
        exact .inr (usesOk_args hvals _ (map_zip_args (mem_args_of_stackEnts he)))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmi
        rcases hmi with rfl | rfl
        · simp [vuseNums_got_ctl] at hu
        · rw [vuseNums_call_reg] at hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact .inl (by omega)
          · exact .inr (usesOk_args hvals u (map_zip_args (mem_args_of_regPairs hu)))
    · intro h; simp [explicitTrapInst] at h
    · trivial

set_option maxHeartbeats 5000000 in
theorem call_bl_ruleOk {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat} (hMem : MemRefines F sb syms isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefine F env exts MR isem) :
    CallRuleOk isem MR env cp exts outB p rule_lower_2508 := by
  intro f ctx hctx hexts ii info inst hi hcl hstk cfg hc m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
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
  have hres := call_results_length hctx hi hcl hext
  simp only [ext_value_list_slice_iff, ext_func_ref_data_iff, hfn] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2508] at heval
  isel_destruct; subst_vars
  simp only [ctor_abi_sig_iff, ctor_gen_call_output_iff, ctor_put_in_regs_vec_iff,
    ctor_gen_call_rets_iff, ctor_try_call_none_iff, ctor_output_vec_iff,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate] at *
  isel_destruct; subst_vars
  simp only [show (4:Nat) < 10 from by decide, ite_true] at *
  subst_vars
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, outRegs_single, outRegs_length,
    Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueReg hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_gen _ _ _ hb hl,
    ctor_gen_call_info_gen _ _ _ _ _ _ _ hl,
    mapM_single_map, Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_info_gen _ _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  obtain ⟨hr8, rfl⟩ := retRegs_eq ‹retRegs _ = some _›
  simp only [ctor_output_vec_iff] at *
  isel_destruct; subst_vars
  have h638 := ‹ApplyInternal _ _ _ _ 46 638 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h638
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_call] at hmi
  cases hmi
  rw [callDefs_outDefs] at hs2
  rw [outRegs_eq]
  refine ⟨_, ?_, _, rfl, call_sym_lowerInstOk hMR hMem hout hCR hctx hext (hexts fn _ hext)
    (hstk fn args _ rfl hext) hb hl hres (by rw [hs2, hs1]; simp [LState.emit, freshN_nextVreg])⟩
  rw [hs2, hs1]; simp [LState.emit, freshN_emitted]

theorem mapM_valueReg_below {ctx : Ctx} {st : LState} (hvb : ValsBelow ctx st) :
    ∀ {xs : List Nat} {rs : List Reg}, xs.mapM ctx.valueReg? = some rs → ∀ x ∈ xs, x < st.nextVreg
  | [], _, _ => by simp
  | x :: xs, rs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, rs', hrs, rfl⟩ := h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hvb _ r hr
    · exact mapM_valueReg_below hvb hrs y hy

set_option maxHeartbeats 5000000 in
theorem call_got_ruleOk {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat} (hMem : MemRefines F sb syms isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefine F env exts MR isem) :
    CallRuleOk isem MR env cp exts outB p rule_lower_2518 := by
  intro f ctx hctx hexts ii info inst hi hcl hstk cfg hc m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
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
  have hres := call_results_length hctx hi hcl hext
  simp only [ext_value_list_slice_iff, ext_func_ref_data_iff, hfn] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2518] at heval
  isel_destruct; subst_vars
  simp only [ctor_abi_sig_iff, ctor_gen_call_output_iff, ctor_put_in_regs_vec_iff,
    ctor_gen_call_rets_iff, ctor_try_call_none_iff, ctor_output_vec_iff, ctor_box_external_name_iff,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate] at *
  isel_destruct; subst_vars
  simp only [show (4:Nat) < 10 from by decide, ite_true] at *
  subst_vars
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, outRegs_single, outRegs_length,
    Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hbelow := mapM_valueReg_below hvb ‹List.mapM ctx.valueReg? args = some _›
  have hrs := mapM_valueReg hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_gen _ _ _ hb hl, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  have h570 := ‹ApplyInternal _ _ _ _ 27 570 _ _ _ _›
  obtain ⟨rfl, hs0⟩ := kL _ (by omega) _ _ _ _ _ h570
  simp only [ctor_gen_call_ind_info_gen _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true,
    ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  obtain ⟨hr8, rfl⟩ := retRegs_eq ‹retRegs _ = some _›
  simp only [ctor_output_vec_iff] at *
  isel_destruct; subst_vars
  have h639 := ‹ApplyInternal _ _ _ _ 46 639 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h639
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_callInd] at hmi
  cases hmi
  have hfr : ∀ k (e : Array MInst), (({ freshN st k with emitted := e } : LState).fresh .int).1 =
      .vreg (st.nextVreg + k) .int := fun k e => by
    simp [LState.fresh, freshN_nextVreg]
  rw [hfr, callDefs_outDefs] at hs2
  rw [hfr] at hs0
  rw [outRegs_eq]
  refine ⟨_, ?_, _, rfl, call_got_lowerInstOk hMR hMem hout hCR hctx hext (hexts fn _ hext)
    (hstk fn args _ rfl hext) hb hl hres hbelow
    (by rw [hs2, hs1, hs0]; simp [LState.emit, LState.fresh, freshN_nextVreg])⟩
  rw [hs2, hs1, hs0]
  simp only [LState.emit, LState.fresh, freshN_emitted]
  rw [← Array.toList_inj]
  simp

end Backend.Proof
