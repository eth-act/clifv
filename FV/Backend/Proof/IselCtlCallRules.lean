import FV.Backend.Proof.IselCtlCall
import FV.Backend.Proof.IselFamily
import FV.Backend.Proof.LowerLemmas

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

theorem mapM_except_length {α β ε : Type} (g : α → Except ε β) :
    ∀ {l : List α} {r : List β}, l.mapM g = .ok r → r.length = l.length
  | [], r, h => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases ha : g a with
    | error e => rw [ha] at h; cases h
    | ok b =>
      rw [ha] at h
      cases hl : l.mapM g with
      | error e => rw [hl] at h; cases h
      | ok bs =>
        rw [hl] at h
        simp [bind, Except.bind, pure, Except.pure] at h
        subst h
        simp [mapM_except_length g hl]

theorem sigParamBytes_length {s : Clif.Signature} {bytes : List Nat}
    (h : sigParamBytes s = .ok bytes) : bytes.length = s.params.length :=
  mapM_except_length _ h

theorem ctor_gen_call_args_bytes {ctx : Ctx} {st : LState} {s : Clif.Signature}
    {rss : List (List Reg)} {v : V} {st' : LState}
    (h : externCtor ctx T.gen_call_args [.op (.sig s), .regsVec rss] st = .ok (v, st')) :
    ∃ bytes, sigParamBytes s = .ok bytes := by
  have : externCtor ctx T.gen_call_args [.op (.sig s), .regsVec rss] st =
      match sigParamBytes s, rss.mapM single? with
      | .ok bytes, some rs =>
        let r := ((((argLocs bytes).1.zip rs).zip bytes).foldl argStep (#[], st))
        .ok (.op (.callArgs r.1.toList), r.2)
      | .error e, _ => .unmodeled s!"gen_call_args: {e}"
      | _, none => .unmodeled "gen_call_args: multi-register value" := rfl
  rw [this] at h
  cases hb : sigParamBytes s with
  | error e => rw [hb] at h; simp at h
  | ok b => exact ⟨b, rfl⟩

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

theorem writeV_cons {V : Type} (ρ : Nat → V) (a : Operand × V) (dv : List (Operand × V)) :
    writeV ρ (a :: dv) = writeV (upd ρ a.1.vreg a.2) dv := rfl

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

theorem uses_retPairs (args : List Nat) (K : Nat) :
    (args.map fun x => Reg.vreg x .int).zip (List.map Reg.x (List.range K)) =
      retPairs (args.zip ((List.range K).map Reg.x)) := by
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

theorem call_sym_lowerInstOk {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} (hCR : CallsRefine F env MR isem) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) {K : Nat} (hK : K = ext.sig.params.length) (h8 : K ≤ 8)
    {st st' : LState} {results : List Nat}
    (hst' : st'.nextVreg = st.nextVreg + ext.sig.returns.length) :
    LowerInstOk isem MR env cp ctx (.call fn args) results st
      (outRegs' st.nextVreg ext.sig.returns.length) st'
      [.call ⟨.sym ext.name, retPairs (args.zip ((List.range K).map Reg.x)),
        callDefs (outDefs st.nextVreg ext.sig.returns.length)⟩] := by
  refine ⟨by omega, ?_, ?_⟩
  · intro m hm d hd
    simp only [List.mem_singleton] at hm
    subst hm
    rw [vdefs_call_sym] at hd
    simp only [outDefs, List.map_map, List.mem_map, List.mem_range, Function.comp_def] at hd
    obtain ⟨j, hj, rfl⟩ := hd
    omega
  · intro fr cm ρ w hfr hvh _ hmr
    split
    · rename_i rvals cm' hO
      obtain ⟨vals, g, hvals, hvl, hal, hg, hgo, hrN⟩ := call_ok_facts hctx hext hfr hO
      have hfst : (args.zip ((List.range K).map Reg.x)).map (·.1) = args :=
        List.map_fst_zip (by simp; omega)
      have hsnd : (args.zip ((List.range K).map Reg.x)).map (·.2) = (List.range K).map Reg.x :=
        List.map_snd_zip (by simp; omega)
      obtain ⟨sym, -, hcall⟩ := hCR
      have huses : (args.zip ((List.range K).map Reg.x)).map (ρ ·.1) = args.map ρ := by
        rw [show (fun x : Nat × Reg => ρ x.1) = ρ ∘ (·.1) from rfl, ← List.map_map, hfst]
      have hus : (retPairs (args.zip ((List.range K).map Reg.x))).map (·.2) =
          (List.range (retPairs (args.zip ((List.range K).map Reg.x))).length).map Reg.x := by
        have : (retPairs (args.zip ((List.range K).map Reg.x))).map (·.2) =
            (args.zip ((List.range K).map Reg.x)).map (·.2) := by simp [retPairs]
        rw [this, hsnd]
        congr 2
        simp [retPairs]
        omega
      have hds : (callDefs (outDefs st.nextVreg ext.sig.returns.length)).map (·.1) =
          (List.range (callDefs (outDefs st.nextVreg ext.sig.returns.length)).length).map Reg.x := by
        simp [callDefs, outDefs]
      have hdl : (callDefs (outDefs st.nextVreg ext.sig.returns.length)).length = rvals.length := by
        simp [callDefs, outDefs, hrN]
      obtain ⟨outs, w', hi, hro, hmr'⟩ := hcall ext.name g fr.slots cm w (.sym ext.name)
        (retPairs (args.zip ((List.range K).map Reg.x)))
        (callDefs (outDefs st.nextVreg ext.sig.returns.length))
        ((args.zip ((List.range K).map Reg.x)).map (ρ ·.1)) (args.map ρ) vals rvals cm' hg
        (.inl ⟨rfl, huses⟩) hus hds (by omega) (allHold_args hvh hvals) hmr hgo hdl
      have hol : outs.length = (outDefs st.nextVreg ext.sig.returns.length).length := by
        simp [outDefs]; rw [← hro.1]; exact hrN
      refine ⟨?_, _, _, seqRun_call_sym hi hol, .inr ?_, hmr'⟩
      · intro mi hmi u hu
        simp only [List.mem_singleton] at hmi
        subst hmi
        rw [vuseNums_call_sym, hfst] at hu
        exact .inr (usesOk_args hvals u hu)
      · rw [← hrN]
        exact resultsHeld_call hro
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
    {cp : Clif.Program} (hMR : MRStable F MR) (hCR : CallsRefine F env MR isem) {f : Clif.Function}
    {ctx : Ctx} (hctx : CtxInv f ctx) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) {K : Nat} (hK : K = ext.sig.params.length) (h8 : K ≤ 8)
    {st st' : LState} {results : List Nat} (hargs : ∀ x ∈ args, x < st.nextVreg)
    (hst' : st'.nextVreg = st.nextVreg + ext.sig.returns.length + 1) :
    LowerInstOk isem MR env cp ctx (.call fn args) results st
      (outRegs' st.nextVreg ext.sig.returns.length) st'
      [.loadExtNameGot (.vreg (st.nextVreg + ext.sig.returns.length) .int) ext.name,
       .call ⟨.reg (.vreg (st.nextVreg + ext.sig.returns.length) .int),
        retPairs (args.zip ((List.range K).map Reg.x)),
        callDefs (outDefs st.nextVreg ext.sig.returns.length)⟩] := by
  refine ⟨by omega, ?_, ?_⟩
  · intro m hm d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
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
      obtain ⟨vals, g, hvals, hvl, hal, hg, hgo, hrN⟩ := call_ok_facts hctx hext hfr hO
      have hfst : (args.zip ((List.range K).map Reg.x)).map (·.1) = args :=
        List.map_fst_zip (by simp; omega)
      have hsnd : (args.zip ((List.range K).map Reg.x)).map (·.2) = (List.range K).map Reg.x :=
        List.map_snd_zip (by simp; omega)
      obtain ⟨sym, hgot, hcall⟩ := hCR
      obtain ⟨w1, hw1, hsw⟩ := hgot (.vreg (st.nextVreg + ext.sig.returns.length) .int) ext.name w
      have hmr1 := hMR _ _ _ _ hsw hmr
      have hrun1 := seqRun_got (F := F) (ρ := ρ) hw1
      generalize ht : st.nextVreg + ext.sig.returns.length = t at hrun1 hw1 ⊢
      have hρ1 : ∀ x ∈ args, upd ρ t (ofX (sym ext.name)) x = ρ x := by
        intro x hx
        have := hargs x hx
        simp only [upd]
        rw [if_neg (by omega)]
      have huses : (args.zip ((List.range K).map Reg.x)).map (upd ρ t (ofX (sym ext.name)) ·.1) =
          args.map ρ := by
        rw [show (fun x : Nat × Reg => upd ρ t (ofX (sym ext.name)) x.1) =
          upd ρ t (ofX (sym ext.name)) ∘ (·.1) from rfl, ← List.map_map, hfst]
        exact List.map_congr_left hρ1
      have hus : (retPairs (args.zip ((List.range K).map Reg.x))).map (·.2) =
          (List.range (retPairs (args.zip ((List.range K).map Reg.x))).length).map Reg.x := by
        have : (retPairs (args.zip ((List.range K).map Reg.x))).map (·.2) =
            (args.zip ((List.range K).map Reg.x)).map (·.2) := by simp [retPairs]
        rw [this, hsnd]
        congr 2
        simp [retPairs]
        omega
      have hds : (callDefs (outDefs st.nextVreg ext.sig.returns.length)).map (·.1) =
          (List.range (callDefs (outDefs st.nextVreg ext.sig.returns.length)).length).map Reg.x := by
        simp [callDefs, outDefs]
      have hdl : (callDefs (outDefs st.nextVreg ext.sig.returns.length)).length = rvals.length := by
        simp [callDefs, outDefs, hrN]
      have ht1 : upd ρ t (ofX (sym ext.name)) t = ofX (sym ext.name) := by simp [upd]
      obtain ⟨outs, w', hi, hro, hmr'⟩ := hcall ext.name g fr.slots cm w1
        (.reg (.vreg t .int))
        (retPairs (args.zip ((List.range K).map Reg.x)))
        (callDefs (outDefs st.nextVreg ext.sig.returns.length))
        (upd ρ t (ofX (sym ext.name)) t ::
          (args.zip ((List.range K).map Reg.x)).map (upd ρ t (ofX (sym ext.name)) ·.1)) (args.map ρ) vals rvals cm' hg
        (.inr ⟨_, rfl, by rw [ht1, huses]⟩) hus hds (by omega) (allHold_args hvh hvals) hmr1 hgo hdl
      have hol : outs.length = (outDefs st.nextVreg ext.sig.returns.length).length := by
        simp [outDefs]; rw [← hro.1]; exact hrN
      have hrun2 := seqRun_call_reg hi hol
      refine ⟨?_, _, _, seqRun_append_fall' isem (ms1 := [_]) (ms2 := [_]) hrun1 hrun2, .inr ?_, hmr'⟩
      · intro mi hmi u hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmi
        rcases hmi with rfl | rfl
        · simp [vuseNums_got_ctl] at hu
        · rw [vuseNums_call_reg, hfst] at hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact .inl (by omega)
          · exact .inr (usesOk_args hvals u hu)
      · rw [← hrN]
        exact resultsHeld_call hro
    · intro h; simp [explicitTrapInst] at h
    · trivial

set_option maxHeartbeats 5000000 in
theorem call_bl_ruleOk {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) (hCR : CallsRefine F env MR isem) :
    CallRuleOk isem MR env cp p rule_lower_2508 := by
  intro f ctx hctx hreg ii info inst hi hcl cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
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
  have h8 : bytes.length ≤ 8 := sigParamBytes_length hb ▸ hreg fn _ hext
  have hrs := mapM_valueReg hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_iff _ _ _ hb h8, ctor_gen_call_info_iff _ _ _ _ _ _ _ hb,
    mapM_single_map, Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_info_iff _ _ _ _ _ _ _ hb, Nat.reduceEqDiff, Nat.reduceLT, ite_true,
    ite_false, Option.some.injEq] at *
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
  rw [uses_retPairs, callDefs_outDefs] at hs2
  rw [outRegs_eq]
  refine ⟨_, ?_, _, rfl, call_sym_lowerInstOk hCR hctx hext (sigParamBytes_length hb) h8
    (by rw [hs2, hs1]; simp [LState.emit, freshN_nextVreg])⟩
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
    (hMR : MRStable F MR) (hCR : CallsRefine F env MR isem) :
    CallRuleOk isem MR env cp p rule_lower_2518 := by
  intro f ctx hctx hreg ii info inst hi hcl cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
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
  have h8 : bytes.length ≤ 8 := sigParamBytes_length hb ▸ hreg fn _ hext
  have hbelow := mapM_valueReg_below hvb ‹List.mapM ctx.valueReg? args = some _›
  have hrs := mapM_valueReg hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_iff _ _ _ hb h8, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  have h570 := ‹ApplyInternal _ _ _ _ 27 570 _ _ _ _›
  obtain ⟨rfl, hs0⟩ := kL _ (by omega) _ _ _ _ _ h570
  simp only [ctor_gen_call_ind_info_iff _ _ _ _ _ _ hb, Nat.reduceEqDiff, Nat.reduceLT, ite_true,
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
  have hfr : ∀ k, ((freshN st k).fresh .int).1 = .vreg (st.nextVreg + k) .int := fun k => by
    simp [LState.fresh, freshN_nextVreg]
  rw [hfr, uses_retPairs, callDefs_outDefs] at hs2
  rw [hfr] at hs0
  rw [outRegs_eq]
  refine ⟨_, ?_, _, rfl, call_got_lowerInstOk hMR hCR hctx hext (sigParamBytes_length hb) h8 hbelow
    (by rw [hs2, hs1, hs0]; simp [LState.emit, LState.fresh, freshN_nextVreg])⟩
  rw [hs2, hs1, hs0]
  simp only [LState.emit, LState.fresh, freshN_emitted]
  rw [← Array.toList_inj]
  simp

end Backend.Proof
