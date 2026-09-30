import FV.Backend.Proof.IselCtlCallRules
import FV.Backend.Proof.IselCtlUnmatch
import FV.Backend.Proof.TryRegs

/-!
# Family Ctl: the `try_call` rules (the normal return)

`TryRuleOk` for `rule_lower_2542` (`bl name`, rule id 1034) and `rule_lower_2551`
(`loadExtNameGot t name; blr t`, rule id 1035) of `lower_branch`: as the `call` rules
(`IselCtlCallRules.lean`), with the defs of `gen_try_call_rets` (the return and payload vregs
of the context, `ctx.tryRegs`) and the `try_call_info` of the targets; with the emitted call
replaced by the `tryCall`, a normal return of the callee continues at the normal-return
successor. `tryUnmatchable`: the other rules of `lower_branch` name another format.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## ISLE data of the `try_call` rules

The terms the `try_call` rules reach beyond `Data` (whose roots are the closure root rules). -/

@[isel_data] theorem term_300_kind : T.«gen_try_call_rets».kind =
    (.decl ⟨false, false, false, false⟩ (some (.external "gen_try_call_rets")) none) := rfl
@[isel_data] theorem term_300_name : T.«gen_try_call_rets».name = "gen_try_call_rets" := rfl
@[isel_data] theorem term_302_kind : T.«try_call_info».kind =
    (.decl ⟨false, false, false, false⟩ (some (.external "try_call_info")) none) := rfl
@[isel_data] theorem term_302_name : T.«try_call_info».name = "try_call_info" := rfl
@[isel_data] theorem term_2297_kind : T.«Opcode.TryCall».kind = (.enumVariant 13) := rfl
@[isel_data] theorem term_2297_name : T.«Opcode.TryCall».name = "Opcode.TryCall" := rfl
@[isel_data] theorem term_2474_kind : T.«InstructionData.TryCall».kind = (.enumVariant 27) := rfl
@[isel_data] theorem term_2474_name : T.«InstructionData.TryCall».name = "InstructionData.TryCall" :=
  rfl

/-- The term facts of the `try_call` rules beyond `Data`. -/
structure TryData (p : Program) : Prop where
  t300 : Interp.termOf p 300 = pure T.«gen_try_call_rets»
  t302 : Interp.termOf p 302 = pure T.«try_call_info»
  t2297 : Interp.termOf p 2297 = pure T.«Opcode.TryCall»
  t2474 : Interp.termOf p 2474 = pure T.«InstructionData.TryCall»

theorem tryData_program : TryData program := ⟨rfl, rfl, rfl, rfl⟩

/-! ## Extern helpers -/

section
variable {ctx : Ctx}

theorem ctor_try_call_info_iff (st : LState) (s : Clif.Signature) (items : List (Option Nat))
    (ls : List Label) (v : V) (st' : LState) :
    externCtor ctx T.try_call_info [.op (.exnTable s items), .labels ls] st = .ok (v, st') ↔
      ∃ ti, tryInfoOf s items ls = some ti ∧ v = .op (.tryCallInfo ti) ∧ st' = st := by
  have : externCtor ctx T.try_call_info [.op (.exnTable s items), .labels ls] st =
      match tryInfoOf s items ls with
      | some ti => .ok (.op (.tryCallInfo ti), st)
      | none => .unmodeled "try_call_info: label count" := rfl
  rw [this]
  cases tryInfoOf s items ls <;> simp [eq_comm]

theorem ctor_gen_try_call_rets_iff (st : LState) (s : Clif.Signature) (v : V) (st' : LState) :
    externCtor ctx T.gen_try_call_rets [.op (.sig s)] st = .ok (v, st') ↔
      ∃ ps, retRegs (sigRets s).length = some ps ∧ ps.length = ctx.tryRegs.1.length ∧
        v = .op (.callRets (ps.zip ctx.tryRegs.1 ++
          ((payloadRegs s.callConv).zip ctx.tryRegs.2).filter fun q => !ps.contains q.1)) ∧
        st' = st := by
  have : externCtor ctx T.gen_try_call_rets [.op (.sig s)] st =
      match retRegs (sigRets s).length with
      | some ps =>
        if ps.length != ctx.tryRegs.1.length then .unmodeled "gen_try_call_rets: return count"
        else .ok (.op (.callRets (ps.zip ctx.tryRegs.1 ++
          ((payloadRegs s.callConv).zip ctx.tryRegs.2).filter fun q => !ps.contains q.1)), st)
      | none => .unmodeled "gen_try_call_rets: more than 8 return values" := rfl
  rw [this]
  cases retRegs (sigRets s).length with
  | none => simp
  | some ps =>
    by_cases h : ps.length = ctx.tryRegs.1.length
    · have e : ¬ ((ps.length != ctx.tryRegs.1.length) = true) := by simp [h]
      simp only [e]
      constructor
      · intro he; cases he; exact ⟨ps, rfl, h, rfl, rfl⟩
      · rintro ⟨ps', hps, -, rfl, rfl⟩; cases hps; rfl
    · have e : (ps.length != ctx.tryRegs.1.length) = true := by simp [h]
      simp only [e, ite_true]
      constructor
      · intro he; cases he
      · rintro ⟨ps', hps, h', -⟩; cases hps; exact absurd h' h

end

/-! ## The call of a `try_call` -/

theorem operands_tryCall_sym (nm : String) (L : List (Nat × Reg)) (D : List (Reg × Nat))
    (info : TryInfo) :
    (MInst.tryCall ⟨.sym nm, retPairs L, callDefs D⟩ info).operands =
      .ok (retOps L ++ callDefOps D).toArray := by
  rw [operands_tryCall_call, operands_call_sym]

theorem operands_tryCall_reg (t : Nat) (L : List (Nat × Reg)) (D : List (Reg × Nat))
    (info : TryInfo) :
    (MInst.tryCall ⟨.reg (.vreg t .int), retPairs L, callDefs D⟩ info).operands =
      .ok (tgtOp t :: (retOps L ++ callDefOps D)).toArray := by
  rw [operands_tryCall_call, operands_call_reg]

theorem seqRun_tryCall_sym {isem : Sem} {nm : String} {L : List (Nat × Reg)}
    {D : List (Reg × Nat)} {info : TryInfo} {ρ : Nat → CV} {w w' : Arm.ArmState} {outs : List CV}
    {j : Nat}
    (h : isem (.tryCall ⟨.sym nm, retPairs L, callDefs D⟩ info) (L.map (ρ ·.1)) w =
      some (outs, w', .goto j))
    (hl : outs.length = D.length) :
    seqRun isem [.tryCall ⟨.sym nm, retPairs L, callDefs D⟩ info] ρ w =
      some (.stop 0 (.tryCall ⟨.sym nm, retPairs L, callDefs D⟩ info)
        (retOps L ++ callDefOps D).toArray ρ w outs w' (.goto j)) := by
  have hl' : outs.length = ((retOps L ++ callDefOps D).toArray.toList.filter Operand.isDef).length := by
    rw [List.toList_toArray, defs_call]; simp [callDefOps, hl]
  simp only [seqRun, operands_tryCall_sym, vuses_call, h, hl', ↓reduceIte]

theorem seqRun_tryCall_reg {isem : Sem} {t : Nat} {L : List (Nat × Reg)}
    {D : List (Reg × Nat)} {info : TryInfo} {ρ : Nat → CV} {w w' : Arm.ArmState} {outs : List CV}
    {j : Nat}
    (h : isem (.tryCall ⟨.reg (.vreg t .int), retPairs L, callDefs D⟩ info) (ρ t :: L.map (ρ ·.1)) w =
      some (outs, w', .goto j))
    (hl : outs.length = D.length) :
    seqRun isem [.tryCall ⟨.reg (.vreg t .int), retPairs L, callDefs D⟩ info] ρ w =
      some (.stop 0 (.tryCall ⟨.reg (.vreg t .int), retPairs L, callDefs D⟩ info)
        (tgtOp t :: (retOps L ++ callDefOps D)).toArray ρ w outs w' (.goto j)) := by
  have hl' : outs.length =
      ((tgtOp t :: (retOps L ++ callDefOps D)).toArray.toList.filter Operand.isDef).length := by
    rw [List.toList_toArray, List.filter_cons_of_neg (by simp [tgtOp, Operand.isDef]), defs_call]
    simp [callDefOps, hl]
  simp only [seqRun, operands_tryCall_reg, vuses_call_reg, h, hl', ↓reduceIte]

/-- The return vregs hold the extern's results: the call's defs `x j ↦ vreg (b + j)`. -/
theorem retsHeld_try {b M : Nat} {rvals : List Clif.Val} {outs : List CV} {ρ : Nat → CV}
    (hol : outs.length = M) (hro : PrefixHold rvals outs) {j : Nat} {v : Clif.Val}
    (hv : rvals[j]? = some v) :
    VHolds v (writeV ρ ((callDefOps (outDefs b M)).zip outs) (b + j)) := by
  have hjr : j < rvals.length := (List.getElem?_eq_some_iff.mp hv).1
  have hjN : j < M := by have := hro.1; omega
  obtain ⟨x, hx⟩ : ∃ x, outs[j]? = some x := ⟨outs[j]'(by omega), by simp⟩
  have hk : ((callDefOps (outDefs b M)).zip outs).map (·.1.vreg) = (List.range M).map (b + ·) := by
    rw [show (fun q : Operand × CV => q.1.vreg) = Operand.vreg ∘ Prod.fst from rfl, ← List.map_map,
      List.map_fst_zip (by simp [callDefOps, outDefs, hol])]
    simp [callDefOps, outDefs]
  have hnd : (((callDefOps (outDefs b M)).zip outs).map (·.1.vreg)).Nodup := by
    rw [hk]
    exact List.Pairwise.map _ (fun a c h e => h (by omega)) List.nodup_range
  have hget : ((callDefOps (outDefs b M)).zip outs)[j]? =
      some (⟨b + j, .int, .def, .late, .fixed (.x j)⟩, x) := by
    rw [List.getElem?_zip_eq_some]
    simp [callDefOps, outDefs, hx, hjN]
  rw [writeV_nodup_ctl _ ρ j _ x hnd hget]
  exact hro.2 j v x hv hx

/-- The defs of the call are the context's return/payload vregs. -/
theorem tryDefs_mem {ctx : Ctx} {N b : Nat}
    (htr : ctx.tryRegs = ((List.range N).map fun j => Reg.vreg (b + j) .int,
      [.vreg b .int, .vreg (b + 1) .int])) :
    ∀ d ∈ (outDefs b (max N 2)).map (·.2), Reg.vreg d .int ∈ tryDefRegs ctx := by
  intro d hd
  simp only [outDefs, List.map_map, List.mem_map, List.mem_range, Function.comp_def] at hd
  obtain ⟨j, hj, rfl⟩ := hd
  show Reg.vreg (b + j) .int ∈ ctx.tryRegs.1 ++ ctx.tryRegs.2
  rw [htr]
  by_cases hjN : j < N
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hjN, rfl⟩)
  · apply List.mem_append_right
    have : j < 2 := by
      rcases Nat.le_total N 2 with h | h
      · rw [Nat.max_eq_right h] at hj; exact hj
      · rw [Nat.max_eq_left h] at hj; omega
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simp

/-- The return vregs of the context. -/
theorem tryRets_get {ctx : Ctx} {N b : Nat}
    (htr : ctx.tryRegs = ((List.range N).map fun j => Reg.vreg (b + j) .int,
      [.vreg b .int, .vreg (b + 1) .int])) {j : Nat} {r : Reg} (hr : ctx.tryRegs.1[j]? = some r) :
    j < N ∧ r = .vreg (b + j) .int := by
  rw [htr] at hr
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hr
  simp only [List.length_map, List.length_range] at hlt
  refine ⟨hlt, ?_⟩
  rw [← heq]; simp

theorem try_sym_lowerTryOk {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {exts : List Clif.ExtFunc} (hCR : CallsRefine F env exts MR isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {fn : Clif.FnRef} {args : List Nat}
    {ext : Clif.ExtFunc} (hext : f.extern? fn = some ext) (hin : ext ∈ exts)
    (h8 : ext.sig.params.length ≤ 8) {info : TryInfo} {b : Nat}
    (htr : ctx.tryRegs = ((List.range (sigRets ext.sig).length).map fun j => Reg.vreg (b + j) .int,
      [.vreg b .int, .vreg (b + 1) .int]))
    {st st' : LState} (hst' : st'.nextVreg = st.nextVreg) :
    LowerTryOk isem MR env cp ctx fn args info st st'
      [.call ⟨.sym ext.name, retPairs (args.zip ((abiArgIdx ext.sig.params 0).map Reg.x)),
        callDefs (outDefs b (max (sigRets ext.sig).length 2))⟩] := by
  refine ⟨by omega, ⟨[], _, rfl, by simp, fun d hd => ?_⟩, ?_⟩
  · rw [vdefs_call_sym] at hd
    exact tryDefs_mem htr d hd
  · intro fr cm ρ w hfr hvh _ hmr
    split
    · rename_i rvals cm' hO
      obtain ⟨vals, g, hvals, hvl, hal, hg, hgo, hrN⟩ := call_ok_facts hctx hext hfr hO
      have hfst : (args.zip ((abiArgIdx ext.sig.params 0).map Reg.x)).map (·.1) = args :=
        List.map_fst_zip (by simp [abiArgIdx_length]; omega)
      obtain ⟨sym, -, -, htry⟩ := hCR
      have huses : (args.zip ((abiArgIdx ext.sig.params 0).map Reg.x)).map (ρ ·.1) = args.map ρ := by
        rw [show (fun x : Nat × Reg => ρ x.1) = ρ ∘ (·.1) from rfl, ← List.map_map, hfst]
      have hdl : (callDefs (outDefs b (max (sigRets ext.sig).length 2))).length =
          max (sigRets ext.sig).length 2 := by
        simp [callDefs, outDefs]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := htry ext hin g fr.slots cm w (.sym ext.name)
        (retPairs (args.zip ((abiArgIdx ext.sig.params 0).map Reg.x)))
        (callDefs (outDefs b (max (sigRets ext.sig).length 2))) info
        ((args.zip ((abiArgIdx ext.sig.params 0).map Reg.x)).map (ρ ·.1)) (args.map ρ) vals rvals
        cm' hg (.inl ⟨rfl, huses⟩) (by rw [hdl]; exact Nat.le_max_left _ _) (by omega)
        (allHold_args hvh hvals) hmr hgo hrN
      have hol' : outs.length = (outDefs b (max (sigRets ext.sig).length 2)).length := by
        rw [hol, hdl]; simp [outDefs]
      rw [show ∀ c : CallInfo, tryFix info [MInst.call c] = [MInst.tryCall c info] from
        fun c => tryFix_append info [] c]
      refine ⟨?_, 0, _, _, ρ, w, outs, w', seqRun_tryCall_sym hi hol', rfl,
        fun j r v hr hv => ?_, hmr'⟩
      · intro mi hmi u hu
        simp only [List.mem_singleton] at hmi
        subst hmi
        rw [vuseNums_call_sym, hfst] at hu
        exact .inr (usesOk_args hvals u hu)
      · obtain ⟨-, rfl⟩ := tryRets_get htr hr
        refine ⟨b + j, rfl, ?_⟩
        rw [vdefUpd_call]
        exact retsHeld_try (by rw [hol', outDefs, List.length_map, List.length_range]) hro hv
    · trivial

set_option maxHeartbeats 5000000 in
theorem try_bl_ruleOk {p : Program} (hp : Data p) (hpT : TryData p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {exts : List Clif.ExtFunc} (hCR : CallsRefine F env exts MR isem) :
    TryRuleOk isem MR env cp exts p rule_lower_2542 := by
  intro f ctx hctx hreg hexts ti fn args et data sig items targets info lo st1 hd he hi hinfo htr
    hvb cfg hc m n st tr env' s1 out st' tr' hm hn hst _ hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he0, hext, hsig⟩ := tryCallData_spec hd
  rw [he] at he0
  simp only [Except.ok.injEq, Prod.mk.injEq] at he0
  obtain ⟨rfl, rfl⟩ := he0
  rw [tryCallData_eq he hext hsig] at hd
  cases hd
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  cases hp
  obtain ⟨t300, t302, t2297, t2474⟩ := hpT
  ctl_inv [*, rule_lower_2542, ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iff] at hmatch heval
  simp only [hi, hfn, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iff, ext_value_list_slice_iff, ctor_put_in_regs_vec_iff] at * <;>
    isel_destruct <;> subst_vars)
  have hx' := ‹ctx.func.extern? fn = some _›
  rw [hctx.func, hext] at hx'
  cases hx'
  have hti' := ‹tryInfoOf ext.sig items targets = some _›
  rw [hinfo] at hti'
  cases hti'
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  have h8 : bytes.length ≤ 8 := sigParamBytes_length hb ▸ hreg fn _ hext
  have hrs := mapM_valueReg hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_iff _ _ _ hb h8, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_info_iff _ _ _ _ _ _ _ hb h8, Option.some.injEq] at *
  isel_destruct; subst_vars
  obtain ⟨hr8, rfl⟩ := retRegs_eq ‹retRegs _ = some _›
  have h638 := ‹ApplyInternal _ _ _ _ 46 638 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h638
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_call] at hmi
  cases hmi
  obtain ⟨-, htrs, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc he) htr
  rw [htrs, exnTableOpnd_cc he, tryDefs_eq _ _ hr8] at hs2
  rw [uses_retPairs] at hs2
  have hcd : ((List.range (max (sigRets ext.sig).length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max (sigRets ext.sig).length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs1 hs2
  refine ⟨_, ?_, try_sym_lowerTryOk hCR hctx hext (hexts fn _ hext) (hreg fn _ hext) htrs
    (by rw [hs2, hs1]; simp [LState.emit])⟩
  rw [hs2, hs1]; simp [LState.emit]

theorem try_got_lowerTryOk {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} (hMR : MRStable F MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefine F env exts MR isem) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc} (hext : f.extern? fn = some ext)
    (hin : ext ∈ exts) (h8 : ext.sig.params.length ≤ 8) {info : TryInfo} {b : Nat}
    (htr : ctx.tryRegs = ((List.range (sigRets ext.sig).length).map fun j => Reg.vreg (b + j) .int,
      [.vreg b .int, .vreg (b + 1) .int]))
    {st st' : LState} (hargs : ∀ x ∈ args, x < st.nextVreg)
    (hst' : st'.nextVreg = st.nextVreg + 1) :
    LowerTryOk isem MR env cp ctx fn args info st st'
      [.loadExtNameGot (.vreg st.nextVreg .int) ext.name,
       .call ⟨.reg (.vreg st.nextVreg .int),
        retPairs (args.zip ((abiArgIdx ext.sig.params 0).map Reg.x)),
        callDefs (outDefs b (max (sigRets ext.sig).length 2))⟩] := by
  refine ⟨by omega, ⟨[.loadExtNameGot (.vreg st.nextVreg .int) ext.name], _, rfl, ?_, ?_⟩, ?_⟩
  · intro m hm d hd
    simp only [List.mem_singleton] at hm
    subst hm
    rw [vdefs_got_ctl] at hd
    simp only [List.mem_singleton] at hd
    omega
  · intro d hd
    rw [vdefs_call_reg] at hd
    exact tryDefs_mem htr d hd
  · intro fr cm ρ w hfr hvh _ hmr
    split
    · rename_i rvals cm' hO
      obtain ⟨vals, g, hvals, hvl, hal, hg, hgo, hrN⟩ := call_ok_facts hctx hext hfr hO
      have hfst : (args.zip ((abiArgIdx ext.sig.params 0).map Reg.x)).map (·.1) = args :=
        List.map_fst_zip (by simp [abiArgIdx_length]; omega)
      obtain ⟨sym, hgot, -, htry⟩ := hCR
      obtain ⟨w1, hw1, hsw⟩ := hgot (.vreg st.nextVreg .int) ext.name w
      have hmr1 := hMR _ _ _ _ hsw hmr
      have hrun1 := seqRun_got (F := F) (ρ := ρ) hw1
      generalize ht : st.nextVreg = t at hrun1 hw1 hargs ⊢
      have hρ1 : ∀ x ∈ args, upd ρ t (ofX (sym ext.name)) x = ρ x := by
        intro x hx
        have := hargs x hx
        simp only [upd]
        rw [if_neg (by omega)]
      have huses : (args.zip ((abiArgIdx ext.sig.params 0).map Reg.x)).map
          (upd ρ t (ofX (sym ext.name)) ·.1) = args.map ρ := by
        rw [show (fun x : Nat × Reg => upd ρ t (ofX (sym ext.name)) x.1) =
          upd ρ t (ofX (sym ext.name)) ∘ (·.1) from rfl, ← List.map_map, hfst]
        exact List.map_congr_left hρ1
      have hdl : (callDefs (outDefs b (max (sigRets ext.sig).length 2))).length =
          max (sigRets ext.sig).length 2 := by
        simp [callDefs, outDefs]
      have ht1 : upd ρ t (ofX (sym ext.name)) t = ofX (sym ext.name) := by simp [upd]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := htry ext hin g fr.slots cm w1
        (.reg (.vreg t .int))
        (retPairs (args.zip ((abiArgIdx ext.sig.params 0).map Reg.x)))
        (callDefs (outDefs b (max (sigRets ext.sig).length 2))) info
        (upd ρ t (ofX (sym ext.name)) t ::
          (args.zip ((abiArgIdx ext.sig.params 0).map Reg.x)).map (upd ρ t (ofX (sym ext.name)) ·.1))
        (args.map ρ) vals rvals cm' hg
        (.inr ⟨_, rfl, by rw [ht1, huses]⟩) (by rw [hdl]; exact Nat.le_max_left _ _) (by omega)
        (allHold_args hvh hvals) hmr1 hgo hrN
      have hol' : outs.length = (outDefs b (max (sigRets ext.sig).length 2)).length := by
        rw [hol, hdl]; simp [outDefs]
      have hrun2 := seqRun_tryCall_reg (info := info) hi hol'
      rw [show ∀ c : CallInfo, tryFix info [MInst.loadExtNameGot (.vreg t .int) ext.name,
          MInst.call c] = [MInst.loadExtNameGot (.vreg t .int) ext.name] ++ [MInst.tryCall c info]
        from fun c => tryFix_append info [_] c]
      refine ⟨?_, _, _, _, _, _, outs, w',
        seqRun_append_fall_stop isem (ms1 := [_]) hrun1 hrun2, rfl, fun j r v hr hv => ?_, hmr'⟩
      · intro mi hmi u hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmi
        rcases hmi with rfl | rfl
        · simp [vuseNums_got_ctl] at hu
        · rw [vuseNums_call_reg, hfst] at hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact .inl (by omega)
          · exact .inr (usesOk_args hvals u hu)
      · obtain ⟨-, rfl⟩ := tryRets_get htr hr
        refine ⟨b + j, rfl, ?_⟩
        rw [vdefUpd_call_reg]
        exact retsHeld_try (by rw [hol', outDefs, List.length_map, List.length_range]) hro hv
    · trivial

set_option maxHeartbeats 20000000 in
theorem try_got_ruleOk {p : Program} (hp : Data p) (hpT : TryData p) {F : BitVec 64 → Prop}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {exts : List Clif.ExtFunc} (hCR : CallsRefine F env exts MR isem) :
    TryRuleOk isem MR env cp exts p rule_lower_2551 := by
  intro f ctx hctx hreg hexts ti fn args et data sig items targets info lo st1 hd he hi hinfo htr
    hvb cfg hc m n st tr env' s1 out st' tr' hm hn hst _ hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kL := fun n (hn : 40 ≤ n) nm d s v s' h => load_ext_name_ok_ctl hp (ctx := ctx) hc (n := n)
    (nm := nm) (d := d) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he0, hext, hsig⟩ := tryCallData_spec hd
  rw [he] at he0
  simp only [Except.ok.injEq, Prod.mk.injEq] at he0
  obtain ⟨rfl, rfl⟩ := he0
  rw [tryCallData_eq he hext hsig] at hd
  cases hd
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  cases hp
  obtain ⟨t300, t302, t2297, t2474⟩ := hpT
  ctl_inv [*, rule_lower_2551, ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iff, ctor_box_external_name_iff] at hmatch heval
  simp only [hi, hfn, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iff, ext_value_list_slice_iff, ctor_put_in_regs_vec_iff,
    ctor_box_external_name_iff] at * <;> isel_destruct <;> subst_vars)
  have hx' := ‹ctx.func.extern? fn = some _›
  rw [hctx.func, hext] at hx'
  cases hx'
  have hti' := ‹tryInfoOf ext.sig items targets = some _›
  rw [hinfo] at hti'
  cases hti'
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
  simp only [ctor_gen_call_ind_info_iff _ _ _ _ _ _ hb h8, Option.some.injEq] at *
  isel_destruct; subst_vars
  obtain ⟨hr8, rfl⟩ := retRegs_eq ‹retRegs _ = some _›
  have h639 := ‹ApplyInternal _ _ _ _ 46 639 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h639
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_callInd] at hmi
  cases hmi
  obtain ⟨-, htrs, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc he) htr
  rw [htrs, exnTableOpnd_cc he, tryDefs_eq _ _ hr8] at hs2
  rw [uses_retPairs] at hs2
  have hcd : ((List.range (max (sigRets ext.sig).length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max (sigRets ext.sig).length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs0 hs1 hs2
  have hfr : ∀ s : LState, (s.fresh .int).1 = .vreg s.nextVreg .int := fun s => rfl
  rw [hfr] at hs2 hs0
  refine ⟨_, ?_, try_got_lowerTryOk hMR hCR hctx hext (hexts fn _ hext) (hreg fn _ hext) htrs
    (fun x hx => by have := hbelow x hx; omega)
    (by rw [hs2, hs1, hs0]; simp [LState.emit, LState.fresh])⟩
  rw [hs2, hs1, hs0]
  simp only [LState.emit, LState.fresh]
  rw [← Array.toList_inj]
  simp

/-! ## Assembly -/

/-- In a list whose rule ids are distinct, a rule is determined by its id. -/
theorem eq_of_mem_of_rid {r r0 : Rule} :
    ∀ {L : List Rule}, (L.map Rule.id).Nodup → r ∈ L → r0 ∈ L → r.id = r0.id → r = r0
  | [], _, hr, _, _ => by cases hr
  | a :: L, hnd, hr, hr0, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    rcases List.mem_cons.mp hr with h1 | h1 <;> rcases List.mem_cons.mp hr0 with h2 | h2
    · rw [h1, h2]
    · subst h1; exact absurd h.symm (fun e => hnd.1 r0 h2 e)
    · subst h2; exact absurd h (fun e => hnd.1 r h1 e)
    · exact eq_of_mem_of_rid hnd.2 h1 h2 h

theorem mem_lower_branch_2542 : rule_lower_2542 ∈ program.rulesOf TId.lower_branch := by
  rw [show TId.lower_branch = 687 from rfl, data_program.r687]
  simp

theorem mem_lower_branch_2551 : rule_lower_2551 ∈ program.rulesOf TId.lower_branch := by
  rw [show TId.lower_branch = 687 from rfl, data_program.r687]
  simp

/-- **`TryRulesCorrect`**: under the callee contract, the `try_call` rules of `lower_branch`
(`bl`, rule id 1034; GOT + `blr`, rule id 1035) are correct. -/
theorem tryRulesCorrect : TryRulesCorrect program := by
  intro F isem MR env cp exts hR hMR hCR r hr hroot
  simp only [tryRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
  have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
    rw [show TId.lower_branch = 687 from rfl, data_program.r687]
    decide +kernel
  rcases hroot with h | h
  · rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2542 (by rw [h]; rfl)]
    exact try_bl_ruleOk data_program tryData_program hR hMR hCR
  · rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2551 (by rw [h]; rfl)]
    exact try_got_ruleOk data_program tryData_program hR hMR hCR

/-- The root format of the rules of `lower_branch` other than the `try_call` rules is not
`TryCall` (2474). -/
def tryFmtOk (r : Rule) : Bool :=
  tryRootRule r ||
    match ruleFmt r with
    | some fT => 2447 ≤ fT && fT < 2447 + 36 && fT != 2474
    | none => false

theorem lower_branch_try_fmts : (program.rulesOf TId.lower_branch).all tryFmtOk = true := by
  rw [show TId.lower_branch = 687 from rfl, data_program.r687]
  decide +kernel

/-- **`TryUnmatchable`**: no rule of `lower_branch` other than 1034/1035 matches a `try_call`. -/
theorem tryUnmatchable : TryUnmatchable program := by
  intro r hr hroot f ctx hctx ti fn args et data targets hd hi cfg m s env' s1 hmatch
  have hok := List.all_eq_true.mp lower_branch_try_fmts r hr
  simp only [tryFmtOk, hroot, Bool.false_or] at hok
  split at hok
  · rename_i fT hfT
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨hlo, hhi⟩, h1⟩ := hok
    obtain ⟨info, fs, hinfo, hdat⟩ :=
      ruleFmt_match (vs := [.labels targets]) data_program fmtKinds_program hfT hlo hhi hmatch
    rw [hi] at hinfo
    cases hinfo
    obtain ⟨sig, items, ext, he, hx, hs⟩ := tryCallData_spec hd
    rw [tryCallData_eq he hx hs] at hd
    cases hd
    simp only [V.data.injEq] at hdat
    omega
  · cases hok

end Backend.Proof
