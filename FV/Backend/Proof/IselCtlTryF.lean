import FV.Backend.Proof.IselCtlCallF
import FV.Backend.Proof.IselCtlTryInd

/-!
# Family Ctl over typed contexts: `try_call` with `f32`/`f64` arguments and returns (S11e6)

The `try_call` rules of `lower_branch` (`bl`, rule 1034 `rule_lower_2542`; GOT + `blr`, rule 1035
`rule_lower_2551`) on float-capable contexts for every extern signature the lowering accepts
(`exnTableOpndC`, `tryCallDataC`), not only integer ones (`IselCtlTryTI`'s `TryRulesCorrectTP`
takes `exnTableOpnd`, integer arguments by `TermIntPos` and integer returns by `tryRegsOf`). As
Cranelift's aarch64 lowering (`gen_call_args`, `gen_try_call_rets`, `try_call_rets`):

* each argument is passed in its value's vreg of the value's class, at `sigArgLocs`' location
  (x0..x7 / v0..v7, then the outgoing area, `str s`/`str d` for a float vreg), as for `call`
  (`IselCtlCallF`);
* each ABI return has a fresh vreg of its class (`tryRegsOfC`), defined by the call from the return
  register `retRegsC` gives it; the exception payload registers x0, x1 that are not return
  registers get fresh integer vregs, also defined by the call (`gen_try_call_rets`).

The contract is `LowerTryOkPC`: `LowerTryOkP` with the return and payload vregs of either class
(`LowerTryOkP.toC`: the integer contract is an instance). `tryRegsOfC_defs`: the call's defs are
`outDefsC b (ps ++ fr) (cs ++ ints)`, the returns' registers `ps` and the remaining payload
registers `fr` into consecutive fresh vregs from `b` (so the defs' vregs are distinct).

Results: `TryRulesCorrectTFP` (the pinned `try_call` family over `CallCtxT`, every extern
signature, with `MemRefinesFP`), `tryRulesCorrectTFP_program`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## The contract and the family -/

/-- **`lower_branch` on a `try_call` with typed returns** (`LowerTryOkP` with the return and
payload vregs of either class): the code ends in a call whose defs are among the return and
payload vregs, the instructions before it define fresh vregs; with the last call replaced by the
`tryCall`, a normal return of the callee runs to the `tryCall` with outcome
`goto info.handlers.length`, the return vregs holding the results. -/
structure LowerTryOkPC (Rd : BitVec 64 → Prop)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (isem : Sem) (MR : MemRelT)
    (env : Clif.Env) (p : Clif.Program) (ctx : Ctx) (ci : Clif.Inst) (info : TryInfo)
    (st st' : LState) (ms : List MInst) : Prop where
  mono : st.nextVreg ≤ st'.nextVreg
  shape : ∃ pre ci, ms = pre ++ [.call ci] ∧
    (∀ m ∈ pre, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg) ∧
    ∀ d ∈ vdefs (.call ci), ∃ c, Reg.vreg d c ∈ tryDefRegs ctx
  run : ∀ (fr : Clif.Frame) (cm : Clif.Mem) (ρ : Nat → CV) (w : Arm.ArmState),
    fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → MR fr.slots cm w → InitIn Rd cm →
    CallPin Pc env ci fr cm →
    match instOutcome env p fr cm ci with
    | .ok (rvals, cm') => UsesOk st fr ms ∧ ∃ k i ops ρ₁ w₁ outs w₂,
        seqRun isem (tryFix info ms) ρ w =
          some (.stop k i ops ρ₁ w₁ outs w₂ (.goto info.handlers.length)) ∧
        k + 1 = ms.length ∧
        (∀ (j : Nat) r v, ctx.tryRegs.1[j]? = some r → rvals[j]? = some v →
          ∃ n c, r = .vreg n c ∧ VHolds v (vdefUpd ops outs ρ₁ n)) ∧
        MR fr.slots cm' w₂
    | _ => True

/-- The integer contract is an instance of the typed one. -/
theorem LowerTryOkP.toC {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {p : Clif.Program} {ctx : Ctx} {ci : Clif.Inst} {info : TryInfo}
    {st st' : LState} {ms : List MInst} (h : LowerTryOkP Rd Pc isem MR env p ctx ci info st st' ms) :
    LowerTryOkPC Rd Pc isem MR env p ctx ci info st st' ms := by
  obtain ⟨hmono, ⟨pre, c, hms, hpre, hdefs⟩, hrun⟩ := h
  refine ⟨hmono, ⟨pre, c, hms, hpre, fun d hd => ⟨.int, hdefs d hd⟩⟩, ?_⟩
  intro fr cm ρ w hf hv hd hmr hin hpin
  have := hrun fr cm ρ w hf hv hd hmr hin hpin
  split
  · rename_i rvals cm' hO
    rw [hO] at this
    obtain ⟨hu, k, i, ops, ρ₁, w₁, outs, w₂, hs, hk, hr, hm⟩ := this
    refine ⟨hu, k, i, ops, ρ₁, w₁, outs, w₂, hs, hk, fun j r v hr' hv' => ?_, hm⟩
    obtain ⟨n, rfl, hh⟩ := hr j r v hr' hv'
    exact ⟨n, .int, rfl, hh⟩
  · trivial

/-- `TryRuleOkTP` over the call facts of float-capable contexts (`CallCtxT`) for `try_call`s of
any extern signature (`tryCallDataC`, `exnTableOpndC`, `tryRegsOfC`), with the typed contract. -/
def TryRuleOkTFP (Rd : BitVec 64 → Prop)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (isem : Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (exts : List Clif.ExtFunc) (outB : Nat) (p : Program)
    (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CallCtxT f ctx → ExternsIn f exts →
  ∀ (ti : Nat) (fn : Clif.FnRef) (args : List Nat) (et : Clif.ExnTable) (data : V)
    (sig : Clif.Signature) (items : List (Option Nat)) (targets : List Label) (info : TryInfo)
    (lo st1 : LState),
  (∀ e, f.extern? fn = some e → SigStackOk e.sig outB) →
  tryCallDataC f (.tryCall fn args et) = .ok data →
  exnTableOpndC f et = .ok (sig, items) →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ → tryInfoOf sig items targets = some info →
  tryRegsOfC sig lo = some (ctx.tryRegs, st1) → ValsBelow ctx lo →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n →
    st1.nextVreg ≤ st.nextVreg →
    (∀ pre post, p.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti, .labels targets]).run (st, tr) =
        .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run (st, tr) =
      .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkPC Rd Pc isem MR env cp ctx (.call fn args) info st st' ms

/-- **The `try_call` roots of `lower_branch` over float-capable contexts, for every extern
signature, with pinned calls**: `TryRulesCorrectTP` with `f32`/`f64` arguments and returns (the
float stack-argument stores under `MemRefinesFP`). -/
def TryRulesCorrectTFP (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → MemRefinesFP Rd F sb isem →
    OutArgsOk F outB MR → CallsRefineP Pc F env exts MR isem →
    ∀ r ∈ p.rulesOf TId.lower_branch, tryRootRule r = true →
      TryRuleOkTFP Rd Pc isem MR env cp exts outB p r

/-! ## The typed return and payload vregs -/

/-- The payload fold of `tryRegsOfC`: a payload register that is a return register (`ps`) gets
that return's vreg, the others consecutive fresh integer vregs. -/
theorem payFoldC (ps : List Reg) (rets : Array Reg) :
    ∀ (pr : List Reg) (acc : Array Reg) (s : LState),
    ∃ pays, (pr.foldl (fun (x : Array Reg × LState) p => match ps.idxOf? p with
        | some i => (x.1.push rets[i]!, x.2)
        | none => (x.1.push (x.2.fresh .int).1, (x.2.fresh .int).2)) (acc, s)).1.toList =
          acc.toList ++ pays ∧
      (pr.zip pays).filter (fun q => !ps.contains q.1) =
        callDefsC (outDefsC s.nextVreg (pr.filter fun p => !ps.contains p)
          (List.replicate (pr.filter fun p => !ps.contains p).length .int)) ∧
      (pr.foldl (fun (x : Array Reg × LState) p => match ps.idxOf? p with
        | some i => (x.1.push rets[i]!, x.2)
        | none => (x.1.push (x.2.fresh .int).1, (x.2.fresh .int).2)) (acc, s)).2.nextVreg =
          s.nextVreg + (pr.filter fun p => !ps.contains p).length
  | [], acc, s => ⟨[], by simp, by simp [callDefsC, outDefsC], by simp⟩
  | p :: pr, acc, s => by
    simp only [List.foldl_cons]
    cases hi : ps.idxOf? p with
    | some i =>
      dsimp only
      have hmem : p ∈ ps := Classical.byContradiction fun hn => by
        rw [List.idxOf?_eq_none_iff.mpr hn] at hi
        cases hi
      obtain ⟨pays, h1, h2, h3⟩ := payFoldC ps rets pr (acc.push rets[i]!) s
      refine ⟨rets[i]! :: pays, by rw [h1]; simp, ?_, ?_⟩
      · rw [List.zip_cons_cons, List.filter_cons_of_neg (by simp [hmem]), h2,
          List.filter_cons_of_neg (by simp [hmem])]
      · rw [h3, List.filter_cons_of_neg (by simp [hmem])]
    | none =>
      dsimp only
      have hnm : p ∉ ps := List.idxOf?_eq_none_iff.mp hi
      obtain ⟨pays, h1, h2, h3⟩ := payFoldC ps rets pr (acc.push (s.fresh .int).1) (s.fresh .int).2
      refine ⟨(s.fresh .int).1 :: pays, by rw [h1]; simp, ?_, ?_⟩
      · rw [List.zip_cons_cons, List.filter_cons_of_pos (by simp [hnm]), h2,
          List.filter_cons_of_pos (by simp [hnm])]
        simp only [callDefsC, outDefsC, LState.fresh, List.length_cons, List.replicate_succ,
          List.zipIdx_cons, List.zip_cons_cons, List.map_cons, Nat.add_zero]
        congr 1
        rw [List.zipIdx_succ]
        simp [List.zip_map_right, List.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
      · rw [h3, List.filter_cons_of_pos (by simp [hnm])]
        simp [LState.fresh]
        omega

/-- The return fold of `tryRegsOfC`: one fresh vreg per return, of the return's class. -/
theorem retFoldC : ∀ (L : List Clif.AbiParam) (acc : Array Reg) (s : LState),
    (L.foldl (fun (x : Array Reg × LState) q =>
        ((x.1.push (x.2.fresh (retClass q)).1), (x.2.fresh (retClass q)).2)) (acc, s)).1.toList =
      acc.toList ++ ((L.map retClass).zipIdx.map fun q => Reg.vreg (s.nextVreg + q.2) q.1) ∧
    (L.foldl (fun (x : Array Reg × LState) q =>
        ((x.1.push (x.2.fresh (retClass q)).1), (x.2.fresh (retClass q)).2)) (acc, s)).2.nextVreg =
      s.nextVreg + L.length
  | [], acc, s => by simp
  | q :: L, acc, s => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := retFoldC L (acc.push (s.fresh (retClass q)).1) (s.fresh (retClass q)).2
    refine ⟨?_, ?_⟩
    · rw [h1]
      simp only [Array.toList_push, List.append_assoc, List.map_cons, List.zipIdx_cons,
        List.map_cons, LState.fresh, Nat.add_zero, List.singleton_append]
      congr 2
      rw [List.zipIdx_succ]
      simp [List.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
    · rw [h2]; simp [LState.fresh]; omega

/-- `outDefsC` of concatenated registers and classes. -/
theorem outDefsC_append (b : Nat) {ps fr : List Reg} {cs ds : List RegClass}
    (h : ps.length = cs.length) :
    outDefsC b (ps ++ fr) (cs ++ ds) = outDefsC b ps cs ++ outDefsC (b + cs.length) fr ds := by
  simp only [outDefsC, List.zipIdx_append, List.map_append, Nat.zero_add]
  rw [List.zip_append (by simp [h] : ps.length = cs.zipIdx.length), List.map_append]
  congr 1
  rw [List.zipIdx_eq_map_add (l := ds)]
  simp [List.zip_map_right, List.map_map, Function.comp_def, Nat.add_assoc]

/-- **The return and payload vregs of a typed `try_call`** (`tryRegsOfC`): the returns' vregs are
fresh from `b = st.nextVreg`, of the returns' classes; the defs `gen_try_call_rets` makes of them
(the return registers `ps`, then the payload registers that are not return registers, `fr`) are
`outDefsC b (ps ++ fr) (cs ++ ints)`: consecutive fresh vregs. Over the declared returns since
#587 (`tryRegsOfC` allocates none for an `sret` callee's struct pointer, as Cranelift). -/
theorem tryRegsOfC_defs {sig : Clif.Signature} {st st1 : LState} {trs : List Reg × List Reg}
    (h : tryRegsOfC sig st = some (trs, st1)) :
    ∃ ps, retRegsC (sig.returns.map retClass) 0 0 = some ps ∧
      trs.1 = (sig.returns.map retClass).zipIdx.map (fun q => Reg.vreg (st.nextVreg + q.2) q.1) ∧
      ps.zip trs.1 ++ ((payloadRegs sig.callConv).zip trs.2).filter (fun q => !ps.contains q.1) =
        callDefsC (outDefsC st.nextVreg
          (ps ++ (payloadRegs sig.callConv).filter fun p => !ps.contains p)
          (sig.returns.map retClass ++
            List.replicate ((payloadRegs sig.callConv).filter fun p => !ps.contains p).length .int)) ∧
      st1.nextVreg = st.nextVreg + sig.returns.length +
        ((payloadRegs sig.callConv).filter fun p => !ps.contains p).length := by
  obtain ⟨rets, pays⟩ := trs
  simp only
  unfold tryRegsOfC at h
  cases hr : retRegsC (sig.returns.map retClass) 0 0 with
  | none => rw [hr] at h; cases h
  | some ps =>
    rw [hr] at h
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨hrets, hpays⟩, hst⟩ := h
    obtain ⟨r1, r2⟩ := retFoldC sig.returns #[] st
    generalize hR : sig.returns.foldl (fun (x : Array Reg × LState) q =>
      ((x.1.push (x.2.fresh (retClass q)).1), (x.2.fresh (retClass q)).2)) (#[], st) = R at r1 r2 hrets hpays hst
    obtain ⟨pl, p1, p2, p3⟩ := payFoldC ps R.1 (payloadRegs sig.callConv) #[] R.2
    have hps : ps.length = (sig.returns.map retClass).length := retRegsC_lengthC _ _ _ hr
    simp only [Array.toList_empty, List.nil_append] at r1 p1
    -- the folds of `tryRegsOfC` are the lemmas' (their `match`es are different matchers)
    have hpl : pays = pl := by rw [← hpays]; exact p1
    have hst' : st1.nextVreg = R.2.nextVreg +
        ((payloadRegs sig.callConv).filter fun p => !ps.contains p).length := by
      rw [← hst]; exact p3
    have hrl : rets = (sig.returns.map retClass).zipIdx.map
        (fun q => Reg.vreg (st.nextVreg + q.2) q.1) := by rw [← hrets, r1]
    refine ⟨ps, rfl, hrl, ?_, by rw [hst', r2]⟩
    rw [hpl, p2, hrl, r2, callDefsC_outDefsC, outDefsC_append _ hps, List.length_map]
    simp [callDefsC]

/-- The typed defs' vregs are consecutive from `b`. -/
theorem outDefsC_app_vregs (b : Nat) {ps fp : List Reg} {cs : List RegClass}
    (hps : ps.length = cs.length) :
    (outDefsC b (ps ++ fp) (cs ++ List.replicate fp.length .int)).map (·.2.1) =
      (List.range (cs.length + fp.length)).map (b + ·) := by
  rw [outDefsC_vregs b (by simp [hps])]
  simp

theorem outDefsC_app_length (b : Nat) {ps fp : List Reg} {cs : List RegClass}
    (hps : ps.length = cs.length) :
    (outDefsC b (ps ++ fp) (cs ++ List.replicate fp.length .int)).length = cs.length + fp.length := by
  rw [outDefsC_length b (by simp [hps])]
  simp

/-- The return vregs hold the extern's results: the call's `j`-th def is the `j`-th return. -/
theorem retsHeld_tryC {b : Nat} {ps fp : List Reg} {cs : List RegClass} (hps : ps.length = cs.length)
    {rvals : List Clif.Val} {outs : List CV} {ρ : Nat → CV}
    (hol : outs.length = cs.length + fp.length) (hro : PrefixHold rvals outs) {j : Nat} {v : Clif.Val}
    (hv : rvals[j]? = some v) {c : RegClass} (hc : cs[j]? = some c) :
    VHolds v (writeV ρ ((callDefOpsC (outDefsC b (ps ++ fp)
      (cs ++ List.replicate fp.length .int))).zip outs) (b + j)) := by
  have hjN : j < cs.length := (List.getElem?_eq_some_iff.mp hc).1
  obtain ⟨x, hx⟩ : ∃ x, outs[j]? = some x := ⟨outs[j]'(by omega), by simp⟩
  obtain ⟨p, hp⟩ : ∃ p, ps[j]? = some p := ⟨ps[j]'(by omega), by simp⟩
  have hk : ((callDefOpsC (outDefsC b (ps ++ fp) (cs ++ List.replicate fp.length .int))).zip
      outs).map (·.1.vreg) = (List.range (cs.length + fp.length)).map (b + ·) := by
    rw [show (fun q : Operand × CV => q.1.vreg) = Operand.vreg ∘ Prod.fst from rfl, ← List.map_map,
      List.map_fst_zip (by simp [callDefOpsC, outDefsC_app_length b hps, hol])]
    rw [← outDefsC_app_vregs b hps]
    simp [callDefOpsC]
  have hnd : (((callDefOpsC (outDefsC b (ps ++ fp) (cs ++ List.replicate fp.length .int))).zip
      outs).map (·.1.vreg)).Nodup := by
    rw [hk]
    exact List.Pairwise.map _ (fun a c h e => h (by omega)) List.nodup_range
  have hget : ((callDefOpsC (outDefsC b (ps ++ fp) (cs ++ List.replicate fp.length .int))).zip
      outs)[j]? = some (⟨b + j, c, .def, .late, .fixed p⟩, x) := by
    rw [List.getElem?_zip_eq_some]
    refine ⟨?_, hx⟩
    have hpj : (ps ++ fp)[j]? = some p := by rw [List.getElem?_append_left (by omega)]; exact hp
    have hcj : (cs ++ List.replicate fp.length .int)[j]? = some c := by
      rw [List.getElem?_append_left hjN]; exact hc
    simp [callDefOpsC, outDefsC, List.getElem?_zip_eq_some, List.getElem?_zipIdx, hpj, hcj]
    exact ⟨_, _, _, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  rw [writeV_nodup_ctl _ ρ j _ x hnd hget]
  obtain ⟨hlen, hall⟩ := hro
  exact hall j v x hv hx

/-- The typed data of a direct `try_call`: its callee's signature is the exception table's. -/
theorem tryCallDataC_spec {f : Clif.Function} {fn : Clif.FnRef} {args : List Clif.ValueId}
    {et : Clif.ExnTable} {data : V} (h : tryCallDataC f (.tryCall fn args et) = .ok data) :
    ∃ sig items ext, exnTableOpndC f et = .ok (sig, items) ∧ f.extern? fn = some ext ∧
      ext.sig = sig := by
  simp only [tryCallDataC] at h
  cases he : exnTableOpndC f et with
  | error e => simp [he, bind, Except.bind] at h
  | ok q =>
    obtain ⟨sig, items⟩ := q
    cases hx : f.extern? fn with
    | none => simp [he, hx, bind, Except.bind] at h
    | some ext =>
      by_cases hs : ext.sig = sig
      · exact ⟨sig, items, ext, rfl, rfl, hs⟩
      · simp [he, hx, hs, bind, Except.bind] at h

theorem tryCallDataC_eq {f : Clif.Function} {fn : Clif.FnRef} {args : List Clif.ValueId}
    {et : Clif.ExnTable} {sig : Clif.Signature} {items : List (Option Nat)} {ext : Clif.ExtFunc}
    (he : exnTableOpndC f et = .ok (sig, items)) (hx : f.extern? fn = some ext) (hs : ext.sig = sig) :
    tryCallDataC f (.tryCall fn args et) = .ok (.data 152 27 [.data 151 13 [], .values args,
      .op (.funcRef fn), .op (.exnTable sig items)]) := by
  simp only [tryCallDataC, he, hx, hs, bind, Except.bind, bne_self_eq_false, Bool.false_eq_true,
    ite_false, pure, Except.pure]
  rfl

/-! ## The call of a typed `try_call` -/

theorem seqRun_tryCall_symC {isem : Sem} {nm : String} {L : List (Nat × RegClass × Reg)}
    {D : List (Reg × Nat × RegClass)} {info : TryInfo} {ρ : Nat → CV} {w w' : Arm.ArmState}
    {outs : List CV} {j : Nat}
    (h : isem (.tryCall ⟨.sym nm, argPairsC L, callDefsC D⟩ info) (L.map (ρ ·.1)) w =
      some (outs, w', .goto j))
    (hl : outs.length = D.length) :
    seqRun isem [.tryCall ⟨.sym nm, argPairsC L, callDefsC D⟩ info] ρ w =
      some (.stop 0 (.tryCall ⟨.sym nm, argPairsC L, callDefsC D⟩ info)
        (retOpsC L ++ callDefOpsC D).toArray ρ w outs w' (.goto j)) := by
  have hl' : outs.length = ((retOpsC L ++ callDefOpsC D).toArray.toList.filter Operand.isDef).length := by
    rw [List.toList_toArray, defs_callC]; simp [callDefOpsC, hl]
  simp only [seqRun, operands_tryCall_call, operands_call_symC, vuses_callC, h, hl', ↓reduceIte]

theorem seqRun_tryCall_regC {isem : Sem} {t : Nat} {L : List (Nat × RegClass × Reg)}
    {D : List (Reg × Nat × RegClass)} {info : TryInfo} {ρ : Nat → CV} {w w' : Arm.ArmState}
    {outs : List CV} {j : Nat}
    (h : isem (.tryCall ⟨.reg (.vreg t .int), argPairsC L, callDefsC D⟩ info) (ρ t :: L.map (ρ ·.1)) w =
      some (outs, w', .goto j))
    (hl : outs.length = D.length) :
    seqRun isem [.tryCall ⟨.reg (.vreg t .int), argPairsC L, callDefsC D⟩ info] ρ w =
      some (.stop 0 (.tryCall ⟨.reg (.vreg t .int), argPairsC L, callDefsC D⟩ info)
        (tgtOp t :: (retOpsC L ++ callDefOpsC D)).toArray ρ w outs w' (.goto j)) := by
  have hl' : outs.length =
      ((tgtOp t :: (retOpsC L ++ callDefOpsC D)).toArray.toList.filter Operand.isDef).length := by
    rw [List.toList_toArray, List.filter_cons_of_neg (by simp [tgtOp, Operand.isDef]), defs_callC]
    simp [callDefOpsC, hl]
  simp only [seqRun, operands_tryCall_call, operands_call_regC, vuses_call_regC, h, hl', ↓reduceIte]

/-- A typed return vreg of the context (`tryRegsOfC`'s): the `j`-th, of the `j`-th class. -/
theorem tryRetsC_get {ctx : Ctx} {cs : List RegClass} {b : Nat}
    (htr : ctx.tryRegs.1 = cs.zipIdx.map fun q => Reg.vreg (b + q.2) q.1) {j : Nat} {r : Reg}
    (hr : ctx.tryRegs.1[j]? = some r) : ∃ c, cs[j]? = some c ∧ r = .vreg (b + j) c := by
  rw [htr] at hr
  simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_eq_some_iff] at hr
  obtain ⟨⟨c, k⟩, hck, rfl⟩ := hr
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hck
  obtain ⟨c', hc', rfl, rfl⟩ := hck
  exact ⟨_, hc', by simp⟩

/-- The defs of the call are the context's return/payload vregs (`gen_try_call_rets` of
`tryRegsOfC`'s vregs). -/
theorem tryDefsC_mem {ctx : Ctx} {ps pr : List Reg} {D : List (Reg × Nat × RegClass)}
    (hD : ps.zip ctx.tryRegs.1 ++ (pr.zip ctx.tryRegs.2).filter (fun q => !ps.contains q.1) =
      callDefsC D) :
    ∀ d ∈ D.map (·.2.1), ∃ c, Reg.vreg d c ∈ tryDefRegs ctx := by
  intro d hd
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
  refine ⟨q.2.2, ?_⟩
  have hm : (q.1, Reg.vreg q.2.1 q.2.2) ∈ callDefsC D := List.mem_map_of_mem hq
  rw [← hD] at hm
  show _ ∈ ctx.tryRegs.1 ++ ctx.tryRegs.2
  rcases List.mem_append.mp hm with hm | hm
  · exact List.mem_append_left _ (List.of_mem_zip hm).2
  · exact List.mem_append_right _ (List.of_mem_zip (List.mem_filter.mp hm).1).2

/-! ## `try_call` by `bl` and by GOT + `blr`, typed -/

theorem try_sym_lowerTryOkTF {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefineP Pc F env exts MR isem) {f : Clif.Function} {ctx : Ctx}
    (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S)) {info : TryInfo}
    (hrets : info.rets ≤ ext.sig.returns.length) {b : Nat} {ps fp : List Reg}
    (hps : ps.length = (ext.sig.returns.map retClass).length)
    (htr : ctx.tryRegs.1 = (ext.sig.returns.map retClass).zipIdx.map fun q => Reg.vreg (b + q.2) q.1)
    (hdefs : ∀ d ∈ (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
      List.replicate fp.length .int)).map (·.2.1), ∃ c, Reg.vreg d c ∈ tryDefRegs ctx)
    {st st' : LState} (hst' : st'.nextVreg = st.nextVreg) :
    LowerTryOkPC Rd Pc isem MR env cp ctx (.call fn args) info st st'
      ((stackEnts ((locs.zip args).zip bytes)).map (argStoreC (valClassOf ctx)) ++
        [.call ⟨.sym ext.name, argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))),
          callDefsC (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
            List.replicate fp.length .int))⟩]) := by
  refine ⟨by omega, ⟨(stackEnts ((locs.zip args).zip bytes)).map (argStoreC (valClassOf ctx)), _, rfl,
    ?_, fun d hd => ?_⟩, ?_⟩
  · intro m hm d hd
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
    simp [vdefs_argStoreC] at hd
  · rw [vdefs_call_symC] at hd
    exact hdefs d hd
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
      obtain ⟨sym, -, -, htry⟩ := hCR
      have hdl : (callDefsC (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
          List.replicate fp.length .int))).length = ext.sig.returns.length + fp.length := by
        rw [callDefsC, List.length_map, outDefsC_app_length b hps, List.length_map]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := htry ext hin g fr.slots cm w1 (.sym ext.name)
        (argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))))
        (callDefsC (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
          List.replicate fp.length .int))) info
        _ _ vals rvals cm' hg (.inl ⟨rfl, rfl⟩) (by rw [hdl]; omega) hrets
        (hargs w1 (SameWorldNF.refl F w1)) hmr1 hpc hgo hrN
      rw [← liftC_vals (valClassOf ctx)] at hi
      have hol' : outs.length = (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
          List.replicate fp.length .int)).length := by
        rw [hol, callDefsC, List.length_map]
      rw [tryFix_append]
      refine ⟨?_, _, _, _, _, _, outs, w',
        seqRun_append_fall_stop isem hrun1 (seqRun_tryCall_symC hi hol'), by simp,
        fun j r v hr hv => ?_, hmr'⟩
      · intro mi hmi u hu
        rcases List.mem_append.mp hmi with hmi | hmi
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmi
          rw [vuseNums_argStoreC, List.mem_singleton] at hu
          subst hu
          exact .inr (usesOk_args hvals _ (map_zip_args (mem_args_of_stackEnts he)))
        · simp only [List.mem_singleton] at hmi
          subst hmi
          rw [vuseNums_call_symC, liftC_fst] at hu
          exact .inr (usesOk_args hvals u (map_zip_args (mem_args_of_regPairs hu)))
      · obtain ⟨c, hc, rfl⟩ := tryRetsC_get htr hr
        refine ⟨b + j, c, rfl, ?_⟩
        rw [vdefUpd_callC]
        exact retsHeld_tryC hps (by rw [hol, hdl, List.length_map]) hro hv hc
    · trivial

theorem try_got_lowerTryOkTF {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefineP Pc F env exts MR isem) {f : Clif.Function} {ctx : Ctx}
    (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hcol : ext.colocated = false)
    (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S)) {info : TryInfo}
    (hrets : info.rets ≤ ext.sig.returns.length) {b : Nat} {ps fp : List Reg}
    (hps : ps.length = (ext.sig.returns.map retClass).length)
    (htr : ctx.tryRegs.1 = (ext.sig.returns.map retClass).zipIdx.map fun q => Reg.vreg (b + q.2) q.1)
    (hdefs : ∀ d ∈ (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
      List.replicate fp.length .int)).map (·.2.1), ∃ c, Reg.vreg d c ∈ tryDefRegs ctx)
    {st st' : LState} (hargs : ∀ x ∈ args, x < st.nextVreg)
    (hst' : st'.nextVreg = st.nextVreg + 1) :
    LowerTryOkPC Rd Pc isem MR env cp ctx (.call fn args) info st st'
      ((stackEnts ((locs.zip args).zip bytes)).map (argStoreC (valClassOf ctx)) ++
       [.loadExtNameGot (.vreg st.nextVreg .int) ext.name,
        .call ⟨.reg (.vreg st.nextVreg .int),
          argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))),
          callDefsC (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
            List.replicate fp.length .int))⟩]) := by
  refine ⟨by omega, ⟨(stackEnts ((locs.zip args).zip bytes)).map (argStoreC (valClassOf ctx)) ++
    [.loadExtNameGot (.vreg st.nextVreg .int) ext.name], _, by rw [List.append_assoc]; rfl, ?_,
    fun d hd => ?_⟩, ?_⟩
  · intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
      simp [vdefs_argStoreC] at hd
    · simp only [List.mem_singleton] at hm
      subst hm
      rw [vdefs_got_ctl] at hd
      simp only [List.mem_singleton] at hd
      omega
  · rw [vdefs_call_regC] at hd
    exact hdefs d hd
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
      obtain ⟨sym, hgot, -, htry⟩ := hCR
      obtain ⟨w2, hw2, hsw⟩ := hgot (.vreg st.nextVreg .int) ext.name w1
      have hmr2 := hMR _ _ _ _ hsw hmr1
      have hrun2 := seqRun_got (F := F) (ρ := ρ) hw2
      generalize ht : st.nextVreg = t at hrun2 hw2 hsw hargs ⊢
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
      have hdl : (callDefsC (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
          List.replicate fp.length .int))).length = ext.sig.returns.length + fp.length := by
        rw [callDefsC, List.length_map, outDefsC_app_length b hps, List.length_map]
      have ht1 : upd ρ t (ofX (sym ext.name)) t = ofX (sym ext.name) := by simp [upd]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := htry ext hin g fr.slots cm w2
        (.reg (.vreg t .int)) (argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))))
        (callDefsC (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
          List.replicate fp.length .int))) info
        (upd ρ t (ofX (sym ext.name)) t ::
          (regPairsOf ((locs.zip args).zip bytes)).map (upd ρ t (ofX (sym ext.name)) ·.1))
        ((regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1)) vals rvals cm' hg
        (.inr ⟨_, rfl, hcol, by rw [ht1, huses]⟩) (by rw [hdl]; omega) hrets
        (hargsAt w2 hsw) hmr2 hpc hgo hrN
      rw [← liftC_vals (valClassOf ctx)] at hi
      have hol' : outs.length = (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
          List.replicate fp.length .int)).length := by
        rw [hol, callDefsC, List.length_map]
      have hrun3 := seqRun_tryCall_regC (info := info) hi hol'
      rw [show ∀ c : CallInfo, tryFix info ((stackEnts ((locs.zip args).zip bytes)).map
          (argStoreC (valClassOf ctx)) ++ [MInst.loadExtNameGot (.vreg t .int) ext.name, MInst.call c]) =
          ((stackEnts ((locs.zip args).zip bytes)).map (argStoreC (valClassOf ctx)) ++
            [MInst.loadExtNameGot (.vreg t .int) ext.name]) ++ [MInst.tryCall c info]
        from fun c => by rw [← tryFix_append info _ c]; simp]
      refine ⟨?_, _, _, _, _, _, outs, w',
        seqRun_append_fall_stop isem (seqRun_append_fall' isem hrun1 hrun2) hrun3, by simp,
        fun j r v hr hv => ?_, hmr'⟩
      · intro mi hmi u hu
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
      · obtain ⟨c, hc, rfl⟩ := tryRetsC_get htr hr
        refine ⟨b + j, c, rfl, ?_⟩
        rw [vdefUpd_call_regC]
        exact retsHeld_tryC hps (by rw [hol, hdl, List.length_map]) hro hv hc
    · trivial

set_option maxHeartbeats 5000000 in
/-- **`try_call` by `bl`** (`rule_lower_2542`) over float-capable contexts, any extern signature. -/
theorem try_bl_ruleOkTF {p : Program} (hp : Data p) (hpT : TryData p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefineP Pc F env exts MR isem) :
    TryRuleOkTFP Rd Pc isem MR env cp exts outB p rule_lower_2542 := by
  intro f ctx hctx hexts ti fn args et data sig items targets info lo st1 hreg hd he hi hinfo
    htr hvb cfg hc m n st tr env' s1 out st' tr' hm hn hst _ hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he0, hext, hsig⟩ := tryCallDataC_spec hd
  rw [he] at he0
  simp only [Except.ok.injEq, Prod.mk.injEq] at he0
  obtain ⟨rfl, rfl⟩ := he0
  rw [tryCallDataC_eq he hext hsig] at hd
  cases hd
  subst hsig
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  obtain ⟨ps0, hps0, htr1, hD, -⟩ := tryRegsOfC_defs htr
  cases hp
  obtain ⟨t300, t302, t2297, t2474⟩ := hpT
  ctl_inv [*, rule_lower_2542, ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iffC] at hmatch heval
  simp only [hi, hfn, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iffC, ext_value_list_slice_iff, ctor_put_in_regs_vec_iff] at * <;>
    isel_destruct <;> subst_vars)
  have hx' := ‹ctx.func.extern? fn = some _›
  rw [hctx.func, hext] at hx'
  cases hx'
  have hti' := ‹tryInfoOf ext.sig items targets = some _›
  rw [hinfo] at hti'
  cases hti'
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegC hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_genC _ _ _ (valClassOf ctx) hb hl, mapM_single_map,
    Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  try (simp only [ctor_gen_try_call_rets_iffC] at *; isel_destruct; subst_vars)
  simp only [ctor_gen_call_info_gen _ _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hps := retRegsC_lengthC _ _ _ hps0
  have h638 := ‹ApplyInternal _ _ _ _ 46 638 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h638
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_call] at hmi
  cases hmi
  have hpsq := ‹retRegsC _ 0 0 = some _›
  rw [hps0] at hpsq
  cases hpsq
  rw [hD] at hs2
  simp only at hs1 hs2
  refine ⟨_, ?_, try_sym_lowerTryOkTF hMR hMem hFP hout hCR hctx.func hext (hexts fn _ hext)
    (hreg _ hext) hb hl (Nat.le_of_eq (tryInfoOf_rets hinfo)) hps htr1
    (tryDefsC_mem hD) (by rw [hs2, hs1]; simp [LState.emit])⟩
  rw [hs2, hs1]; simp [LState.emit]

set_option maxHeartbeats 20000000 in
/-- **`try_call` by GOT + `blr`** (`rule_lower_2551`) over float-capable contexts, any extern
signature. -/
theorem try_got_ruleOkTF {p : Program} (hp : Data p) (hpT : TryData p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefineP Pc F env exts MR isem) :
    TryRuleOkTFP Rd Pc isem MR env cp exts outB p rule_lower_2551 := by
  intro f ctx hctx hexts ti fn args et data sig items targets info lo st1 hreg hd he hi hinfo
    htr hvb cfg hc m n st tr env' s1 out st' tr' hm hn hst hfirst hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kL := fun n (hn : 40 ≤ n) nm d s v s' h => load_ext_name_ok_ctl hp (ctx := ctx) hc (n := n)
    (nm := nm) (d := d) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he0, hext, hsig⟩ := tryCallDataC_spec hd
  rw [he] at he0
  simp only [Except.ok.injEq, Prod.mk.injEq] at he0
  obtain ⟨rfl, rfl⟩ := he0
  rw [tryCallDataC_eq he hext hsig] at hd
  cases hd
  subst hsig
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  have hcol : ext.colocated = false := try_got_not_colocated hp hpT hi hfirst hfn
  clear hfirst
  obtain ⟨ps0, hps0, htr1, hD, hst1⟩ := tryRegsOfC_defs htr
  cases hp
  obtain ⟨t300, t302, t2297, t2474⟩ := hpT
  ctl_inv [*, rule_lower_2551, ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iffC, ctor_box_external_name_iff] at hmatch heval
  simp only [hi, hfn, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iffC, ext_value_list_slice_iff, ctor_put_in_regs_vec_iff,
    ctor_box_external_name_iff] at * <;> isel_destruct <;> subst_vars)
  have hx' := ‹ctx.func.extern? fn = some _›
  rw [hctx.func, hext] at hx'
  cases hx'
  have hti' := ‹tryInfoOf ext.sig items targets = some _›
  rw [hinfo] at hti'
  cases hti'
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
  try (simp only [ctor_gen_try_call_rets_iffC] at *; isel_destruct; subst_vars)
  simp only [ctor_gen_call_ind_info_gen _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hps := retRegsC_lengthC _ _ _ hps0
  have h639 := ‹ApplyInternal _ _ _ _ 46 639 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h639
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_callInd] at hmi
  cases hmi
  have hpsq := ‹retRegsC _ 0 0 = some _›
  rw [hps0] at hpsq
  cases hpsq
  rw [hD] at hs2
  rw [show ∀ s : LState, (s.fresh .int).1 = .vreg s.nextVreg .int from fun s => rfl] at hs2 hs0
  simp only at hs0 hs1 hs2
  refine ⟨_, ?_, try_got_lowerTryOkTF hMR hMem hFP hout hCR hctx.func hext (hexts fn _ hext) hcol
    (hreg _ hext) hb hl (Nat.le_of_eq (tryInfoOf_rets hinfo)) hps htr1 (tryDefsC_mem hD)
    (fun x hx => by have := hbelow x hx; omega)
    (by rw [hs2, hs1, hs0]; simp [LState.emit, LState.fresh])⟩
  rw [hs2, hs1, hs0]
  simp only [LState.emit, LState.fresh]
  rw [← Array.toList_inj]
  simp

/-! ## Assembly -/

/-- **`TryRulesCorrectTFP`**: under the pinned callee contract and the guarded integer and float
memory forms, the `try_call` rules of `lower_branch` (1034, 1035) are correct over float-capable
contexts, for `try_call`s of any extern signature (`f32`/`f64` arguments in v0..v7 or on the
stack, `f32`/`f64` returns from v0..v7 into fresh float vregs). -/
theorem tryRulesCorrectTFP_program : TryRulesCorrectTFP program := by
  intro Rd Pc F isem MR env cp exts sb syms outB _ hMR hMem hFP hout hCR r hr hroot
  simp only [tryRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
  have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
    rw [show TId.lower_branch = 687 from rfl, data_program.r687]
    decide +kernel
  rcases hroot with h | h
  · rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2542 (by rw [h]; rfl)]
    exact try_bl_ruleOkTF data_program tryData_program hMR hMem hFP hout hCR
  · rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2551 (by rw [h]; rfl)]
    exact try_got_ruleOkTF data_program tryData_program hMR hMem hFP hout hCR

end Backend.Proof
