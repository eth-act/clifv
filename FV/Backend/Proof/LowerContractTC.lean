import FV.Backend.Proof.IselCtlTryF
import FV.Compile.SubsetTC

/-!
# The driver's typed `try_call`s from the typed rule family (S11e6, #419)

`LowerContractT.lean`'s `try_call` part for `lowerFunction`'s typed `try_call`s (`tryCallDataC`,
`exnTableOpndC`, `tryRegsOfC`, `DriverCheckC.lean`):

* `LowerTryOkC`: `LowerTryOk` with return and payload vregs of either class (the unpinned
  instance of `LowerTryOkPC`, `LowerTryOkPC.toOk`; `LowerTryOk.toC`: the integer contract is an
  instance);
* `TryUnmatchableTC`, `tryUnmatchableTC_program`: the rules of `lower_branch` other than 1034,
  1035 never match a typed `try_call` (they only read the data's format);
* `TryCallsTC` (the driver's typed `try_call` calls of one context) and `tryCallsTC_of_rules`,
  from the proven typed family `tryRulesCorrectTFP_program` (`IselCtlTryF.lean`) and
  `tryUnmatchableTC_program`; no rule-family premise is left;
* contexts: `ctxT_of_functionETC` (`CtxT` of `buildCtx`'s context of a `functionETC` function),
  `termIntPos_of_functionETC` (the integer operands of its other terminators).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64 Backend.Proof.Driver

/-- **`lower_branch` on a `try_call` with typed returns** (`LowerTryOk` with the return and
payload vregs of either class). -/
structure LowerTryOkC {W : Type} (isem : ISem CV W) (MR : MemRelTW W) (env : Clif.Env)
    (p : Clif.Program) (ctx : Ctx)
    (ci : Clif.Inst) (info : TryInfo) (st st' : LState) (ms : List MInst) :
    Prop where
  mono : st.nextVreg ≤ st'.nextVreg
  shape : ∃ pre ci, ms = pre ++ [.call ci] ∧
    (∀ m ∈ pre, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg) ∧
    ∀ d ∈ vdefs (.call ci), ∃ c, Reg.vreg d c ∈ tryDefRegs ctx
  run : ∀ (fr : Clif.Frame) (cm : Clif.Mem) (ρ : Nat → CV) (w : W),
    fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → MR fr.slots cm w →
    match instOutcome env p fr cm ci with
    | .ok (rvals, cm') => UsesOk st fr ms ∧ ∃ k i ops ρ₁ w₁ outs w₂,
        seqRun isem (tryFix info ms) ρ w =
          some (.stop k i ops ρ₁ w₁ outs w₂ (.goto info.handlers.length)) ∧
        k + 1 = ms.length ∧
        (∀ (j : Nat) r v, ctx.tryRegs.1[j]? = some r → rvals[j]? = some v →
          ∃ n c, r = .vreg n c ∧ VHolds v (vdefUpd ops outs ρ₁ n)) ∧
        MR fr.slots cm' w₂
    | _ => True

/-- The unpinned typed contract from the pinned one (no read guard, no call pin). -/
theorem LowerTryOkPC.toOk {isem : Sem} {MR : MemRelT} {env : Clif.Env} {p : Clif.Program}
    {ctx : Ctx} {ci : Clif.Inst} {info : TryInfo} {st st' : LState} {ms : List MInst}
    (h : LowerTryOkPC (fun _ => True) (fun _ _ _ _ => True) isem MR env p ctx ci info st st' ms) :
    LowerTryOkC isem MR env p ctx ci info st st' ms :=
  ⟨h.mono, h.shape, fun fr cm ρ w hf hv hd hmr =>
    h.run fr cm ρ w hf hv hd hmr (fun _ _ _ => trivial) ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial⟩⟩

/-- The integer contract is an instance of the typed one. -/
theorem LowerTryOk.toC {W : Type} {isem : ISem CV W} {MR : MemRelTW W} {env : Clif.Env}
    {p : Clif.Program} {ctx : Ctx} {ci : Clif.Inst} {info : TryInfo} {st st' : LState}
    {ms : List MInst} (h : LowerTryOk isem MR env p ctx ci info st st' ms) :
    LowerTryOkC isem MR env p ctx ci info st st' ms := by
  obtain ⟨hmono, ⟨pre, c, hms, hpre, hdefs⟩, hrun⟩ := h
  refine ⟨hmono, ⟨pre, c, hms, hpre, fun d hd => ⟨.int, hdefs d hd⟩⟩, ?_⟩
  intro fr cm ρ w hf hv hd hmr
  have := hrun fr cm ρ w hf hv hd hmr
  split
  · rename_i rvals cm' hO
    rw [hO] at this
    obtain ⟨hu, k, i, ops, ρ₁, w₁, outs, w₂, hs, hk, hr, hm⟩ := this
    refine ⟨hu, k, i, ops, ρ₁, w₁, outs, w₂, hs, hk, fun j r v hr' hv' => ?_, hm⟩
    obtain ⟨n, rfl, hh⟩ := hr j r v hr' hv'
    exact ⟨n, .int, rfl, hh⟩
  · trivial

/-! ## The typed `try_call` vregs -/

theorem getElem!_mem_toList_reg (rets : Array Reg) (i : Nat) (h : i < rets.size) :
    rets[i]! ∈ rets.toList := by
  rw [getElem!_pos rets i h]
  exact Array.getElem_mem_toList h

/-- The payload fold of `tryRegsOfC` allocates above the returns: every payload vreg is a return's
or fresh. -/
theorem payBoundC (ps : List Reg) (rets : Array Reg) (lo hi0 : Nat) (hlo : lo ≤ hi0)
    (hsz : ps.length ≤ rets.size)
    (hrets : ∀ r ∈ rets.toList, ∃ n c, r = .vreg n c ∧ lo ≤ n ∧ n < hi0) :
    ∀ (pr : List Reg) (acc : Array Reg) (s : LState), hi0 ≤ s.nextVreg →
    (∀ r ∈ acc.toList, ∃ n c, r = .vreg n c ∧ lo ≤ n ∧ n < s.nextVreg) →
    s.nextVreg ≤ (pr.foldl (fun (x : Array Reg × LState) p => match ps.idxOf? p with
        | some i => (x.1.push rets[i]!, x.2)
        | none => (x.1.push (x.2.fresh .int).1, (x.2.fresh .int).2)) (acc, s)).2.nextVreg ∧
    ∀ r ∈ (pr.foldl (fun (x : Array Reg × LState) p => match ps.idxOf? p with
        | some i => (x.1.push rets[i]!, x.2)
        | none => (x.1.push (x.2.fresh .int).1, (x.2.fresh .int).2)) (acc, s)).1.toList,
      ∃ n c, r = .vreg n c ∧ lo ≤ n ∧ n < (pr.foldl (fun (x : Array Reg × LState) p =>
        match ps.idxOf? p with
        | some i => (x.1.push rets[i]!, x.2)
        | none => (x.1.push (x.2.fresh .int).1, (x.2.fresh .int).2)) (acc, s)).2.nextVreg
  | [], acc, s, _, h3 => ⟨Nat.le_refl _, h3⟩
  | p :: pr, acc, s, h1, h3 => by
    simp only [List.foldl_cons]
    cases hi : ps.idxOf? p with
    | some i =>
      dsimp only
      have hlt : i < ps.length := (List.idxOf?_eq_some_iff.mp hi).1
      obtain ⟨n, c, hn, h4, h5⟩ := hrets _ (getElem!_mem_toList_reg rets i (by omega))
      exact payBoundC ps rets lo hi0 hlo hsz hrets pr _ s h1 (by
        intro r hr
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact h3 r hr
        · exact ⟨n, c, hn, h4, by omega⟩)
    | none =>
      dsimp only
      have := payBoundC ps rets lo hi0 hlo hsz hrets pr (acc.push (s.fresh .int).1) (s.fresh .int).2
        (by simp only [LState.fresh]; omega) (by
          intro r hr
          simp only [Array.toList_push, List.mem_append, List.mem_singleton, LState.fresh] at hr ⊢
          rcases hr with hr | rfl
          · obtain ⟨n, c, h, h', h''⟩ := h3 r hr
            exact ⟨n, c, h, h', by omega⟩
          · exact ⟨_, _, rfl, by omega, by omega⟩)
      refine ⟨Nat.le_trans (by simp [LState.fresh]) this.1, this.2⟩

/-- **The vregs of a typed `try_call` are fresh**: every return and payload vreg of
`tryRegsOfC sig st` is a vreg allocated from `st` (below the state after). -/
theorem tryRegsOfC_bounds {sig : Clif.Signature} {st st1 : LState} {trs : List Reg × List Reg}
    (h : tryRegsOfC sig st = some (trs, st1)) :
    ∀ r ∈ trs.1 ++ trs.2, ∃ n c, r = .vreg n c ∧ st.nextVreg ≤ n ∧ n < st1.nextVreg := by
  obtain ⟨rets, pays⟩ := trs
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
    have hps : ps.length = (sig.returns.map retClass).length := retRegsC_lengthC _ _ _ hr
    simp only [List.nil_append] at r1
    have hRb : ∀ r ∈ R.1.toList, ∃ n c, r = .vreg n c ∧ st.nextVreg ≤ n ∧ n < R.2.nextVreg := by
      intro r hr'
      rw [r1] at hr'
      obtain ⟨⟨c, i⟩, hq, rfl⟩ := List.mem_map.mp hr'
      obtain ⟨-, hlt, -⟩ := List.mem_zipIdx hq
      simp only [List.length_map, Nat.zero_add] at hlt
      exact ⟨_, _, rfl, Nat.le_add_right _ _, by rw [r2]; omega⟩
    have hsz : ps.length ≤ R.1.size := by
      have := congrArg List.length r1
      simp only [Array.length_toList, List.length_map, List.length_zipIdx] at this
      rw [hps, List.length_map, this]; exact Nat.le_refl _
    obtain ⟨hmono, hpb⟩ := payBoundC ps R.1 st.nextVreg R.2.nextVreg (by rw [r2]; omega) hsz hRb
      (payloadRegs sig.callConv) #[] R.2 (Nat.le_refl _) (by simp)
    intro r hr'
    simp only [List.mem_append] at hr'
    rcases hr' with hr' | hr'
    · rw [← hrets] at hr'
      obtain ⟨n, c, h1, h2, h3⟩ := hRb r hr'
      exact ⟨n, c, h1, h2, by rw [← hst]; exact Nat.lt_of_lt_of_le h3 hmono⟩
    · rw [← hpays] at hr'
      obtain ⟨n, c, h1, h2, h3⟩ := hpb r hr'
      exact ⟨n, c, h1, h2, by rw [← hst]; exact h3⟩

/-- The `i`-th return vreg of a typed `try_call` is the `i`-th fresh vreg (of the return's
class). Over the declared returns (#587: the old `sigRets` bound is false for an `sret` callee,
whose struct pointer gets no vreg, as in Cranelift). -/
theorem tryRegsOfC_rets {sig : Clif.Signature} {st st1 : LState} {trs : List Reg × List Reg}
    (h : tryRegsOfC sig st = some (trs, st1)) {i : Nat} (hi : i < sig.returns.length) :
    ∃ c, trs.1[i]? = some (.vreg (st.nextVreg + i) c) := by
  obtain ⟨ps, -, h1, -, -⟩ := tryRegsOfC_defs h
  rw [h1]
  exact ⟨retClass sig.returns[i], by simp [hi]⟩

/-- The rules of `lower_branch` other than the `try_call` roots never match a typed `try_call`
(data `tryCallDataC`), in any context. -/
def TryUnmatchableTC (p : Program) : Prop :=
  ∀ r ∈ p.rulesOf TId.lower_branch, tryRootRule r = false →
  ∀ (ctx : Ctx) (f : Clif.Function) (ti : Nat) (fn : Clif.FnRef) (args : List Nat)
    (et : Clif.ExnTable) (data : V) (targets : List Label),
  tryCallDataC f (.tryCall fn args et) = .ok data → ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config) (m : Nat) (s : LState × Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId),
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run s ≠ .ok (some env', s1)

/-- **`TryUnmatchableTC`**: no rule of `lower_branch` other than 1034/1035 matches a typed
`try_call`. -/
theorem tryUnmatchableTC_program : TryUnmatchableTC program := by
  intro r hr hroot ctx f ti fn args et data targets hd hi cfg m s env' s1 hmatch
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
    obtain ⟨sig, items, ext, he, hx, hs⟩ := tryCallDataC_spec hd
    rw [tryCallDataC_eq he hx hs] at hd
    cases hd
    simp only [V.data.injEq] at hdat
    omega
  · cases hok

theorem tryOkC_of_rules {p : Program} (hp : Data p) (hrules : TryRulesCorrectTFP p)
    (hun : TryUnmatchableTC p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {exts : List Clif.ExtFunc}
    (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms isem) (hFP : MemRefinesFP (fun _ => True) F sb isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) (hcr : CallsRefine F env exts MR isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CallCtxT f ctx)
    (hext : ExternsIn f exts) {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable}
    {data : V} {sig : Clif.Signature} {items : List (Option Nat)} {targets : List Label}
    {info : TryInfo} {lo st1 : LState} (hra : ∀ e, f.extern? fn = some e → SigStackOk e.sig outB)
    (hd : tryCallDataC f (.tryCall fn args et) = .ok data)
    (he : exnTableOpndC f et = .ok (sig, items))
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOfC sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower_branch).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId}
    (hst : st1.nextVreg ≤ st.nextVreg)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower_branch [.inst ti, .labels targets]).run
      (st, tr) = .ok (some out, (st', tr'))) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkC isem MR env cp ctx (.call fn args) info st st' ms := by
  change 1002 + (p.rulesOf 687).length ≤ n at hn
  obtain ⟨r, pre0, post0, hsplit, hpre0, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some_first hco hp.t687 term_687_kind rfl h
  have hr : r ∈ p.rulesOf TId.lower_branch := by
    change r ∈ p.rulesOf 687; rw [hsplit]; simp
  have hfirst : ∀ pre post, p.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre,
      ∃ m', 1000 ≤ m' ∧ ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti, .labels targets]).run
        (st, tr) = .ok (none, s') := by
    intro pre post hsp r' hr'
    have hnd : (pre0 ++ r :: post0).Nodup := hsplit ▸ lower_branch_rules_nodup hp
    have hpre := prefix_unique_of_nodup hnd (hsplit.symm.trans hsp)
    subst hpre
    obtain ⟨m', hm', s', h'⟩ := hpre0 r' hr'
    exact ⟨m', by omega, s', h'⟩
  simp only [Prod.mk.injEq] at hs
  rw [← hs.1] at heval
  cases hroot : tryRootRule r
  · exact absurd hmatch (hun r hr hroot ctx f ti fn args et data targets hd hi cfg m (st, tr) env' s1)
  · obtain ⟨ms, h1, h2⟩ := hrules (fun _ => True) (fun _ _ _ _ => True) F isem MR env cp exts sb
      syms outB hR hMR (memRefinesR_of hMem) hFP hout (hcr.toP _) r hr hroot f ctx hctx hext ti fn
      args et data sig items targets info lo st1 hra hd he hi hinfo htr hvb cfg hco m n st tr env'
      s1 out st' tr2 (by omega) (by omega) hst hfirst hmatch heval
    exact ⟨ms, h1, h2.toOk⟩

set_option maxRecDepth 20000 in
/-- `tryOkC_of_rules` for the exported program and the backend's call on a typed `try_call`. -/
theorem tryOkC_runTerm
    {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {exts : List Clif.ExtFunc} (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat}
    {syms : String → Option Nat} (hMem : MemRefines F sb syms isem)
    (hFP : MemRefinesFP (fun _ => True) F sb isem) {outB : Nat}
    (hout : OutArgsOk F outB MR)
    (hcr : CallsRefine F env exts MR isem) {f : Clif.Function} {ctx : Ctx} (hctx : CallCtxT f ctx)
    (hext : ExternsIn f exts) {ti : Nat} {fn : Clif.FnRef}
    {args : List Nat} {et : Clif.ExnTable} {data : V} {sig : Clif.Signature}
    {items : List (Option Nat)} {targets : List Label} {info : TryInfo} {lo st1 : LState}
    (hra : ∀ e, f.extern? fn = some e → SigStackOk e.sig outB)
    (hd : tryCallDataC f (.tryCall fn args et) = .ok data)
    (he : exnTableOpndC f et = .ok (sig, items))
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOfC sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hst : st1.nextVreg ≤ st.nextVreg)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkC isem MR env cp ctx (.call fn args) info st st' ms := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower_branch] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower_branch.ret T.lower_branch.id
      [.inst ti, .labels targets]).run (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf TId.lower_branch).length ≤ 1000 := by
      rw [show TId.lower_branch = 687 from rfl, data_program.r687]; decide
    obtain ⟨ms, h1, h2⟩ := tryOkC_of_rules data_program tryRulesCorrectTFP_program
      tryUnmatchableTC_program hR hMR hMem hFP hout hcr hctx hext hra hd he hi hinfo htr hvb rfl
      (by omega) hst ha
    exact ⟨ms, by simpa using h1, h2⟩

end Backend.Proof

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- Every `lower_branch` call `lowerFunction` makes on a direct `try_call` of `f` in context
`ctx`, with the typed helpers, satisfies `LowerTryOkC` (`TryCallsT` with typed `try_call`s). -/
def TryCallsTC {W : Type} (f : Clif.Function) (ctx : Ctx) (sem : ISem CV W) (MR : MemRelTW W)
    (env : Clif.Env) (p : Clif.Program) (outB : Nat) : Prop :=
  ∀ ti fn args et data sig items targets info trs lo st1 out st' tr,
    (∀ e, f.extern? fn = some e → SigStackOk e.sig outB) →
    tryCallDataC f (.tryCall fn args et) = .ok data →
    exnTableOpndC f et = .ok (sig, items) → ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ →
    tryInfoOf sig items targets = some info → tryRegsOfC sig lo = some (trs, st1) →
    ValsBelow ctx lo →
    runTerm (tryCtx ctx ti data trs) "lower_branch" [.inst ti, .labels targets]
      { st1 with emitted := #[] } = .ok (some out, st', tr) →
    LowerTryOkC sem MR env p (tryCtx ctx ti data trs) (.call fn args) info
      { st1 with emitted := #[] } st' st'.emitted.toList

/-- The call facts of a float-capable context hold after filling in a terminator's data and the
`try_call` vregs. -/
theorem callCtxT_tryCtx {f : Clif.Function} {ctx : Ctx} (h : CtxInvT f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V)
    (trs : List Reg × List Reg) : CallCtxT f (tryCtx ctx ti data trs) :=
  let h' := ctxInvT_termCtx h hph data
  ⟨h'.func, h'.data, h'.resTys, h'.valueReg⟩

/-- **From the proven typed `try_call` family to the driver's typed `try_call` calls** in a
float-capable context (under the callee contract for `f`'s externs and the float accesses'
`MemRefinesFP`). -/
theorem tryCallsTC_of_rules {F : BitVec 64 → Prop} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {f : Clif.Function} {ctx : Ctx}
    (hR : Refines F sem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat} (hMem : MemRefines F sb syms sem)
    (hFP : MemRefinesFP (fun _ => True) F sb sem)
    {outB : Nat} (hout : OutArgsOk F outB MR) (hcr : CallsRefine F env (f.externs.map (·.2)) MR sem)
    (hctx : CtxInvT f ctx) : TryCallsTC f ctx sem MR env p outB := by
  intro ti fn args et data sig items targets info trs lo st1 out st' tr hra hd he hph
    hinfo hregs hvb hrun
  have hctx' := callCtxT_tryCtx hctx hph data trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOfC sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  obtain ⟨ms, hem, hok⟩ := tryOkC_runTerm hR hMR hMem hFP hout hcr hctx' (externsIn_self f) hra
    hd he hi hinfo hregs' hvb' (st := { st1 with emitted := #[] }) (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]; exact hok

/-! ## Contexts of the scope with typed `try_call`s -/

/-- The callees of the `call` statements of `buildCtx`'s context of a `functionETC` function have
integer signatures. -/
theorem callsE_of_functionETC {f : Clif.Function} (hT : Compile.functionETC f = true)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hb : buildCtx f = .ok (ctx, ranges, st0)) : CallsE f ctx := by
  intro ii info fn args e hi hc he
  obtain ⟨B, hB, s, hs, -, hsi⟩ := (ctxSpec_of hb).inst_of hi hc
  simp only [Compile.functionETC, Compile.callsE, Bool.and_eq_true, List.all_eq_true] at hT
  have := hT.1.1.1.2 B hB s hs
  rw [← hsi] at this
  simpa [he] using this

/-- **`CtxT` of a `functionETC` function's context** (the typed shape gives `CtxInvT` and
`InstScopeT`). -/
theorem ctxT_of_functionETC {f : Clif.Function} (hT : Compile.functionETC f = true)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hb : buildCtx f = .ok (ctx, ranges, st0)) (hinv : CtxInvT f ctx) (hsc : InstScopeT ctx) :
    CtxT f ctx :=
  ⟨hinv, hsc.toTF, callsE_of_functionETC hT hb⟩

/-- The integer-position operands of a `functionETC` function's terminators other than the
direct `try_call`s. -/
theorem termIntPos_of_functionETC {f : Clif.Function} (hT : Compile.functionETC f = true)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hb : buildCtx f = .ok (ctx, ranges, st0)) {B : Clif.Block} (hB : B ∈ f.blocks)
    (hnt : ∀ fn args et, B.term ≠ .tryCall fn args et) : TermIntPos ctx B.term := by
  intro x hx t ht
  refine (ctxSpec_of hb).eCTys_of_not_floatDef ht fun hfd => ?_
  simp only [Compile.functionETC, Compile.opsTypedTC, Bool.and_eq_true, List.all_eq_true] at hT
  have hx' : x ∈ Compile.termIntOperandsC B.term := by
    cases h : B.term <;> rw [h] at hx <;> first | exact absurd h (hnt _ _ _) | exact hx
  have := (hT.1.2 B hB).2 x hx'
  simp [hfd] at this

/-! ## Contexts of the scope with the float operations (S11f) -/

/-- The callees of the `call` statements of `buildCtx`'s context of a `functionETCF` function
have integer signatures. -/
theorem callsE_of_functionETCF {f : Clif.Function} (hT : Compile.functionETCF f = true)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hb : buildCtx f = .ok (ctx, ranges, st0)) : CallsE f ctx := by
  intro ii info fn args e hi hc he
  obtain ⟨B, hB, s, hs, -, hsi⟩ := (ctxSpec_of hb).inst_of hi hc
  simp only [Compile.functionETCF, Compile.callsE, Bool.and_eq_true, List.all_eq_true] at hT
  have := hT.1.1.1.2 B hB s hs
  rw [← hsi] at this
  simpa [he] using this

/-- **`CtxT` of a `functionETCF` function's context** (`CtxInvT` and `InstScopeTF` from the
shape). -/
theorem ctxT_of_functionETCF {f : Clif.Function} (hT : Compile.functionETCF f = true)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hb : buildCtx f = .ok (ctx, ranges, st0)) (hinv : CtxInvT f ctx) (hsc : InstScopeTF ctx) :
    CtxT f ctx :=
  ⟨hinv, hsc, callsE_of_functionETCF hT hb⟩

/-- The integer-position operands of a `functionETCF` function's terminators other than the
direct `try_call`s. -/
theorem termIntPos_of_functionETCF {f : Clif.Function} (hT : Compile.functionETCF f = true)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hb : buildCtx f = .ok (ctx, ranges, st0)) {B : Clif.Block} (hB : B ∈ f.blocks)
    (hnt : ∀ fn args et, B.term ≠ .tryCall fn args et) : TermIntPos ctx B.term := by
  intro x hx t ht
  refine (ctxSpec_of hb).eCTys_of_not_floatDef ht fun hfd => ?_
  simp only [Compile.functionETCF, Compile.opsTypedTCF, Bool.and_eq_true, List.all_eq_true] at hT
  have hx' : x ∈ Compile.termIntOperandsC B.term := by
    cases h : B.term <;> rw [h] at hx <;> first | exact absurd h (hnt _ _ _) | exact hx
  have := (hT.1.2 B hB).2 x hx'
  simp [hfd] at this

end Backend.Proof.Driver
