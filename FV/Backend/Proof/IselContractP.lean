import FV.Backend.Proof.IselContract

/-!
# The call contracts with pinned calls (agent/link-widen, stage 2)

Non-interference of a compiled function (two VCode runs from worlds that differ only on bytes
CLIF never initialised give one outcome, `docs/contracts/e2e.md` "Widening" item 2) runs the
rule contracts on each of the two worlds and pairs the runs instruction by instruction. At a
call the two runs must pass the callee the same stack-passed arguments; the bytes are the
arguments' because each run's call is the one of the **same CLIF call** (its values and memory).
The variants here let the semantics see that: the callee contracts take an extra premise
`Pc name sig vals cm` (the call's extern, signature, argument values and CLIF memory), which
the rule obligations' runs discharge from `CallPin Pc` (the CLIF call of the instruction at the
run's frame and memory), and the obligations also assume `InitIn Rd cm` (the memory rules' read
footprint, `MemRulesCorrectR`):

* `LowerInstOkP Rd Pc`, `LowerTryOkP Rd Pc`: `LowerInstOk`/`LowerTryOk` whose runs assume
  `InitIn Rd cm` and `CallPin Pc inst fr cm`;
* `CallsRefineP Pc`, `IndCallsRefineP Pc`: `CallsRefine`/`IndCallsRefine` with the premise
  `Pc name sig vals cm` at the calls;
* `CallRulesCorrectP`, `IndRulesCorrectP`, `TryRulesCorrectP`, `TryIndRulesCorrectP`: the rule
  statements under `MemRefinesR Rd` (they use only its store clause) and the pinned contracts;
  the former statements follow (`callRulesCorrect_of_P`, …: `Pc`, `Rd` true);
* `lowerInstOkP_runTerm`, `tryOkP_runTerm`, `tryIndOkP_runTerm`: every `lower`/`lower_branch`
  call of the backend satisfies the pinned obligation.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- **The CLIF call of an instruction**, pinned: a returning `call` of the extern `e` on the
values `vals` of the frame `fr` and a returning `call_indirect` (declared signature `s`) of the
extern `n` at the callee address, from memory `cm` (the extern's semantics in `env` returns),
satisfy `Pc`. -/
def CallPin (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (env : Clif.Env)
    (inst : Clif.Inst) (fr : Clif.Frame) (cm : Clif.Mem) : Prop :=
  (∀ fn args e vals g rvals cm', inst = .call fn args → fr.func.extern? fn = some e →
    fr.getMany args = .ok vals → env.extern e.name = some g → g vals cm = .returned rvals cm' →
    Pc e.name e.sig vals cm) ∧
  (∀ sig callee args s x vals n g rvals cm', inst = .callIndirect sig callee args →
    fr.func.sigDecls.lookup sig = some s → fr.get callee = .ok ⟨.i64, x⟩ →
    fr.getMany args = .ok vals → cm.symbols n = some x.toNat → env.extern n = some g →
    g vals cm = .returned rvals cm' → vals.map (·.ty) = Clif.AbiParam.tys s.params →
    Pc n s vals cm)

/-- **`lower` on a non-terminator, pinned** (`LowerInstOkR` whose run also assumes the pinned
CLIF call `CallPin Pc`). -/
structure LowerInstOkP (Rd : BitVec 64 → Prop)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (isem : Sem) (MR : MemRelT)
    (env : Clif.Env) (p : Clif.Program) (ctx : Ctx) (inst : Clif.Inst) (results : List Nat)
    (st : LState) (rss : List (List Reg)) (st' : LState) (ms : List MInst) : Prop where
  mono : st.nextVreg ≤ st'.nextVreg
  defs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg
  run : ∀ (fr : Clif.Frame) (cm : Clif.Mem) (ρ : Nat → CV) (w : Arm.ArmState),
    fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → MR fr.slots cm w → InitIn Rd cm →
    CallPin Pc env inst fr cm →
    match instOutcome env p fr cm inst with
    | .ok (vals, cm') => UsesOk st fr ms ∧ ∃ ρ' w', seqRun isem ms ρ w = some (.fall ρ' w') ∧
        (results = [] ∨ ResultsHeld st.nextVreg fr rss vals ρ') ∧ MR fr.slots cm' w'
    | .trap c => explicitTrapInst inst = true → UsesOk st fr ms ∧
        ∃ k i ops ρ₁ w₁ outs w₂, seqRun isem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ .halt) ∧
          trapCode? i = some c
    | .stuck _ => True

section
variable {Rd : BitVec 64 → Prop} {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
  {isem : Sem} {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {ctx : Ctx} {inst : Clif.Inst}
  {results : List Nat} {st : LState} {rss : List (List Reg)} {st' : LState} {ms : List MInst}

theorem LowerInstOk.toP (h : LowerInstOk isem MR env p ctx inst results st rss st' ms) :
    LowerInstOkP Rd Pc isem MR env p ctx inst results st rss st' ms :=
  ⟨h.mono, h.defs, fun fr cm ρ w hf hv hd hmr _ _ => h.run fr cm ρ w hf hv hd hmr⟩

theorem LowerInstOkR.toP (h : LowerInstOkR Rd isem MR env p ctx inst results st rss st' ms) :
    LowerInstOkP Rd Pc isem MR env p ctx inst results st rss st' ms :=
  ⟨h.mono, h.defs, fun fr cm ρ w hf hv hd hmr hi _ => h.run fr cm ρ w hf hv hd hmr hi⟩

theorem LowerInstOkP.toOk
    (h : LowerInstOkP (fun _ => True) (fun _ _ _ _ => True) isem MR env p ctx inst results st rss
      st' ms) :
    LowerInstOk isem MR env p ctx inst results st rss st' ms :=
  ⟨h.mono, h.defs, fun fr cm ρ w hf hv hd hmr =>
    h.run fr cm ρ w hf hv hd hmr (fun _ _ _ => trivial) ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial⟩⟩

end

/-- **`CallsRefine` with pinned calls**: the call clauses are required only for the calls
`Pc` admits (the extern's name and signature, the argument values, the CLIF memory). -/
def CallsRefineP (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (env : Clif.Env) (exts : List Clif.ExtFunc) (MR : MemRelT)
    (isem : Sem) : Prop :=
  ∃ sym : String → BitVec 64,
    (∀ (rd : Reg) (n : String) (w : Arm.ArmState), ∃ w',
      isem (.loadExtNameGot rd n) [] w = some ([ofX (sym n)], w', .next) ∧ SameWorldNF F w' w) ∧
    (∀ ext ∈ exts, ∀ g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (w : Arm.ArmState)
      (dest : CallDest) (us ds : List (Reg × Reg)) (uses args : List CV)
      (vals rvals : List Clif.Val) (cm' : Clif.Mem),
      env.extern ext.name = some g →
      (dest = .sym ext.name ∧ uses = args ∨ ∃ r, dest = .reg r ∧ uses = ofX (sym ext.name) :: args) →
      ds.length = (sigRets ext.sig).length →
      ArgsAt ext.sig vals args w → MR sl cm w → Pc ext.name ext.sig vals cm →
      g vals cm = .returned rvals cm' → rvals.length = ext.sig.returns.length →
      ∃ outs w', isem (.call ⟨dest, us, ds⟩) uses w = some (outs, w', .next) ∧
        outs.length = ds.length ∧ PrefixHold rvals outs ∧ MR sl cm' w') ∧
    ∀ ext ∈ exts, ∀ g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (w : Arm.ArmState)
      (dest : CallDest) (us ds : List (Reg × Reg)) (ti : TryInfo) (uses args : List CV)
      (vals rvals : List Clif.Val) (cm' : Clif.Mem),
      env.extern ext.name = some g →
      (dest = .sym ext.name ∧ uses = args ∨ ∃ r, dest = .reg r ∧ uses = ofX (sym ext.name) :: args) →
      (sigRets ext.sig).length ≤ ds.length →
      ArgsAt ext.sig vals args w → MR sl cm w → Pc ext.name ext.sig vals cm →
      g vals cm = .returned rvals cm' → rvals.length = ext.sig.returns.length →
      ∃ outs w', isem (.tryCall ⟨dest, us, ds⟩ ti) uses w = some (outs, w', .goto ti.handlers.length) ∧
        outs.length = ds.length ∧ PrefixHold rvals outs ∧ MR sl cm' w'

theorem CallsRefine.toP {F : BitVec 64 → Prop} {env : Clif.Env} {exts : List Clif.ExtFunc}
    {MR : MemRelT} {isem : Sem} (h : CallsRefine F env exts MR isem)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) :
    CallsRefineP Pc F env exts MR isem := by
  obtain ⟨sym, h1, h2, h3⟩ := h
  exact ⟨sym, h1, fun ext hin g sl cm w dest us ds uses args vals rvals cm' a1 a2 a3 a4 a5 _ a7 a8 =>
    h2 ext hin g sl cm w dest us ds uses args vals rvals cm' a1 a2 a3 a4 a5 a7 a8,
    fun ext hin g sl cm w dest us ds ti uses args vals rvals cm' a1 a2 a3 a4 a5 _ a7 a8 =>
    h3 ext hin g sl cm w dest us ds ti uses args vals rvals cm' a1 a2 a3 a4 a5 a7 a8⟩

/-- **`IndCallsRefine` with pinned calls** (premise `Pc n sig vals cm`). -/
def IndCallsRefineP (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (env : Clif.Env) (sigs : List Clif.Signature) (MR : MemRelT) (isem : Sem) : Prop :=
  (∀ sig ∈ sigs, ∀ (n : String) g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem)
      (w : Arm.ArmState) (a : Nat) (r : Reg) (us ds : List (Reg × Reg)) (u : CV) (args : List CV)
      (vals rvals : List Clif.Val) (cm' : Clif.Mem),
    env.extern n = some g → cm.symbols n = some a → lo64 u = BitVec.ofNat 64 a →
    ds.length = (sigRets sig).length → vals.length ≤ 8 → AllHold vals args → MR sl cm w →
    Pc n sig vals cm →
    g vals cm = .returned rvals cm' → rvals.length = sig.returns.length →
    vals.map (·.ty) = Clif.AbiParam.tys sig.params →
    ∃ outs w', isem (.call ⟨.reg r, us, ds⟩) (u :: args) w = some (outs, w', .next) ∧
      outs.length = ds.length ∧ PrefixHold rvals outs ∧ MR sl cm' w') ∧
  (∀ sig ∈ sigs, ∀ (n : String) g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem)
      (w : Arm.ArmState) (a : Nat) (r : Reg) (us ds : List (Reg × Reg)) (ti : TryInfo) (u : CV)
      (args : List CV) (vals rvals : List Clif.Val) (cm' : Clif.Mem),
    env.extern n = some g → cm.symbols n = some a → lo64 u = BitVec.ofNat 64 a →
    (sigRets sig).length ≤ ds.length → vals.length ≤ 8 → AllHold vals args → MR sl cm w →
    Pc n sig vals cm →
    g vals cm = .returned rvals cm' → rvals.length = sig.returns.length →
    vals.map (·.ty) = Clif.AbiParam.tys sig.params →
    ∃ outs w', isem (.tryCall ⟨.reg r, us, ds⟩ ti) (u :: args) w =
        some (outs, w', .goto ti.handlers.length) ∧
      outs.length = ds.length ∧ PrefixHold rvals outs ∧ MR sl cm' w')

theorem IndCallsRefine.toP {env : Clif.Env} {sigs : List Clif.Signature} {MR : MemRelT}
    {isem : Sem} (h : IndCallsRefine env sigs MR isem)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) :
    IndCallsRefineP Pc env sigs MR isem :=
  ⟨fun sig hin n g sl cm w a r us ds u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 _ a9 a10 a11 =>
    h.1 sig hin n g sl cm w a r us ds u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 a9 a10 a11,
   fun sig hin n g sl cm w a r us ds ti u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 _ a9 a10 a11 =>
    h.2 sig hin n g sl cm w a r us ds ti u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 a9 a10 a11⟩

/-- `CallRuleOk` with the pinned obligation. -/
def CallRuleOkP (Rd : BitVec 64 → Prop)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (isem : Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (exts : List Clif.ExtFunc) (outB : Nat) (p : Program)
    (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx → ExternsIn f exts →
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

/-- **The call rules with pinned calls**: under guarded memory forms (`MemRefinesR`: the call
rules use only the stores) and the pinned callee contract. -/
def CallRulesCorrectP (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → OutArgsOk F outB MR →
    CallsRefineP Pc F env exts MR isem →
    ∀ r ∈ p.rulesOf TId.lower, callRootRule r = true → CallRuleOkP Rd Pc isem MR env cp exts outB p r

theorem callRulesCorrect_of_P {p : Program} (h : CallRulesCorrectP p) : CallRulesCorrect p := by
  intro F isem MR env cp exts sb syms outB hR hMR hMem hout hCR r hr hroot f ctx hctx hexts ii info
    inst hi hc hstk cfg hco m n st tr env' s1 out st' tr' hm hn hvb hpre hmatch heval
  obtain ⟨ms, rss, h1, h2, h3⟩ := h (fun _ => True) (fun _ _ _ _ => True) F isem MR env cp exts sb
    syms outB hR hMR (memRefinesR_of hMem) hout (hCR.toP _) r hr hroot f ctx hctx hexts ii info
    inst hi hc hstk cfg hco m n st tr env' s1 out st' tr' hm hn hvb hpre hmatch heval
  exact ⟨ms, rss, h1, h2, h3.toOk⟩

/-- `IndRuleOk` with the pinned obligation. -/
def IndRuleOkP (Rd : BitVec 64 → Prop)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (isem : Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (sigs : List Clif.Signature) (p : Program) (r : Rule) :
    Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
  IndSigOk f sigs inst →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOkP Rd Pc isem MR env cp ctx inst info.results st rss st' ms

/-- **The `call_indirect` rule with pinned calls.** -/
def IndRulesCorrectP (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (sigs : List Clif.Signature),
    Refines F isem → MRStable F MR → IndCallsRefineP Pc env sigs MR isem →
    ∀ r ∈ p.rulesOf TId.lower, indRootRule r = true → IndRuleOkP Rd Pc isem MR env cp sigs p r

theorem indRulesCorrect_of_P {p : Program} (h : IndRulesCorrectP p) : IndRulesCorrect p := by
  intro F isem MR env cp sigs hR hMR hCR r hr hroot f ctx hctx ii info inst hi hc hsig cfg hco m n
    st tr env' s1 out st' tr' hm hn hvb hpre hmatch heval
  obtain ⟨ms, rss, h1, h2, h3⟩ := h (fun _ => True) (fun _ _ _ _ => True) F isem MR env cp sigs hR
    hMR (hCR.toP _) r hr hroot f ctx hctx ii info inst hi hc hsig cfg hco m n st tr env' s1 out st'
    tr' hm hn hvb hpre hmatch heval
  exact ⟨ms, rss, h1, h2, h3.toOk⟩

/-- **`lower` with pinned obligations**: every rule family under its contract (`LowerRulesCorrect`,
`MemRulesCorrectR` under `MemRefinesR Rd`, the call rules under the pinned contracts). -/
theorem lowerInstOkP_of_rules {p : Program} (hp : Data p) (hrules : LowerRulesCorrect p)
    (hex : ExcludedUnmatchable p) (hcalls : CallRulesCorrectP p) (hind : IndRulesCorrectP p)
    (hmem : MemRulesCorrectR p) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {exts : List Clif.ExtFunc} (hcr : CallsRefineP Pc F env exts MR isem)
    {sigs : List Clif.Signature} (hicr : IndCallsRefineP Pc env sigs MR isem)
    (hMem : MemRefinesR Rd F sb syms isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hnorm : ExternsIn f exts) (hE : Compile.functionE f = true)
    (hMRo : MemRelOk F sb syms f MR) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hsig : IndSigOk f sigs inst)
    (hstk : ∀ fn args e, inst = .call fn args → f.extern? fn = some e → SigStackOk e.sig outB)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId} (hvb : ValsBelow ctx st)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower [.inst ii]).run (st, tr) =
      .ok (some out, (st', tr'))) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOkP Rd Pc isem MR env cp ctx inst info.results st rss st' ms := by
  change 1002 + (p.rulesOf 686).length ≤ n at hn
  obtain ⟨r, pre0, post0, hsplit, hpre0, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some_first hco hp.t686 term_686_kind rfl h
  have hr : r ∈ p.rulesOf TId.lower := by
    change r ∈ p.rulesOf 686; rw [hsplit]; simp
  have hfirst : ∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s') := by
    intro pre post hsp r' hr'
    have hnd : (pre0 ++ r :: post0).Nodup := hsplit ▸ lower_rules_nodup hp
    have hpre := prefix_unique_of_nodup hnd (hsplit.symm.trans hsp)
    subst hpre
    obtain ⟨m', hm', s', h'⟩ := hpre0 r' hr'
    exact ⟨m', by omega, s', h'⟩
  simp only [Prod.mk.injEq] at hs
  rw [← hs.1] at heval
  cases hroot : closureRoot r
  · exact absurd hmatch (hex r hr hroot f ctx hctx hE ii info inst hi hc cfg m (st, tr) env' s1)
  · cases hcall : callRootRule r
    · cases hind' : indRootRule r
      · cases hm : memRootRule r
        · obtain ⟨ms, rss, h1, h2, h3⟩ := hrules F isem MR env cp hR hMR r hr hroot hcall hind' hm f
            ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr2 (by omega) (by omega)
            hvb hfirst hmatch heval
          exact ⟨ms, rss, h1, h2, h3.toP⟩
        · obtain ⟨ms, rss, h1, h2, h3⟩ := hmem Rd F sb syms isem MR env cp hR hMR hMem r hr hm f ctx
            hctx hMRo ii info inst hi hc cfg hco m n st tr env' s1 out st' tr2 (by omega) (by omega)
            hvb hfirst hmatch heval
          exact ⟨ms, rss, h1, h2, h3.toP⟩
      · exact hind Rd Pc F isem MR env cp sigs hR hMR hicr r hr hind' f ctx hctx ii info inst hi hc
          hsig cfg hco m n st tr env' s1 out st' tr2 (by omega) (by omega) hvb hfirst hmatch heval
    · exact hcalls Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hcr r hr hcall f ctx
        hctx hnorm ii info inst hi hc hstk
        cfg hco m n st tr env' s1 out st' tr2 (by omega) (by omega) hvb hfirst hmatch heval

set_option maxRecDepth 20000 in
/-- `lowerInstOkP_of_rules` for the exported program and the backend's own call
(`runTerm ctx "lower" [.inst ii]`). -/
theorem lowerInstOkP_runTerm (hrules : LowerRulesCorrect program)
    (hex : ExcludedUnmatchable program) (hcalls : CallRulesCorrectP program)
    (hind : IndRulesCorrectP program) (hmem : MemRulesCorrectR program) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    {exts : List Clif.ExtFunc} (hcr : CallsRefineP Pc F env exts MR isem)
    {sigs : List Clif.Signature} (hicr : IndCallsRefineP Pc env sigs MR isem)
    (hMem : MemRefinesR Rd F sb syms isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hnorm : ExternsIn f exts) (hE : Compile.functionE f = true)
    (hMRo : MemRelOk F sb syms f MR) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hsig : IndSigOk f sigs inst)
    (hstk : ∀ fn args e, inst = .call fn args → f.extern? fn = some e → SigStackOk e.sig outB)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower" [.inst ii] st = .ok (some out, st', tr)) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOkP Rd Pc isem MR env cp ctx inst info.results st rss st' ms := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower.ret T.lower.id [.inst ii]).run
      (st, #[]) with
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
    have hlen : (program.rulesOf TId.lower).length ≤ 1000 := by
      rw [show TId.lower = 686 from rfl, data_program.r686]; decide
    obtain ⟨ms, rss, h1, h2, h3⟩ := lowerInstOkP_of_rules data_program hrules hex hcalls hind hmem
      hR hMR hcr hicr hMem hctx hout hnorm hE hMRo hi hc hsig hstk rfl (by omega) hvb ha
    exact ⟨ms, rss, by simpa using h1, h2, h3⟩

/-! ## `try_call` -/

/-- **`lower_branch` on a `try_call`/`try_call_indirect`, pinned** (`LowerTryOk` whose run
assumes `InitIn Rd cm` and the pinned CLIF call `CallPin Pc ci`). -/
structure LowerTryOkP (Rd : BitVec 64 → Prop)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (isem : Sem) (MR : MemRelT)
    (env : Clif.Env) (p : Clif.Program) (ctx : Ctx) (ci : Clif.Inst) (info : TryInfo)
    (st st' : LState) (ms : List MInst) : Prop where
  mono : st.nextVreg ≤ st'.nextVreg
  shape : ∃ pre ci, ms = pre ++ [.call ci] ∧
    (∀ m ∈ pre, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg) ∧
    ∀ d ∈ vdefs (.call ci), Reg.vreg d .int ∈ tryDefRegs ctx
  run : ∀ (fr : Clif.Frame) (cm : Clif.Mem) (ρ : Nat → CV) (w : Arm.ArmState),
    fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → MR fr.slots cm w → InitIn Rd cm →
    CallPin Pc env ci fr cm →
    match instOutcome env p fr cm ci with
    | .ok (rvals, cm') => UsesOk st fr ms ∧ ∃ k i ops ρ₁ w₁ outs w₂,
        seqRun isem (tryFix info ms) ρ w =
          some (.stop k i ops ρ₁ w₁ outs w₂ (.goto info.handlers.length)) ∧
        k + 1 = ms.length ∧
        (∀ (j : Nat) r v, ctx.tryRegs.1[j]? = some r → rvals[j]? = some v →
          ∃ n, r = .vreg n .int ∧ VHolds v (vdefUpd ops outs ρ₁ n)) ∧
        MR fr.slots cm' w₂
    | _ => True

theorem LowerTryOkP.toOk {isem : Sem} {MR : MemRelT} {env : Clif.Env} {p : Clif.Program}
    {ctx : Ctx} {ci : Clif.Inst} {info : TryInfo} {st st' : LState} {ms : List MInst}
    (h : LowerTryOkP (fun _ => True) (fun _ _ _ _ => True) isem MR env p ctx ci info st st' ms) :
    LowerTryOk isem MR env p ctx ci info st st' ms :=
  ⟨h.mono, h.shape, fun fr cm ρ w hf hv hd hmr =>
    h.run fr cm ρ w hf hv hd hmr (fun _ _ _ => trivial) ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial⟩⟩

/-- `TryRuleOk` with the pinned obligation. -/
def TryRuleOkP (Rd : BitVec 64 → Prop)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (isem : Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (exts : List Clif.ExtFunc) (outB : Nat) (p : Program)
    (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx → ExternsIn f exts →
  ∀ (ti : Nat) (fn : Clif.FnRef) (args : List Nat) (et : Clif.ExnTable) (data : V)
    (sig : Clif.Signature) (items : List (Option Nat)) (targets : List Label) (info : TryInfo)
    (lo st1 : LState),
  (∀ e, f.extern? fn = some e → SigStackOk e.sig outB) →
  tryCallData f (.tryCall fn args et) = .ok data → exnTableOpnd f et = .ok (sig, items) →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ → tryInfoOf sig items targets = some info →
  tryRegsOf sig lo = some (ctx.tryRegs, st1) → ValsBelow ctx lo →
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
      LowerTryOkP Rd Pc isem MR env cp ctx (.call fn args) info st st' ms

/-- **The `try_call` rules with pinned calls.** -/
def TryRulesCorrectP (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → OutArgsOk F outB MR →
    CallsRefineP Pc F env exts MR isem →
    ∀ r ∈ p.rulesOf TId.lower_branch, tryRootRule r = true →
      TryRuleOkP Rd Pc isem MR env cp exts outB p r

theorem tryRulesCorrect_of_P {p : Program} (h : TryRulesCorrectP p) : TryRulesCorrect p := by
  intro F isem MR env cp exts sb syms outB hR hMR hMem hout hCR r hr hroot f ctx hctx hext ti fn
    args et data sig items targets info lo st1 hra hd he hi hinfo htr hvb cfg hco m n st tr env' s1
    out st' tr' hm hn hst hfirst hmatch heval
  obtain ⟨ms, h1, h2⟩ := h (fun _ => True) (fun _ _ _ _ => True) F isem MR env cp exts sb syms outB
    hR hMR (memRefinesR_of hMem) hout (hCR.toP _) r hr hroot f ctx hctx hext ti fn args et data sig
    items targets info lo st1 hra hd he hi hinfo htr hvb cfg hco m n st tr env' s1 out st' tr' hm hn
    hst hfirst hmatch heval
  exact ⟨ms, h1, h2.toOk⟩

/-- `TryIndRuleOk` with the pinned obligation. -/
def TryIndRuleOkP (Rd : BitVec 64 → Prop)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (isem : Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (sigs : List Clif.Signature) (p : Program) (r : Rule) :
    Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx →
  ∀ (ti : Nat) (callee : Nat) (args : List Nat) (et : Clif.ExnTable) (data : V)
    (sig : Clif.Signature) (items : List (Option Nat)) (targets : List Label) (info : TryInfo)
    (lo st1 : LState),
  tryCallData f (.tryCallIndirect callee args et) = .ok data →
  exnTableOpnd f et = .ok (sig, items) → sig ∈ sigs → sig.params.length ≤ 8 →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ → tryInfoOf sig items targets = some info →
  tryRegsOf sig lo = some (ctx.tryRegs, st1) → ValsBelow ctx lo →
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
      LowerTryOkP Rd Pc isem MR env cp ctx (.callIndirect et.sig callee args) info st st' ms

/-- **The `try_call_indirect` rule with pinned calls.** -/
def TryIndRulesCorrectP (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (sigs : List Clif.Signature),
    Refines F isem → MRStable F MR → IndCallsRefineP Pc env sigs MR isem →
    ∀ r ∈ p.rulesOf TId.lower_branch, tryIndRootRule r = true →
      TryIndRuleOkP Rd Pc isem MR env cp sigs p r

theorem tryIndRulesCorrect_of_P {p : Program} (h : TryIndRulesCorrectP p) :
    TryIndRulesCorrect p := by
  intro F isem MR env cp sigs hR hMR hCR r hr hroot f ctx hctx ti callee args et data sig items
    targets info lo st1 hd he hsig h8 hi hinfo htr hvb cfg hco m n st tr env' s1 out st' tr' hm hn
    hst hfirst hmatch heval
  obtain ⟨ms, h1, h2⟩ := h (fun _ => True) (fun _ _ _ _ => True) F isem MR env cp sigs hR hMR
    (hCR.toP _) r hr hroot f ctx hctx ti callee args et data sig items targets info lo st1 hd he
    hsig h8 hi hinfo htr hvb cfg hco m n st tr env' s1 out st' tr' hm hn hst hfirst hmatch heval
  exact ⟨ms, h1, h2.toOk⟩

theorem tryOkP_of_rules {p : Program} (hp : Data p) (hrules : TryRulesCorrectP p)
    (hun : TryUnmatchable p) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {F : BitVec 64 → Prop}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {exts : List Clif.ExtFunc}
    (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hcr : CallsRefineP Pc F env exts MR isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (hext : ExternsIn f exts) {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable}
    {data : V} {sig : Clif.Signature} {items : List (Option Nat)} {targets : List Label}
    {info : TryInfo} {lo st1 : LState} (hra : ∀ e, f.extern? fn = some e → SigStackOk e.sig outB)
    (hd : tryCallData f (.tryCall fn args et) = .ok data) (he : exnTableOpnd f et = .ok (sig, items))
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOf sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower_branch).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId}
    (hst : st1.nextVreg ≤ st.nextVreg)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower_branch [.inst ti, .labels targets]).run
      (st, tr) = .ok (some out, (st', tr'))) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkP Rd Pc isem MR env cp ctx (.call fn args) info st st' ms := by
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
  · exact absurd hmatch (hun r hr hroot f ctx hctx ti fn args et data targets hd hi cfg m (st, tr) env' s1)
  · exact hrules Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hcr r hr hroot f ctx hctx
      hext ti fn args et data sig items targets info lo st1 hra hd he hi hinfo htr hvb cfg hco m n st
      tr env' s1 out st' tr2 (by omega) (by omega) hst hfirst hmatch heval

set_option maxRecDepth 20000 in
theorem tryOkP_runTerm (hrules : TryRulesCorrectP program) (hun : TryUnmatchable program)
    {Rd : BitVec 64 → Prop} {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {exts : List Clif.ExtFunc} (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat}
    {syms : String → Option Nat} (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR)
    (hcr : CallsRefineP Pc F env exts MR isem) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (hext : ExternsIn f exts) {ti : Nat} {fn : Clif.FnRef}
    {args : List Nat} {et : Clif.ExnTable} {data : V} {sig : Clif.Signature}
    {items : List (Option Nat)} {targets : List Label} {info : TryInfo} {lo st1 : LState}
    (hra : ∀ e, f.extern? fn = some e → SigStackOk e.sig outB)
    (hd : tryCallData f (.tryCall fn args et) = .ok data) (he : exnTableOpnd f et = .ok (sig, items))
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOf sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hst : st1.nextVreg ≤ st.nextVreg)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkP Rd Pc isem MR env cp ctx (.call fn args) info st st' ms := by
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
    obtain ⟨ms, h1, h2⟩ := tryOkP_of_rules data_program hrules hun hR hMR hMem hout hcr hctx hext
      hra hd he hi hinfo htr hvb rfl (by omega) hst ha
    exact ⟨ms, by simpa using h1, h2⟩

theorem tryIndOkP_of_rules {p : Program} (hp : Data p) (hrules : TryIndRulesCorrectP p)
    (hun : TryIndUnmatchable p) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {F : BitVec 64 → Prop}
    {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sigs : List Clif.Signature}
    (hR : Refines F isem) (hMR : MRStable F MR) (hcr : IndCallsRefineP Pc env sigs MR isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti callee : Nat} {args : List Nat}
    {et : Clif.ExnTable} {data : V} {sig : Clif.Signature} {items : List (Option Nat)}
    {targets : List Label} {info : TryInfo} {lo st1 : LState}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
    (he : exnTableOpnd f et = .ok (sig, items)) (hsig : sig ∈ sigs) (h8 : sig.params.length ≤ 8)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOf sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower_branch).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId}
    (hst : st1.nextVreg ≤ st.nextVreg)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower_branch [.inst ti, .labels targets]).run
      (st, tr) = .ok (some out, (st', tr'))) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkP Rd Pc isem MR env cp ctx (.callIndirect et.sig callee args) info st st' ms := by
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
  cases hroot : tryIndRootRule r
  · exact absurd hmatch
      (hun r hr hroot f ctx hctx ti callee args et data targets hd hi cfg m (st, tr) env' s1)
  · exact hrules Rd Pc F isem MR env cp sigs hR hMR hcr r hr hroot f ctx hctx ti callee args et data
      sig items targets info lo st1 hd he hsig h8 hi hinfo htr hvb cfg hco m n st tr env' s1 out st'
      tr2 (by omega) (by omega) hst hfirst hmatch heval

set_option maxRecDepth 20000 in
theorem tryIndOkP_runTerm (hrules : TryIndRulesCorrectP program) (hun : TryIndUnmatchable program)
    {Rd : BitVec 64 → Prop} {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {sigs : List Clif.Signature} (hR : Refines F isem) (hMR : MRStable F MR)
    (hcr : IndCallsRefineP Pc env sigs MR isem) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    {ti callee : Nat} {args : List Nat} {et : Clif.ExnTable} {data : V} {sig : Clif.Signature}
    {items : List (Option Nat)} {targets : List Label} {info : TryInfo} {lo st1 : LState}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
    (he : exnTableOpnd f et = .ok (sig, items)) (hsig : sig ∈ sigs) (h8 : sig.params.length ≤ 8)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOf sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hst : st1.nextVreg ≤ st.nextVreg)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkP Rd Pc isem MR env cp ctx (.callIndirect et.sig callee args) info st st' ms := by
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
    obtain ⟨ms, h1, h2⟩ := tryIndOkP_of_rules data_program hrules hun hR hMR hcr hctx hd he hsig h8
      hi hinfo htr hvb rfl (by omega) hst ha
    exact ⟨ms, by simpa using h1, h2⟩

end Backend.Proof
