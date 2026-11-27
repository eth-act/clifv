import FV.E2E.LinkSiteTC
import FV.Backend.Proof.IselCtlTryF

/-!
# The call contracts with the call site's registers (#753, stage R1)

At a `blr` through a vreg that is no GOT load (a vtable slot), the typed link's model of a call
(`E2E.LinkSys.XT`) may enter any function `h` the caller declares through the GOT, whatever the
site's registers: `LinkSys.OkT.blrRegs` asks the site's registers to be `regLocs h.sig` for every
such `h`, which fails where the site's signature passes an `sret` pointer in x8 and `h`'s does not,
or the reverse (#753). The plan (#753 issuecomment-6956067039) carries the site's registers
through the call contracts instead; this module is its first stage:

* `SiteRegsR s us ds`: a call site passes its register arguments in the parameter registers of
  `s` (`E2E.regLocs s`) and defines the declared returns of `s` from their ABI return registers by
  class (`retRegsT` of the returns' `retClass`: `gen_call_rets`);
* `CallsRefinePR`, `IndCallsRefinePR`: `CallsRefineP`/`IndCallsRefineP` whose GOT clauses (`call`,
  `try_call` through the GOT) and indirect clauses (`call_indirect`, `try_call_indirect`) are
  required only at call sites with `SiteRegsR` of the callee's signature (GOT) or of the site's
  signature (indirect); the contracts without registers give them (`CallsRefineP.toPR`,
  `IndCallsRefineP.toPR`);
* the rule families over them: `CallRulesCorrectPR`, `IndRulesCorrectPR`, `TryRulesCorrectPR`,
  `TryIndRulesCorrectPR` (`CtxInv` contexts), `…TPR` (`CtxT`), `CallRulesCorrectTFPR`,
  `TryRulesCorrectTFPR` (`CallCtxT`); each gives its family without registers
  (`callRulesCorrectP_of_PR`, …);
* `siteRegsR_int`, `siteRegsR_callC`, `siteRegsR_tryC`: the call sites the lowering emits have
  `SiteRegsR` (used by the rule theorems of `IselCtlCallPR`, `IselCtlCallTPR`, `IselCtlCallTFPR`);
* `regLocs_of_abiMatch`: signatures `Clif.Signature.abiMatch` relates (the CLIF semantics'
  condition for an indirect call to enter a function) have the same parameter registers;
  `siteRegsR_of_abiMatch` moves `SiteRegsR` from a site's signature to the entered function's.

Nothing uses these yet (stage R1 of 4); the generated code is unchanged.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option autoImplicit false

/-! ## The registers of a call site -/

/-- **A call site's registers for the signature `s`**: its uses pass the register arguments in
the parameter registers of `s` (`E2E.regLocs`: x0..x7 and v0..v7 by class, an `sret` pointer in
x8), and its first defs take the declared returns of `s` from their ABI return registers by
class (`retRegsT` of the returns' `retClass`, as `gen_call_rets` defines them; the defs past them
are a `try_call`'s exception payload registers). -/
def SiteRegsR (s : Clif.Signature) (us ds : List (Reg × Reg)) : Prop :=
  us.map (·.2) = E2E.regLocs s ∧
    (ds.map (·.1)).take s.returns.length = retRegsT (s.returns.map retClass) 0 0

theorem args_length_of {vals : List Clif.Val} {args : List Nat} {s : Clif.Signature}
    (hlen : vals.length = args.length) (hty : vals.map (·.ty) = Clif.AbiParam.tys s.params) :
    args.length = s.params.length := by
  have := congrArg List.length hty
  simp only [List.length_map, Clif.AbiParam.tys] at this
  omega

theorem regPairsOf_snd {g : ArgLoc → Option Reg} (hg1 : ∀ r, g (.reg r) = some r)
    (hg2 : ∀ o, g (.stack o) = none) :
    ∀ (locs : List ArgLoc) (args bytes : List Nat), locs.length ≤ args.length →
      locs.length ≤ bytes.length →
      (regPairsOf ((locs.zip args).zip bytes)).map (·.2) = locs.filterMap g
  | [], _, _, _, _ => by simp [regPairsOf]
  | _ :: _, [], _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, h => by simp at h
  | l :: ls, a :: as, b :: bs, h1, h2 => by
    have ih := regPairsOf_snd hg1 hg2 ls as bs (by simp at h1; omega) (by simp at h2; omega)
    simp only [regPairsOf] at ih ⊢
    cases l with
    | reg r => simp [List.filterMap_cons, hg1, ih]
    | stack o => simp [List.filterMap_cons, hg2, ih]

/-- The registers of the register-passed arguments of a call of `s` are the parameter registers
of `s`. -/
theorem regPairsOf_regLocs {s : Clif.Signature} {locs : List ArgLoc} {S : Nat}
    {bytes args : List Nat} (hl : sigArgLocs s = .ok (locs, S)) (hb : sigParamBytes s = .ok bytes)
    (ha : args.length = s.params.length) :
    (regPairsOf ((locs.zip args).zip bytes)).map (·.2) = E2E.regLocs s := by
  have hlocs : locsOf s = locs := by simp [locsOf, hl]
  have hll := (sigArgLocs_shape hl).1
  have hbl := sigParamBytes_length hb
  unfold E2E.regLocs
  rw [hlocs]
  exact regPairsOf_snd (fun _ => rfl) (fun _ => rfl) locs args bytes (by omega) (by omega)

theorem retRegsT_replicate_int (n : Nat) :
    retRegsT (List.replicate n .int) 0 0 = (List.range n).map Reg.x := by
  rw [retRegsT_int, List.range_eq_range']

/-- Integer ABI returns (`sigRets`) are integer declared returns. -/
theorem returns_retClass_of_sigRets {s : Clif.Signature}
    (h : (sigRets s).map retClass = List.replicate (sigRets s).length .int) :
    s.returns.map retClass = List.replicate s.returns.length .int := by
  cases hr : s.returns with
  | nil => rfl
  | cons p ps =>
    have hs : sigRets s = s.returns := by
      unfold sigRets
      split
      · simp [hr]
      · rfl
    rw [hs, hr] at h
    exact h

theorem returns_retClass_of_sigIntB {s : Clif.Signature} (h : sigIntB s = true) :
    s.returns.map retClass = List.replicate s.returns.length .int := by
  refine List.eq_replicate_iff.mpr ⟨by simp, fun c hc => ?_⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  exact retClass_int (List.all_eq_true.mp (sigIntB_iff.mp h).2 p hp)

/-- **The integer call sites the lowering emits** (`call`, `call_indirect`: `M` the number of
returns; `try_call`, `try_call_indirect`: `max` of it and the two payload registers) have their
signature's registers. -/
theorem siteRegsR_int {s : Clif.Signature} {locs : List ArgLoc} {S : Nat} {bytes args : List Nat}
    (hl : sigArgLocs s = .ok (locs, S)) (hb : sigParamBytes s = .ok bytes)
    (ha : args.length = s.params.length)
    (hint : s.returns.map retClass = List.replicate s.returns.length .int) (b : Nat) {M : Nat}
    (hM : s.returns.length ≤ M) :
    SiteRegsR s (retPairs (regPairsOf ((locs.zip args).zip bytes))) (callDefs (outDefs b M)) := by
  refine ⟨?_, ?_⟩
  · rw [← regPairsOf_regLocs hl hb ha]
    simp [retPairs, List.map_map, Function.comp_def]
  · rw [hint, retRegsT_replicate_int]
    simp only [callDefs, outDefs, List.map_map, Function.comp_def]
    first
      | rw [← List.map_take, List.take_range, Nat.min_eq_left hM]
      | rw [List.map_take, List.take_range, Nat.min_eq_left hM]
      | rw [List.take_map, List.take_range, Nat.min_eq_left hM]

theorem argPairsC_liftC_snd (cls : Nat → RegClass) (L : List (Nat × Reg)) :
    (argPairsC (liftC cls L)).map (·.2) = L.map (·.2) := by
  simp [argPairsC, liftC, List.map_map, Function.comp_def]

theorem callDefsC_outDefsC_fst (b : Nat) {ps : List Reg} {cs : List RegClass}
    (h : ps.length = cs.length) : (callDefsC (outDefsC b ps cs)).map (·.1) = ps := by
  have e : (callDefsC (outDefsC b ps cs)).map (·.1) = (ps.zip cs.zipIdx).map Prod.fst := by
    simp [callDefsC, outDefsC, List.map_map, Function.comp_def]
  rw [e, List.map_fst_zip (by simp [h])]

/-- **The typed `call` sites the lowering emits** (arguments in vregs of their classes, returns
from `retRegsC` of their classes) have their signature's registers. -/
theorem siteRegsR_callC {s : Clif.Signature} {locs : List ArgLoc} {S : Nat}
    {bytes args : List Nat} (hl : sigArgLocs s = .ok (locs, S))
    (hb : sigParamBytes s = .ok bytes) (ha : args.length = s.params.length)
    (cls : Nat → RegClass) {ps : List Reg} (hps : retRegsC (s.returns.map retClass) 0 0 = some ps)
    (b : Nat) :
    SiteRegsR s (argPairsC (liftC cls (regPairsOf ((locs.zip args).zip bytes))))
      (callDefsC (outDefsC b ps (s.returns.map retClass))) := by
  have hpl := retRegsC_lengthC _ _ _ hps
  refine ⟨by rw [argPairsC_liftC_snd, regPairsOf_regLocs hl hb ha], ?_⟩
  rw [callDefsC_outDefsC_fst b hpl, ← retRegsC_eq _ _ _ _ hps]
  exact List.take_of_length_le (by simp [hpl])

/-- **The typed `try_call` sites the lowering emits** (the returns' registers, then the payload
registers that are not return registers) have their signature's registers. -/
theorem siteRegsR_tryC {s : Clif.Signature} {locs : List ArgLoc} {S : Nat}
    {bytes args : List Nat} (hl : sigArgLocs s = .ok (locs, S))
    (hb : sigParamBytes s = .ok bytes) (ha : args.length = s.params.length)
    (cls : Nat → RegClass) {ps : List Reg} (hps : retRegsC (s.returns.map retClass) 0 0 = some ps)
    (b : Nat) (fp : List Reg) :
    SiteRegsR s (argPairsC (liftC cls (regPairsOf ((locs.zip args).zip bytes))))
      (callDefsC (outDefsC b (ps ++ fp) (s.returns.map retClass ++
        List.replicate fp.length .int))) := by
  have hpl := retRegsC_lengthC _ _ _ hps
  refine ⟨by rw [argPairsC_liftC_snd, regPairsOf_regLocs hl hb ha], ?_⟩
  rw [callDefsC_outDefsC_fst b (by simp [hpl]), ← retRegsC_eq _ _ _ _ hps]
  exact List.take_left' (by simpa using hpl)

/-! ## Signatures `abiMatch` relates -/

/-- An ABI parameter without its extension flag (which no placement reads). -/
def stripExt (p : Clif.AbiParam) : Clif.AbiParam := { ty := p.ty, purpose := p.purpose }

theorem map_stripExt_eq : ∀ {ps qs : List Clif.AbiParam},
    Clif.AbiParam.tys ps = Clif.AbiParam.tys qs →
    Clif.AbiParam.purposes ps = Clif.AbiParam.purposes qs → ps.map stripExt = qs.map stripExt
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [Clif.AbiParam.tys] at h
  | _ :: _, [], h, _ => by simp [Clif.AbiParam.tys] at h
  | p :: ps, q :: qs, h1, h2 => by
    simp only [Clif.AbiParam.tys, Clif.AbiParam.purposes, List.map_cons, List.cons.injEq] at h1 h2
    rw [List.map_cons, List.map_cons, map_stripExt_eq (ps := ps) (qs := qs) h1.2 h2.2]
    simp [stripExt, h1.1, h2.1]

theorem mapM_map_stripExt {α : Type} (f : Clif.AbiParam → Except String α)
    (hf : ∀ p, f (stripExt p) = f p) : ∀ ps : List Clif.AbiParam,
    (ps.map stripExt).mapM f = ps.mapM f
  | [] => rfl
  | p :: ps => by
    rw [List.map_cons, List.mapM_cons, List.mapM_cons, hf, mapM_map_stripExt f hf ps]

theorem paramLocs_stripExt (ps : List Clif.AbiParam) (bytes : List Nat) :
    paramLocs (ps.map stripExt) bytes = paramLocs ps bytes := by
  unfold paramLocs
  simp [List.any_map, List.zip_map_left, List.filter_map, List.map_map, List.foldl_map,
    Function.comp_def, stripExt]
  all_goals rfl

/-- The argument locations of a signature depend on its parameters' types and purposes only. -/
theorem sigArgLocs_stripExt (s : Clif.Signature) :
    sigArgLocs { params := s.params.map stripExt } = sigArgLocs s := by
  have ha : sigArgs { params := s.params.map stripExt } = sigArgs s := by
    unfold sigArgs
    exact mapM_map_stripExt _ (by intro p; rfl) s.params
  unfold sigArgLocs
  rw [ha]
  simp only [paramLocs_stripExt]

/-- **Signatures `abiMatch` relates have the same parameter registers** (the same parameter
types and purposes: the same `sigArgLocs`). -/
theorem regLocs_of_abiMatch {d t : Clif.Signature} (h : d.abiMatch t = true) :
    E2E.regLocs d = E2E.regLocs t := by
  obtain ⟨h1, h2, -⟩ := Clif.Signature.abiMatch_eq_true.mp h
  have hd : sigArgLocs d = sigArgLocs t := by
    rw [← sigArgLocs_stripExt d, ← sigArgLocs_stripExt t, map_stripExt_eq h1 h2]
  unfold E2E.regLocs locsOf
  rw [hd]

/-- Signatures `abiMatch` relates whose returns are all `normal` have the same return classes. -/
theorem retClasses_of_abiMatch {d t : Clif.Signature} (h : d.abiMatch t = true)
    (hd : ∀ p ∈ d.returns, p.purpose = .normal) (ht : ∀ p ∈ t.returns, p.purpose = .normal) :
    d.returns.map retClass = t.returns.map retClass := by
  obtain ⟨-, -, h3⟩ := Clif.Signature.abiMatch_eq_true.mp h
  have e : ∀ (s : Clif.Signature), (∀ p ∈ s.returns, p.purpose = .normal) →
      s.returns.map retClass = (Clif.AbiParam.tys s.returns).map tyClass := by
    intro s hs
    rw [Clif.AbiParam.tys, List.map_map]
    exact List.map_congr_left fun p hp => by simp [retClass, hs p hp]
  rw [e d hd, e t ht, h3]

/-- **`SiteRegsR` moves along `abiMatch`** (with the same return classes, `retClasses_of_abiMatch`):
a site with the registers of its signature `d` has those of every function signature `t` it may
enter. -/
theorem siteRegsR_of_abiMatch {d t : Clif.Signature} (h : d.abiMatch t = true)
    (hr : d.returns.map retClass = t.returns.map retClass) {us ds : List (Reg × Reg)}
    (hs : SiteRegsR d us ds) : SiteRegsR t us ds := by
  obtain ⟨h1, h2⟩ := hs
  have hl : d.returns.length = t.returns.length := by
    have := congrArg List.length hr
    simpa using this
  exact ⟨h1.trans (regLocs_of_abiMatch h), by rw [← hl, ← hr]; exact h2⟩

/-! ## The contracts -/

/-- **`CallsRefineP` with the site's registers**: the clauses of a call through the GOT (`blr` of
a `loadExtNameGot`) are required only at sites with the callee's registers (`SiteRegsR`); the
`bl` clauses are `CallsRefineP`'s. -/
def CallsRefinePR (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (env : Clif.Env) (exts : List Clif.ExtFunc) (MR : MemRelT)
    (isem : Sem) : Prop :=
  ∃ sym : String → BitVec 64,
    (∀ (rd : Reg) (n : String) (w : Arm.ArmState), ∃ w',
      isem (.loadExtNameGot rd n) [] w = some ([ofX (sym n)], w', .next) ∧ SameWorldNF F w' w) ∧
    (∀ ext ∈ exts, ∀ g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (w : Arm.ArmState)
      (dest : CallDest) (us ds : List (Reg × Reg)) (uses args : List CV)
      (vals rvals : List Clif.Val) (cm' : Clif.Mem),
      env.extern ext.name = some g →
      (dest = .sym ext.name ∧ uses = args ∨
        ∃ r, dest = .reg r ∧ ext.colocated = false ∧ uses = ofX (sym ext.name) :: args ∧
          SiteRegsR ext.sig us ds) →
      ds.length = ext.sig.returns.length →
      ArgsAt ext.sig vals args w → MR sl cm w → Pc ext.name ext.sig vals cm →
      g vals cm = .returned rvals cm' → rvals.length = ext.sig.returns.length →
      ∃ outs w', isem (.call ⟨dest, us, ds⟩) uses w = some (outs, w', .next) ∧
        outs.length = ds.length ∧ PrefixHold rvals outs ∧ MR sl cm' w') ∧
    ∀ ext ∈ exts, ∀ g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (w : Arm.ArmState)
      (dest : CallDest) (us ds : List (Reg × Reg)) (ti : TryInfo) (uses args : List CV)
      (vals rvals : List Clif.Val) (cm' : Clif.Mem),
      env.extern ext.name = some g →
      (dest = .sym ext.name ∧ uses = args ∨
        ∃ r, dest = .reg r ∧ ext.colocated = false ∧ uses = ofX (sym ext.name) :: args ∧
          SiteRegsR ext.sig us ds) →
      ext.sig.returns.length ≤ ds.length → ti.rets ≤ ext.sig.returns.length →
      ArgsAt ext.sig vals args w → MR sl cm w → Pc ext.name ext.sig vals cm →
      g vals cm = .returned rvals cm' → rvals.length = ext.sig.returns.length →
      ∃ outs w', isem (.tryCall ⟨dest, us, ds⟩ ti) uses w = some (outs, w', .goto ti.handlers.length) ∧
        outs.length = ds.length ∧ PrefixHold rvals outs ∧ MR sl cm' w'

theorem CallsRefineP.toPR {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {env : Clif.Env} {exts : List Clif.ExtFunc} {MR : MemRelT}
    {isem : Sem} (h : CallsRefineP Pc F env exts MR isem) : CallsRefinePR Pc F env exts MR isem := by
  obtain ⟨sym, h1, h2, h3⟩ := h
  refine ⟨sym, h1, fun ext hin g sl cm w dest us ds uses args vals rvals cm' a1 a2 =>
    h2 ext hin g sl cm w dest us ds uses args vals rvals cm' a1 ?_,
    fun ext hin g sl cm w dest us ds ti uses args vals rvals cm' a1 a2 =>
    h3 ext hin g sl cm w dest us ds ti uses args vals rvals cm' a1 ?_⟩
  · rcases a2 with a2 | ⟨r, e1, e2, e3, -⟩
    · exact .inl a2
    · exact .inr ⟨r, e1, e2, e3⟩
  · rcases a2 with a2 | ⟨r, e1, e2, e3, -⟩
    · exact .inl a2
    · exact .inr ⟨r, e1, e2, e3⟩

/-- **`IndCallsRefineP` with the site's registers**: the indirect clauses are required only at
sites with the registers of the site's signature (`SiteRegsR sig`). -/
def IndCallsRefinePR (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (env : Clif.Env) (sigs : List Clif.Signature) (MR : MemRelT) (isem : Sem) : Prop :=
  (∀ sig ∈ sigs, ∀ (n : String) g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem)
      (w : Arm.ArmState) (a : Nat) (r : Reg) (us ds : List (Reg × Reg)) (u : CV) (args : List CV)
      (vals rvals : List Clif.Val) (cm' : Clif.Mem),
    env.extern n = some g → (∀ s, env.sigOf n = some s → sig.abiMatch s = true) →
    cm.symbols n = some a → lo64 u = BitVec.ofNat 64 a →
    ds.length = sig.returns.length → ArgsAt sig vals args w → MR sl cm w →
    Pc n sig vals cm →
    g vals cm = .returned rvals cm' → rvals.length = sig.returns.length →
    vals.map (·.ty) = Clif.AbiParam.tys sig.params → SiteRegsR sig us ds →
    ∃ outs w', isem (.call ⟨.reg r, us, ds⟩) (u :: args) w = some (outs, w', .next) ∧
      outs.length = ds.length ∧ PrefixHold rvals outs ∧ MR sl cm' w') ∧
  (∀ sig ∈ sigs, ∀ (n : String) g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem)
      (w : Arm.ArmState) (a : Nat) (r : Reg) (us ds : List (Reg × Reg)) (ti : TryInfo) (u : CV)
      (args : List CV) (vals rvals : List Clif.Val) (cm' : Clif.Mem),
    env.extern n = some g → (∀ s, env.sigOf n = some s → sig.abiMatch s = true) →
    cm.symbols n = some a → lo64 u = BitVec.ofNat 64 a →
    sig.returns.length ≤ ds.length → ti.rets ≤ sig.returns.length →
    ArgsAt sig vals args w → MR sl cm w →
    Pc n sig vals cm →
    g vals cm = .returned rvals cm' → rvals.length = sig.returns.length →
    vals.map (·.ty) = Clif.AbiParam.tys sig.params → SiteRegsR sig us ds →
    ∃ outs w', isem (.tryCall ⟨.reg r, us, ds⟩ ti) (u :: args) w =
        some (outs, w', .goto ti.handlers.length) ∧
      outs.length = ds.length ∧ PrefixHold rvals outs ∧ MR sl cm' w')

theorem IndCallsRefineP.toPR {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {env : Clif.Env} {sigs : List Clif.Signature} {MR : MemRelT} {isem : Sem}
    (h : IndCallsRefineP Pc env sigs MR isem) : IndCallsRefinePR Pc env sigs MR isem :=
  ⟨fun sig hin n g sl cm w a r us ds u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 _ =>
    h.1 sig hin n g sl cm w a r us ds u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11,
   fun sig hin n g sl cm w a r us ds ti u args vals rvals cm' a1 a2 a3 a4 a5 a0 a6 a7 a8 a9 a10
      a11 _ =>
    h.2 sig hin n g sl cm w a r us ds ti u args vals rvals cm' a1 a2 a3 a4 a5 a0 a6 a7 a8 a9 a10
      a11⟩

/-! ## The rule families -/

/-- **The call rules with the registered callee contract** (`CallRulesCorrectP` with
`CallsRefinePR`). -/
def CallRulesCorrectPR (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → OutArgsOk F outB MR →
    CallsRefinePR Pc F env exts MR isem →
    ∀ r ∈ p.rulesOf TId.lower, callRootRule r = true → CallRuleOkP Rd Pc isem MR env cp exts outB p r

/-- **The `call_indirect` rule with the registered indirect-call contract** (`IndRulesCorrectP` with
`IndCallsRefinePR`). -/
def IndRulesCorrectPR (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (sigs : List Clif.Signature) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → OutArgsOk F outB MR →
    IndStack sigs outB → IndCallsRefinePR Pc env sigs MR isem →
    ∀ r ∈ p.rulesOf TId.lower, indRootRule r = true → IndRuleOkP Rd Pc isem MR env cp sigs p r

/-- **The `try_call` rules with the registered callee contract** (`TryRulesCorrectP` with
`CallsRefinePR`). -/
def TryRulesCorrectPR (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → OutArgsOk F outB MR →
    CallsRefinePR Pc F env exts MR isem →
    ∀ r ∈ p.rulesOf TId.lower_branch, tryRootRule r = true →
      TryRuleOkP Rd Pc isem MR env cp exts outB p r

/-- **The `try_call_indirect` rule with the registered indirect-call contract**
(`TryIndRulesCorrectP` with `IndCallsRefinePR`). -/
def TryIndRulesCorrectPR (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (sigs : List Clif.Signature) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → OutArgsOk F outB MR →
    IndStack sigs outB → IndCallsRefinePR Pc env sigs MR isem →
    ∀ r ∈ p.rulesOf TId.lower_branch, tryIndRootRule r = true →
      TryIndRuleOkP Rd Pc isem MR env cp sigs p r

/-- `CallRulesCorrectTP` with `CallsRefinePR`. -/
def CallRulesCorrectTPR (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → OutArgsOk F outB MR →
    CallsRefinePR Pc F env exts MR isem →
    ∀ r ∈ p.rulesOf TId.lower, callRootRule r = true →
      CallRuleOkTP Rd Pc isem MR env cp exts outB p r

/-- `IndRulesCorrectTP` with `IndCallsRefinePR`. -/
def IndRulesCorrectTPR (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (sigs : List Clif.Signature) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → OutArgsOk F outB MR →
    IndStack sigs outB → IndCallsRefinePR Pc env sigs MR isem →
    ∀ r ∈ p.rulesOf TId.lower, indRootRule r = true → IndRuleOkTP Rd Pc isem MR env cp sigs p r

/-- `TryRulesCorrectTP` with `CallsRefinePR`. -/
def TryRulesCorrectTPR (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → OutArgsOk F outB MR →
    CallsRefinePR Pc F env exts MR isem →
    ∀ r ∈ p.rulesOf TId.lower_branch, tryRootRule r = true →
      TryRuleOkTP Rd Pc isem MR env cp exts outB p r

/-- `TryIndRulesCorrectTP` with `IndCallsRefinePR`. -/
def TryIndRulesCorrectTPR (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (sigs : List Clif.Signature) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → OutArgsOk F outB MR →
    IndStack sigs outB → IndCallsRefinePR Pc env sigs MR isem →
    ∀ r ∈ p.rulesOf TId.lower_branch, tryIndRootRule r = true →
      TryIndRuleOkTP Rd Pc isem MR env cp sigs p r

/-- `CallRulesCorrectTFP` with `CallsRefinePR`. -/
def CallRulesCorrectTFPR (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → MemRefinesFP Rd F sb isem →
    OutArgsOk F outB MR → CallsRefinePR Pc F env exts MR isem →
    ∀ r ∈ p.rulesOf TId.lower, callRootRule r = true →
      CallRuleOkTFP Rd Pc isem MR env cp exts outB p r

/-- `TryRulesCorrectTFP` with `CallsRefinePR`. -/
def TryRulesCorrectTFPR (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → MemRefinesFP Rd F sb isem →
    OutArgsOk F outB MR → CallsRefinePR Pc F env exts MR isem →
    ∀ r ∈ p.rulesOf TId.lower_branch, tryRootRule r = true →
      TryRuleOkTFP Rd Pc isem MR env cp exts outB p r

/-! ## The families without registers -/

theorem callRulesCorrectP_of_PR {p : Program} (h : CallRulesCorrectPR p) : CallRulesCorrectP p :=
  fun Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hCR =>
    h Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hCR.toPR

theorem indRulesCorrectP_of_PR {p : Program} (h : IndRulesCorrectPR p) : IndRulesCorrectP p :=
  fun Rd Pc F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hCR =>
    h Rd Pc F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hCR.toPR

theorem tryRulesCorrectP_of_PR {p : Program} (h : TryRulesCorrectPR p) : TryRulesCorrectP p :=
  fun Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hCR =>
    h Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hCR.toPR

theorem tryIndRulesCorrectP_of_PR {p : Program} (h : TryIndRulesCorrectPR p) :
    TryIndRulesCorrectP p :=
  fun Rd Pc F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hCR =>
    h Rd Pc F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hCR.toPR

theorem callRulesCorrectTP_of_PR {p : Program} (h : CallRulesCorrectTPR p) :
    CallRulesCorrectTP p :=
  fun Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hCR =>
    h Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hCR.toPR

theorem indRulesCorrectTP_of_PR {p : Program} (h : IndRulesCorrectTPR p) : IndRulesCorrectTP p :=
  fun Rd Pc F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hCR =>
    h Rd Pc F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hCR.toPR

theorem tryRulesCorrectTP_of_PR {p : Program} (h : TryRulesCorrectTPR p) : TryRulesCorrectTP p :=
  fun Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hCR =>
    h Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hCR.toPR

theorem tryIndRulesCorrectTP_of_PR {p : Program} (h : TryIndRulesCorrectTPR p) :
    TryIndRulesCorrectTP p :=
  fun Rd Pc F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hCR =>
    h Rd Pc F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hCR.toPR

theorem callRulesCorrectTFP_of_PR {p : Program} (h : CallRulesCorrectTFPR p) :
    CallRulesCorrectTFP p :=
  fun Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hFP hout hCR =>
    h Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hFP hout hCR.toPR

theorem tryRulesCorrectTFP_of_PR {p : Program} (h : TryRulesCorrectTFPR p) :
    TryRulesCorrectTFP p :=
  fun Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hFP hout hCR =>
    h Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hFP hout hCR.toPR

end Backend.Proof
