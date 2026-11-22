import FV.E2E.SemanticReturnPinsPass
import FV.E2E.DeadCleanupPairTC

/-! # The typed theorems composed with `i128` legalisation and constant-phi removal (#1112)

Outside subset E `lean-backend` names the typed scope's theorems (`backend_correct_final_cleanupT`,
`backend_correct_world_cleanupTC`, `backend_correct_world_cleanupTCF`: `FVTest.Backend.FnVerdict`,
typed path). They take the artifact of the **compiled** function, which is cg_clif's function after
the `i128` legalisation (`Opt.Legal.checkW f g cert`) and constant-phi removal (`Opt.ConstPhi.run`
when `Opt.ConstPhi.keeps`). The theorems here have the same artifact hypotheses and conclude about
the run of the **source** function, as `FV/E2E/SemanticReturnPinsPass.lean` does for the Stock
path (#1100) and `FV/E2E/MidValPassLegacy.lean` for the mid-end validator (#1119):

* `backend_correct_pass_final_cleanupT`, `backend_correct_pass_world_cleanupTCF`,
  `backend_correct_pass_world_cleanupTC`: any pass `T` whose output simulates its input and keeps
  its shape (`Opt.FunSimX`, `ShapeFacts`; `lean-backend` names them at `T := Opt.ConstPhi.run`),
  `T f` compiled; the subset premise is the typed theorem's own, of the compiled `T f`
  (`pass_entry`, as `backend_correct_pass_finalTCF`).
* `backend_correct_legal_wide_final_cleanupT`, `backend_correct_legal_wide_world_cleanupTCF`,
  `backend_correct_legal_wide_world_cleanupTC` (`Clif.Rust.env`): `f` legalised to `g`, `g`
  compiled; every return of `f`'s run is a return of `g`'s run with the values expanded by the ABI
  groups of `f`'s returns, and every trap a trap with the same code (`Opt.Legal.checkW_refines`).
  `ArmRefinesLegalT` is `ArmRefinesLegal` with returned values by class (`ArmRefinesT`).
* `backend_correct_legal_pass_wide_final_cleanupT`, `backend_correct_legal_pass_wide_world_cleanupTCF`,
  `backend_correct_legal_pass_wide_world_cleanupTC` (`Clif.Rust.env`): `f` legalised to `g`, then
  `T g` compiled (`legal_pass_refines_wide`).

Non-vacuity: `FVTest/Backend/TypedPassWitness.lean`.
-/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
set_option autoImplicit false

/-- What the Arm run does for an outcome of the original function `f` whose results are expanded
by the ABI groups `rg`, returned values by class: a return with values `vals` is a return of the
expanded values as `ArmRefinesT`; traps as `ArmRefinesT`. -/
def ArmRefinesLegalT (rg : List (List Opt.Legalize128.SlotEl)) (fb : FnBin) (base ra : BitVec 64)
    (astep : Arm.ArmState → Arm.ArmState) (s : Arm.ArmState) : Clif.Outcome → Prop
  | .returned vals cm => ∃ vals', Opt.Legal.ExpRel rg vals vals' ∧
      ArmRefinesT fb base ra astep s (.returned vals' cm)
  | o => ArmRefinesT fb base ra astep s o

/-- `ArmRefinesLegalT` of the source outcome from the refinement of the source run by the runs
of `p'` from `cs'` and `ArmRefinesT` of every such run. -/
theorem armRefinesLegalT_of {rg : List (List Opt.Legalize128.SlotEl)} {env : Clif.Env}
    {p p' : Clif.Program} {fuel : Nat} {cs cs' : Clif.State} {fb : FnBin} {base ra : BitVec 64}
    {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState}
    (hr1 : ∀ vals m, Clif.runLoop env p fuel cs = .returned vals m → ∃ vals',
      Opt.Legal.ExpRel rg vals vals' ∧ ∃ n, Clif.runLoop env p' n cs' = .returned vals' m)
    (hr2 : ∀ c, Clif.runLoop env p fuel cs = .trapped c → ∃ n,
      Clif.runLoop env p' n cs' = .trapped c)
    (hB : ∀ n, ArmRefinesT fb base ra astep s (Clif.runLoop env p' n cs')) :
    ArmRefinesLegalT rg fb base ra astep s (Clif.runLoop env p fuel cs) := by
  cases hrun : Clif.runLoop env p fuel cs with
  | returned vals m1 =>
    obtain ⟨vals', hv, k, hk⟩ := hr1 vals m1 hrun
    have := hB k
    rw [hk] at this
    exact ⟨vals', hv, this⟩
  | trapped c =>
    obtain ⟨k, hk⟩ := hr2 c hrun
    have := hB k
    rw [hk] at this
    exact this
  | stuck _ => trivial
  | outOfFuel => trivial

/-- The source run of `f` refined by the (wide) legalisation's run (`Opt.Legal.checkW_refines`
from the entry states): a return is a return of the expanded values, a trap a trap with the same
code. -/
theorem legal_refines_wide {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true)
    {p p' : Clif.Program} {env : Clif.Env}
    (hH : Opt.Legal.HelperOk env) (hXL : Opt.Legal.ExtLegal env)
    (hK : Opt.Legal.EnvKeepsAllocs env)
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hsigs : Opt.Legal.Ind128 f → ∀ n s, env.sigOf n = some s → Opt.Legalize128.sig128 s = false)
    {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hM : Opt.Legal.MemBounded cs.mem) (htrS : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals m, Clif.runLoop env p fuel cs = .returned vals m → ∃ vals',
      Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧ ∃ n,
        Clif.runLoop env p' n cs' = .returned vals' m) ∧
    (∀ c, Clif.runLoop env p fuel cs = .trapped c → ∃ n,
      Clif.runLoop env p' n cs' = .trapped c) := by
  let C : Opt.Legal.Ctx := ⟨f, g, cert⟩
  have hEnv : Opt.Legal.EnvOk env C p p' := ⟨hext, hext', hH, hXL, hK, hind, hsigs⟩
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hTr := noMemTrap_of_trapsExplicit htrS hcs.callers
  have hI := noIndInternal_of_trapsExplicit htrS hcs.callers
  rw [hcs.func] at hI
  obtain ⟨hr1, hr2⟩ := Opt.Legal.checkW_refines (C := C) hchk hEnv hb hb' hcs.func h2 h3 h4 h5
    hcs'.func h2' h3' h5' hsl hexp hM hTr hI fuel
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  rw [hst] at hr1 hr2
  rw [hst'] at hr1 hr2
  exact ⟨fun vals m h => hr1 vals m h, fun c h => hr2 c h⟩

/-! ## Constant-phi removal (a pass) -/

/-- **`backend_correct_final_cleanupT` over a pass**: for `T f` in the typed scope
(`InSubsetT` of the transformed program) compiled through the dead cleanup (`CompiledCleanupT`),
the Arm run of the compiled `T f` refines the CLIF run of the *source* program `p` from `f`'s
entry state, returned values by class (`ArmRefinesT`). Premises: `backend_correct_final_cleanupT`'s
about the compiled `T f`, externs keep the link-time symbols (`hE`), the transformed program's run
traps only explicitly (`htr`). `lean-backend` names it at `T := Opt.ConstPhi.run`. -/
theorem backend_correct_pass_final_cleanupT {T : Clif.Function → Clif.Function}
    (hP : ∀ f, Opt.FunSimX f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT (passProg T p) (T f)) (hc : CompiledCleanupT (T f) k vc vcp rf af fa fb)
    (hT : TypedRules)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (T f).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T f) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs (T f)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbols env)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env (passProg T p) (passEntry T f cs)) (fuel : Nat) :
    ArmRefinesT fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  have hF := hS f
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := pass_entry hP hE hcs fuel (p := p)
  exact armRefinesT_of_outcome hn (backend_correct_final_cleanupT hsub hc hT hcov hC hCT hTls
    (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs'
    (by rw [rel_holds_slots hF.slots, hsl, hmem]; exact hrel) htr n')

/-- **`backend_correct_world_cleanupTCF` over a pass**: for `T f` in the typed scope with the
proven float operations compiled through the dead cleanup (`CompiledCleanupTCF`), every return
and trap of the CLIF run of the *source* program `p` from `f`'s entry state is matched by the Arm
run of the compiled `T f` as in `backend_correct_world_cleanupTCF`. Premises: that theorem's
about the compiled `T f`, externs keep the link-time symbols (`hE`), the transformed program's
run traps only explicitly (`htr`). -/
theorem backend_correct_pass_world_cleanupTCF {T : Clif.Function → Clif.Function}
    (hP : ∀ f, Opt.FunSimX f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hsub : InSubsetTCF (passProg T p) (T f))
    (hc : CompiledCleanupTCF (T f) k vc vcp rf af fa fb) (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs (T f))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbols env)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env (passProg T p) (passEntry T f cs)) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) := by
  have hF := hS f
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := pass_entry hP hE hcs fuel (p := p)
  have hW : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ (T f) c =
      RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c := relW_slots hF.slots c
  have key := backend_correct_world_cleanupTCF (K := K) hsub hc hT hcov
    (by rw [hW, hF.externs]; exact hX) (by rw [hW]; exact hXI) hsym hslot hcs'
    (by rw [hW, hsl, hmem]; exact hrel) (by rw [hF.sig]; exact hargs) htr n'
  rw [hF.sig] at key
  exact ⟨fun vals cm hrun => key.1 vals cm (hn.1 _ _ hrun), fun c' hrun => key.2 c' (hn.2 _ hrun)⟩

/-- **`backend_correct_world_cleanupTC` over a pass** (`backend_correct_pass_world_cleanupTCF`
for the scope with typed `try_call`s). -/
theorem backend_correct_pass_world_cleanupTC {T : Clif.Function → Clif.Function}
    (hP : ∀ f, Opt.FunSimX f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hsub : InSubsetTC (passProg T p) (T f))
    (hc : CompiledCleanupTC (T f) k vc vcp rf af fa fb) (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs (T f))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbols env)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env (passProg T p) (passEntry T f cs)) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) :=
  backend_correct_pass_world_cleanupTCF hP hS hsub.toTCF hc.toTCF hT hcov hX hXI hsym hslot hE hcs
    hrel hargs htr fuel

/-! ## `i128` legalisation -/

/-- **`backend_correct_final_cleanupT` for an `i128` function** (`backend_correct_legal_wide_cleanup`
for the typed scope), under `Clif.Rust.env`: `f` legalised to `g` (`Opt.Legal.checkW f g cert`),
`g` in the typed scope compiled through the dead cleanup; the Arm code of `g`, entered with the
ABI-split arguments, refines the run of the *source* `f`, returned values by class
(`ArmRefinesLegalT`). -/
theorem backend_correct_legal_wide_final_cleanupT {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p' g) (hc : CompiledCleanupT g k vc vcp rf af fa fb) (hT : TypedRules)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ g.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls g = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk Clif.Rust.env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk Clif.Rust.env (indSigs g) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val}
    {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hargs : ArgsIn g.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicit Clif.Rust.env p cs) (htr : TrapsExplicit Clif.Rust.env p' cs')
    (fuel : Nat) :
    ArmRefinesLegalT ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) := by
  obtain ⟨hr1, hr2⟩ := legal_refines_wide hchk Clif.Rust.helperOk_env Clif.Rust.extLegal_env
    Clif.Rust.envKeepsAllocs_env hext hext' hind (fun _ _ _ h => by cases h) hexp hcs hcs' hsl
    hmem (hmem ▸ memBounded_of_holds hrel) htrS fuel
  exact armRefinesLegalT_of hr1 hr2 fun n => backend_correct_final_cleanupT hsub hc hT hcov hC
    hCT hTls hX hXI hsym hslot hent hres hbe hargs hcs' hrel htr n

/-- **`backend_correct_world_cleanupTCF` for an `i128` function**, under `Clif.Rust.env`: `f`
legalised to `g`, `g` in the typed scope with the proven float operations compiled through the
dead cleanup; every return of the run of the *source* `f` is a return of `g`'s run with the values
expanded by the ABI groups of `f`'s returns, matched by the Arm run of the compiled `g` as in
`backend_correct_world_cleanupTCF`; every trap is a trap with the same code. -/
theorem backend_correct_legal_wide_world_cleanupTCF {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hsub : InSubsetTCF p' g) (hc : CompiledCleanupTCF g k vc vcp rf af fa fb) (hT : TypedRules)
    {K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk Clif.Rust.env (g.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c) X)
    (hXI : XCallsIndOk Clif.Rust.env (indSigs g)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c cs'.frame.slots cs'.mem w₀)
    (hargs : ArgsAtEntry F g.sig args' w₀)
    (htrS : TrapsExplicit Clif.Rust.env p cs) (htr : TrapsExplicit Clif.Rust.env p' cs')
    (fuel : Nat) :
    (∀ vals cm, Clif.runLoop Clif.Rust.env p fuel cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals' us ∧ vals'.map (·.ty) = Clif.AbiParam.tys g.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals' outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop Clif.Rust.env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) := by
  obtain ⟨hr1, hr2⟩ := legal_refines_wide hchk Clif.Rust.helperOk_env Clif.Rust.extLegal_env
    Clif.Rust.envKeepsAllocs_env hext hext' hind (fun _ _ _ h => by cases h) hexp hcs hcs' hsl
    hmem (hmem ▸ memBounded_of_holds hrel.1) htrS fuel
  have key := fun n => backend_correct_world_cleanupTCF (K := K) hsub hc hT hcov hX hXI hsym hslot
    hcs' hrel hargs htr n
  refine ⟨fun vals cm hrun => ?_, fun c' hrun => ?_⟩
  · obtain ⟨vals', hv, n, hn⟩ := hr1 vals cm hrun
    exact ⟨vals', hv, (key n).1 vals' cm hn⟩
  · obtain ⟨n, hn⟩ := hr2 c' hrun
    exact (key n).2 c' hn

/-- **`backend_correct_world_cleanupTC` for an `i128` function**
(`backend_correct_legal_wide_world_cleanupTCF` for the scope with typed `try_call`s). -/
theorem backend_correct_legal_wide_world_cleanupTC {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hsub : InSubsetTC p' g) (hc : CompiledCleanupTC g k vc vcp rf af fa fb) (hT : TypedRules)
    {K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk Clif.Rust.env (g.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c) X)
    (hXI : XCallsIndOk Clif.Rust.env (indSigs g)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c cs'.frame.slots cs'.mem w₀)
    (hargs : ArgsAtEntry F g.sig args' w₀)
    (htrS : TrapsExplicit Clif.Rust.env p cs) (htr : TrapsExplicit Clif.Rust.env p' cs')
    (fuel : Nat) :
    (∀ vals cm, Clif.runLoop Clif.Rust.env p fuel cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals' us ∧ vals'.map (·.ty) = Clif.AbiParam.tys g.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals' outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop Clif.Rust.env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) :=
  backend_correct_legal_wide_world_cleanupTCF hchk hsub.toTCF hc.toTCF hT hext hext' hind hcov hX
    hXI hsym hslot hexp hcs hcs' hsl hmem hrel hargs htrS htr fuel

/-! ## `i128` legalisation, then constant-phi removal -/

/-- **`backend_correct_final_cleanupT` for an `i128` function legalised, then transformed by a
pass** (`backend_correct_legal_pass_wide_cleanup` for the typed scope), under `Clif.Rust.env`:
`f` legalised to `g`, `T g` in the typed scope compiled through the dead cleanup; the Arm code of
`T g`, entered with the ABI-split arguments, refines the run of the *source* `f`
(`ArmRefinesLegalT`). -/
theorem backend_correct_legal_pass_wide_final_cleanupT {T : Clif.Function → Clif.Function}
    {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true)
    (hP : ∀ f, Opt.FunSimX f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT (passProg T p') (T g)) (hc : CompiledCleanupT (T g) k vc vcp rf af fa fb)
    (hT : TypedRules)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ (T g).blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls (T g) = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk Clif.Rust.env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk Clif.Rust.env (indSigs (T g)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val}
    {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hargs : ArgsIn g.sig args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicit Clif.Rust.env p cs)
    (htr : TrapsExplicit Clif.Rust.env (passProg T p') (passEntry T g cs'))
    (fuel : Nat) :
    ArmRefinesLegalT ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs) := by
  have hF := hS g
  obtain ⟨hr1, hr2⟩ := legal_pass_refines_wide hchk hP Clif.Rust.helperOk_env
    Clif.Rust.extLegal_env Clif.Rust.envKeepsAllocs_env RustSyms.envKeepsSymbols_env hext hext'
    hind (fun _ _ _ h => by cases h) hexp hcs hcs' hsl hmem (hmem ▸ memBounded_of_holds hrel) htrS
    fuel
  obtain ⟨hcs'', hsl', hmem', -⟩ := pass_entry hP RustSyms.envKeepsSymbols_env hcs' 0 (p := p')
  exact armRefinesLegalT_of hr1 hr2 fun n => backend_correct_final_cleanupT hsub hc hT hcov hC hCT
    hTls (fun s' => by rw [rel_holds_slots hF.slots, hF.externs]; exact hX s')
    (fun s' => by rw [rel_holds_slots hF.slots]; exact hXI s') hsym hslot hent hres hbe
    (by rw [hF.sig]; exact hargs) hcs''
    (by rw [rel_holds_slots hF.slots, hsl', hmem']; exact hrel) htr n

/-- **`backend_correct_world_cleanupTCF` for an `i128` function legalised, then transformed by a
pass**, under `Clif.Rust.env`: `f` legalised to `g`, `T g` in the typed scope with the proven float
operations compiled through the dead cleanup; every return of the run of the *source* `f` is a
return of `g`'s run with the values expanded by the ABI groups of `f`'s returns, matched by the Arm
run of the compiled `T g` as in `backend_correct_world_cleanupTCF`; every trap is a trap with the
same code. -/
theorem backend_correct_legal_pass_wide_world_cleanupTCF {T : Clif.Function → Clif.Function}
    {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true)
    (hP : ∀ f, Opt.FunSimX f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hsub : InSubsetTCF (passProg T p') (T g))
    (hc : CompiledCleanupTCF (T g) k vc vcp rf af fa fb) (hT : TypedRules) {K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk Clif.Rust.env (g.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c) X)
    (hXI : XCallsIndOk Clif.Rust.env (indSigs (T g))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c cs'.frame.slots cs'.mem w₀)
    (hargs : ArgsAtEntry F g.sig args' w₀)
    (htrS : TrapsExplicit Clif.Rust.env p cs)
    (htr : TrapsExplicit Clif.Rust.env (passProg T p') (passEntry T g cs')) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop Clif.Rust.env p fuel cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals' us ∧ vals'.map (·.ty) = Clif.AbiParam.tys g.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals' outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop Clif.Rust.env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) := by
  have hF := hS g
  obtain ⟨hr1, hr2⟩ := legal_pass_refines_wide hchk hP Clif.Rust.helperOk_env
    Clif.Rust.extLegal_env Clif.Rust.envKeepsAllocs_env RustSyms.envKeepsSymbols_env hext hext'
    hind (fun _ _ _ h => by cases h) hexp hcs hcs' hsl hmem (hmem ▸ memBounded_of_holds hrel.1)
    htrS fuel
  obtain ⟨hcs'', hsl', hmem', -⟩ := pass_entry hP RustSyms.envKeepsSymbols_env hcs' 0 (p := p')
  have hW : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ (T g) c =
      RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c := relW_slots hF.slots c
  have key := fun n => backend_correct_world_cleanupTCF (K := K) hsub hc hT hcov
    (by rw [hW, hF.externs]; exact hX) (by rw [hW]; exact hXI) hsym hslot hcs''
    (by rw [hW, hsl', hmem']; exact hrel) (by rw [hF.sig]; exact hargs) htr n
  refine ⟨fun vals cm hrun => ?_, fun c' hrun => ?_⟩
  · obtain ⟨vals', hv, n, hn⟩ := hr1 vals cm hrun
    have h := (key n).1 vals' cm hn
    rw [hF.sig] at h
    exact ⟨vals', hv, h⟩
  · obtain ⟨n, hn⟩ := hr2 c' hrun
    exact (key n).2 c' hn

/-- **`backend_correct_world_cleanupTC` for an `i128` function legalised, then transformed by a
pass** (`backend_correct_legal_pass_wide_world_cleanupTCF` for the scope with typed `try_call`s). -/
theorem backend_correct_legal_pass_wide_world_cleanupTC {T : Clif.Function → Clif.Function}
    {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true)
    (hP : ∀ f, Opt.FunSimX f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hsub : InSubsetTC (passProg T p') (T g))
    (hc : CompiledCleanupTC (T g) k vc vcp rf af fa fb) (hT : TypedRules) {K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk Clif.Rust.env (g.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c) X)
    (hXI : XCallsIndOk Clif.Rust.env (indSigs (T g))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c cs'.frame.slots cs'.mem w₀)
    (hargs : ArgsAtEntry F g.sig args' w₀)
    (htrS : TrapsExplicit Clif.Rust.env p cs)
    (htr : TrapsExplicit Clif.Rust.env (passProg T p') (passEntry T g cs')) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop Clif.Rust.env p fuel cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals' us ∧ vals'.map (·.ty) = Clif.AbiParam.tys g.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals' outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop Clif.Rust.env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) :=
  backend_correct_legal_pass_wide_world_cleanupTCF hchk hP hS hsub.toTCF hc.toTCF hT hext hext' hind
    hcov hX hXI hsym hslot hexp hcs hcs' hsl hmem hrel hargs htrS htr fuel

end E2E
