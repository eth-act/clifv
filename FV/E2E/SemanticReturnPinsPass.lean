import FV.E2E.CompiledSemanticReturnPins
import FV.E2E.PassX
import FV.E2E.Legal

/-! # The Stock path's theorem composed with `i128` legalisation and constant-phi removal (#1100)

On the Stock path (`lean-backend`'s default: no `--opt`, no `try_call` in the file) a function is
compiled after the `i128` legalisation (`Opt.Legalize128.parsedFile128`, accepted by
`Opt.Legal.checkW`) and constant-phi removal (`Opt.ConstPhi.select`, i.e. `Opt.ConstPhi.run` when
`Opt.ConstPhi.keeps`). Its theorem `backend_correct_world_niX_semantic_return_pins` takes the
Stock artifact `CompiledSemanticReturnPins` of the **compiled** function. The theorems here have
the same artifact as hypothesis and conclude about the run of cg_clif's **source** function:

* `backend_correct_legal_env_wide_semantic_return_pins`, `backend_correct_legal_wide_semantic_return_pins`
  (`Clif.Rust.env`): `f` legalised to `g` (`Opt.Legal.checkW f g cert`), `g` compiled; every
  return of `f`'s run is a return of `g`'s run with the values expanded by the ABI groups
  (`Opt.Legal.checkW_refines`), and the Stock conclusion holds for it. As
  `backend_correct_legal_env_wide_cleanup` for the legacy artifact.
* `backend_correct_pass_semantic_return_pins`: any pass `T` whose output simulates its input and
  keeps its shape (`Opt.FunSimX`, `ShapeFacts`; `lean-backend` names it at
  `T := Opt.ConstPhi.run`, `Opt.ConstPhi.run_simX`, `Opt.ConstPhi.run_shape`), `T f` compiled
  (`pass_entry`). As `backend_correct_pass_cleanup`.
* `backend_correct_legal_pass_env_wide_semantic_return_pins`,
  `backend_correct_legal_pass_wide_semantic_return_pins` (`Clif.Rust.env`): `f` legalised to `g`,
  then `T g` compiled. As `backend_correct_legal_pass_env_wide_cleanup`.

The Stock theorem's conclusion is about every return of the run (no trap clause), so is each
composition. Non-vacuity: `FVTest/Backend/SemanticReturnPinsPassWitness.lean` (a real function of
the examples that constant-phi removal changes, every checkable premise proved).
-/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The return-pin contract reads only the function's signature. -/
theorem ReturnPinMode.valid_sig {f g : Clif.Function} (h : g.sig = f.sig) (mode : ReturnPinMode) :
    mode.Valid g = mode.Valid f := by
  cases mode <;> funext vals us <;> simp [ReturnPinMode.Valid, ReturnABI, returnPins, h]

/-- `RelW` reads only the function's slots. -/
theorem relW_slots {Γ : Rel} {f g : Clif.Function} (h : g.slots = f.slots) (c : BitVec 64) :
    RelW Γ g c = RelW Γ f c := by
  unfold RelW
  rw [rel_holds_slots h]

/-- **The Stock path's theorem over a pass** (`backend_correct_world_niX_semantic_return_pins`
composed with any pass `T` whose output simulates its input and keeps its shape): for an
in-subset function `f` of `p` whose transformation `T f` was compiled with the Stock artifact,
every return of the CLIF run of the *source* program `p` from `f`'s entry state is matched by
the Arm run of the compiled `T f`, as in the Stock theorem. Premises: the Stock theorem's about
the compiled `T f`, externs keep the link-time symbols (`hE`), the transformed program's run traps
only explicitly (`htr`). `lean-backend` names it at `T := Opt.ConstPhi.run`. -/
theorem backend_correct_pass_semantic_return_pins {T : Clif.Function → Clif.Function}
    (hT : ∀ f, Opt.FunSimX f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {mode : ReturnPinMode}
    (hsub : InSubset p f) (hc : CompiledSemanticReturnPins (T f) k vc vcp rf af fa fb mode)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
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
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnPinMode.Valid mode f vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs (T f)) c
          (CallLg env (f.externs.map (·.2)) (indSigs (T f))) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  intro vals cm hrun
  have hF := hS f
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := pass_entry hT hE hcs fuel (p := p)
  have hW : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ (T f) c =
      RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c := relW_slots hF.slots c
  have key := backend_correct_world_niX_semantic_return_pins (K := K) (inSubset_pass hS hsub) hc hcov
    (by rw [hW, hF.externs]; exact hX) (by rw [hW]; exact hXI) hsym hslot hcs'
    (by rw [hW, hsl, hmem]; exact hrel) (by rw [hF.sig]; exact hargs) htr n' vals cm
    (hn.1 _ _ hrun)
  rw [ReturnPinMode.valid_sig hF.sig, hW, hF.externs, hF.sig, hsl, hmem] at key
  exact key

/-- **The Stock path's theorem for an `i128` function legalised** (any environment with the
contracts of `Opt.Legal.checkW_refines`): for `f` legalised to `g` (`Opt.Legal.checkW f g cert`)
and `g` compiled with the Stock artifact, every return of the CLIF run of the *source* `f` in `p`
(arguments `args`) is a return of `g`'s run in `p'` (arguments `args'`, the ABI split of
`args`; same slots and memory) with the values expanded by the ABI groups of `f`'s returns,
and that return is matched by the Arm run of the compiled `g` as in the Stock theorem. -/
theorem backend_correct_legal_env_wide_semantic_return_pins {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {mode : ReturnPinMode}
    (hsub : InSubset p' g) (hc : CompiledSemanticReturnPins g k vc vcp rf af fa fb mode)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    -- the environment's contracts (`FV/Opt/Proof/LegalExt.lean`)
    (hH : Opt.Legal.HelperOk env) (hXL : Opt.Legal.ExtLegal env)
    (hK : Opt.Legal.EnvKeepsAllocs env)
    -- calls of `f` and `g` go to the environment
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    -- an indirect call of `f` resolves to the same extern in both programs
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    -- at an indirect call with an `i128` signature, no known signature has `i128`
    (hsigs : Opt.Legal.Ind128 f → ∀ n s, env.sigOf n = some s → Opt.Legalize128.sig128 s = false)
    -- the Stock theorem's premises about `g`
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (g.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c) X)
    (hXI : XCallsIndOk env (indSigs g)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the run: `f` on `args`, `g` on the ABI-split `args'` (same slots and memory)
    {w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c cs'.frame.slots cs'.mem w₀)
    (hargs : ArgsAtEntry F g.sig args' w₀)
    (htrS : TrapsExplicit env p cs) (htr : TrapsExplicit env p' cs') (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnPinMode.Valid mode g vals' us ∧ us.length = outs.length ∧
        PrefixHold vals' outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
        (XNI F syms (g.externs.map (·.2)) (indSigs g) c
          (CallLg env (g.externs.map (·.2)) (indSigs g)) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c cs'.frame.slots cs'.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip args' → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip args' → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  intro vals cm hrun
  let C : Opt.Legal.Ctx := ⟨f, g, cert⟩
  have hE : Opt.Legal.EnvOk env C p p' := ⟨hext, hext', hH, hXL, hK, hind, hsigs⟩
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hholds : Rel.holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g
      cs'.frame.slots cs'.mem w₀ := hrel.1
  have hM : Opt.Legal.MemBounded cs.mem := hmem ▸ memBounded_of_holds hholds
  have hT := noMemTrap_of_trapsExplicit htrS hcs.callers
  have hI := noIndInternal_of_trapsExplicit htrS hcs.callers
  rw [hcs.func] at hI
  obtain ⟨hr1, -⟩ := Opt.Legal.checkW_refines (C := C) hchk hE hb hb' hcs.func h2 h3 h4 h5
    hcs'.func h2' h3' h5' hsl hexp hM hT hI fuel
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  rw [hst, hst'] at hr1
  obtain ⟨vals', hv, n, hn⟩ := hr1 vals cm hrun
  exact ⟨vals', hv, backend_correct_world_niX_semantic_return_pins hsub hc hcov hX hXI hsym hslot
    hcs' hrel hargs htr n vals' cm hn⟩

/-- **`backend_correct_legal_env_wide_semantic_return_pins` under `Clif.Rust.env`** (the
environment's contracts discharged; no known signature, so `hsigs` holds). The theorem
`lean-backend` names for an `i128`-legalised function on the Stock path. -/
theorem backend_correct_legal_wide_semantic_return_pins {f g : Clif.Function}
    {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {mode : ReturnPinMode}
    (hsub : InSubset p' g) (hc : CompiledSemanticReturnPins g k vc vcp rf af fa fb mode)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
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
    ∀ vals cm, Clif.runLoop Clif.Rust.env p fuel cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnPinMode.Valid mode g vals' us ∧ us.length = outs.length ∧
        PrefixHold vals' outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
        (XNI F syms (g.externs.map (·.2)) (indSigs g) c
          (CallLg Clif.Rust.env (g.externs.map (·.2)) (indSigs g)) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c cs'.frame.slots cs'.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip args' → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip args' → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) :=
  backend_correct_legal_env_wide_semantic_return_pins hchk hsub hc Clif.Rust.helperOk_env
    Clif.Rust.extLegal_env Clif.Rust.envKeepsAllocs_env hext hext' hind (fun _ _ _ h => by cases h)
    hcov hX hXI hsym hslot hexp hcs hcs' hsl hmem hrel hargs htrS htr fuel

/-- **The Stock path's theorem for an `i128` function legalised, then transformed by a pass**
(any environment with the contracts of `Opt.Legal.checkW_refines` keeping the link-time
symbols): `f` legalised to `g` (`Opt.Legal.checkW f g cert`), `T g` compiled with the Stock
artifact; every return of the CLIF run of the *source* `f` in `p` is a return of `g`'s run in `p'`
with the values expanded by the ABI groups of `f`'s returns, matched by the Arm run of the
compiled `T g` as in the Stock theorem (`backend_correct_pass_semantic_return_pins` at `g`). -/
theorem backend_correct_legal_pass_env_wide_semantic_return_pins {T : Clif.Function → Clif.Function}
    {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true)
    (hT : ∀ f, Opt.FunSimX f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {mode : ReturnPinMode}
    (hsub : InSubset p' g) (hc : CompiledSemanticReturnPins (T g) k vc vcp rf af fa fb mode)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hH : Opt.Legal.HelperOk env) (hXL : Opt.Legal.ExtLegal env)
    (hK : Opt.Legal.EnvKeepsAllocs env) (hE : Opt.EnvKeepsSymbols env)
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite f sig) →
      p'.funcs.map (·.name) = p.funcs.map (·.name) ∧ p.externNames <+: p'.externNames)
    (hsigs : Opt.Legal.Ind128 f → ∀ n s, env.sigOf n = some s → Opt.Legalize128.sig128 s = false)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (g.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c) X)
    (hXI : XCallsIndOk env (indSigs (T g))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c cs'.frame.slots cs'.mem w₀)
    (hargs : ArgsAtEntry F g.sig args' w₀)
    (htrS : TrapsExplicit env p cs)
    (htr : TrapsExplicit env (passProg T p') (passEntry T g cs')) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnPinMode.Valid mode g vals' us ∧ us.length = outs.length ∧
        PrefixHold vals' outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
        (XNI F syms (g.externs.map (·.2)) (indSigs (T g)) c
          (CallLg env (g.externs.map (·.2)) (indSigs (T g))) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c cs'.frame.slots cs'.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip args' → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip args' → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  intro vals cm hrun
  let C : Opt.Legal.Ctx := ⟨f, g, cert⟩
  have hEnv : Opt.Legal.EnvOk env C p p' := ⟨hext, hext', hH, hXL, hK, hind, hsigs⟩
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hholds : Rel.holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g
      cs'.frame.slots cs'.mem w₀ := hrel.1
  have hM : Opt.Legal.MemBounded cs.mem := hmem ▸ memBounded_of_holds hholds
  have hTr := noMemTrap_of_trapsExplicit htrS hcs.callers
  have hI := noIndInternal_of_trapsExplicit htrS hcs.callers
  rw [hcs.func] at hI
  obtain ⟨hr1, -⟩ := Opt.Legal.checkW_refines (C := C) hchk hEnv hb hb' hcs.func h2 h3 h4 h5
    hcs'.func h2' h3' h5' hsl hexp hM hTr hI fuel
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  rw [hst, hst'] at hr1
  obtain ⟨vals', hv, n, hn⟩ := hr1 vals cm hrun
  exact ⟨vals', hv, backend_correct_pass_semantic_return_pins hT hS hsub hc hcov hX hXI hsym hslot
    hE hcs' hrel hargs htr n vals' cm hn⟩

/-- **`backend_correct_legal_pass_env_wide_semantic_return_pins` under `Clif.Rust.env`** (the
environment's contracts and `Opt.EnvKeepsSymbols` discharged). The theorem `lean-backend` names,
at `T := Opt.ConstPhi.run`, for an `i128`-legalised function that constant-phi removal changed
on the Stock path. -/
theorem backend_correct_legal_pass_wide_semantic_return_pins {T : Clif.Function → Clif.Function}
    {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.checkW f g cert = true)
    (hT : ∀ f, Opt.FunSimX f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {mode : ReturnPinMode}
    (hsub : InSubset p' g) (hc : CompiledSemanticReturnPins (T g) k vc vcp rf af fa fb mode)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
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
    ∀ vals cm, Clif.runLoop Clif.Rust.env p fuel cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnPinMode.Valid mode g vals' us ∧ us.length = outs.length ∧
        PrefixHold vals' outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
        (XNI F syms (g.externs.map (·.2)) (indSigs (T g)) c
          (CallLg Clif.Rust.env (g.externs.map (·.2)) (indSigs (T g))) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c cs'.frame.slots cs'.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip args' → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip args' → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) :=
  backend_correct_legal_pass_env_wide_semantic_return_pins hchk hT hS hsub hc Clif.Rust.helperOk_env
    Clif.Rust.extLegal_env Clif.Rust.envKeepsAllocs_env RustSyms.envKeepsSymbols_env hext hext' hind
    (fun _ _ _ h => by cases h)
    hcov hX hXI hsym hslot hexp hcs hcs' hsl hmem hrel hargs htrS htr fuel

end E2E
