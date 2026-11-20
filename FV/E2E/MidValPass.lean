import FV.E2E.SemanticReturnPinsPass
import FV.Opt.Proof.MidValCondProg

/-! # The per-function theorems through the mid-end validator (#1119, plumbing layer 1)

In a build whose Cranelift `opt_level` is not `none`, `lean-backend --midval-opt` compiles
Cranelift's optimised function `g` (cg_clif's `.opt.clif`) in place of cg_clif's **source**
function `f` (the `.unopt.clif`) when it decides the re-check of the mid-end validator's
certificate with its branch-condition hints, `Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints =
true` (#1128, #1139; `checkCertC … [] = checkCert …`). The theorems here
take that decided premise and the artifact of the **compiled** function (`g` through the usual
`i128` legalisation, constant-phi removal and backend) and conclude, with the conclusion text of the
theorem `lean-backend` names for `g` today, about the run of the program with the source function
`f`:

* `p` is a program with the source functions, `q` one whose functions are `p`'s or validated
  replacements (`Opt.MidVal.ValidatedC p.funcs q.funcs`: the same function, or a `g` with
  `checkCertC (ConstPhi.run f) g cert hints = true`); `midEntry g cs` is the entry state of `g` with the
  registers, slots and memory of `f`'s entry state `cs`.
* `midval_entry` (`Clif.runLoop`) and `midval_entryX` (`Clif.runLoopX`, with unwinding): the
  source run from `f`'s entry is refined by `q`'s run from `g`'s entry (`Opt.MidVal.checkedC_simMU`,
  `Opt.runLoopX_refinesSRMU`; the plain run through `Clif.runLoopX_toX`).
* The Stock path (`backend_correct_world_niX_semantic_return_pins` and its compositions with the
  `i128` legalisation and constant-phi removal, `FV/E2E/SemanticReturnPinsPass.lean`):
  `backend_correct_midval_semantic_return_pins`, `backend_correct_midval_pass_semantic_return_pins`,
  `backend_correct_midval_legal_wide_semantic_return_pins`,
  `backend_correct_midval_legal_pass_wide_semantic_return_pins`. The other paths:
  `FV/E2E/MidValPassLegacy.lean`.

Non-vacuity: `FVTest/Backend/MidValPassWitness.lean` (a real pair of the measured release crates,
every checkable premise decided). -/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The entry state of `g` with the registers, slots and memory of the entry state `cs`. -/
def midEntry (g : Clif.Function) (cs : Clif.State) : Clif.State :=
  match g.entry? with
  | some b => ⟨⟨g, cs.frame.regs, cs.frame.slots, b.body, b.term⟩, [], cs.mem⟩
  | none => cs

/-- An environment of `Clif.run` whose externs keep the symbols keeps them with unwinding (its
externs never unwind). -/
theorem envKeepsSymbolsX_toX {env : Clif.Env} (hE : Opt.EnvKeepsSymbols env) :
    Opt.EnvKeepsSymbolsX env.toX := by
  intro name g hg vals m
  simp only [Clif.Env.toX, Option.map_eq_some_iff] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  refine ⟨fun rvals m' h => ?_, fun e m' h =>
    absurd (show (g0 vals m).toX = .unwound e m' from h) (Clif.Outcome.toX_ne_unwound _ e m')⟩
  change (g0 vals m).toX = .returned rvals m' at h
  cases h0 : g0 vals m with
  | returned r mm =>
    rw [h0] at h
    cases h
    exact hE name g0 hg0 vals m _ _ h0
  | trapped c => rw [h0] at h; cases h
  | stuck msg => rw [h0] at h; cases h
  | outOfFuel => rw [h0] at h; cases h

/-- Refinement of the runs with unwinding of two plain outcomes is their refinement. -/
theorem outcomeRefines_of_toX {o o' : Clif.Outcome} (h : Opt.XOutcomeRefines o.toX o'.toX) :
    Opt.OutcomeRefines o o' := by
  refine ⟨fun vals m ho => ?_, fun c ho => ?_⟩
  · subst ho
    have h1 := h.1 vals m rfl
    cases o' <;> first | rfl | (cases h1; rfl) | cases h1
  · subst ho
    have h1 := h.2.1 c rfl
    cases o' <;> first | rfl | (cases h1; rfl) | cases h1

/-- The entry of `g` matching the entry of the source function `f`, and the related states. -/
theorem midval_sr {f g : Clif.Function} {cert : Opt.MidVal.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry f args cs) :
    ClifEntry g args (midEntry g cs) ∧
      (midEntry g cs).frame.slots = cs.frame.slots ∧ (midEntry g cs).mem = cs.mem ∧
      Opt.SRMU cs.mem.symbols cs.toX (midEntry g cs).toX := by
  have hsim := Opt.MidVal.checkedC_simMU hchk
  obtain ⟨b, hb, hbody, hterm, hty, hregs⟩ := hcs.entry
  obtain ⟨R, hR, hent⟩ := hsim.sim cs.mem.symbols
  obtain ⟨b', hb', hpar, hrel⟩ := hent b hb
  have hoe : midEntry g cs =
      ⟨⟨g, cs.frame.regs, cs.frame.slots, b'.body, b'.term⟩, [], cs.mem⟩ := by
    simp [midEntry, hb']
  have hcx : cs.toX = ⟨cs, []⟩ := by simp [Clif.State.toX, hcs.callers]
  rw [hoe, hcx]
  refine ⟨⟨rfl, rfl, by rw [hsim.sig]; exact hcs.sig, ⟨b', hb', rfl, rfl, by rw [hpar]; exact hty,
    by rw [hpar]; exact hregs⟩, by rw [hsim.slots]; exact hcs.slotIds⟩, rfl, rfl,
    rfl, rfl, Opt.GRMU.of hR ?_, ?_⟩
  · show R cs.frame ⟨g, cs.frame.regs, cs.frame.slots, b'.body, b'.term⟩ cs.mem
    rw [ClifEntry.frame_eq hcs hbody hterm]
    exact hrel args cs.frame.regs cs.frame.slots cs.mem hty.symm hregs hcs.slotIds rfl
  · show Opt.CallersRelMU _ _ cs.callers [] [] []
    rw [hcs.callers]; exact .nil _

/-- **The source run from `f`'s entry, refined by the run of the program with validated
functions from `g`'s entry** (`Clif.runLoop`). -/
theorem midval_entry {f g : Clif.Function} {cert : Opt.MidVal.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    {env : Clif.Env} (hE : Opt.EnvKeepsSymbols env) {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs) (fuel : Nat) :
    ClifEntry g args (midEntry g cs) ∧
      (midEntry g cs).frame.slots = cs.frame.slots ∧ (midEntry g cs).mem = cs.mem ∧
      ∃ n', Opt.OutcomeRefines (Clif.runLoop env p fuel cs)
        (Clif.runLoop env q n' (midEntry g cs)) := by
  obtain ⟨hcs', hsl, hmem, hSR⟩ := midval_sr hchk hcs
  obtain ⟨n', hn⟩ := Opt.runLoopX_refinesSRMU (envKeepsSymbolsX_toX hE) hv.funsSimMU fuel _ _ hSR
  rw [Clif.runLoopX_toX, Clif.runLoopX_toX] at hn
  exact ⟨hcs', hsl, hmem, n', outcomeRefines_of_toX hn⟩

/-- **`midval_entry` with unwinding** (`Clif.runLoopX`; returns, traps and exceptions leaving the
run are matched). -/
theorem midval_entryX {f g : Clif.Function} {cert : Opt.MidVal.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    {env : Clif.XEnv} (hE : Opt.EnvKeepsSymbolsX env) {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs) (fuel : Nat) :
    ClifEntry g args (midEntry g cs) ∧
      (midEntry g cs).frame.slots = cs.frame.slots ∧ (midEntry g cs).mem = cs.mem ∧
      ∃ n', Opt.XOutcomeRefines (Clif.runLoopX env p fuel cs.toX)
        (Clif.runLoopX env q n' (midEntry g cs).toX) := by
  obtain ⟨hcs', hsl, hmem, hSR⟩ := midval_sr hchk hcs
  exact ⟨hcs', hsl, hmem, Opt.runLoopX_refinesSRMU hE hv.funsSimMU fuel _ _ hSR⟩

/-! ## The Stock path -/

/-- **The Stock path's theorem through the mid-end validator**
(`backend_correct_world_niX_semantic_return_pins` for the compiled `g`): for cg_clif's source
function `f` and Cranelift's optimised function `g` with `checkCertC (ConstPhi.run f) g cert hints`
decided, `g` compiled with the Stock artifact, every return of the CLIF run of the *source*
program `p` from `f`'s entry state is matched by the Arm run of the compiled `g`, as in the Stock
theorem. Premises: the Stock theorem's about the compiled `g` in the program `q` of validated
functions (`ValidatedC p.funcs q.funcs`), externs keep the link-time symbols (`hE`), `q`'s run from
`g`'s entry traps only explicitly (`htr`). -/
theorem backend_correct_midval_semantic_return_pins {f g : Clif.Function} {cert : Opt.MidVal.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {mode : ReturnPinMode}
    (hsub : InSubset q g) (hc : CompiledSemanticReturnPins g k vc vcp rf af fa fb mode)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs g)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbols env)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env q (midEntry g cs)) (fuel : Nat) :
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
        (XNI F syms (f.externs.map (·.2)) (indSigs g) c
          (CallLg env (f.externs.map (·.2)) (indSigs g)) X → XTls F X →
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
  have hF := Opt.MidVal.checkedC_simMU hchk
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := midval_entry hchk hv hE hcs fuel
  have hW : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c =
      RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c := relW_slots hF.slots c
  have key := backend_correct_world_niX_semantic_return_pins (K := K) hsub hc hcov
    (by rw [hW, hF.externs]; exact hX) (by rw [hW]; exact hXI) hsym hslot hcs'
    (by rw [hW, hsl, hmem]; exact hrel) (by rw [hF.sig]; exact hargs) htr n' vals cm
    (hn.1 _ _ hrun)
  rw [ReturnPinMode.valid_sig hF.sig, hW, hF.externs, hF.sig, hsl, hmem] at key
  exact key

/-- **The Stock path's theorem through the mid-end validator and a pass**
(`backend_correct_pass_semantic_return_pins` at `g`; `lean-backend` names it at
`T := Opt.ConstPhi.run`): `T g` compiled with the Stock artifact. -/
theorem backend_correct_midval_pass_semantic_return_pins {T : Clif.Function → Clif.Function}
    (hT : ∀ f, Opt.FunSimX f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {f g : Clif.Function} {cert : Opt.MidVal.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {mode : ReturnPinMode}
    (hsub : InSubset q g) (hc : CompiledSemanticReturnPins (T g) k vc vcp rf af fa fb mode)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs (T g))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbols env)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env (passProg T q) (passEntry T g (midEntry g cs))) (fuel : Nat) :
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
        (XNI F syms (f.externs.map (·.2)) (indSigs (T g)) c
          (CallLg env (f.externs.map (·.2)) (indSigs (T g))) X → XTls F X →
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
  have hF := Opt.MidVal.checkedC_simMU hchk
  obtain ⟨hcs', hsl, hmem, n', hn⟩ := midval_entry hchk hv hE hcs fuel
  have hW : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g c =
      RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c := relW_slots hF.slots c
  have key := backend_correct_pass_semantic_return_pins (K := K) hT hS hsub hc hcov
    (by rw [hW, hF.externs]; exact hX) (by rw [hW]; exact hXI) hsym hslot hE hcs'
    (by rw [hW, hsl, hmem]; exact hrel) (by rw [hF.sig]; exact hargs) htr n' vals cm
    (hn.1 _ _ hrun)
  rw [ReturnPinMode.valid_sig hF.sig, hW, hF.externs, hF.sig, hsl, hmem] at key
  exact key

/-- **The Stock path's theorem through the mid-end validator for an `i128` function**
(`backend_correct_legal_wide_semantic_return_pins` at `g`, under `Clif.Rust.env`): `g` legalised to
`g'` (`Opt.Legal.checkW g g' certL`), `g'` compiled with the Stock artifact; every return of the run
of the *source* program `p` from `f`'s entry is a return of `g'`'s run in `p'` with the values
expanded by the ABI groups of `f`'s returns, matched by the Arm run of the compiled `g'`. -/
theorem backend_correct_midval_legal_wide_semantic_return_pins {f g g' : Clif.Function}
    {cert : Opt.MidVal.Cert} {certL : Opt.Legalize128.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q p' : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    (hchkL : Opt.Legal.checkW g g' certL = true)
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {mode : ReturnPinMode}
    (hsub : InSubset p' g') (hc : CompiledSemanticReturnPins g' k vc vcp rf af fa fb mode)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hext : ∀ fn e, g.extern? fn = some e → q.func? e.name = none)
    (hext' : ∀ fn e, g'.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite g sig) →
      p'.funcs.map (·.name) = q.funcs.map (·.name) ∧ q.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk Clif.Rust.env (g'.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g' c) X)
    (hXI : XCallsIndOk Clif.Rust.env (indSigs g')
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g' c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry g' args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g' c cs'.frame.slots cs'.mem w₀)
    (hargs : ArgsAtEntry F g'.sig args' w₀)
    (htrS : TrapsExplicit Clif.Rust.env q (midEntry g cs)) (htr : TrapsExplicit Clif.Rust.env p' cs')
    (fuel : Nat) :
    ∀ vals cm, Clif.runLoop Clif.Rust.env p fuel cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnPinMode.Valid mode g' vals' us ∧ us.length = outs.length ∧
        PrefixHold vals' outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
        (XNI F syms (g'.externs.map (·.2)) (indSigs g') c
          (CallLg Clif.Rust.env (g'.externs.map (·.2)) (indSigs g')) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g' c cs'.frame.slots cs'.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g'.sig).zip args' → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g'.sig).zip args' → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  intro vals cm hrun
  have hF := Opt.MidVal.checkedC_simMU hchk
  obtain ⟨hcs1, hsl1, hmem1, n', hn⟩ := midval_entry hchk hv RustSyms.envKeepsSymbols_env hcs fuel
  have key := backend_correct_legal_wide_semantic_return_pins (K := K) hchkL hsub hc hext hext' hind hcov hX
    hXI hsym hslot (by rw [hF.sig]; exact hexp) hcs1 hcs' (hsl.trans hsl1.symm)
    (hmem.trans hmem1.symm) hrel hargs htrS htr n' vals cm (hn.1 _ _ hrun)
  rw [hF.sig] at key
  exact key

/-- **The Stock path's theorem through the mid-end validator for an `i128` function, then a
pass** (`backend_correct_legal_pass_wide_semantic_return_pins` at `g`, under `Clif.Rust.env`;
`lean-backend` names it at `T := Opt.ConstPhi.run`): `g` legalised to `g'`, `T g'` compiled with
the Stock artifact. -/
theorem backend_correct_midval_legal_pass_wide_semantic_return_pins
    {T : Clif.Function → Clif.Function}
    (hT : ∀ f, Opt.FunSimX f (T f)) (hS : ∀ f, ShapeFacts f (T f))
    {f g g' : Clif.Function} {cert : Opt.MidVal.Cert} {certL : Opt.Legalize128.Cert}
    {hints : List (Clif.BlockId × List Opt.MidVal.Wrap)}
    (hchk : Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints = true)
    {p q p' : Clif.Program} (hv : Opt.MidVal.ValidatedC p.funcs q.funcs)
    (hchkL : Opt.Legal.checkW g g' certL = true)
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {mode : ReturnPinMode}
    (hsub : InSubset p' g') (hc : CompiledSemanticReturnPins (T g') k vc vcp rf af fa fb mode)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hext : ∀ fn e, g.extern? fn = some e → q.func? e.name = none)
    (hext' : ∀ fn e, g'.extern? fn = some e → p'.func? e.name = none)
    (hind : (∃ sig, Opt.Legal.IndSite g sig) →
      p'.funcs.map (·.name) = q.funcs.map (·.name) ∧ q.externNames <+: p'.externNames)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk Clif.Rust.env (g'.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g' c) X)
    (hXI : XCallsIndOk Clif.Rust.env (indSigs (T g'))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g' c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry g' args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g' c cs'.frame.slots cs'.mem w₀)
    (hargs : ArgsAtEntry F g'.sig args' w₀)
    (htrS : TrapsExplicit Clif.Rust.env q (midEntry g cs))
    (htr : TrapsExplicit Clif.Rust.env (passProg T p') (passEntry T g' cs')) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop Clif.Rust.env p fuel cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnPinMode.Valid mode g' vals' us ∧ us.length = outs.length ∧
        PrefixHold vals' outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
        (XNI F syms (g'.externs.map (·.2)) (indSigs (T g')) c
          (CallLg Clif.Rust.env (g'.externs.map (·.2)) (indSigs (T g'))) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g' c cs'.frame.slots cs'.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g'.sig).zip args' → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g'.sig).zip args' → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  intro vals cm hrun
  have hF := Opt.MidVal.checkedC_simMU hchk
  obtain ⟨hcs1, hsl1, hmem1, n', hn⟩ := midval_entry hchk hv RustSyms.envKeepsSymbols_env hcs fuel
  have key := backend_correct_legal_pass_wide_semantic_return_pins (K := K) hchkL hT hS hsub hc hext hext'
    hind hcov hX hXI hsym hslot (by rw [hF.sig]; exact hexp) hcs1 hcs' (hsl.trans hsl1.symm)
    (hmem.trans hmem1.symm) hrel hargs htrS htr n' vals cm (hn.1 _ _ hrun)
  rw [hF.sig] at key
  exact key

end E2E
