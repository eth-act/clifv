import FV.Concurrency.IselResume
import FV.Concurrency.CallArity

/-!
# The call's arguments at layer 2 (#473, (2b))

At a call statement related by layer 2's `Match` to a VCode configuration at the call's direct
`call`, the VCode use values hold the CLIF argument values as the callee signature places them
(`ArgsAt`). The lowering proof shows this only inside the driver's statement step, through the
callee contract `XCallsOk`; here it is read off the step with a **guarded** external semantics
(`xcallG`): its `call` steps only when the uses and the world satisfy `ArgsAt` (`ArgG`). The
contract holds for it (the guard is one of the contract's premises), so the driver's step of
the call statement in the extern view (as `IselResume.isel_resumeC`) makes the VCode `call`
step under `xcallG`, hence the guard held.

* `xcallG`, `ArgG`; **`isel_resumeG`** (`isel_resumeC` under `xcallG`);
* `argG_of_vstep`: a VCode step of a direct `call` under `xcallG` satisfies the guard.
-/

namespace Concurrency.CallArgsL2

open Arm ArmThread ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread
  IselThread E2E IselCall IselCheck IselResume

open Classical in
/-- The external semantics whose `call` returns `outs` and the world `y` when `G` holds. -/
noncomputable def xcallG (X : ExtSem) (G : Option String → List CV → ArmState → Prop)
    (outs : List CV) (y : ArmState) : ExtSem :=
  { X with call := fun d u w0 => if G d u w0 then some (outs, y) else none }

/-- The guard: the uses are the arguments `vals` of `ext` as the callee contract passes them. -/
def ArgG (X : ExtSem) (ext : Clif.ExtFunc) (vals : List Clif.Val) :
    Option String → List CV → ArmState → Prop :=
  fun d u w0 => ∃ args, (d = some ext.name ∧ u = args ∨
      d = none ∧ ext.colocated = false ∧ u = ofX (X.sym ext.name 0) :: args) ∧
    ArgsAt ext.sig vals args w0

/-- **Layer 2 resuming after a call, under the guarded external semantics** (module doc). -/
theorem isel_resumeG {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {Γ : E2E.Rel} {fctx : FnCtx} {X : ExtSem} {c : BitVec 64}
    {slots : List (Clif.SlotId × Nat)}
    (hshape : LowerShape f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) (hchk : threadCheckBlC f bl = true)
    (hlow : lowerCheck f vc = true) (hind : indSigs f = []) (hv : verifiable f = true)
    (hnt : f.blocks.all (fun B => !B.term.isTry) = true)
    (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps)) (hout0 : vc.outgoing = 0)
    (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : ArmState}
    (hm : Match f ctx R gn bl A (RelW Γ f c) slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hc : stm.inst = .call fn args)
    {ext : Clif.ExtFunc} (hext : s.frame.func.extern? fn = some ext)
    (huniq : ∀ e ∈ f.externs, e.2.name = ext.name → e.2 = ext)
    {vals : List Clif.Val} (hvals : s.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params)
    {rvals : List Clif.Val} {cm' : Clif.Mem}
    (hrty : rvals.map (·.ty) = Clif.AbiParam.tys ext.sig.returns)
    {regs' : Clif.Regs} (hregs : s.frame.regs.setMany stm.results rvals = some regs')
    {outs : List CV} {y : ArmState} (hlen : outs.length = (sigRets ext.sig).length)
    (hpre : PrefixHold rvals outs) (hmr : RelW Γ f c slots cm' y) :
    ∃ ρ', VStep vc (csem Γ.F fctx (xcallG X (ArgG X ext vals) outs y))
        (.run ⟨b, k, ρ, w⟩) (.run ⟨b, k + 1, ρ', y⟩) ∧
      Match f ctx R gn bl A (RelW Γ f c) slots
        { s with frame := { s.frame with regs := regs', body := rest }, mem := cm' }
        ⟨b, k + 1, ρ', y⟩ := by
  -- the extern view
  let env' := envX Clif.Env.empty ext.name vals s.mem rvals cm'
  let XG := xcallG X (ArgG X ext vals) outs y
  have hX : XCallsOk env' (f.externs.map (·.2)) (pinSl (RelW Γ f c) slots) XG := by
    intro e0 hmem g sl cm w0 d uses args0 vals0 rvals0 cm0 hg hd hargs hmr0 hret _
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
    simp only [env', envX, externX] at hg
    split at hg
    · rename_i hn
      have he' := huniq e he hn
      rw [he'] at hd hargs ⊢
      cases hg
      simp only at hret
      split at hret
      · rename_i hvc
        obtain ⟨rfl, rfl⟩ := hvc
        cases hret
        obtain ⟨-, rfl⟩ := hmr0
        refine ⟨outs, y, ?_, hlen, hpre, hmr, rfl⟩
        have hG : ArgG X ext vals0 d uses w0 := ⟨args0, hd, hargs⟩
        simp only [XG, xcallG, hG, ite_true]
      · cases hret
    · cases hg
  have hsym' : ∀ n b, Γ.syms n = some b → XG.sym n 0 = BitVec.ofNat 64 b := hsym
  have H := driverHypT_mk (p := pNil) hshape hcert hbr hlow hind hv hnt hcfg hout0 hslot hsym'
    (mrStable_pin (mrStable_relW Γ f c) slots) (outArgsOk_pin (outArgsOk_relW Γ f c) slots)
    (memRelOk_pin (memRelOk_relW Γ f c) slots) hX
  -- the CLIF step of the call in the extern view
  have hs : Clif.step env' pNil s =
      .next { s with frame := { s.frame with regs := regs', body := rest }, mem := cm' } := by
    rw [step_stmt env' pNil s stm rest hbody (fun _ _ _ _ _ => rfl)
      (fun sig callee args h => by rw [hc] at h; cases h), hc]
    simp only [instOutcome, hext, hvals, Clif.Res.ofOption, Clif.checkTys, htys, beq_self_eq_true,
      Clif.Res.check, env', envX, externX, pNil, Clif.Program.func?, List.find?_nil, ite_true, hrty,
      and_self, Clif.Res.bind, bind, pure]
    simp [Clif.StepResult.ofRes, Clif.continueWith, hregs]
  obtain ⟨B, j, ρ', w', hB, hstm, hbd, hk, hstar, hsr, hM⟩ :=
    IselStep.stmt_matchNT H (match_pin.mpr hm) hbody
      (fun sig callee args h => by rw [hc] at h; cases h) (fun _ _ _ _ _ => rfl) hs
  -- the call's code is the one `call`
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨-, -, hsllen, -⟩ := hshape.blk b B L hB hL
  have hjlt : j < B.body.length := (List.getElem?_eq_some_iff.mp hstm).1
  obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
    ⟨L.sl[j]'(by omega), List.getElem?_eq_getElem _⟩
  have hok := callOk_ofC hchk hB hstm hL hsl hc
  simp only [callOkB, hc, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff] at hok
  obtain ⟨hms, hex⟩ := hok
  have hseg := seg_eq (R := R) hB hL hstm hsl
  rw [hex, List.append_nil] at hseg
  split at hms
  · rename_i nm us ds hem
    rw [hem] at hseg
    rw [hseg] at hstar hsr hM
    simp only [List.map_cons, List.map_nil, List.length_singleton] at hstar hsr hM
    -- the world after the call
    have hw' : w' = y := by
      simp only [seqRun, MInst.mapRegs, csem, XG, xcallG, Option.map_some] at hsr
      split at hsr
      · cases hsr
      · split at hsr
        · rename_i hG
          simp at hsr
          done
        · rename_i hsem
          split at hsem
          · simp at hsem
            obtain ⟨rfl, rfl, rfl⟩ := hsem
            split at hsr
            · simp [SeqEnd.succ] at hsr
              exact hsr.2.symm
            · cases hsr
          · simp at hsem
    subst hw'
    cases hstar with
    | step _ hv h0 =>
      cases h0
      exact ⟨ρ', hv, match_pin.mp hM⟩
  · cases hms

/-- **A VCode step of a direct `call` under `xcallG` satisfies the guard** at its uses and
world. -/
theorem argG_of_vstep {vc : VCode} {F : BitVec 64 → Prop} {fctx : FnCtx} {X : ExtSem}
    {G : Option String → List CV → ArmState → Prop} {outs : List CV} {y : ArmState}
    {b k : Nat} {ρ : Nat → CV} {w : ArmState} {c' : VConf CV ArmState}
    (h : VStep vc (csem F fctx (xcallG X G outs y)) (.run ⟨b, k, ρ, w⟩) c')
    {vb : VBlock} {nm : String} {us ds : List (Reg × Reg)} (hvb : vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.call ⟨.sym nm, us, ds⟩)) :
    ∃ ops, (MInst.call ⟨.sym nm, us, ds⟩).operands = .ok ops ∧ G (some nm) (vuses ops ρ) w := by
  cases h with
  | step hvb1 hi1 hops1 hsem _ _ =>
    rw [hvb] at hvb1; cases hvb1
    rw [hi] at hi1; cases hi1
    simp only [csem, xcallG] at hsem
    split at hsem
    · exact ⟨_, hops1, by assumption⟩
    · simp at hsem

/-- The CLIF results of every call statement are as many as its extern's returns. -/
def callResLenB (f : Clif.Function) : Bool :=
  f.blocks.all fun B => B.body.all fun stm => match stm.inst with
    | .call fn _ => match f.extern? fn with
      | some e => stm.results.length == e.sig.returns.length
      | none => true
    | _ => true

theorem callResLen_of {f : Clif.Function} (h : callResLenB f = true) {bi j : Nat}
    {B : Clif.Block} {stm : Clif.Stmt} (hB : f.blocks[bi]? = some B) (hstm : B.body[j]? = some stm)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hc : stm.inst = .call fn args)
    {ext : Clif.ExtFunc} (hext : f.extern? fn = some ext) :
    stm.results.length = ext.sig.returns.length := by
  unfold callResLenB at h
  rw [List.all_eq_true] at h
  have h1 := List.all_eq_true.mp (h B (List.mem_of_getElem? hB)) stm (List.mem_of_getElem? hstm)
  simp only [hc, hext, beq_iff_eq] at h1
  exact h1

theorem setMany_some : ∀ (r : Clif.Regs) (xs : List Clif.ValueId) (vs : List Clif.Val),
    xs.length = vs.length → ∃ r', r.setMany xs vs = some r'
  | r, [], [], _ => ⟨r, rfl⟩
  | r, _ :: xs, _ :: vs, h => setMany_some _ xs vs (by simpa using h)
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

/-- **The call's VCode use values hold the CLIF arguments** (module doc): at a call statement
matched by layer 2, the VCode configuration is at a direct `call` of the extern's name whose use
values are the CLIF argument values as `ArgsAt ext.sig` places them. -/
theorem isel_argsAt {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {Γ : E2E.Rel} {F : BitVec 64 → Prop} {fctx : FnCtx} {X : ExtSem} {c : BitVec 64}
    {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem F fctx X) (RelW Γ f c) env p)
    (hchk : threadCheckBlC f bl = true) (hres : callResLenB f = true)
    (hlow : lowerCheck f vc = true) (hind : indSigs f = []) (hv : verifiable f = true)
    (hnt : f.blocks.all (fun B => !B.term.isTry) = true) (hout0 : vc.outgoing = 0)
    (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    {s : Clif.State} {vs : VState CV ArmState}
    (hm : Match f ctx R gn bl A (RelW Γ f c) slots s vs)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hc : stm.inst = .call fn args)
    {ext : Clif.ExtFunc} (hext : s.frame.func.extern? fn = some ext)
    (huniq : ∀ e ∈ f.externs, e.2.name = ext.name → e.2 = ext)
    {vals : List Clif.Val} (hvals : s.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params) :
    ∃ vb us ds ops, vc.blocks[vs.b]? = some vb ∧
      vb.insts[vs.k]? = some (.call ⟨.sym ext.name, us, ds⟩) ∧
      (MInst.call ⟨.sym ext.name, us, ds⟩).operands = .ok ops ∧
      ArgsAt ext.sig vals (vuses ops vs.ρ) vs.w := by
  obtain ⟨vb, nm, us, ds, hvb, hi⟩ := match_atCall H hchk hm ⟨stm, rest, fn, args, hbody, hc⟩
  have hextf : f.extern? fn = some ext := by rw [← hm.2.1]; exact hext
  let rvals : List Clif.Val := ext.sig.returns.map fun q => ⟨q.ty, 0⟩
  let outs : List CV := (sigRets ext.sig).map fun _ => 0
  have hrty : rvals.map (·.ty) = Clif.AbiParam.tys ext.sig.returns := by
    simp [rvals, Clif.AbiParam.tys]
  have hrl : stm.results.length = rvals.length := by
    obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -, -, -⟩ := hm
    obtain ⟨-, hstm, -⟩ := drop_cons_split (hbd ▸ hbody)
    simp only [rvals, List.length_map]
    exact callResLen_of hres hB hstm hc hextf
  obtain ⟨regs', hregs⟩ := setMany_some s.frame.regs stm.results rvals hrl
  have hlen : outs.length = (sigRets ext.sig).length := by simp [outs]
  have hpre : PrefixHold rvals outs := by
    refine ⟨by simpa [rvals, outs] using CallArity.returns_le_sigRets ext.sig, ?_⟩
    intro j v x hv hx
    simp only [rvals, List.getElem?_map, Option.map_eq_some_iff] at hv
    simp only [outs, List.getElem?_map, Option.map_eq_some_iff] at hx
    obtain ⟨q, -, rfl⟩ := hv
    obtain ⟨-, -, rfl⟩ := hx
    simp [VHolds]
  obtain ⟨b, k, ρ, w⟩ := vs
  have hmr : RelW Γ f c slots s.mem w := hm.2.2.2.1
  obtain ⟨ρ', hstep, -⟩ := isel_resumeG (fctx := fctx) (X := X) H.shape H.cert H.brIdx hchk hlow
    hind hv hnt H.cfg hout0 hslot hsym hm hbody hc hext huniq hvals htys hrty hregs hlen hpre hmr
  obtain ⟨ops, hops, args0, hd, hargs⟩ := argG_of_vstep hstep hvb hi
  rcases hd with ⟨hn, hu⟩ | ⟨hn, -⟩
  · simp only [Option.some.injEq] at hn
    subst hn
    exact ⟨vb, us, ds, ops, hvb, hi, hops, hu ▸ hargs⟩
  · cases hn

end Concurrency.CallArgsL2
