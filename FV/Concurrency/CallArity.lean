import FV.Concurrency.CallResumeAll
import FV.Concurrency.CallResumeChecks

/-!
# The arity part of `resume_all`'s `habi` as a check (#473, step (3))

`CallResumeAll.resume_all`'s `habi` asks, besides the def registers (`CallResumeChecks`), that
the paused call defines one register per declared return of the CLIF extern `ext` the call
statement names (an `sret` callee's struct pointer is not a call result, #587):
`info.defs.length = ext.sig.returns.length` (and `rvals.length ≤ info.defs.length`, which
follows from it and the CLIF return types). The VCode alone does not
know `ext`, so the check is per statement on the driver's lowering `bl`, in the style of
`IselCheck.callOkB`:

* `callArityB f stm sl`: a `call fn _` statement whose code is one `call` defines
  `ext.sig.returns.length` registers, `ext` being `f.extern? fn`;
* `callArityBl f bl` on every statement, `callArityC f` on the driver's lowering of `f`.

`match_atCallA` carries the statement's instruction through `IselCall.match_atCall`, and
`pmatch_call_fwd` through `prepare`; **`resume_allA`** is `resume_all` with `habi` replaced by the
two checks (`CallDefsRet` for the registers, `callArityBl` for the arity).
-/

namespace Concurrency.CallArity

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck ThreadRefine IselCall IselCallRet ArmAllocThread E2E SegShape
  CallResumeAll CallResumeChecks CallRetResume CallResumeL IselResume

/-- **The arity check on one statement** (module doc). -/
def callArityB (f : Clif.Function) (stm : Clif.Stmt) (sl : SLow) : Bool :=
  match stm.inst with
  | .call fn _ =>
    match sl.st'.emitted.toList with
    | [.call ⟨_, _, ds⟩] =>
      match f.extern? fn with
      | some ext => ds.length == ext.sig.returns.length
      | none => false
    | _ => true
  | _ => true

/-- The arity check on the driver's lowering `bl`. -/
def callArityBl (f : Clif.Function) (bl : List BLow) : Bool :=
  (f.blocks.zip bl).all fun (B, L) => (B.body.zip L.sl).all fun (stm, sl) => callArityB f stm sl

/-- The arity check on the driver's lowering of `f`. -/
def callArityC (f : Clif.Function) : Bool :=
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => false
    | some bl => callArityBl f bl

theorem callArityBl_of_C {f : Clif.Function} (h : callArityC f = true) {ctx : Ctx}
    {ranges : _} {st0 : LState} (hb : buildCtx f = .ok (ctx, ranges, st0))
    {bl : List BLow}
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl) : callArityBl f bl = true := by
  unfold callArityC at h
  rw [hb] at h
  simp only at h
  rw [hl] at h
  exact h

theorem callArity_of {f : Clif.Function} {bl : List BLow} (h : callArityBl f bl = true)
    {bi j : Nat} {B : Clif.Block} {stm : Clif.Stmt} (hB : f.blocks[bi]? = some B)
    (hstm : B.body[j]? = some stm) {L : BLow} (hL : bl[bi]? = some L) {sl : SLow}
    (hsl : L.sl[j]? = some sl) : callArityB f stm sl = true :=
  all_zip_getElem (all_zip_getElem h hB hL) hstm hsl

/-- A signature's CLIF returns are at most its ABI returns. -/
theorem returns_le_sigRets (s : Clif.Signature) : s.returns.length ≤ (sigRets s).length := by
  unfold sigRets
  split
  · split
    · rename_i h; simp [List.isEmpty_iff.mp h]
    · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- **`match_atCall` with the arity**: the matched call statement's direct `call` defines one
register per ABI return of its extern. -/
theorem match_atCallA {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
    {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (har : callArityBl f bl = true) {s : Clif.State}
    {vs : VState CV ArmState} (hm : Match f ctx R gn bl A MR slots s vs) {stm : Clif.Stmt}
    {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest) {fn : Clif.FnRef}
    {args : List Clif.ValueId} (hcl : stm.inst = .call fn args) {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) :
    ∃ vb n us ds, vc.blocks[vs.b]? = some vb ∧
      vb.insts[vs.k]? = some (.call ⟨.sym n, us, ds⟩) ∧ ds.length = ext.sig.returns.length := by
  obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, hk, -, -⟩ := hm
  obtain ⟨hjlt, hstm, -⟩ := drop_cons_split (hbd ▸ hbody)
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, hsllen, -, -, -, -, -, hcode, htne, -⟩ := H.shape.blk vs.b B L hB hL
  obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
    ⟨L.sl[j]'(by omega), List.getElem?_eq_getElem _⟩
  have hok := callOk_ofC hchk hB hstm hL hsl hcl
  have har1 := callArity_of har hB hstm hL hsl
  simp only [callOkB, hcl, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff] at hok
  obtain ⟨hms, hex⟩ := hok
  have hseg := seg_eq (R := R) hB hL hstm hsl
  rw [hex, List.append_nil] at hseg
  split at hms
  · rename_i n us ds hem
    simp only [callArityB, hcl, hem, hext, beq_iff_eq] at har1
    rw [hem] at hseg
    have h0 := (seg_at hcode htne hjlt).1 0 (by rw [hseg]; simp)
    have h1 : ∀ (h : 0 < (seg f R bl vs.b j).length), (seg f R bl vs.b j)[0] =
        .call ⟨.sym n, us.map fun (v, p) => (R v, p), ds.map fun (p, v) => (p, R v)⟩ := by
      rw [hseg]; intro _; rfl
    rw [Nat.add_zero, ← hk, h1] at h0
    exact ⟨vb, n, _, _, hvb, h0, by rw [List.length_map, har1]⟩
  · cases hms

/-- **`resume_allX` with `habi` from checks** (module doc): the def registers by
`CallDefsRet` for the callee's return registers, the arity by `callArityBl`; the return's ABI
facts of `resume_allX`. -/
theorem resume_allAX {RA : RL} (hRA : RA.Wf) (hgv : RA.gv = fun _ _ => False)
    (hX0 : NoCall RA.X) {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {Γ : E2E.Rel} {c : BitVec 64} {env : Clif.Env} {p : Clif.Program}
    {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) (RelW Γ f c) env p)
    (hchk : threadCheckBlC f bl = true) (har : callArityBl f bl = true)
    (hlow : lowerCheck f vc = true) (hind : indSigs f = [])
    (hv : verifiable f = true) (hnt : f.blocks.all (fun B => !B.term.isTry) = true)
    (hout0 : vc.outgoing = 0) (hΓF : Γ.F = RA.F) (hslot : RA.ctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → RA.X.sym n 0 = BitVec.ofNat 64 b)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV}
    (hvdef : CallDefsVirt RA.vc)
    {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState}
    (hq : Q RA x (.run cM')) (hA : AInv RA (.run cM')) (hP : Pause RA (.run cM'))
    (hat : AtCallS s') (hm2 : Match f ctx R gn bl A (RelW Γ f c) slots s' vV')
    (hm3 : PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP'))
    (hm4 : MatchRun cc ins ckeep r₀ cM' vP') {y : ArmState}
    (hpc : Arm.r .PC y = Arm.r .PC x + 4#64) (herr : Arm.r .ERR y = .None)
    (hsp : spOf y = spOf x) (hmem : ∀ a, RA.FK a → y.mem a = x.mem a)
    (hcs : ∀ r ∈ calleeSaved, ckeep r (regVal y r) = ckeep r (regVal x r))
    (hprog : y.program = x.program) (hfp : xreg 29 y = xreg 29 x)
    {usB : List (Reg × Reg)} {ysB : List CV} {rvals : List Clif.Val}
    (hus : ∀ (j : Nat) (v q : Reg) (u : CV), usB[j]? = some (v, q) → ysB[j]? = some u →
      regVal y q = u)
    (hpreB : PrefixHold rvals ysB) (hdr : CallDefsRet RA.vc (usB.map (·.2)))
    {FB : BitVec 64 → Prop} {cmB : Clif.Mem} {wB : ArmState} {bases : List Nat}
    (hB : MemRel FB Γ.syms cmB wB)
    (hval : ∀ a n, ((cmB.free bases).leave).valid a n = true → s'.mem.valid a n = true)
    (hmemB : ∀ a, ¬ FB a → y.mem a = wB.mem a)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s'.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hcl : stm.inst = .call fn args)
    {ext : Clif.ExtFunc} (hext : s'.frame.func.extern? fn = some ext)
    (huniq : ∀ e ∈ f.externs, e.2.name = ext.name → e.2 = ext)
    {vals : List Clif.Val} (hvals : s'.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params)
    (hrty : rvals.map (·.ty) = Clif.AbiParam.tys ext.sig.returns)
    {regs' : Clif.Regs} (hregs : s'.frame.regs.setMany stm.results rvals = some regs') :
    ∃ vV'' vP'' cM'',
      Match f ctx R gn bl A (RelW Γ f c) slots { s' with
          frame := { s'.frame with regs := regs', body := rest }, mem := (cmB.free bases).leave }
        vV'' ∧
      PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV'') (.run vP'') ∧
      MatchRun cc ins ckeep r₀ cM'' vP'' ∧ Q RA y (.run cM'') ∧ AInv RA (.run cM'') := by
  have hextf : f.extern? fn = some ext := by rw [← hm2.2.1]; exact hext
  have hrl : rvals.length = ext.sig.returns.length := by
    have := congrArg List.length hrty
    simpa [Clif.AbiParam.tys] using this
  have habi : ∀ (vb : VBlock) (info : CallInfo),
      RA.vc.blocks[vP'.b]? = some vb → vb.insts[vP'.k]? = some (.call info) →
      (∀ (j : Nat) (d : Reg × Reg), info.defs[j]? = some d → ∃ v, usB[j]? = some (v, d.1)) ∧
      rvals.length ≤ info.defs.length ∧ info.defs.length = ext.sig.returns.length := by
    intro vb info hvb hi
    obtain ⟨b0, k0, ρ0, w0⟩ := vV'
    obtain ⟨vb0, n, us, ds, hvb0, hi0, hlen⟩ :=
      match_atCallA H hchk har hm2 hbody hcl hextf
    obtain ⟨b', vb', e, hvb', hi', -, -⟩ := pmatch_call_fwd H3 hX0 hm3 hvb0 hi0
    cases e
    simp only at hvb hi
    rw [hvb'] at hvb; cases hvb
    rw [hi'] at hi; cases hi
    refine ⟨habi_regs hdr hvb' hi', ?_, hlen⟩
    simp only at hlen ⊢
    omega
  exact resume_allX hRA hgv hX0 H hchk hlow hind hv hnt hout0 hΓF hslot hsym H3 hc hvdef hq
    hA hP hat hm2 hm3 hm4 hpc herr hsp hmem hcs hprog hfp hus hpreB hB hval hmemB hbody hcl hext
    huniq hvals htys hrty hregs habi

/-- **`resume_all` with `habi` from checks** (module doc): the def registers by
`CallDefsRet` for the callee's `rets` registers, the arity by `callArityBl`. -/
theorem resume_allA {RA RB : RL} (hRA : RA.Wf) (hRB : RB.Wf) (hgv : RA.gv = fun _ _ => False)
    (hX0 : NoCall RA.X) {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {Γ : E2E.Rel} {c : BitVec 64} {env : Clif.Env} {p : Clif.Program}
    {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) (RelW Γ f c) env p)
    (hchk : threadCheckBlC f bl = true) (har : callArityBl f bl = true)
    (hlow : lowerCheck f vc = true) (hind : indSigs f = [])
    (hv : verifiable f = true) (hnt : f.blocks.all (fun B => !B.term.isTry) = true)
    (hout0 : vc.outgoing = 0) (hΓF : Γ.F = RA.F) (hslot : RA.ctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → RA.X.sym n 0 = BitVec.ofNat 64 b)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV}
    (hvdef : CallDefsVirt RA.vc)
    {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState}
    (hq : Q RA x (.run cM')) (hA : AInv RA (.run cM')) (hP : Pause RA (.run cM'))
    (hat : AtCallS s') (hm2 : Match f ctx R gn bl A (RelW Γ f c) slots s' vV')
    (hm3 : PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP'))
    (hm4 : MatchRun cc ins ckeep r₀ cM' vP')
    {ra : BitVec 64} (hent : AbiCall RB.fb RB.base ra RB.s0) {r₀B : Reg → CV} {y : ArmState}
    (hy : RetC RB ra r₀B y)
    (hfx : ∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f RB.s0 = Arm.r f x)
    (hlr : xreg 30 RB.s0 = Arm.r .PC x + 4#64)
    (hm0 : ∀ a, RA.FK a → RB.s0.mem a = x.mem a) (hG : ∀ a, RA.FK a → RB.G a)
    (hr₀B : ∀ r ∈ calleeSaved, ckeep r (r₀B r) =
      ckeep r (locVal RB.fr (iterN RB.step (prologueLines RB.af.saves RB.af.frameSize).length RB.s0) (.reg r)))
    (hprog : y.program = x.program)
    {usB : List (Reg × Reg)} {ysB : List CV} {rvals : List Clif.Val}
    (hus : ∀ (j : Nat) (v q : Reg) (u : CV), usB[j]? = some (v, q) → ysB[j]? = some u →
      regVal y q = u)
    (hpreB : PrefixHold rvals ysB) (hdr : CallDefsRet RA.vc (usB.map (·.2)))
    {FB : BitVec 64 → Prop} {cmB : Clif.Mem} {wB : ArmState} {bases : List Nat}
    (hB : MemRel FB Γ.syms cmB wB)
    (hval : ∀ a n, ((cmB.free bases).leave).valid a n = true → s'.mem.valid a n = true)
    (hmemB : ∀ a, ¬ FB a → y.mem a = wB.mem a)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s'.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hcl : stm.inst = .call fn args)
    {ext : Clif.ExtFunc} (hext : s'.frame.func.extern? fn = some ext)
    (huniq : ∀ e ∈ f.externs, e.2.name = ext.name → e.2 = ext)
    {vals : List Clif.Val} (hvals : s'.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params)
    (hrty : rvals.map (·.ty) = Clif.AbiParam.tys ext.sig.returns)
    {regs' : Clif.Regs} (hregs : s'.frame.regs.setMany stm.results rvals = some regs') :
    ∃ vV'' vP'' cM'',
      Match f ctx R gn bl A (RelW Γ f c) slots { s' with
          frame := { s'.frame with regs := regs', body := rest }, mem := (cmB.free bases).leave }
        vV'' ∧
      PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV'') (.run vP'') ∧
      MatchRun cc ins ckeep r₀ cM'' vP'' ∧ Q RA y (.run cM'') ∧ AInv RA (.run cM'') := by
  obtain ⟨hpc, herr, hsp, hmem, hx29, hcs⟩ := hy
  obtain ⟨he, hsp0, hra⟩ := ArmAllocThread.entry_premises hRB hent hfx hlr
  exact resume_allAX hRA hgv hX0 H hchk har hlow hind hv hnt hout0 hΓF hslot hsym H3 hc hvdef hq
    hA hP hat hm2 hm3 hm4 (hpc.trans hra) herr (hsp.trans hsp0)
    (fun a ha => (hmem a (hG a ha)).trans (hm0 a ha))
    (fun r hr => (hcs r hr).trans ((hr₀B r hr).trans (he r hr))) hprog
    (hx29.trans (hfx (.GPR 29#5) (by simp) (by simp))) hus hpreB hdr hB hval
    hmemB hbody hcl hext huniq hvals htys hrty hregs

end Concurrency.CallArity
