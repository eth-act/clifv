import FV.Concurrency.CallArgsL2
import FV.Concurrency.CallArgsAt
import FV.Concurrency.LinkedMachine

/-!
# The callee's `ArgsAtEntry` at a direct call (#473, (2b))

At a direct call the callee's driver theorem asks `ArgsAtEntry F sig vals w₀` of its body-entry
world. Layer 2 gives `ArgsAt ext.sig vals` of the VCode use values (`CallArgsL2.isel_argsAt`),
layers 3–4b the `j`-th use value in the `j`-th use register (`CallArgsAt.call_uses_q`). What joins
them is a per-statement check, in the style of `CallArity.callArityB`:

* `allRegs? locs`: the registers of the argument locations `locs` when all are registers;
* `callUseRegsB f stm sl`: a `call fn _` statement whose code is one `call` passes its arguments
  in registers only, its use registers being `locsOf ext.sig`'s registers in order, all argument
  registers (x0–x8, v0–v7); `callUseRegsBl`, `callUseRegsC` on the driver's lowering;
* `match_atCallU`: `match_atCall` with that check;
* `argsHold_of_uses`: `ArgsAt` of the use values and the use values in the use registers give
  every register-passed argument in its register;
* **`callee_args`**: at the call end of a caller's segment (the three relations and `Q` at the
  paused call), every argument is in its `locsOf ext.sig` register of the machine state, all in
  registers, all argument registers;
* **`callee_argsAtEntry`**: then `ArgsAtEntry F ext.sig vals` holds of the callee's body-entry
  world `bodyOf FB.af (Link.enter FB x)` after the `bl` (`Link.step_call`, `Link.enter_call`), for
  any frame `F`; `callee_argsAtEntry_sig` for a callee whose signature is `ext.sig`.
-/

namespace Concurrency.CallArgsEntry

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck ThreadRefine IselCall IselCallRet ArmAllocThread E2E SegShape
  CallResumeAll CallResumeChecks CallRetResume CallResumeL IselResume CallArity CallArgsAt
  CallArgsL2 LinkedMachine

/-- The registers of argument locations, when all of them are registers. -/
def allRegs? : List ArgLoc → Option (List Reg)
  | [] => some []
  | .reg r :: ls => (allRegs? ls).map (r :: ·)
  | .stack _ :: _ => none

theorem allRegs?_eq : ∀ {locs : List ArgLoc} {rs : List Reg}, allRegs? locs = some rs →
    locs = rs.map ArgLoc.reg
  | [], rs, h => by simp only [allRegs?, Option.some.injEq] at h; subst h; rfl
  | .reg r :: ls, rs, h => by
    simp only [allRegs?, Option.map_eq_some_iff] at h
    obtain ⟨rs', h', rfl⟩ := h
    rw [allRegs?_eq h']
    rfl
  | .stack _ :: _, _, h => by simp [allRegs?] at h

/-- **The use-register check on one statement** (module doc). -/
def callUseRegsB (f : Clif.Function) (stm : Clif.Stmt) (sl : SLow) : Bool :=
  match stm.inst with
  | .call fn _ =>
    match sl.st'.emitted.toList with
    | [.call ⟨_, us, _⟩] =>
      match f.extern? fn with
      | some ext => allRegs? (locsOf ext.sig) == some (us.map (·.2)) && us.all (·.2.isArgReg)
      | none => false
    | _ => true
  | _ => true

/-- The use-register check on the driver's lowering `bl`. -/
def callUseRegsBl (f : Clif.Function) (bl : List BLow) : Bool :=
  (f.blocks.zip bl).all fun (B, L) => (B.body.zip L.sl).all fun (stm, sl) => callUseRegsB f stm sl

/-- The use-register check on the driver's lowering of `f`. -/
def callUseRegsC (f : Clif.Function) : Bool :=
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => false
    | some bl => callUseRegsBl f bl

theorem callUseRegsBl_of_C {f : Clif.Function} (h : callUseRegsC f = true) {ctx : Ctx}
    {ranges : _} {st0 : LState} (hb : buildCtx f = .ok (ctx, ranges, st0))
    {bl : List BLow}
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl) : callUseRegsBl f bl = true := by
  unfold callUseRegsC at h
  rw [hb] at h
  simp only at h
  rw [hl] at h
  exact h

theorem callUseRegs_of {f : Clif.Function} {bl : List BLow} (h : callUseRegsBl f bl = true)
    {bi j : Nat} {B : Clif.Block} {stm : Clif.Stmt} (hB : f.blocks[bi]? = some B)
    (hstm : B.body[j]? = some stm) {L : BLow} (hL : bl[bi]? = some L) {sl : SLow}
    (hsl : L.sl[j]? = some sl) : callUseRegsB f stm sl = true :=
  all_zip_getElem (all_zip_getElem h hB hL) hstm hsl

/-- **`match_atCall` with the use registers**: the matched call statement's direct `call` uses
`locsOf ext.sig`'s registers, in order, all argument registers. -/
theorem match_atCallU {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
    {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBlC f bl = true) (hcu : callUseRegsBl f bl = true) {s : Clif.State}
    {vs : VState CV ArmState} (hm : Match f ctx R gn bl A MR slots s vs) {stm : Clif.Stmt}
    {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest) {fn : Clif.FnRef}
    {args : List Clif.ValueId} (hcl : stm.inst = .call fn args) {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) :
    ∃ vb n us ds, vc.blocks[vs.b]? = some vb ∧
      vb.insts[vs.k]? = some (.call ⟨.sym n, us, ds⟩) ∧
      allRegs? (locsOf ext.sig) = some (us.map (·.2)) ∧ ∀ u ∈ us, u.2.isArgReg = true := by
  obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, hk, -, -⟩ := hm
  obtain ⟨hjlt, hstm, -⟩ := drop_cons_split (hbd ▸ hbody)
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, hsllen, -, -, -, -, -, hcode, htne, -⟩ := H.shape.blk vs.b B L hB hL
  obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
    ⟨L.sl[j]'(by omega), List.getElem?_eq_getElem _⟩
  have hok := callOk_ofC hchk hB hstm hL hsl hcl
  have hcu1 := callUseRegs_of hcu hB hstm hL hsl
  simp only [callOkB, hcl, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff] at hok
  obtain ⟨hms, hex⟩ := hok
  have hseg := seg_eq (R := R) hB hL hstm hsl
  rw [hex, List.append_nil] at hseg
  split at hms
  · rename_i n us ds hem
    simp only [callUseRegsB, hcl, hem, hext, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
      at hcu1
    rw [hem] at hseg
    have h0 := (seg_at hcode htne hjlt).1 0 (by rw [hseg]; simp)
    have h1 : ∀ (h : 0 < (seg f R bl vs.b j).length), (seg f R bl vs.b j)[0] =
        .call ⟨.sym n, us.map fun (v, p) => (R v, p), ds.map fun (p, v) => (p, R v)⟩ := by
      rw [hseg]; intro _; rfl
    rw [Nat.add_zero, ← hk, h1] at h0
    refine ⟨vb, n, _, _, hvb, h0, ?_, ?_⟩
    · rw [hcu1.1, List.map_map]; rfl
    · intro u hu
      obtain ⟨u0, hu0, rfl⟩ := List.mem_map.mp hu
      exact hcu1.2 u0 hu0
  · cases hms

/-- The register-passed arguments of all-register locations, index by index. -/
theorem regArgs_get : ∀ (rs : List Reg) (vals : List Clif.Val) (j : Nat) (r : Reg)
    (v : Clif.Val), ((rs.map ArgLoc.reg).zip vals)[j]? = some (.reg r, v) →
    (((rs.map ArgLoc.reg).zip vals).filterMap fun q => match q.1 with
      | .reg _ => some q.2
      | .stack _ => none)[j]? = some v ∧ rs[j]? = some r
  | [], _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | r0 :: rs, v0 :: vals, 0, r, v, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq, ArgLoc.reg.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | r0 :: rs, v0 :: vals, j + 1, r, v, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.getElem?_cons_succ] at h
    simpa using regArgs_get rs vals j r v h

/-- **The register-passed arguments in their registers** (module doc): from `ArgsAt` of the use
values `xs` and the `j`-th use value in the `j`-th use register, with the use registers the
argument locations' registers. -/
theorem argsHold_of_uses {sig : Clif.Signature} {vals : List Clif.Val} {xs : List CV}
    {w : ArmState} (hA : ArgsAt sig vals xs w) {us : List (Reg × Reg)}
    (hlocs : allRegs? (locsOf sig) = some (us.map (·.2))) {s : ArmState}
    (hu : ∀ (j : Nat) (v p : Reg) (x : CV), us[j]? = some (v, p) → xs[j]? = some x →
      regVal s p = x) :
    ∀ (r : Reg) (v : Clif.Val), (ArgLoc.reg r, v) ∈ (locsOf sig).zip vals →
      VHolds v (regVal s r) := by
  intro r v hmem
  have hl := allRegs?_eq hlocs
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  rw [hl] at hj
  obtain ⟨hv, hr⟩ := regArgs_get _ vals j r v hj
  obtain ⟨-, ⟨hlen, hall⟩, -⟩ := hA
  have hv' : (regArgVals sig vals)[j]? = some v := by
    unfold regArgVals; rw [hl]; exact hv
  have hjx : j < xs.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hv').1
  have hx := List.getElem?_eq_getElem hjx
  rw [List.getElem?_map, Option.map_eq_some_iff] at hr
  obtain ⟨⟨v0, p⟩, hup, rfl⟩ := hr
  rw [hu j v0 p _ hup hx]
  exact hall j v _ hv' hx

/-- **The callee's arguments at the `bl`** (module doc): at the call end of the caller's segment,
every argument of the call is in its `locsOf ext.sig` register of the machine state `x`; there are
no stack-passed arguments and the argument locations are argument registers. -/
theorem callee_args {RA : RL} (hX0 : NoCall RA.X) {f : Clif.Function} {vc : VCode} {ctx : Ctx}
    {st0 : LState} {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow}
    {A : Nat → Nat → List Clif.ValueId} {Γ : E2E.Rel} {c : BitVec 64} {env : Clif.Env}
    {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) (RelW Γ f c) env p)
    (hchk : threadCheckBlC f bl = true) (hres : callResLenB f = true)
    (hcu : callUseRegsBl f bl = true)
    (hlow : lowerCheck f vc = true) (hind : indSigs f = []) (hv : verifiable f = true)
    (hnt : f.blocks.all (fun B => !B.term.isTry) = true) (hout0 : vc.outgoing = 0)
    (hslot : RA.ctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → RA.X.sym n 0 = BitVec.ofNat 64 b)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV}
    (huv : CallUsesVirt RA.vc) (hdv : CallDefsVirt RA.vc)
    {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState}
    (hq : Q RA x (.run cM')) (hP : Pause RA (.run cM'))
    (hm2 : Match f ctx R gn bl A (RelW Γ f c) slots s' vV')
    (hm3 : PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP'))
    (hm4 : MatchRun cc ins ckeep r₀ cM' vP')
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s'.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hcl : stm.inst = .call fn args)
    {ext : Clif.ExtFunc} (hext : s'.frame.func.extern? fn = some ext)
    (huniq : ∀ e ∈ f.externs, e.2.name = ext.name → e.2 = ext)
    {vals : List Clif.Val} (hvals : s'.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params) :
    (∀ (r : Reg) (v : Clif.Val), (ArgLoc.reg r, v) ∈ (locsOf ext.sig).zip vals →
      VHolds v (regVal x r)) ∧ (∀ off, ArgLoc.stack off ∉ locsOf ext.sig) ∧
    ∀ r, ArgLoc.reg r ∈ locsOf ext.sig → r.isArgReg = true := by
  have hextf : f.extern? fn = some ext := by rw [← hm2.2.1]; exact hext
  obtain ⟨vb, us, ds, ops, hvb, hi, hops, hA⟩ := isel_argsAt H hchk hres hlow hind hv hnt hout0
    hslot hsym hm2 hbody hcl hext huniq hvals htys
  obtain ⟨vbU, nU, usU, dsU, hvbU, hiU, hlocs, harg⟩ := match_atCallU H hchk hcu hm2 hbody hcl hextf
  rw [hvb] at hvbU; cases hvbU
  rw [hi] at hiU; cases hiU
  have hl := allRegs?_eq hlocs
  obtain ⟨b0, k0, ρ0, w0⟩ := vV'
  obtain ⟨b', vb', e, hvb', hi', -, -⟩ := pmatch_call_fwd H3 hX0 hm3 hvb hi
  cases e
  obtain ⟨b2, k2, allocs, its, m, w2, vb2, info2, rfl, e2, -, -, -⟩ :=
    atCall_of_pause hX0 H hchk H3 hc hP ⟨stm, rest, fn, args, hbody, hcl⟩ hm2 hm3 hm4
  simp only [VState.mk.injEq] at e2
  obtain ⟨rfl, rfl, -, rfl⟩ := e2
  have hu := call_uses_q hq hc hm4 hvb' hi' (huv _ _ _ _ hvb' hi') (hdv _ _ _ _ hvb' hi') hops
  refine ⟨argsHold_of_uses hA hlocs hu, ?_, ?_⟩
  · intro off hm
    rw [hl] at hm
    simp at hm
  · intro r hm
    rw [hl] at hm
    obtain ⟨r', hr', e⟩ := List.mem_map.mp hm
    cases e
    obtain ⟨u, hu', rfl⟩ := List.mem_map.mp hr'
    exact harg u hu'

/-- An argument register is unchanged by the `bl` and the prologue: it is in the callee's
body-entry world `bodyOf FB.af (Link.enter FB x)` what it is in `x`. -/
theorem regVal_bodyOf_enter (FB : LFn) (x : ArmState) {r : Reg} (hr : r.isArgReg = true) :
    regVal (bodyOf FB.af (Link.enter FB x)) r = regVal x r := by
  cases r with
  | x n =>
    simp only [Reg.isArgReg, decide_eq_true_eq] at hr
    have hne : ∀ m, 8 < m → m < 32 → StateField.GPR (rnum n) ≠ .GPR (BitVec.ofNat 5 m) := by
      intro m h1 h2 e
      have := congrArg (fun f => match f with | StateField.GPR j => j.toNat | _ => 0) e
      simp [rnum] at this; omega
    simp only [regVal]
    rw [r_bodyOf _ _ (hne 29 (by omega) (by omega)) (hne 31 (by omega) (by omega)),
      Link.r_enter (by simp) (hne 30 (by omega) (by omega))]
  | v n =>
    simp only [regVal]
    rw [r_bodyOf _ _ (by simp) (by simp), Link.r_enter (by simp) (by simp)]
  | _ => simp [Reg.isArgReg] at hr

/-- **The callee's `ArgsAtEntry` after the `bl`** (module doc): the call's arguments as the
callee's entry code reads them in its body-entry world, for any frame `F`. -/
theorem callee_argsAtEntry {RA : RL} (hX0 : NoCall RA.X) {f : Clif.Function} {vc : VCode}
    {ctx : Ctx} {st0 : LState} {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow}
    {A : Nat → Nat → List Clif.ValueId} {Γ : E2E.Rel} {c : BitVec 64} {env : Clif.Env}
    {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) (RelW Γ f c) env p)
    (hchk : threadCheckBlC f bl = true) (hres : callResLenB f = true)
    (hcu : callUseRegsBl f bl = true)
    (hlow : lowerCheck f vc = true) (hind : indSigs f = []) (hv : verifiable f = true)
    (hnt : f.blocks.all (fun B => !B.term.isTry) = true) (hout0 : vc.outgoing = 0)
    (hslot : RA.ctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → RA.X.sym n 0 = BitVec.ofNat 64 b)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV}
    (huv : CallUsesVirt RA.vc) (hdv : CallDefsVirt RA.vc)
    {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState}
    (hq : Q RA x (.run cM')) (hP : Pause RA (.run cM'))
    (hm2 : Match f ctx R gn bl A (RelW Γ f c) slots s' vV')
    (hm3 : PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP'))
    (hm4 : MatchRun cc ins ckeep r₀ cM' vP')
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s'.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hcl : stm.inst = .call fn args)
    {ext : Clif.ExtFunc} (hext : s'.frame.func.extern? fn = some ext)
    (huniq : ∀ e ∈ f.externs, e.2.name = ext.name → e.2 = ext)
    {vals : List Clif.Val} (hvals : s'.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params)
    (FB : LFn) (F : BitVec 64 → Prop) :
    ArgsAtEntry F ext.sig vals (bodyOf FB.af (Link.enter FB x)) := by
  obtain ⟨hreg, hstk, harg⟩ := callee_args hX0 H hchk hres hcu hlow hind hv hnt hout0 hslot hsym
    H3 hc huv hdv hq hP hm2 hm3 hm4 hbody hcl hext huniq hvals htys
  intro loc v hm
  cases loc with
  | reg r =>
    show VHolds v (regVal _ r)
    rw [regVal_bodyOf_enter FB x (harg r (List.of_mem_zip hm).1)]
    exact hreg r v hm
  | stack off => exact absurd (List.of_mem_zip hm).1 (hstk off)

/-- `callee_argsAtEntry` for a callee `fB` whose signature is the extern's. -/
theorem callee_argsAtEntry_sig {RA : RL} (hX0 : NoCall RA.X) {f : Clif.Function} {vc : VCode}
    {ctx : Ctx} {st0 : LState} {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow}
    {A : Nat → Nat → List Clif.ValueId} {Γ : E2E.Rel} {c : BitVec 64} {env : Clif.Env}
    {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) (RelW Γ f c) env p)
    (hchk : threadCheckBlC f bl = true) (hres : callResLenB f = true)
    (hcu : callUseRegsBl f bl = true)
    (hlow : lowerCheck f vc = true) (hind : indSigs f = []) (hv : verifiable f = true)
    (hnt : f.blocks.all (fun B => !B.term.isTry) = true) (hout0 : vc.outgoing = 0)
    (hslot : RA.ctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → RA.X.sym n 0 = BitVec.ofNat 64 b)
    {L : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc L ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV}
    (huv : CallUsesVirt RA.vc) (hdv : CallDefsVirt RA.vc)
    {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState}
    (hq : Q RA x (.run cM')) (hP : Pause RA (.run cM'))
    (hm2 : Match f ctx R gn bl A (RelW Γ f c) slots s' vV')
    (hm3 : PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) L ss' (.run vV') (.run vP'))
    (hm4 : MatchRun cc ins ckeep r₀ cM' vP')
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s'.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hcl : stm.inst = .call fn args)
    {ext : Clif.ExtFunc} (hext : s'.frame.func.extern? fn = some ext)
    (huniq : ∀ e ∈ f.externs, e.2.name = ext.name → e.2 = ext)
    {vals : List Clif.Val} (hvals : s'.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params)
    (FB : LFn) (F : BitVec 64 → Prop) {fB : Clif.Function} (hsig : fB.sig = ext.sig) :
    ArgsAtEntry F fB.sig vals (bodyOf FB.af (Link.enter FB x)) :=
  hsig ▸ callee_argsAtEntry hX0 H hchk hres hcu hlow hind hv hnt hout0 hslot hsym H3 hc huv hdv hq
    hP hm2 hm3 hm4 hbody hcl hext huniq hvals htys FB F

end Concurrency.CallArgsEntry
