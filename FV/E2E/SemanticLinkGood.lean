import FV.E2E.LinkGood
import FV.E2E.LinkReturnPinGood

/-! Per-state linked execution facts for the actual production artifact contract.
Original facts and variants remain available. -/
set_option autoImplicit false
namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem insnAt_ofLine_semantic {fa : FnAsm} {fb : FnBin} {lm : Std.HashMap Lbl Nat} {base : BitVec 64}
    (hl : fa.layout = .ok fb) (hm : labelOffsets fa.lines = .ok lm)
    (hfit : 4 * fb.words.size ≤ 2 ^ 64) {u : Arm.ArmState} (hprog : u.program = fb.program base)
    {j : Nat} {x : Insn} {t : Option Clif.TrapCode} (hj : fa.lines.toList[j]? = some (.ins x t)) :
    insnAt fa (progBase u) (base + BitVec.ofNat 64 (lineOffset fa.lines.toList j)) = some x := by
  have shared := E2E.LinkSys.insnAt_ofLine_return_pins (fa := fa) (fb := fb) (lm := lm) (base := base) (u := u) (j := j) (x := x) (t := t) hl hm hfit hprog hj
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared
theorem progCallG_semantic (hL : L.OkSemanticNI) [hR : L.CrunOk] {M : Nat} (hM : 0 < M) (ihG : L.ThmG κ (M - 1)) {n : String}
    {h : Clif.Function} (hpf : L.P.func? n = some h) (hcal : ∃ g ∈ L.P.funcs, L.Callee g h)
    (hib : ((RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0 ∧
      (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves) ∨ L.NeedNI)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (L.A h).af + κ (M - 1) h ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a → F a ∧ ¬ L.Img a)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem} (hmr : MemRel F L.syms cm w) (hargs : ArgsAt h.sig vals uses w)
    (hsav : StackArgsAvoid F h.sig vals w) (hpl : L.NeedSlots → L.PlaceAt cm (spv w))
    (hinit : Clif.initState L.P n vals cm = .ok cs)
    (hrun : L.crun M cs = .returned rvals cm') :
    ∀ t, L.CallerOk F h uses w t → L.RunGoodL (M - 1) h (enterAt (L.A h) t) := by
  have shared := E2E.LinkSys.progCallG_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (n := n) (h := h) (F := F) (uses := uses) (w := w) (vals := vals) (cm := cm) (cs := cs) (rvals := rvals) (cm' := cm') L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hM ihG hpf hcal hib himgF herr hal hroom hdead hmr hargs hsav hpl hinit hrun
/-- **The callee's states of a returning call of a function of `P`** (`progOsCore_semantic`'s premises):
from `ThmG` one level down. -/
theorem progGoodCore_semantic (hL : L.OkSemanticNI) [L.CrunOk] {M : Nat} (ihG : 0 < M → L.ThmG κ (M - 1))
    {g h : Clif.Function} (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs) (hcallee : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} (hLu : Lu.map (·.2) = regLocs h.sig)
    {t w w' : Arm.ArmState} {outs : List CV}
    (hG : ∀ a, G a → t.mem a = s0.mem a) (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    (hx : L.progX κ M F h (Lu.map (fun q => regVal t q.2)) w = some (outs, w')) :
    L.RunGoodL (M - 1) h (enterAt (L.A h) t) := by
  have shared := E2E.LinkSys.progGoodCore_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (h := h) (F := F) (G := G) (s0 := s0) (Lu := Lu) (t := t) (w := w) (w' := w') (outs := outs) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared ihG hg hh hcallee himgF himgG himgS hLu hG hra hsw hx
/-- **The callee of a `blr` at a call state is one `g` may enter through the call's register**
(`BlrTo`): the callee contract's premise (`RL.CallPre`) is a call through `L.X`, which enters a
function of `P` only when `g` may enter it (`IndTo`), and pins a call through the GOT to its
symbol (`gotGuard`). -/
theorem blrTo_of_pre_semantic (hL : L.OkSemanticNI) {M : Nat} {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) {u : Arm.ArmState} {h : Clif.Function}
    (hpre : (L.actRL κ M g F G s).CallPre u) (hprog : u.program = (L.A g).fb.program (L.A g).base)
    {xr : Reg} (hx0 : insnAt (L.A g).fa (progBase u) (Arm.r .PC u) = some (.blr xr))
    (hb : (blrTarget u).bind (symCallee L.Xb L.P) = some h) :
    ∃ info tv, (L.A g).vcp.CallSite info ∧ info.dest = .reg (.vreg tv .int) ∧ L.BlrTo g tv h := by
  have shared := E2E.LinkSys.blrTo_of_pre_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (F := F) (G := G) (ra := ra) (s := s) (w₀ := w₀) (u := u) (h := h) (xr := xr) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hg he hpre hprog hx0 hb
/-- **The crux: the callee's states at a call state.** At a state `u` of the activation of `g`
at depth `M` where the callee contract's premise holds (`RL.CallPre`, which `RL.GoodX.call` gives
at a `bl`/`blr` line) and the machine calls `h` (`CallsAtL`), every state of `h`'s run entered
from `u` whose step ends without error has the per-state facts: the premise is the antecedent of
`progOs_semantic`/`progOsReg_semantic` (`calleeOk_semantic`), whose linked call of `h` is the callee activation of
`progCall_semantic`, whose states `ThmG` one level down covers. -/
theorem callGood_semantic (hL : L.OkSemanticNI) [L.CrunOk] {M : Nat} (ihG : 0 < M → L.ThmG κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) {u : Arm.ArmState} {h : Clif.Function}
    (hpre : (L.actRL κ M g F G s).CallPre u) (hprog : u.program = (L.A g).fb.program (L.A g).base)
    (hcall : L.CallsAtL g u h) : L.RunGoodL (M - 1) h (enterAt (L.A h) u) := by
  have shared := E2E.LinkSys.callGood_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (F := F) (G := G) (ra := ra) (s := s) (w₀ := w₀) (u := u) (h := h) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared ihG hg he hpre hprog hcall
/-! ## The states of an activation's run -/

/-- **The states of the activation of `g` at depth `M` entered in `s`** from its trace (the
register-level `GoodX` of every state before `n`), when every state before its return whose step
ends without error is before `n`: its own states from the trace, the nested ones from the call
states (`callGood_semantic`). -/
theorem runGood_of_trace_semantic (hL : L.OkSemanticNI) [L.CrunOk] {M : Nat} (ihG : 0 < M → L.ThmG κ (M - 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64}
    {s w₀ : Arm.ArmState} (he : L.MachEntry κ M g F G ra s w₀) {n : Nat}
    (hgood : ∀ i < n, actGoodX (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb
      (L.A g).base s (L.X κ M g F) (L.hooks M) (κ M g) G (GotV (L.A g).vcp)
      (runX (L.mach M g) i s))
    (hbound : ∀ k, (∀ j ≤ k, ¬ RetL (L.A g) s (runX (L.mach M g) j s)) →
      Arm.r .ERR (runX (L.mach M g) (k + 1) s) = .None → k < n) :
    L.RunGoodL M g s := by
  have shared := E2E.LinkSys.runGood_of_trace_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (F := F) (G := G) (ra := ra) (s := s) (w₀ := w₀) (n := n) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared ihG hg he hgood hbound
/-- A returning activation (`ActRet`) has returned in the sense of `RetL`. -/
theorem retL_of_actRet_semantic {g : Clif.Function} {ra : BitVec 64} {s t : Arm.ArmState}
    {F G : BitVec 64 → Prop} {us : List (Reg × Reg)} {outs : List CV} {wf : Arm.ArmState}
    (habi : AbiCall (L.A g).fb (L.A g).base ra s) (hret : ActRet ra F G us outs wf s t) :
    RetL (L.A g) s t := by
  have shared := E2E.LinkSys.retL_of_actRet_return_pins (g := g) (ra := ra) (s := s) (t := t) (F := F) (G := G) (us := us) (outs := outs) (wf := wf) L habi hret
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared
/-- **The per-state part of the induction step.** -/
theorem thmG_of_semantic (hL : L.OkSemanticNI) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.Thm κ (M - 1))
    (ihG : 0 < M → L.ThmG κ (M - 1)) : L.ThmG κ M := by
  have shared := E2E.LinkSys.thmG_of_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ ih ihG
/-- **The per-state part of the linking statement at every depth.** -/
theorem thmG_semantic (hL : L.OkSemanticNI) [L.CrunOk] (hκ : L.Budget κ) : ∀ M, L.ThmG κ M := by
  have shared := E2E.LinkSys.thmG_return_pins (modes := fun _ => .ordinary) (κ := κ) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ
/-- **The induction step of the linking statement with the per-state facts.** -/
theorem thmX_of_semantic (hL : L.OkSemanticNI) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmX κ (M - 1)) :
    L.ThmX κ M := by
  have shared := E2E.LinkSys.thmX_of_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ ih
/-- **The linking statement with the per-state facts at every depth.** -/
theorem thmX_semantic (hL : L.OkSemanticNI) [L.CrunOk] (hκ : L.Budget κ) : ∀ M, L.ThmX κ M := by
  have shared := E2E.LinkSys.thmX_return_pins (modes := fun _ => .ordinary) (κ := κ) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ
/-! ## `RunGoodL` does not read the callee runs -/

theorem reachL_withCrun_semantic {L : LinkSys} {cr : Nat → Clif.State → Clif.Outcome} {M : Nat}
    {f : Clif.Function} {c : Arm.ArmState} {M' : Nat} {g : Clif.Function} {c' t : Arm.ArmState}
    (h : L.ReachL M f c M' g c' t) : (L.withCrun cr).ReachL M f c M' g c' t := by
  have shared := E2E.LinkSys.reachL_withCrun_return_pins (L := L) (cr := cr) (M := M) (f := f) (c := c) (M' := M') (g := g) (c' := c') (t := t) h
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared
theorem goodAt_withCrun_semantic {L : LinkSys} {cr : Nat → Clif.State → Clif.Outcome} {M : Nat}
    {g : Clif.Function} {c t : Arm.ArmState} (h : (L.withCrun cr).GoodAt M g c t) :
    L.GoodAt M g c t := by
  have shared := E2E.LinkSys.goodAt_withCrun_return_pins (L := L) (cr := cr) (M := M) (g := g) (c := c) (t := t) h
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared
/-- **`RunGoodL` does not depend on the callee runs** of the linked system (the linked machine
does not read them). -/
theorem runGoodL_withCrun_semantic {L : LinkSys} {cr : Nat → Clif.State → Clif.Outcome} {M : Nat}
    {f : Clif.Function} {c : Arm.ArmState} (h : (L.withCrun cr).RunGoodL M f c) :
    L.RunGoodL M f c := by
  have shared := E2E.LinkSys.runGoodL_withCrun_return_pins (L := L) (cr := cr) (M := M) (f := f) (c := c) h
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared
end LinkSys

/-- **`backend_correct_program_core_semantic` with the run's per-state facts** for a returning or
trapping outcome (`RunGoodL`), for any callee runs (`LinkSys.CrunOk`). -/
theorem backend_correct_program_coreX_semantic (L : LinkSys) (hL : L.OkSemanticNI) [L.CrunOk]
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs) {o : Clif.Outcome}
    (hlink : ((∃ vals cm, o = .returned vals cm) ∨ ∃ c, o = .trapped c) →
      ∃ m, Clif.runLoop (L.envR M f) L.P.bare m cs = o) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s o ∧
      ((∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c) → L.RunGoodL M f s) := by
  have shared := E2E.backend_correct_program_coreX_return_pins (modes := fun _ => .ordinary) (κ := κ) (f := f) (ra := ra) (s := s) (w₀ := w₀) (args := args) (cs := cs) (o := o) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr hlink
/-- **`backend_correct_program_budgetX_semantic`**: `backend_correct_program_budget_semantic` with the run's per-state facts for a returning or
trapping outcome. -/
theorem backend_correct_program_budgetX_semantic (L : LinkSys) (hL : L.OkSemanticNI)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) ∧
      ((∃ vals cm, Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) ∨
        (∃ c, Clif.runLoop L.base L.P (M + 1) cs = .trapped c) → L.RunGoodL M f s) := by
  have shared := E2E.backend_correct_program_budgetX_return_pins (modes := fun _ => .ordinary) (κ := κ) (f := f) (ra := ra) (s := s) (w₀ := w₀) (args := args) (cs := cs) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr
/-- **`backend_correct_program_peak_semantic` with the run's per-state facts** for a returning or
trapping outcome (L1d): the linked machine of the run's peak call depth `d` (`Clif.DepthLe`),
the program callees with fuel `F` and bounded depth (`Clif.linkEnvD`). -/
theorem backend_correct_program_peakX_semantic (L : LinkSys) (hL : L.OkSemanticNI)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (F d : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ d f) (L.A f).af s)
    (hF : L.F = frameWG (κ d f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ d f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (hd : Clif.DepthLe L.base L.P d cs)
    (htr : TrapsExplicit (Clif.linkEnvD L.P L.base F d) L.P.bare cs) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach d f) s (Clif.runLoop L.base L.P (F + 1) cs) ∧
      ((∃ vals cm, Clif.runLoop L.base L.P (F + 1) cs = .returned vals cm) ∨
        (∃ c, Clif.runLoop L.base L.P (F + 1) cs = .trapped c) → L.RunGoodL d f s) := by
  have shared := E2E.backend_correct_program_peakX_return_pins (modes := fun _ => .ordinary) (κ := κ) (f := f) (ra := ra) (s := s) (w₀ := w₀) (args := args) (cs := cs) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    LinkSys.actRLMode,LinkSys.actRL,LinkSys.ThmXReturnPins,LinkSys.ThmX,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ hf F d hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl hd htr
end E2E
