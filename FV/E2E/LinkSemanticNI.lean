import FV.E2E.LinkReturnPinProgram

/-! Additive whole-program proofs for actual validated output.
Uses the existing LinkSys, hooks, CLIF runs, machine, depth/peak budgets and
binary artifacts. Only the proof contract's compilation field is generalized;
all38 non-compilation input/layout/environment conditions and old theorem variants are
preserved. Actual raw Stock artifacts use the paired semantic interface. Existing production theorem variants remain available. -/
set_option autoImplicit false

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
open Clif Opt



namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem callerOk_canon_semantic (hL : L.OkSemanticNI) {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) (uses : List CV)
    (w : Arm.ArmState) : L.CallerOk F g uses w (L.canon g uses w) := by
  have shared := E2E.LinkSys.callerOk_canon_return_pins (modes := fun _ => .ordinary) (g := g) (F := F) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hg himgF uses w
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem bodyEntryW_compat_semantic (hL : L.OkSemanticNI) {h : Clif.Function} (hh : h ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {uses : List CV}
    {w t : Arm.ArmState} (ht : L.CallerOk F h uses w t) :
    BodyEntryW F (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t)
      (bodyOf (L.A h).af (enterAt (L.A h) (L.canon h uses w))) := by
  have shared := E2E.LinkSys.bodyEntryW_compat_return_pins (modes := fun _ => .ordinary) (h := h) (F := F) (uses := uses) (w := w) (t := t) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hh himgF ht
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem frameSize_mod_semantic (hL : L.OkSemanticNI) {h : Clif.Function} (hh : h ∈ L.P.funcs) :
    (L.A h).af.frameSize % 16 = 0 := by
  have shared := E2E.LinkSys.frameSize_mod_return_pins (modes := fun _ => .ordinary) (h := h) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hh
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem frameDrop_eq_semantic (hL : L.OkSemanticNI) {h : Clif.Function} (hh : h ∈ L.P.funcs) :
    frameDrop (L.A h).af = (L.A h).af.frameSize + 16 := by
  have shared := E2E.LinkSys.frameDrop_eq_return_pins (modes := fun _ => .ordinary) (h := h) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hh
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem progCall_semantic (hL : L.OkSemanticNI) [hR : L.CrunOk] {M : Nat} (hM : 0 < M) (ih : L.Thm κ (M - 1)) {n : String}
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
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
      us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A h).vc.RetsSite us ∧
      (∀ t, L.CallerOk F h uses w t → ∃ k,
        L.pcall M h t =
          Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program ∧
        ActRet (Arm.r .PC t + 4) F
          (fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a)
          us outs wf (enterAt (L.A h) t) (runX (L.mach (M - 1) h) k (enterAt (L.A h) t))) ∧
      (L.NeedNI → ∀ (Z : BitVec 64 → Prop) (t : Arm.ArmState), (∀ a, F a → Z a) →
        SameWorld Z t w → (∀ a, L.Img a → t.mem a = L.imgMem a) →
        (∀ r ∈ regLocs h.sig, regVal t r = regVal (L.canon h uses w) r) →
        RaOk (L.A h) (Arm.r .PC t) →
        MemRel F L.syms cm t →
        (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf h.sig).zip vals → ∀ k < v.ty.bytes,
          t.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
            w.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k)) → ∃ k,
        L.pcall M h t =
          Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program ∧
        ActRet (Arm.r .PC t + 4) Z
          (fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a)
          us outs wf (enterAt (L.A h) t) (runX (L.mach (M - 1) h) k (enterAt (L.A h) t))) := by
  have shared := E2E.LinkSys.progCall_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (n := n) (h := h) (F := F) (uses := uses) (w := w) (vals := vals) (cm := cm) (cs := cs) (rvals := rvals) (cm' := cm') L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hM ih hpf hcal hib himgF herr hal hroom hdead hmr hargs hsav hpl hinit hrun
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem X_ext_semantic (hL : L.OkSemanticNI) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} {d : Option String}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hx : (L.X κ M g F).call d uses w = some (outs, w'))
    (herr : Arm.r .ERR w = .None) : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  have shared := E2E.LinkSys.X_ext_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (F := F) (d := d) (uses := uses) (w := w) (outs := outs) (w' := w') L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hx herr
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem budget_K_semantic (hL : L.OkSemanticNI) : L.Budget fun M _ => L.K M := by
  have shared := E2E.LinkSys.budget_K_return_pins (modes := fun _ => .ordinary)  L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem progOsCore_semantic (hL : L.OkSemanticNI) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.Thm κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lu : List (Nat × Reg)} {Ld : List (Reg × Nat)} (hLu : Lu.map (·.2) = regLocs h.sig)
    (hLd : (Ld.map (·.1)).take (sigRets h.sig).length =
      (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x)
    {info : CallInfo} (hdefs0 : info.defs = callDefs Ld)
    {ops : Array Operand} {regs : Array Reg}
    (hdefs : ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOps Ld).zip (Ld.map (·.1)))
    {t w w' : Arm.ArmState} {outs : List CV}
    (hK : κ M g ≤ (spOf t).toNat) (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    (hx : L.progX κ M F h (Lu.map (fun q => regVal t q.2)) w = some (outs, w')) :
    SameWorld F (L.pcall M h t) w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (κ M g) (spOf t) a) t (L.pcall M h t) ∧
      (∀ p ∈ defRegs ops regs outs, regVal (L.pcall M h t) p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ (MInst.call info).clobbers → regVal (L.pcall M h t) r = regVal t r) ∧
      (∀ r ∈ (MInst.call info).clobbers, r ∈ calleeSaved →
        ckeep r (regVal (L.pcall M h t) r) = ckeep r (regVal t r)) := by
  have shared := E2E.LinkSys.progOsCore_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (h := h) (F := F) (G := G) (s0 := s0) (Lu := Lu) (Ld := Ld) (info := info) (ops := ops) (regs := regs) (t := t) (w := w) (w' := w') (outs := outs) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ ih hg hh hcallee himgF himgG himgS hLu (CallReturnPins.ordinary hLd) hdefs0 hdefs hK hG hra hsw hx
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem got_target_semantic (hL : L.OkSemanticNI) {a : BitVec 64} {h : Clif.Function} {n : String}
    (hs : symCallee L.Xb L.P a = some h) (e : a = L.Xb.sym n 0) : n = h.name := by
  have shared := E2E.LinkSys.got_target_return_pins (modes := fun _ => .ordinary) (a := a) (h := h) (n := n) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hs e
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem progOs_semantic (hL : L.OkSemanticNI) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.Thm κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} {h : Clif.Function} (hsite : L.ProgSite g info h) (ctx : FnCtx) :
    CallSoundCtlG F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.X κ M g F)) (.call info) .next := by
  have shared := E2E.LinkSys.progOs_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (F := F) (G := G) (s0 := s0) (info := info) (h := h) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ ih hg himgF himgG himgS hsite ctx
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem progOsReg_semantic (hL : L.OkSemanticNI) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.Thm κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) (hreg : ∀ n, info.dest ≠ .sym n)
    (ctx : FnCtx) :
    CallSoundCtlG F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.X κ M g F)) (.call info) .next := by
  have shared := E2E.LinkSys.progOsReg_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (F := F) (G := G) (s0 := s0) (info := info) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ ih hg himgF himgG himgS hsite hreg ctx
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem calleeOk_semantic (hL : L.OkSemanticNI) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.Thm κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) :
    CalleeOkG F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.X κ M g F) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) := by
  have shared := E2E.LinkSys.calleeOk_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (F := F) (G := G) (ra := ra) (s := s) (w₀ := w₀) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ ih hg he
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem calleeTryOk_semantic (hL : L.OkSemanticNI) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.Thm κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) :
    CalleeTryOkG F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.X κ M g F) (L.hooks M)
      (L.A g).vcp.TrySite (GotV (L.A g).vcp) := by
  have shared := E2E.LinkSys.calleeTryOk_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (F := F) (G := G) (ra := ra) (s := s) (w₀ := w₀) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ ih hg he
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem find_sym_semantic (hL : L.OkSemanticNI) (n : String) :
    (∀ h, L.P.func? n = some h → L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == L.Xb.sym n 0) = some h) ∧
    (L.P.func? n = none → L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == L.Xb.sym n 0) = none) := by
  have shared := E2E.LinkSys.find_sym_return_pins (modes := fun _ => .ordinary)  L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared n
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem progResult_semantic (hL : L.OkSemanticNI) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.Thm κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat) (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a)
    (halign : c.toNat % 16 = 0)
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : Arm.ArmState} {args : List CV}
    {vals rvals : List Clif.Val} {cm' : Clif.Mem} {cs : Clif.State}
    (hargs : ArgsAt h.sig vals args w) (hsav : StackArgsAvoid F h.sig vals w)
    (hmr : RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
      g c sl cm w)
    (hpl : L.NeedSlots → L.PlaceAt cm c) (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hret : L.crun M cs = .returned rvals cm') :
    ∃ outs w', L.progX κ M F h args w = some (outs, w') ∧ outs.length = (sigRets h.sig).length ∧
      PrefixHold rvals outs ∧
      RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c sl cm' w' := by
  have shared := E2E.LinkSys.progResult_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (h := h) (F := F) (c := c) (sl := sl) (cm := cm) (w := w) (args := args) (vals := vals) (rvals := rvals) (cm' := cm') (cs := cs) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ ih hg hh hcallee himgF hroom hdead halign hargs hsav hmr hpl hinit hret
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem envOf_keeps_semantic (hL : L.OkSemanticNI) [hR : L.CrunOk] {M : Nat} {g : Clif.Function} {c : BitVec 64}
    (hk : Opt.EnvKeepsSymbols L.base) : Opt.EnvKeepsSymbols (L.envOf M g c) := by
  have shared := E2E.LinkSys.envOf_keeps_return_pins (modes := fun _ => .ordinary) (M := M) (g := g) (c := c) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hk
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem xCallsOk_semantic (hL : L.OkSemanticNI) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.Thm κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat)
    (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0) :
    XCallsOk (L.envOf M g c) (g.externs.map (·.2))
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c) (L.X κ M g F) := by
  have shared := E2E.LinkSys.xCallsOk_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (F := F) (c := c) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ ih hg himgF hroom hdead halign
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem xCallsIndOk_semantic (hL : L.OkSemanticNI) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.Thm κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat)
    (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0) :
    XCallsIndOk (L.envOf M g c) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c) (L.X κ M g F) := by
  have shared := E2E.LinkSys.xCallsIndOk_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (F := F) (c := c) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ ih hg himgF hroom hdead halign
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem regVal_canon_eq_semantic (hL : L.OkSemanticNI) {h : Clif.Function} (hh : h ∈ L.P.funcs) {args : List CV}
    (hlen : args.length = (regLocs h.sig).length) (w w' : Arm.ArmState) :
    ∀ r ∈ regLocs h.sig, regVal (L.canon h args w') r = regVal (L.canon h args w) r := by
  have shared := E2E.LinkSys.regVal_canon_eq_return_pins (modes := fun _ => .ordinary) (h := h) (args := args) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hh hlen w w'
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem progX_ni_semantic (hL : L.OkSemanticNI) [hR : L.CrunOk] (hN : L.NeedNI) {M : Nat} (ih : 0 < M → L.Thm κ (M - 1))
    {g h : Clif.Function} (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h) {F Z : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) (hFZ : ∀ a, F a → Z a) {w w' : Arm.ArmState}
    (hsw : SameWorld Z w w') {cm : Clif.Mem} {vals : List Clif.Val} {args : List CV}
    (hm : MemRel F L.syms cm w) (hm' : MemRel F L.syms cm w') (ha : ArgsAt h.sig vals args w)
    (ha' : ArgsAt h.sig vals args w') {cs : Clif.State} {rvals : List Clif.Val} {cm' : Clif.Mem}
    (hpl : L.NeedSlots → L.PlaceAt cm (spv w)) (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hrun : L.crun M cs = .returned rvals cm') {o o' : List CV}
    {x x' : Arm.ArmState} (hx : L.progX κ M F h args w = some (o, x))
    (hx' : L.progX κ M F h args w' = some (o', x')) : o = o' ∧ SameWorld Z x x' := by
  have shared := E2E.LinkSys.progX_ni_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (h := h) (F := F) (Z := Z) (w := w) (w' := w') (cm := cm) (vals := vals) (args := args) (cs := cs) (rvals := rvals) (cm' := cm') (o := o) (o' := o') (x := x) (x' := x') L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hN ih hg hh hcallee himgF hFZ hsw hm hm' ha ha' hpl hinit hrun hx hx'
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem xni_semantic (hL : L.OkSemanticNI) [L.CrunOk] (hN : L.NeedNI) {M : Nat} (ih : 0 < M → L.Thm κ (M - 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) (c : BitVec 64) :
    XNI F L.syms (g.externs.map (·.2)) (indSigs g) c
      (CallLg (L.envOf M g c) (g.externs.map (·.2)) (indSigs g)) (L.X κ M g F) := by
  have shared := E2E.LinkSys.xni_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (F := F) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hN ih hg himgF c
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem xTls_semantic (hL : L.OkSemanticNI) (hN : L.NeedNI) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} :
    XTls F (L.X κ M g F) := by
  have shared := E2E.LinkSys.xTls_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) (g := g) (F := F) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hN
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem actInv_step_semantic (hL : L.OkSemanticNI) [hR : L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs) {c : BitVec 64}
    {s s1 : Clif.State} (hJ : L.ActInv g c s)
    (hs : Clif.step (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare s = .next s1) :
    L.ActInv g c s1 := by
  have shared := E2E.LinkSys.actInv_step_return_pins (modes := fun _ => .ordinary) (M := M) (g := g) (c := c) (s := s) (s1 := s1) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hg hJ hs
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem step_envOf_link_semantic (hL : L.OkSemanticNI) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} {s : Clif.State} (hJ : L.ActInv g c s) {r : Clif.StepResult}
    (hs : Clif.step (L.envOf M g c) L.P.bare s = r) (hr : ∀ m, r ≠ .stuck m) :
    Clif.step (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare s = r := by
  have shared := E2E.LinkSys.step_envOf_link_return_pins (modes := fun _ => .ordinary) (M := M) (g := g) (c := c) (s := s) (r := r) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hg hJ hs hr
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem runLoop_envOf_semantic (hL : L.OkSemanticNI) [L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} :
    ∀ (n : Nat) (s : Clif.State), L.ActInv g c s →
      Clif.runLoop (L.envOf M g c) L.P.bare n s = Clif.runLoop (L.envR M g) L.P.bare n s := by
  have shared := E2E.LinkSys.runLoop_envOf_return_pins (modes := fun _ => .ordinary) (M := M) (g := g) (c := c) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hg
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem reach_envOf_semantic (hL : L.OkSemanticNI) [L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} {cs s : Clif.State} (hr : Reach (L.envOf M g c) L.P.bare cs s)
    (hJ : L.ActInv g c cs) :
    Reach (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs s ∧ L.ActInv g c s := by
  have shared := E2E.LinkSys.reach_envOf_return_pins (modes := fun _ => .ordinary) (M := M) (g := g) (c := c) (cs := cs) (s := s) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hg hr hJ
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem trapsExplicit_envOf_semantic (hL : L.OkSemanticNI) [L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} {cs : Clif.State} (hJ : L.ActInv g c cs)
    (h : TrapsExplicit (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs) :
    TrapsExplicit (L.envOf M g c) L.P.bare cs := by
  have shared := E2E.LinkSys.trapsExplicit_envOf_return_pins (modes := fun _ => .ordinary) (M := M) (g := g) (c := c) (cs := cs) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hg hJ h
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem thm_of_semantic (hL : L.OkSemanticNI) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.Thm κ (M - 1)) : L.Thm κ M := by
  have shared := E2E.LinkSys.thm_of_return_pins (modes := fun _ => .ordinary) (κ := κ) (M := M) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ ih
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem thm_semantic (hL : L.OkSemanticNI) [L.CrunOk] (hκ : L.Budget κ) : ∀ M, L.Thm κ M := by
  have shared := E2E.LinkSys.thm_return_pins (modes := fun _ => .ordinary) (κ := κ) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem OkSemanticNI.withCrun {L : LinkSys} (hL : L.OkSemanticNI) (c : Nat → Clif.State → Clif.Outcome) :
    (L.withCrun c).OkSemanticNI := by
  cases hL; constructor <;> assumption
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem crunOk_std_semantic (hL : L.OkSemanticNI) : L.std.CrunOk := by
  have shared := E2E.LinkSys.crunOk_std_return_pins (modes := fun _ => .ordinary)  L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared
end LinkSys

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem crunOk_peak_semantic (hL : L.OkSemanticNI) (F : Nat) : (L.peak F).CrunOk := by
  have shared := E2E.LinkSys.crunOk_peak_return_pins (modes := fun _ => .ordinary)  L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared F
end LinkSys

theorem backend_correct_program_core_semantic (L : LinkSys) (hL : L.OkSemanticNI) [L.CrunOk]
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
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s o := by
  have shared := E2E.backend_correct_program_core_return_pins (modes := fun _ => .ordinary) (κ := κ) (f := f) (ra := ra) (s := s) (w₀ := w₀) (args := args) (cs := cs) (o := o) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr hlink
theorem backend_correct_program_budget_semantic (L : LinkSys) (hL : L.OkSemanticNI)
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
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) := by
  have shared := E2E.backend_correct_program_budget_return_pins (modes := fun _ => .ordinary) (κ := κ) (f := f) (ra := ra) (s := s) (w₀ := w₀) (args := args) (cs := cs) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr
theorem backend_correct_program_peak_semantic (L : LinkSys) (hL : L.OkSemanticNI)
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
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach d f) s (Clif.runLoop L.base L.P (F + 1) cs) := by
  have shared := E2E.backend_correct_program_peak_return_pins (modes := fun _ => .ordinary) (κ := κ) (f := f) (ra := ra) (s := s) (w₀ := w₀) (args := args) (cs := cs) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ hf F d hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl hd htr
theorem backend_correct_program_semantic (L : LinkSys) (hL : L.OkSemanticNI) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (L.K M) (L.A f).af s)
    (hF : L.F = frameWG (L.K M) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + L.K M) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) := by
  have shared := E2E.backend_correct_program_return_pins (modes := fun _ => .ordinary) (f := f) (ra := ra) (s := s) (w₀ := w₀) (args := args) (cs := cs) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl htr
theorem backend_correct_program_returned_budget_semantic (L : LinkSys) (hL : L.OkSemanticNI)
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
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.returned vals cm) := by
  have shared := E2E.backend_correct_program_returned_budget_return_pins (modes := fun _ => .ordinary) (κ := κ) (f := f) (ra := ra) (s := s) (w₀ := w₀) (args := args) (cs := cs) (vals := vals) (cm := cm) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl hrun
theorem backend_correct_program_returned_semantic (L : LinkSys) (hL : L.OkSemanticNI) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (L.K M) (L.A f).af s)
    (hF : L.F = frameWG (L.K M) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + L.K M) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.returned vals cm) := by
  have shared := E2E.backend_correct_program_returned_return_pins (modes := fun _ => .ordinary) (f := f) (ra := ra) (s := s) (w₀ := w₀) (args := args) (cs := cs) (vals := vals) (cm := cm) L hL.toReturnPins
  try simp only [LinkSys.XMode_ordinary,LinkSys.progXMode_ordinary,LinkSys.modeReturnPins,
    ReturnPinMode.pins,ReturnPinMode.Valid] at shared
  exact shared hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl hrun
end E2E
