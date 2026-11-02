import FV.E2E.ReturnPinExecutableKernel
import FV.E2E.ReturnPinBinary
import FV.E2E.SemanticExecGoodReads

namespace E2E.ReturnPinExecBytes
open Backend Backend.Proof E2E.LinkCheck E2E.SemanticBinary E2E.BinCheck E2E.SemanticExecBytes
set_option autoImplicit false
set_option Elab.async false
variable {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {file : ByteArray}

/-- The existing executable contract follows from the checked allocation and image. -/
theorem fnOk {D : List Clif.DataObject} (hI : ReturnPinStackBound.okB I = true)
    (hbin : BinOkWithResults I I.results D file)
    {F : BitVec 64 → Prop} (hL : (SemanticStackBound.ofInput I B F).OkSemanticReturnPins)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) : FnOk I file g := by
  exact E2E.ReturnPinExecBytesFor.fnOk
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (D := D) (hI := hI)
    (hbin := hbin) (F := F) (hL := hL)
    (g := g) (hg := hg)

theorem codeMap_sound {I : SemanticStackBound.CompilerInput} (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) :
    (I.symAddr g.name 0 = (art I g).base ∨ noBlrB I (tabOf I.results) g.name = true) ∧
    ∀ g' ∈ (prog I).funcs, g.name ≠ g'.name →
      ((art I g).base.toNat + 4 * (art I g).fb.words.size ≤ (art I g').base.toNat ∨
        (art I g').base.toNat + 4 * (art I g').fb.words.size ≤ (art I g).base.toNat) ∨
      ((art I g).base = (art I g').base ∧
        linesAlikeB (prog I) (art I g).fa.lines.toList (art I g').fa.lines.toList = true) := by
  exact E2E.ReturnPinExecBytesFor.codeMap_sound
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (I := I) (hI := hI)
    (hc := hc) (g := g) (hg := hg)

theorem relocAt_inv (hI : ReturnPinStackBound.okB I = true) {a : BitVec 64} (h : RelocAtWithResults I I.results a) :
    ∃ g ∈ (prog I).funcs, ∃ rl ∈ (art I g).fb.relocs, ∃ i < 4, a = wAt (art I g) (rl.offset + i) := by
  exact E2E.ReturnPinExecBytesFor.relocAt_inv
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (hI := hI) (a := a)
    (h := h)

theorem line_overlap (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {g h : Clif.Function} (hg : g ∈ (prog I).funcs)
    (hh : h ∈ (prog I).funcs) {j j' : Nat} {l l' : Line}
    (hj : (art I g).fa.lines.toList[j]? = some l) (hj' : (art I h).fa.lines.toList[j']? = some l')
    (hl : l.isLabel = false) (hl' : l'.isLabel = false) {k k' : Nat} (hk : k < 4) (hk' : k' < 4)
    (he : (art I g).base.toNat + lineOffset (art I g).fa.lines.toList j + k =
      (art I h).base.toNat + lineOffset (art I h).fa.lines.toList j' + k') :
    lineAlikeB (prog I) l l' = true := by
  exact E2E.ReturnPinExecBytesFor.line_overlap
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (hI := hI) (hc := hc)
    (hF := hF) (g := g) (h := h)
    (hg := hg) (hh := hh) (j := j)
    (j' := j') (l := l) (l' := l')
    (hj := hj) (hj' := hj') (hl := hl)
    (hl' := hl') (k := k) (k' := k')
    (hk := hk) (hk' := hk') (he := he)

theorem relocAt_img (hI : ReturnPinStackBound.okB I = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {a : BitVec 64} (h : RelocAtWithResults I I.results a) : ImgT (tabOf I.results) a := by
  exact E2E.ReturnPinExecBytesFor.relocAt_img
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (hI := hI) (hF := hF)
    (a := a) (h := h)

theorem word_static (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {g : Clif.Function} (hg : g ∈ (prog I).funcs)
    {j : Nat} {tg bs : Lbl} (hj : (art I g).fa.lines.toList[j]? = some (.word tg bs)) :
    ∀ k < 4, ¬ RelocAtWithResults I I.results (wAt (art I g) (lineOffset (art I g).fa.lines.toList j) +
      BitVec.ofNat 64 k) := by
  exact E2E.ReturnPinExecBytesFor.word_static
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (hI := hI) (hc := hc)
    (hF := hF) (g := g) (hg := hg)
    (j := j) (tg := tg) (bs := bs)
    (hj := hj)

theorem insn_of_good (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat} {g : Clif.Function}
    (hg : g ∈ (prog I).funcs) {c t : Arm.ArmState} (hgood : (sys I B).GoodAt M g c t) :
    ∀ i, insnAt (art I g).fa (art I g).base (Arm.r .PC t) = some i → i.hooked = false →
      ∀ a, (fileWord file (Arm.r .PC t)).bind Arm.decode_raw_inst = some a →
      ∀ e, Sim I t e → Sim I (Arm.exec_inst a t) (Arm.exec_inst a e) := by
  exact E2E.ReturnPinExecBytesFor.insn_of_good
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (hI := hI) (hc := hc)
    (hF := hF) (M := M) (g := g)
    (hg := hg) (c := c) (t := t)
    (hgood := hgood)

theorem symAddr_of_blrTo {I : SemanticStackBound.CompilerInput} {B : BaseEnv} (hI : ReturnPinStackBound.okB I = true)
    (hc : codeMapB I (tabOf I.results) = true) {g h : Clif.Function} (hg : g ∈ (prog I).funcs)
    (hh : h ∈ (prog I).funcs) {info : CallInfo} {t : Nat} (hs : (art I g).vcp.CallSite info)
    (hd : info.dest = .reg (.vreg t .int)) (hb : (sys I B).BlrTo g t h) :
    I.symAddr h.name 0 = (art I h).base := by
  exact E2E.ReturnPinExecBytesFor.symAddr_of_blrTo
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (I := I) (B := B)
    (hI := hI) (hc := hc) (g := g)
    (h := h) (hg := hg) (hh := hh)
    (info := info) (t := t) (hs := hs)
    (hd := hd) (hb := hb)

variable {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {file : ByteArray}


theorem siteAt_static (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {a : BitVec 64} {i : Insn}
    (hi : insnAt (art I g).fa (art I g).base a = some i) :
    siteAt I a = some (siteOf (prog I) i) := by
  exact E2E.ReturnPinExecBytesFor.siteAt_static
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (hI := hI) (hc := hc)
    (hF := hF) (g := g) (hg := hg)
    (a := a) (i := i) (hi := hi)

theorem plain_static (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) {a : BitVec 64} {i : Insn}
    (hi : insnAt (art I g).fa (art I g).base a = some i) (hr : i.reloc? = none) :
    ∀ k < 4, ¬ RelocAtWithResults I I.results (a + BitVec.ofNat 64 k) := by
  exact E2E.ReturnPinExecBytesFor.plain_static
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (hI := hI) (hc := hc)
    (hF := hF) (g := g) (hg := hg)
    (a := a) (i := i) (hi := hi)
    (hr := hr)

theorem stepOk_of_d (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    (hH : HooksSim I B) {M : Nat} {g : Clif.Function} (hg : g ∈ (prog I).funcs)
    {m : Arm.ArmState} (h : StepOkD I B file M g m) : StepOk I B file M g m:= by
  exact E2E.ReturnPinExecBytesFor.stepOk_of_d
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (hI := hI) (hc := hc)
    (hF := hF) (hH := hH) (M := M)
    (g := g) (hg := hg) (m := m)
    (h := h)

theorem runOkSN_of_n (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hH : HooksSim I B) {M : Nat}
    {f : Clif.Function} (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (h : RunOkN I B file M f c) : RunOkSN I B file M f c := by
  exact E2E.ReturnPinExecBytesFor.runOkSN_of_n
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (hI := hI) (hc := hc)
    (hF := hF) (hH := hH) (M := M)
    (f := f) (hf := hf) (c := c)
    (h := h)

theorem pairsClosed_art (hI : ReturnPinStackBound.okB I = true) {g : Clif.Function} (hg : g ∈ (prog I).funcs) :
    PairsClosed (art I g).fa.lines.toList := by
  exact E2E.ReturnPinExecBytesFor.pairsClosed_art
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (hI := hI) (g := g)
    (hg := hg)

theorem raNotSecond_enter (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {g h : Clif.Function} (hg : g ∈ (prog I).funcs)
    {u : Arm.ArmState} (hp : u.program = (art I g).fb.program (art I g).base)
    (hcall : CallsAt I B g u h) : ¬ Second I h (xreg 30 (enterAt (art I h) u)) := by
  exact E2E.ReturnPinExecBytesFor.raNotSecond_enter
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (hI := hI) (hc := hc)
    (hF := hF) (g := g) (h := h)
    (hg := hg) (u := u) (hp := hp)
    (hcall := hcall)

theorem reachL_of_reachN (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat} {f : Clif.Function} {c : Arm.ArmState}
    {M' : Nat} {g : Clif.Function} {t : Arm.ArmState} (h : ReachN I B M f c M' g t) :
    f ∈ (prog I).funcs → (sys I B).RunGoodL M f c → ¬ Second I f (xreg 30 c) →
    ∃ c', (sys I B).ReachL M f c M' g c' t ∧ ¬ Second I g (xreg 30 c') := by
  exact E2E.ReturnPinExecBytesFor.reachL_of_reachN
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (hI := hI) (hc := hc)
    (hF := hF) (M := M) (f := f)
    (c := c) (M' := M') (g := g)
    (t := t) (h := h)

theorem destsInt_of_ok {L : LinkSys} {modes : Clif.Function → E2E.ReturnPinMode} (hL : L.OkReturnPins modes) {g : Clif.Function} (hg : g ∈ L.P.funcs) :
    (L.A g).vcp.DestsInt := by
  exact E2E.ReturnPinExecBytesFor.destsInt_of_ok
    (L := L) (modes := modes) (hL := hL)
    (g := g) (hg := hg)

theorem stepOkD_of_good (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    (hD : ∀ g ∈ (prog I).funcs, (art I g).vcp.DestsInt)
    {M : Nat} {g : Clif.Function} (hg : g ∈ (prog I).funcs) {c t : Arm.ArmState}
    (hgood : (sys I B).GoodAt M g c t) (hs : ¬ Second I g (xreg 30 c))
    (he : Arm.r .ERR ((sys I B).mach M g t) = .None) (hr : StepOkR I B file M g t) :
    StepOkD I B file M g t := by
  exact E2E.ReturnPinExecBytesFor.stepOkD_of_good
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (hI := hI) (hc := hc)
    (hF := hF) (hD := hD) (M := M)
    (g := g) (hg := hg) (c := c)
    (t := t) (hgood := hgood) (hs := hs)
    (he := he) (hr := hr)

theorem runOkN_of_good (hI : ReturnPinStackBound.okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hD : ∀ g ∈ (prog I).funcs, (art I g).vcp.DestsInt)
    {M : Nat} {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 c ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    (hgood : (sys I B).RunGoodL M f c) (hreads : RunReadsN I B file M f c) :
    RunOkN I B file M f c := by
  exact E2E.ReturnPinExecBytesFor.runOkN_of_good
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (hI := hI) (hc := hc)
    (hF := hF) (hD := hD) (M := M)
    (f := f) (hf := hf) (c := c)
    (hra := hra) (hgood := hgood) (hreads := hreads)

theorem image_checked (hI : ReturnPinStackBound.okB I = true) : imgB (tabOf I.results) = true := by
  exact E2E.ReturnPinExecBytesFor.image_checked
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (hI := hI)

end E2E.ReturnPinExecBytes
