import FV.E2E.ReturnPinExecutableKernel
import FV.E2E.ReturnPinExecStatic
import FV.E2E.SemanticExecGot

namespace E2E.LinkSys
open Backend Backend.Proof
theorem OkReturnPins.extImgProduction {L : LinkSys} {modes : Clif.Function → E2E.ReturnPinMode} (hL : L.OkReturnPins modes) {F S : BitVec 64 → Prop} {m : Arm.Memory}
    (hm : ∀ a, L.Img a → m a = L.imgMem a) (hF : ∀ a, L.Img a ∨ S a → F a) :
    (L.extImgProduction F S m).OkReturnPins modes := by
  exact E2E.LinkSys.OkReturnPins.extImgProductionFor
    (L := L) (modes := modes) (hL := hL)
    (F := F) (S := S) (m := m)
    (hm := hm) (hF := hF)

end E2E.LinkSys

namespace E2E.ReturnPinExecBytes
open Backend Backend.Proof E2E.LinkCheck E2E.SemanticBinary E2E.BinCheck E2E.SemanticExecBytes
set_option autoImplicit false
set_option Elab.async false
variable {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {file : ByteArray}
theorem sysS_entry {D : List Clif.DataObject} (hI : ReturnPinStackBound.okB I = true) (hbin : BinOkWithResults I I.results D file)
    (hB : BaseOk (sys I B)) {f : Clif.Function} (hfm : f ∈ (prog I).funcs)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    {K : Nat}
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + K) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (frameDrop (art I f).af + K) r args cs.mem)
    (hr : ClifRun I B f r args cs) :
    (sysS I B f K r S).OkSemanticReturnPins ∧
    AbiEntry (art I f).fb (art I f).base (xreg 30 r) (modelOf I f r) ∧
    StackAvail K (art I f).af (modelOf I f r) ∧
    (∀ a, (sysS I B f K r S).Img a →
      ¬ StackBelow (frameDrop (art I f).af + K) (spv (modelOf I f r)) a) ∧
    BodyEntry (art I f).af (modelOf I f r) (bodyOf (art I f).af (modelOf I f r)) ∧
    ArgsIn f.sig args (modelOf I f r) ∧
    StackArgsAvoid (sysS I B f K r S).Img f.sig args (modelOf I f r) ∧
    Rel.holds ⟨(sysS I B f K r S).F, (sysS I B f K r S).syms, (art I f).af.slotBase,
      (RAFrame.compute (art I f).vcp (art I f).rf).intBase⟩ f cs.frame.slots cs.mem
      (bodyOf (art I f).af (modelOf I f r)) ∧
    ((sysS I B f K r S).NeedSlots →
      (sysS I B f K r S).PlaceAt cs.mem (spv (bodyOf (art I f).af (modelOf I f r)))) := by
  exact E2E.ReturnPinExecBytesFor.sysS_entry
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (D := D) (hI := hI)
    (hbin := hbin) (hB := hB) (f := f)
    (hfm := hfm) (r := r) (args := args)
    (cs := cs) (hX := hX) (K := K)
    (ho := ho) (S := S) (hav := hav)
    (hr := hr)

theorem runGood_sysS_of {D : List Clif.DataObject} (hI : ReturnPinStackBound.okB I = true) (hbin : BinOkWithResults I I.results D file)
    (hB : BaseOk (sys I B)) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    {K : Nat} {κ : Nat → Clif.Function → Nat}
    (hκ : (SemanticStackBound.ofInput I B (worldF I f K r)).Budget κ) (hK : κ M f = K)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + K) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (frameDrop (art I f).af + K) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)) :
    (sysS I B f K r S).RunGoodL M f (modelOf I f r) := by
  exact E2E.ReturnPinExecBytesFor.runGood_sysS_of
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (D := D) (hI := hI)
    (hbin := hbin) (hB := hB) (f := f)
    (hfm := hfm) (M := M) (r := r)
    (args := args) (cs := cs) (hX := hX)
    (K := K) (κ := κ) (hκ := hκ)
    (hK := hK) (ho := ho) (S := S)
    (hav := hav) (hr := hr) (htr := htr)
    (hout := hout)

theorem runGood_sysS {D : List Clif.DataObject} (hI : ReturnPinStackBound.okB I = true) (hbin : BinOkWithResults I I.results D file)
    (hB : BaseOk (sys I B)) {n : String} (hn : SemanticStackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (SemanticStackBound.stackFn I f) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)) :
    (sysS I B f (SemanticStackBound.bud I f) r S).RunGoodL M f (modelOf I f r) := by
  exact E2E.ReturnPinExecBytesFor.runGood_sysS
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (D := D) (hI := hI)
    (hbin := hbin) (hB := hB) (n := n)
    (hn := hn) (f := f) (hf := hf)
    (M := M) (r := r) (args := args)
    (cs := cs) (hX := hX) (ho := ho)
    (S := S) (hav := hav) (hr := hr)
    (htr := htr) (hout := hout)

theorem runGood_sysS_depth {D : List Clif.DataObject} (hI : ReturnPinStackBound.okB I = true) (hbin : BinOkWithResults I I.results D file)
    (hB : BaseOk (sys I B)) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    {S : BitVec 64 → Prop}
    (hav : OutsideAvoids S f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)) :
    (sysS I B f (I.D * M) r S).RunGoodL M f (modelOf I f r) := by
  exact E2E.ReturnPinExecBytesFor.runGood_sysS_depth
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (D := D) (hI := hI)
    (hbin := hbin) (hB := hB) (f := f)
    (hfm := hfm) (M := M) (r := r)
    (args := args) (cs := cs) (hX := hX)
    (ho := ho) (S := S) (hav := hav)
    (hr := hr) (htr := htr) (hout := hout)

theorem runGood_sysS_peak {D : List Clif.DataObject} (hI : ReturnPinStackBound.okB I = true) (hbin : BinOkWithResults I I.results D file)
    (hB : BaseOk (sys I B)) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) (F d : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    {S : BitVec 64 → Prop}
    (hav : OutsideAvoids S f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs)
    (hout : (∃ vals cm, Clif.runLoop B.env (prog I) (F + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (F + 1) cs = .trapped c)) :
    (sysS I B f (I.D * d) r S).RunGoodL d f (modelOf I f r) := by
  exact E2E.ReturnPinExecBytesFor.runGood_sysS_peak
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (D := D) (hI := hI)
    (hbin := hbin) (hB := hB) (f := f)
    (hfm := hfm) (F := F) (d := d)
    (r := r) (args := args) (cs := cs)
    (hX := hX) (ho := ho) (S := S)
    (hav := hav) (hr := hr) (hd := hd)
    (htr := htr) (hout := hout)

theorem got_of_good {D : List Clif.DataObject} (hI : ReturnPinStackBound.okB I = true) (hbin : BinOkWithResults I I.results D file)
    (hgot : GotOk I file) {f : Clif.Function} {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    {g : Clif.Function} (hg : g ∈ (prog I).funcs) (hFg : FnOk I file g) {M Kc : Nat}
    {c t : Arm.ArmState} (hgood : (sysS I B f Kc r (GotSlot I file)).GoodAt M g c t) :
    ∀ rl ∈ (art I g).fb.relocs, rl.type = .adrGotPage →
    Arm.r .PC t = wAt (art I g) (rl.offset + 4) → ∀ (rd G : Nat), rd < 31 → G % 8 = 0 →
    inR (-2 ^ 20) (2 ^ 20) (BinCheck.pageOf G - BinCheck.pageOf (wAt (art I g) rl.offset).toNat) = true →
    fileWord file (wAt (art I g) rl.offset) =
      some (adrpW rd (BinCheck.pageOf G - BinCheck.pageOf (wAt (art I g) rl.offset).toNat)) →
    fileWord file (wAt (art I g) (rl.offset + 4)) = some (ldrW rd rd (G % 4096 / 8)) → ∀ i < 8,
    ¬ RelocAtWithResults I I.results (BitVec.ofNat 64 G + BitVec.ofNat 64 i) ∧
    t.mem (BitVec.ofNat 64 G + BitVec.ofNat 64 i) =
      (Elf.loadMem file (BitVec.ofNat 64 G + BitVec.ofNat 64 i)).getD 0 := by
  exact E2E.ReturnPinExecBytesFor.got_of_good
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (D := D) (hI := hI)
    (hbin := hbin) (hgot := hgot) (f := f)
    (r := r) (hX := hX) (g := g)
    (hg := hg) (hFg := hFg) (M := M)
    (Kc := Kc) (c := c) (t := t)
    (hgood := hgood)

end E2E.ReturnPinExecBytes
