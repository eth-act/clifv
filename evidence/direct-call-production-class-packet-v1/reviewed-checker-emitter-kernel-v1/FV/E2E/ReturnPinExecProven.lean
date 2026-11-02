import FV.E2E.ReturnPinExecutableKernel
import FV.E2E.ReturnPinExecGot

namespace E2E.ReturnPinExecBytes
open Backend Backend.Proof E2E.LinkCheck E2E.SemanticBinary E2E.BinCheck E2E.SemanticExecBytes
set_option autoImplicit false
set_option Elab.async false
variable {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {file : ByteArray}
theorem exec_of_runGood {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : ReturnPinStackBound.okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) {B : BaseEnv} (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {f : Clif.Function} (hfm : f ∈ (prog I).funcs) {M K : Nat}
    {r : Arm.ArmState} (hX : (imageOf file).Intact r)
    (hent : AbiEntry (art I f).fb (art I f).base (xreg 30 r) (modelOf I f r))
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → RelocAtWithResults I I.results a) {o : Clif.Outcome}
    (hA : ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r) o)
    (hgood : ((∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c)) →
      (sys I B).RunGoodL M f (modelOf I f r) ∧
        (sysS I B f K r (GotSlot I file)).RunGoodL M f (modelOf I f r)) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAtWithResults I I.results) o := by
  exact E2E.ReturnPinExecBytesFor.exec_of_runGood
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (I := I) (D := D)
    (file := file) (hI := hI) (hcm := hcm)
    (hbin := hbin) (hgot := hgot) (B := B)
    (hB := hB) (hH := hH) (f := f)
    (hfm := hfm) (M := M) (K := K)
    (r := r) (hX := hX) (hent := hent)
    (hd := hd) (o := o) (hA := hA)
    (hgood := hgood)

theorem binary_correct_exec_proven {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : ReturnPinStackBound.okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls I I.results) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAtWithResults I I.results)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  exact E2E.ReturnPinExecBytesFor.binary_correct_exec_proven
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (I := I) (D := D)
    (file := file) (hI := hI) (hcm := hcm)
    (hbin := hbin) (hgot := hgot) (B := B)
    (hB := hB) (hH := hH) (n := n)
    (f := f) (hf := hf) (hc := hc)
    (M := M) (r := r) (args := args)
    (cs := cs) (hX := hX) (ho := ho)
    (hav := hav) (hr := hr) (htr := htr)

theorem binary_correct_exec_depth_proven {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : ReturnPinStackBound.okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAtWithResults I I.results)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  exact E2E.ReturnPinExecBytesFor.binary_correct_exec_depth_proven
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (I := I) (D := D)
    (file := file) (hI := hI) (hcm := hcm)
    (hbin := hbin) (hgot := hgot) (B := B)
    (hB := hB) (hH := hH) (n := n)
    (f := f) (hf := hf) (M := M)
    (r := r) (args := args) (cs := cs)
    (hX := hX) (ho := ho) (hav := hav)
    (hr := hr) (htr := htr)

theorem binary_correct_exec_peak_proven {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : ReturnPinStackBound.okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv) (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAtWithResults I I.results)
      (Clif.runLoop B.env (prog I) (F + 1) cs) := by
  exact E2E.ReturnPinExecBytesFor.binary_correct_exec_peak_proven
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (I := I) (D := D)
    (file := file) (hI := hI) (hcm := hcm)
    (hbin := hbin) (hgot := hgot) (B := B)
    (hB := hB) (hH := hH) (n := n)
    (f := f) (hf := hf) (F := F)
    (d := d) (r := r) (args := args)
    (cs := cs) (hX := hX) (ho := ho)
    (hav := hav) (hr := hr) (hd := hd)
    (htr := htr)

end E2E.ReturnPinExecBytes
