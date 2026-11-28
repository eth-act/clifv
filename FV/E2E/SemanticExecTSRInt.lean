import FV.E2E.SemanticExecTSR

/-!
# `binary_correct_exec_provenTSR` for programs with integer returns (#753, stage R4)

`binary_correct_exec_provenTSR`'s conclusion `ExecBytes.ExecRefinesT` (each returned value in the
ABI return register of its class) is `SemanticExecBytes.ExecRefines` (each returned value in
`x0`, `x1`, …) when the returned values are integers (`ExecBytes.ExecRefinesT.toExecRefines`).
A returned value of the whole-program run from `f`'s entry has a type of `f`'s returns
(`Clif.runLoop_returned_tys`), so `binary_correct_exec_provenTSR_int` concludes `ExecRefines` for a
program whose functions return integers only, a premise decided by evaluation.
-/
namespace E2E.SemanticExecBytes
set_option autoImplicit false
open Backend Backend.Proof E2E.LinkCheck E2E.BinCheck Elf SemanticBinary

/-- `ExecBytes.ExecRefinesT.toExecRefines` for `SemanticExecBytes.ExecRefines` (the same
definition). -/
theorem execRefines_of_execRefinesT {fb : FnBin} {base ra : BitVec 64}
    {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {R : BitVec 64 → Prop}
    {o : Clif.Outcome} (h : ExecBytes.ExecRefinesT fb base ra astep s R o)
    (hint : ∀ vals cm, o = .returned vals cm → ∀ v ∈ vals, v.ty.isInt = true) :
    ExecRefines fb base ra astep s R o := by
  have h' := ExecBytes.ExecRefinesT.toExecRefines h hint
  cases o with
  | returned vals cm => exact h'
  | trapped c => exact h'
  | stuck _ => trivial
  | outOfFuel => trivial

private theorem entry_mem {f : Clif.Function} {b : Clif.Block} (h : f.entry? = some b) :
    b ∈ f.blocks := by
  simp only [Clif.Function.entry?] at h
  cases hb : f.blocks with
  | nil => rw [hb] at h; cases h
  | cons x xs =>
    rw [hb] at h
    simp only [List.head?_cons, Option.some.injEq] at h
    rw [h]
    exact List.mem_cons_self ..

/-- **`binary_correct_exec_provenTSR` with integer returns**: when every function of the
program returns integers only, the executable machine run from `r` refines the whole-program
CLIF run with each returned value in `x0`, `x1`, … (`ExecRefines`, the conclusion of the integer
checkers' `binary_correct_exec_proven`). -/
theorem binary_correct_exec_provenTSR_int {I : SemanticStackBound.CompilerInput}
    {D : List Clif.DataObject}
    {file : ByteArray} (hI : SemanticStackBound.okBTSR I = true)
    (hcm : codeMapB I (tabOf I.results) = true)
    (hint : (prog I).funcs.all (fun g => g.sig.returns.all (·.ty.isInt)) = true)
    (hbin : BinCheck.BinOkWithResults I I.results D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I B))
    (hH : HooksSim I B) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls I I.results) f) (M : Nat)
    {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (RelocAtWithResults I I.results) (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  refine execRefines_of_execRefinesT
    (binary_correct_exec_provenTSR hI hcm hbin hgot B hB hH hf hc M hX ho hav hr htr) ?_
  intro vals cm hrun v hv
  have hfm := (Clif.Program.func?_some hf).1
  have hL := SemanticStackBound.okBTS_soundR hI
    (baseOk_F (F' := worldF I f (SemanticStackBound.bud I f) r) hB) fun _ h => .inr h
  have hcs := hr.entry
  have hLe : Clif.LInv (prog I) cs := by
    obtain ⟨b, hb, h2, h3, -, -⟩ := hcs.entry
    refine ⟨⟨by rw [hcs.func]; exact hfm, .inl ⟨b, by rw [hcs.func]; exact entry_mem hb,
      ?_, ?_⟩⟩, fun c hc => by rw [hcs.callers] at hc; cases hc⟩
    · rw [h2]; exact List.suffix_refl _
    · rw [h3]
  have hty := Clif.runLoop_returned_tys (P := prog I) hL.free (M + 1) cs vals cm hLe hrun
  have hty' : vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns := by
    simpa only [Clif.State.bottom, hcs.callers, hcs.func, List.getLast?_nil, Option.map_none,
      Option.getD_none] using hty
  have hmem : v.ty ∈ f.sig.returns.map (·.ty) := by
    rw [← show Clif.AbiParam.tys f.sig.returns = f.sig.returns.map (·.ty) from rfl, ← hty']
    exact List.mem_map.2 ⟨v, hv, rfl⟩
  obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hmem
  rw [← hpe]
  exact List.all_eq_true.1 (List.all_eq_true.1 hint f hfm) p hp

end E2E.SemanticExecBytes
