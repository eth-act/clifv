module

public import FV.Concurrency.LinkedMachine
public import FV.Concurrency.CallLoadData

@[expose] public section

/-!
# The linked machine of the compiled caller and the compiled `atomic_load` (#473, calls)

The link `link2` of `CallSeg.WitnessC`'s two compiled functions: the compiled `atomic_load`
(`act vcpL rfL` at `0x20000`, named `ld`) and its caller (`act vcpC rfC` at `0x30000`, named
`f`). It is well formed (`ok2`), its hook of `bl ld` is `enterL` (`H_ld`), the caller's `bl ld`
line enters the callee's code (`M_blC`), the callee's `ret` into the caller's code switches back
to the caller's program (`M_retL`, as `MC2`), and the machine agrees with both activations at
their lines other than `ret` (`agreesAtC`, `agreesAtL`).

Checks by `native_decide` (witness only).
-/

namespace Concurrency.LinkedMachine.Witness

open Arm Backend Backend.Proof CallSeg.WitnessC RealizeCompiled RealizeCompiled.Witness
  RealizeCompiled.WitnessL
open ArmAllocThread.Witness (act ok_getD)

/-- The compiled `atomic_load` at `0x20000`. -/
def ldF : LFn := { LFn.of (act vcpL rfL) with base := 0x20000#64 }

/-- The compiled caller at `0x30000`. -/
def callerF : LFn := { LFn.of (act vcpC rfC) with base := 0x30000#64 }

/-- **The link of the two functions.** -/
def link2 : Link := ⟨[("ld", ldF), ("f", callerF)]⟩

theorem facts2 : (act vcpL rfL).fa.layout.toBool = true ∧
    (labelOffsets (act vcpL rfL).fa.lines).toBool = true ∧
    (act vcpC rfC).fa.layout.toBool = true ∧
    (labelOffsets (act vcpC rfC).fa.lines).toBool = true ∧
    0 < (act vcpL rfL).fb.words.size ∧ 0 < (act vcpC rfC).fb.words.size ∧
    0x20000 + 4 * (act vcpL rfL).fb.words.size ≤ 0x30000 ∧
    0x30000 + 4 * (act vcpC rfC).fb.words.size ≤ 2 ^ 64 := by
  native_decide

theorem laidL : ldF.LaidOut where
  layout := ok_getD facts2.1
  lm := ok_getD facts2.2.1
  pos := facts2.2.2.2.2.1
  fit := by
    show (0x20000#64 : BitVec 64).toNat + 4 * (act vcpL rfL).fb.words.size ≤ 2 ^ 64
    have := facts2.2.2.2.2.2.2.1
    simp only [BitVec.toNat_ofNat]
    omega

theorem laidC : callerF.LaidOut where
  layout := ok_getD facts2.2.2.1
  lm := ok_getD facts2.2.2.2.1
  pos := facts2.2.2.2.2.2.1
  fit := by
    show (0x30000#64 : BitVec 64).toNat + 4 * (act vcpC rfC).fb.words.size ≤ 2 ^ 64
    have := facts2.2.2.2.2.2.2.2
    simp only [BitVec.toNat_ofNat]
    omega

theorem mem_ld : ("ld", ldF) ∈ link2.fns := .head _

theorem mem_caller : ("f", callerF) ∈ link2.fns := .tail _ (.head _)

/-- **The link is well formed.** -/
theorem ok2 : link2.Ok where
  sep := by
    refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    refine ⟨by decide, .inl ?_⟩
    show (0x20000#64 : BitVec 64).toNat + 4 * (act vcpL rfL).fb.words.size ≤
      (0x30000#64 : BitVec 64).toNat
    have := facts2.2.2.2.2.2.2.1
    simp only [BitVec.toNat_ofNat]
    omega
  laid := by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact laidL
    · rw [List.mem_singleton] at hp
      subst hp
      exact laidC

theorem find_ld : link2.find "ld" = some ldF := rfl

/-- **The link's hook of `bl ld` is `enterL`.** -/
theorem H_ld (s : ArmState) : link2.H.call (some "ld") s = enterL s := by
  rw [Link.H_call_some find_ld]
  rfl

/-- The caller's line 24 is `bl ld` (as a check). -/
def blB : Bool :=
  match ((act vcpC rfC).fa.lines.toList[24]? : Option Line) with
  | some (Line.ins (Insn.bl n) none) => n == "ld"
  | _ => false

theorem blB_eq : blB = true := by native_decide

theorem blC : callerF.fa.lines.toList[24]? = some (.ins (.bl "ld") none) := by
  have h := blB_eq
  unfold blB at h
  show (act vcpC rfC).fa.lines.toList[24]? = _
  split at h
  · rename_i n hn
    simp only [beq_iff_eq] at h
    subst h
    exact hn
  · cases h

/-- **The caller's `bl ld` enters the compiled `atomic_load`** (`Link.M_bl`). -/
theorem M_blC {s : ArmState} (hs : s.program = RC.fb.program RC.base)
    (hpc : Arm.r .PC s = RC.pcOf 24) : link2.M s = enterL s :=
  Link.M_bl ok2 mem_caller blC hs hpc find_ld

/-- **The callee's `ret` into the caller's code** switches back to the caller's program
(`Link.M_ret_x30`, as `MC2`'s return). -/
theorem M_retL {s : ArmState} (hs : s.program = pL) (hr : ldF.IsRet s)
    (herr : Arm.r .ERR s = .None) (ha : callerF.InRange (E2E.xreg 30 s)) :
    link2.M s = set_program (w .PC (E2E.xreg 30 s) s) (RC.fb.program RC.base) :=
  Link.M_ret_x30 ok2 mem_ld mem_caller hs hr herr ha

/-- **The machine agrees with the caller's activation** (`Link.agreesAt_M`). -/
theorem agreesAtC : ArmAllocThread.AgreesAt (link2.act callerF sC0 0 GL) link2.M :=
  Link.agreesAt_M ok2 mem_caller sC0 0 GL

/-- **The machine agrees with the callee's activation entered by a call** (`Link.agreesAt_M`). -/
theorem agreesAtL (s : ArmState) :
    ArmAllocThread.AgreesAt (link2.act ldF (enterL s) 0 RC.F) link2.M :=
  Link.agreesAt_M ok2 mem_ld (enterL s) 0 RC.F

end Concurrency.LinkedMachine.Witness
