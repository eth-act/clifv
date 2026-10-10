import FV.Backend.DeadCleanup

namespace Backend.DeadCleanup

theorem pureForm_targets {m : MInst} (h : pureForm m = true) : m.targets = [] := by
  cases m <;> simp [pureForm, MInst.targets] at *

theorem pureForm_keptDefs {m : MInst} (h : pureForm m = true) :
    m.keptDefs = none ∧ m.normalDead = none := by
  cases m <;> simp [pureForm, MInst.keptDefs, MInst.normalDead, MInst.isBranch] at *

/-- Filtering does not introduce or reorder instructions. -/
theorem scan_sublist (nregs : Nat) (ms : List MInst) (live : List Nat) :
    (scan nregs ms live).1.Sublist ms := by
  induction ms with
  | nil => simp [scan]
  | cons m ms ih =>
    simp only [scan]
    split
    · exact (ih).cons m
    · exact (ih).cons_cons m

/-- A non-whitelisted final instruction remains the final instruction. -/
theorem scan_last (nregs : Nat) (ms : List MInst) (m : MInst) (live : List Nat)
    (hm : pureForm m = false) : (scan nregs (ms ++ [m]) live).1.getLast? = some m := by
  induction ms with
  | nil => simp [scan, discard, hm]
  | cons a ms ih =>
    simp only [List.cons_append, scan]
    split
    · exact ih
    · cases hk : (scan nregs (ms ++ [m]) live).1 with
      | nil => simpa [hk] using ih
      | cons x xs => simpa [hk] using ih

/-- Every instruction retained in a block came from that block. -/
theorem cleanBlock_inst_mem (vc : VCode) (idx : Nat) (b : VBlock) (m : MInst)
    (h : m ∈ (cleanBlock vc idx b).insts.toList) : m ∈ b.insts.toList := by
  exact (scan_sublist vc.classes.size b.insts.toList (exitLive vc idx b)).subset (by
    simpa [cleanBlock] using h)

/-- The cleanup changes no block identity or edge interface. -/
theorem cleanBlock_interface (vc : VCode) (idx : Nat) (b : VBlock) :
    (cleanBlock vc idx b).label = b.label ∧
    (cleanBlock vc idx b).params = b.params ∧
    (cleanBlock vc idx b).branchArgs = b.branchArgs := ⟨rfl, rfl, rfl⟩

/-- Classes and frame/rule metadata remain unchanged. -/
theorem clean_metadata (vc : VCode) :
    (clean vc).name = vc.name ∧ (clean vc).classes = vc.classes ∧
    (clean vc).slotBytes = vc.slotBytes ∧ (clean vc).outgoing = vc.outgoing ∧
    (clean vc).rulesFired = vc.rulesFired ∧ (clean vc).blocks.size = vc.blocks.size := by
  simp [clean]

/-! Non-vacuity: a real redundant integer producer is deleted; a real live
producer used by `rets` is retained. Both branches of the scan are exercised
without native proof certificates. -/

def deadMvn : MInst := .aluRRR .orrNot .size64 (.vreg 2 .int) .xzr (.vreg 1 .int)
def liveBic : MInst := .aluRRR .andNot .size64 (.vreg 3 .int) (.vreg 0 .int) (.vreg 1 .int)
def liveReturn : MInst := .rets [(.vreg 3 .int, .x 0)]

example : (scan 4 [deadMvn, liveBic, liveReturn] []).1 = [liveBic, liveReturn] := by decide
example : (scan 4 [deadMvn] [2]).1 = [deadMvn] := by decide
example : (scan 4 [.aluRRR .orrNot .size64 (.x 7) .xzr (.vreg 1 .int)] []).1 =
    [.aluRRR .orrNot .size64 (.x 7) .xzr (.vreg 1 .int)] := by decide
example : (scan 4 [.aluRRR .subS .size64 (.vreg 2 .int) (.vreg 0 .int)
    (.vreg 1 .int)] []).1 =
    [.aluRRR .subS .size64 (.vreg 2 .int) (.vreg 0 .int) (.vreg 1 .int)] := by decide
example : pureForm liveBic = true ∧ liveBic.targets = [] ∧
    liveBic.keptDefs = none ∧ liveBic.normalDead = none := by
  exact ⟨rfl, pureForm_targets rfl, (pureForm_keptDefs rfl).1, (pureForm_keptDefs rfl).2⟩
example : ∃ vc : VCode, vc.blocks.size = 1 ∧
    (clean vc).blocks[0]!.insts.toList = [liveBic, liveReturn] := by
  refine ⟨⟨"cleanup_witness", #[⟨0, #[deadMvn, liveBic, liveReturn], #[], #[]⟩],
    #[.int, .int, .int, .int], 0, 0, #[]⟩, ?_, ?_⟩ <;> decide

end Backend.DeadCleanup
