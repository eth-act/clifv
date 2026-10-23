import FV.Backend.Proof.DeadCleanupSem

/-! Witnesses for #552: the cleanup removes a `cset` whose def is dead (the boolean of an
`icmp` that the `brif` rule re-compares; Cranelift does not lower it, `machinst/lower.rs`
`lower_clif_block`), keeps a live one, and removes the first of two compares once nothing
reads its flags before the second overwrites them. -/

namespace Backend.DeadCleanup
open Backend.Proof

private def cmp01 : MInst := .aluRRR .subS .size64 .xzr (.vreg 0 .int) (.vreg 1 .int)
private def cmp0 : MInst := .aluRRImm12 .subS .size64 .xzr (.vreg 0 .int) ⟨16, false⟩
private def deadCset : MInst := .cset (.vreg 2 .int) .hi
private def liveCset : MInst := .cset (.vreg 3 .int) .lo
private def retCset : MInst := .rets [(.vreg 3 .int, .x 0)]

example : pureForm deadCset = true ∧ pureNoFlags deadCset = false := ⟨rfl, rfl⟩

/-- The `icmp` + `brif`/`select` shape: the first compare and its dead `cset` go, the second
compare and its live reader stay. -/
example : (scan 4 [cmp01, deadCset, cmp01, liveCset, retCset] []).1 =
    [cmp01, liveCset, retCset] := by decide

/-- A compare followed by a different compare (`cmp x0, #16` after `cmp x0, x1`). -/
example : (scan 4 [cmp01, cmp0, liveCset, retCset] []).1 = [cmp0, liveCset, retCset] := by
  decide

/-- A compare whose flags a `cset` reads is kept. -/
example : (scan 4 [cmp01, liveCset, cmp0, retCset] []).1 =
    [cmp01, liveCset, retCset] := by decide

example : ∃ vc : VCode, vc.blocks.size = 1 ∧
    (clean vc).blocks[0]!.insts.toList = [cmp01, liveCset, retCset] := by
  refine ⟨⟨"cset_witness", #[⟨0, #[cmp01, deadCset, cmp01, liveCset, retCset], #[], #[]⟩],
    #[.int, .int, .int, .int], 0, 0, #[]⟩, ?_, ?_⟩ <;> decide

example : pureForm (.mov .size64 (.vreg 1 .int) (.vreg 0 .int)) = true :=
  pureForm_of_pureNoFlags rfl

/-- The specification semantics satisfies the compare-overwrite premise of the cleanup. -/
example : CmpOverwrite (mspec 0) := mspec_cmpOverwrite 0

end Backend.DeadCleanup
