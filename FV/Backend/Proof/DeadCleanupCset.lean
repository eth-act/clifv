import FV.Backend.Proof.DeadCleanupStructure

/-! Witnesses for #552: the cleanup removes a `cset` whose def is dead (the boolean of an
`icmp` that the `brif` rule re-compares; Cranelift does not lower it, `machinst/lower.rs`
`lower_clif_block`), keeps a live one, and keeps the compare (it writes the flags). -/

namespace Backend.DeadCleanup

private def cmp01 : MInst := .aluRRR .subS .size64 .xzr (.vreg 0 .int) (.vreg 1 .int)
private def deadCset : MInst := .cset (.vreg 2 .int) .hi
private def liveCset : MInst := .cset (.vreg 3 .int) .lo
private def retCset : MInst := .rets [(.vreg 3 .int, .x 0)]

example : pureForm deadCset = true ∧ pureNoFlags deadCset = false := ⟨rfl, rfl⟩

example : (scan 4 [cmp01, deadCset, cmp01, liveCset, retCset] []).1 =
    [cmp01, cmp01, liveCset, retCset] := by decide

example : ∃ vc : VCode, vc.blocks.size = 1 ∧
    (clean vc).blocks[0]!.insts.toList = [cmp01, cmp01, liveCset, retCset] := by
  refine ⟨⟨"cset_witness", #[⟨0, #[cmp01, deadCset, cmp01, liveCset, retCset], #[], #[]⟩],
    #[.int, .int, .int, .int], 0, 0, #[]⟩, ?_, ?_⟩ <;> decide

example : pureForm (.mov .size64 (.vreg 1 .int) (.vreg 0 .int)) = true :=
  pureForm_of_pureNoFlags rfl

end Backend.DeadCleanup
