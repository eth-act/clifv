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

/-- A compare whose flags a `cset` reads is kept; so is one whose flags reach the block end. -/
example : (scan 4 [cmp01, liveCset, cmp0, retCset] []).1 =
    [cmp01, liveCset, cmp0, retCset] := by decide

private def movA : MInst := .mov .size64 (.vreg 6 .int) (.vreg 1 .int)
private def ret2 : MInst := .rets [(.vreg 3 .int, .x 0), (.vreg 6 .int, .x 1)]
private def ext4 : MInst := .extend (.vreg 4 .int) (.vreg 0 .int) false 8 32
private def cmpE4 : MInst := .aluRRImm12 .subS .size32 .xzr (.vreg 4 .int) ⟨45, false⟩
private def ext5 : MInst := .extend (.vreg 5 .int) (.vreg 0 .int) false 8 32
private def cmpE5 : MInst := .aluRRImm12 .subS .size32 .xzr (.vreg 5 .int) ⟨45, false⟩

/-- A live flag-free producer between the compares (`cmp; mov; cmp; csel`): the first
compare goes, the producer stays. -/
example : (scan 7 [cmp01, movA, cmp0, liveCset, ret2] []).1 =
    [movA, cmp0, liveCset, ret2] := by
  decide

/-- The `icmp` of an `i8` (`uxtb; cmp`) whose user compares again (`uxtb; cmp; b.eq`): the first
compare goes, and with it its extension, as in Cranelift's single `uxtb; cmp`. -/
example : (scan 7 [ext4, cmpE4, ext5, cmpE5, liveCset, retCset] []).1 =
    [ext5, cmpE5, liveCset, retCset] := by decide

example : ∃ vc : VCode, vc.blocks.size = 1 ∧
    (clean vc).blocks[0]!.insts.toList = [cmp01, liveCset, retCset] := by
  refine ⟨⟨"cset_witness", #[⟨0, #[cmp01, deadCset, cmp01, liveCset, retCset], #[], #[]⟩],
    #[.int, .int, .int, .int], 0, 0, #[]⟩, ?_, ?_⟩ <;> decide

example : pureForm (.mov .size64 (.vreg 1 .int) (.vreg 0 .int)) = true :=
  pureForm_of_pureNoFlags rfl

/-- The specification semantics satisfies the compare-overwrite premise of the cleanup. -/
example : CmpOverwrite (mspec 0) := mspec_cmpOverwrite 0

private def lslDead : MInst := .aluRRImmShift .lsl .size64 (.vreg 2 .int) (.vreg 0 .int) 1
private def orr3 : MInst := .aluRRR .orr .size64 (.vreg 3 .int) (.vreg 1 .int) (.vreg 0 .int)
private def asr6 : MInst := .aluRRImmShift .asr .size64 (.vreg 6 .int) (.vreg 1 .int) 63

/-- An unused shift goes (#555: the `ishl` a shifted-operand `bor` folds). -/
example : (scan 4 [lslDead, orr3, retCset] []).1 = [orr3, retCset] := by decide

/-- A live shift between two compares stays; the first compare goes (#552). -/
example : (scan 7 [cmp01, asr6, cmp0, liveCset, ret2] []).1 =
    [asr6, cmp0, liveCset, ret2] := by decide

/-- Flags are tracked within a block only: an unused compare before a `jump` stays, even when
the successor compares first (the cross-block rule never changed generated code, #608), and
so does one whose successor reads the flags first. -/
example : ∃ vc : VCode, (clean vc).blocks[0]!.insts.toList = [cmp01, .jump 1] := by
  refine ⟨⟨"cset_jump", #[⟨0, #[cmp01, .jump 1], #[], #[]⟩,
    ⟨1, #[cmp0, liveCset, retCset], #[], #[]⟩], #[.int, .int, .int, .int], 0, 0, #[]⟩, ?_⟩
  decide +kernel

example : ∃ vc : VCode, (clean vc).blocks[0]!.insts.toList = [cmp01, .jump 1] := by
  refine ⟨⟨"cset_jump_live", #[⟨0, #[cmp01, .jump 1], #[], #[]⟩,
    ⟨1, #[liveCset, cmp0, retCset], #[], #[]⟩], #[.int, .int, .int, .int], 0, 0, #[]⟩, ?_⟩
  decide +kernel

example : JumpPlain (mspec 0) := mspec_jumpPlain 0

end Backend.DeadCleanup
