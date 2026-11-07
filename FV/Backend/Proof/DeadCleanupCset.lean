import FV.Backend.Proof.DeadCleanupSem

/-! Witnesses for #552: the cleanup removes a `cset` whose def is dead (the boolean of an
`icmp` that the `brif` rule re-compares; Cranelift does not lower it, `machinst/lower.rs`
`lower_clif_block`), keeps a live one, and removes the first of two compares once nothing
reads its flags before the second overwrites them, for integer and float (`fcmp`, #967)
compares, also across the float constant moves of a `select` (`fmov #imm`, `movi`), and drops the
head of a dead chain (the operand extension of a dropped compare, #968). -/

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
    #[.int, .int, .int, .int], 0, 0, #[], #[]⟩, ?_, ?_⟩ <;> decide

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
    ⟨1, #[cmp0, liveCset, retCset], #[], #[]⟩], #[.int, .int, .int, .int], 0, 0, #[], #[]⟩, ?_⟩
  decide +kernel

example : ∃ vc : VCode, (clean vc).blocks[0]!.insts.toList = [cmp01, .jump 1] := by
  refine ⟨⟨"cset_jump_live", #[⟨0, #[cmp01, .jump 1], #[], #[]⟩,
    ⟨1, #[liveCset, cmp0, retCset], #[], #[]⟩], #[.int, .int, .int, .int], 0, 0, #[], #[]⟩, ?_⟩
  decide +kernel

example : JumpPlain (mspec 0) := mspec_jumpPlain 0

private def fcmp00 : MInst := .fpuCmp .size32 (.vreg 0 .float) (.vreg 0 .float)
private def fcmp01 : MInst := .fpuCmp .size64 (.vreg 0 .float) (.vreg 1 .float)

/-- The float compare (#967): `fcmp` is a compare form, and its specification writes only the
flags (`fcmpFlags`), so the compare-overwrite premise covers it. -/
example : cmpForm fcmp00 = true ∧ cmpForm fcmp01 = true := ⟨rfl, rfl⟩

example (w : Arm.ArmState) : ∃ w', mspec 0 fcmp01 [0#128, 0#128] w = some ([], w', .next) :=
  ⟨_, rfl⟩

/-- The `fcmp` + `select`/`brif` shape of an `*_is_nan_*` test (`fcmp s0, s0`): the first
float compare and its dead `cset` go, the second float compare and its live reader stay. -/
example : (scan 4 [fcmp00, deadCset, fcmp00, liveCset, retCset] []).1 =
    [fcmp00, liveCset, retCset] := by decide

/-- A float compare whose flags a `cset` reads is kept; an integer compare whose flags a float
compare overwrites goes. -/
example : (scan 4 [fcmp01, liveCset, cmp01, retCset] []).1 =
    [fcmp01, liveCset, cmp01, retCset] := by decide

example : (scan 4 [cmp01, fcmp01, liveCset, retCset] []).1 = [fcmp01, liveCset, retCset] := by
  decide

/-- The whole pass on a one-block function with float registers drops the dead `fcmp`. -/
example : ∃ vc : VCode, vc.blocks.size = 1 ∧
    (prune vc).blocks[0]!.insts.toList = [fcmp00, liveCset, retCset] := by
  refine ⟨⟨"fcmp_witness", #[⟨0, #[fcmp00, deadCset, fcmp00, liveCset, retCset], #[], #[]⟩],
    #[.float, .int, .int, .int], 0, 0, #[], #[]⟩, ?_, ?_⟩ <;> decide +kernel

private def fcmpLe : MInst := .fpuCmp .size32 (.vreg 0 .float) (.vreg 1 .float)
private def fmovOne : MInst := .fpuMoveFPImm (.vreg 6 .float) ⟨0x70#8, .size32⟩ .size32
private def moviZero : MInst := .vecDupImm (.vreg 7 .float) ⟨0#8, 0, false, false⟩ false .size32x2
private def fcselLs : MInst :=
  .fpuCSel .size32 (.vreg 8 .float) (.vreg 6 .float) (.vreg 7 .float) .ls
private def retF : MInst := .rets [(.vreg 8 .float, .v 0)]

/-- The float constant moves (`fmov s, #1.0`, `movi v.2s, #0`) are flag-free producers: their
specification keeps the world, and from a world whose flags a compare wrote they step alike. -/
example : flagFree fmovOne = true ∧ flagFree moviZero = true := ⟨rfl, rfl⟩

example (w : Arm.ArmState) : ∃ outs, mspec 0 fmovOne [] w = some (outs, w, .next) :=
  ⟨_, by simp only [mspec, ispec, fmovOne]; rfl⟩

example (w : Arm.ArmState) : mspec 0 moviZero [] w = some ([0#128], w, .next) := by
  simp [mspec, ispec, defOut, moviVal_zero, moviZero]

example (p : Arm.PState) (w : Arm.ArmState) :
    mspec 0 moviZero [] (Arm.write_pstate p w) =
      (mspec 0 moviZero [] w).map (fun r => (r.1, Arm.write_pstate p r.2.1, r.2.2)) :=
  mspec_flagFree_pstate rfl p w

/-- `select_le_f32` (`fcmp le`, two `f32const`s, `select`; #967): the dead first `fcmp` goes
across the constant moves between it and the `fcmp` of the `select`, which stays with them. -/
example : (scan 9 [fcmpLe, deadCset, fmovOne, moviZero, fcmpLe, fcselLs, retF] []).1 =
    [fmovOne, moviZero, fcmpLe, fcselLs, retF] := by decide

/-- An unused constant move goes. -/
example : (scan 9 [fmovOne, moviZero, retF] [8]).1 = [retF] := by decide

private def fcselEq : MInst :=
  .fpuCSel .size32 (.vreg 8 .float) (.vreg 6 .float) (.vreg 7 .float) .eq

/-- **The head of a dead chain** (#968, `select-float.clif` `%select_icmp_i8_f32`: `icmp` of an
`i8`, then a float `select` that compares again): the lowering emits `uxtb; cmp; cset` for the
`icmp` and `uxtb; cmp; fcsel` for the `select`. A round with every read live (`allUses`) drops
the dead `cset` and the first compare, but keeps the first `uxtb`, whose only reader is that
compare. The boundary of the pass is the reads of what that round keeps (`exitLive`), so the
pass drops the `uxtb` too: Cranelift's single `uxtb; cmp; fcsel`. -/
example : ∃ vc : VCode,
    (scan vc.classes.size vc.blocks[0]!.insts.toList (allUses vc)).1 =
      [ext4, ext5, cmpE5, fcselEq, retF] ∧
    (prune vc).blocks[0]!.insts.toList = [ext5, cmpE5, fcselEq, retF] := by
  refine ⟨⟨"dead_chain", #[⟨0, #[ext4, cmpE4, deadCset, ext5, cmpE5, fcselEq, retF], #[], #[]⟩],
    #[.int, .int, .int, .int, .int, .int, .float, .float, .float], 0, 0, #[], #[]⟩, ?_, ?_⟩ <;>
    decide +kernel

/-- A chain whose head is read elsewhere stays: the `uxtb` of the dropped compare also feeds a
returned value. -/
private def ret4 : MInst := .rets [(.vreg 8 .float, .v 0), (.vreg 4 .int, .x 0)]

example : ∃ vc : VCode,
    (prune vc).blocks[0]!.insts.toList = [ext4, ext5, cmpE5, fcselEq, ret4] := by
  refine ⟨⟨"live_chain", #[⟨0, #[ext4, cmpE4, deadCset, ext5, cmpE5, fcselEq, ret4], #[], #[]⟩],
    #[.int, .int, .int, .int, .int, .int, .float, .float, .float], 0, 0, #[], #[]⟩, ?_⟩
  decide +kernel

/-- A chain head that a kept instruction of another block reads stays: the boundary holds every
read of the code that the first round keeps, in every block (`ret34` returns the `uxtb`). -/
private def ret34 : MInst := .rets [(.vreg 3 .int, .x 0), (.vreg 4 .int, .x 1)]

example : ∃ vc : VCode,
    (prune vc).blocks[0]!.insts.toList = [ext4, ext5, cmpE5, liveCset, .jump 1] := by
  refine ⟨⟨"cross_block_chain",
    #[⟨0, #[ext4, cmpE4, deadCset, ext5, cmpE5, liveCset, .jump 1], #[], #[]⟩,
      ⟨1, #[ret34], #[], #[]⟩], #[.int, .int, .int, .int, .int, .int], 0, 0, #[], #[]⟩, ?_⟩
  decide +kernel

end Backend.DeadCleanup
