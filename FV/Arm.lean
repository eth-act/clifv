/-
Root of the `FV.Arm` library: the AArch64 model, ported from LNSym
(github.com/leanprover/LNSym @ 5c05220, Apache-2.0). See `docs/contracts/arm.md`
and `third_party/NOTICE-lnsym.md`.

This file imports every module under `FV/Arm`, so `lake build FV.Arm` builds the whole model,
its memory theory and the symbolic-simulation tactics.
-/
module

public import FV.Arm.Attr
public import FV.Arm.BitVec
public import FV.Arm.Decode
public import FV.Arm.Decode.BR
public import FV.Arm.Decode.DPI
public import FV.Arm.Decode.DPR
public import FV.Arm.Decode.DPSFP
public import FV.Arm.Decode.LDST
public import FV.Arm.Decode.Reserved
public import FV.Arm.Exec
public import FV.Arm.FromMathlib
public import FV.Arm.Insts
public import FV.Arm.Insts.BR.Compare_branch
public import FV.Arm.Insts.BR.Cond_branch_imm
public import FV.Arm.Insts.BR.Hints
public import FV.Arm.Insts.BR.Insts
public import FV.Arm.Insts.BR.Mrs
public import FV.Arm.Insts.BR.Test_branch
public import FV.Arm.Insts.BR.Uncond_branch_imm
public import FV.Arm.Insts.BR.Uncond_branch_reg
public import FV.Arm.Insts.Common
public import FV.Arm.Insts.DPI.Add_sub_imm
public import FV.Arm.Insts.DPI.Bitfield
public import FV.Arm.Insts.DPI.Extract
public import FV.Arm.Insts.DPI.Insts
public import FV.Arm.Insts.DPI.Logical_imm
public import FV.Arm.Insts.DPI.Move_wide_imm
public import FV.Arm.Insts.DPI.PC_rel_addressing
public import FV.Arm.Insts.DPR.Add_sub_carry
public import FV.Arm.Insts.DPR.Add_sub_ext_reg
public import FV.Arm.Insts.DPR.Add_sub_shifted_reg
public import FV.Arm.Insts.DPR.Conditional_compare
public import FV.Arm.Insts.DPR.Conditional_select
public import FV.Arm.Insts.DPR.Data_processing_one_source
public import FV.Arm.Insts.DPR.Data_processing_three_source
public import FV.Arm.Insts.DPR.Data_processing_two_source
public import FV.Arm.Insts.DPR.Insts
public import FV.Arm.Insts.DPR.Logical_shifted_reg
public import FV.Arm.Insts.DPSFP.Advanced_simd_across_lanes
public import FV.Arm.Insts.DPSFP.Advanced_simd_modified_immediate
public import FV.Arm.Insts.DPSFP.Advanced_simd_copy
public import FV.Arm.Insts.DPSFP.Advanced_simd_three_same
public import FV.Arm.Insts.DPSFP.Advanced_simd_two_reg_misc
public import FV.Arm.Insts.DPSFP.Conversion_between_FP_and_Int
public import FV.Arm.Insts.DPSFP.FP_compare
public import FV.Arm.Insts.DPSFP.FP_conditional_select
public import FV.Arm.Insts.DPSFP.FP_data_processing_one_source
public import FV.Arm.Insts.DPSFP.FP_data_processing_three_source
public import FV.Arm.Insts.DPSFP.FP_data_processing_two_source
public import FV.Arm.Insts.DPSFP.FP_immediate
public import FV.Arm.Insts.DPSFP.Insts
public import FV.Arm.Insts.LDST.Insts
public import FV.Arm.Insts.LDST.Reg_imm
public import FV.Arm.Insts.LDST.Reg_literal
public import FV.Arm.Insts.LDST.Reg_pair
public import FV.Arm.Insts.LDST.Reg_unscaled_imm
public import FV.Arm.Insts.Reserved.Udf
public import FV.Arm.Map
public import FV.Arm.Memory.Attr
public import FV.Arm.Memory.MemoryProofs
public import FV.Arm.Memory.Separate
public import FV.Arm.Memory.SeparateProofs
public import FV.Arm.MinTheory
public import FV.Arm.State
public import FV.Arm.Tactics.Attr
public import FV.Arm.Tactics.BvOmegaBench
public import FV.Arm.Tactics.Common
public import FV.Arm.Tactics.FetchAndDecode
public import FV.Arm.Tactics.IntroHyp
public import FV.Arm.Tactics.Simp
public import FV.Arm.Tactics.StepThms
public import FV.Arm.Tactics.Sym
public import FV.Arm.Tactics.Sym.AxEffects
public import FV.Arm.Tactics.Sym.Common
public import FV.Arm.Tactics.Sym.Context
public import FV.Arm.Tactics.Sym.FetchAndDecode
public import FV.Arm.Tactics.Sym.LCtxSearch
public import FV.Arm.Tactics.Sym.MemoryEffects
public import FV.Arm.Tactics.Sym.ProgramInfo
public import FV.Arm.Tpidr

@[expose] public section
