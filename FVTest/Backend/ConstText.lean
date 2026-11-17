import FV.Backend.Isel

/-! # #1069: the reason for a constant outside E names its CLIF opcode

The parser stores `f16const` as `Inst.iconst .f16`; `instData` reported it as `iconst.f16`. -/

#guard Backend.instData default (.iconst .f16 0) matches .error "f16const"
#guard Backend.instData default (.iconst .i128 0) matches .error "iconst.i128"
