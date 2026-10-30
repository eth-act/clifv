import FV.Backend.Isel

/-!
The ISLE float data-movement roots of S11e4 (#238) on the lowering itself: `f32const`/`f64const`
(584/585: `fmov s/d, #imm`, `movi` for zero), `load.f32`/`load.f64` (1047/1048: `ldr s/d`),
`store` of an `f32`/`f64` (1073/1074: `str s/d`), the float arm of `select` (971: the
condition's flag instruction, then `fcsel`) and `bitcast` (1080/1083/1084/1085: `fmov` between
the register files, or no code). These are the instruction selections Cranelift 0.136.1 makes
for the same CLIF (`lower.isle:63/68/2625/2628/2746/2750/2267/2779/2793/2798/2803`).
`lake build FVTest.Backend.FloatMove`.
-/

open Backend

/-- The first function of a CLIF text, lowered. -/
def lowerTextF (src : String) : Except String VCode :=
  match (Clif.parseFile src).funcs with
  | p :: _ => match p.func with
    | .ok f => lowerFunction f
    | .error _ => .error "parse error"
  | [] => .error "no function"

/-- The entry block's instructions of a lowering. -/
def entryF (src : String) : Option (List MInst) :=
  match lowerTextF src with
  | .ok vc => vc.blocks[0]?.map (·.insts.toList)
  | .error _ => none

/-- The flags of a plain `load`/`store` (`MemFlags::new()`: may trap with `heap_oob`). -/
def plainFlags : Clif.MemFlags :=
  { trapCode := some .heapOob, aligned := false, readonly := false, canMove := false,
    endianness := none }

-- `f32const 1.0`: `fmov s, #1.0` (Cranelift `constants.clif`: `fmov d0, #1` for `f64const 0x1.0`)
#guard entryF "function %c() -> f32 {\nblock0:\n    v0 = f32const 0x1.0p0\n    return v0\n}\n" ==
  some [.args [], .fpuMoveFPImm (.vreg 1 .float) ⟨0x70, .size32⟩ .size32, .rets [(.vreg 1 .float, .v 0)]]

-- `select.f32` on an `i8`: `ands wzr, w0, #255; fcsel s, s, s, ne` (Cranelift `select.clif`,
-- `%select_f32`)
#guard entryF "function %s(i8, f32, f32) -> f32 {\nblock0(v0: i8, v1: f32, v2: f32):\n    v3 = select v0, v1, v2\n    return v3\n}\n" ==
  some [.args [(.vreg 0 .int, .x 0), (.vreg 1 .float, .v 0), (.vreg 2 .float, .v 1)],
    .aluRRImmLogic .andS .size32 .xzr (.vreg 0 .int) ⟨255, .size32⟩,
    .fpuCSel .size32 (.vreg 4 .float) (.vreg 1 .float) (.vreg 2 .float) .ne, .rets [(.vreg 4 .float, .v 0)]]

-- `select.f64` on an `i32`: `subs wzr, w0, wzr; fcsel d, d, d, ne`
#guard entryF "function %s(i32, f64, f64) -> f64 {\nblock0(v0: i32, v1: f64, v2: f64):\n    v3 = select v0, v1, v2\n    return v3\n}\n" ==
  some [.args [(.vreg 0 .int, .x 0), (.vreg 1 .float, .v 0), (.vreg 2 .float, .v 1)],
    .aluRRR .subS .size32 .xzr (.vreg 0 .int) .xzr,
    .fpuCSel .size64 (.vreg 4 .float) (.vreg 1 .float) (.vreg 2 .float) .ne, .rets [(.vreg 4 .float, .v 0)]]

-- `load.f32 v0+8`: `ldr s, [x0, #8]`; `store` of an `f64`: `str d, [x0]`
#guard entryF "function %z(i64) -> f32 {\nblock0(v0: i64):\n    v1 = load.f32 v0+8\n    return v1\n}\n" ==
  some [.args [(.vreg 0 .int, .x 0)], .fpuLoad .size32 (.vreg 2 .float) (.unsignedOffset (.vreg 0 .int) 8) plainFlags,
    .rets [(.vreg 2 .float, .v 0)]]
#guard entryF "function %z(i64, f64) {\nblock0(v0: i64, v1: f64):\n    store v1, v0\n    return\n}\n" ==
  some [.args [(.vreg 0 .int, .x 0), (.vreg 1 .float, .v 0)],
    .fpuStore .size64 (.vreg 1 .float) (.unsignedOffset (.vreg 0 .int) 0) plainFlags, .rets []]
