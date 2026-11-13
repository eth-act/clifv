import FV.Opt.ConstPhi
import FV.Clif.Parse

/-!
Tests of `Opt.ConstPhi` (#990): the solver agrees with Cranelift's `remove_constant_phis`, the
checker `cpOk` accepts the solutions and rejects corrupted ones.

* Filetests (`runtests/br_table.clif`, `runtests/brif.clif`, `runtests/fibonacci.clif` of the
  pinned wasmtime v49.0.1): the expected functions are the stock compiler's input after the pass.
  Lean compiles `%br_table_upper_reg`, `%brif_different_args` and `%fuzzgen_2` given these
  expected functions (with `--stock-config`) to the stock compiler's bytes.
* Crate functions (`examples/survey`, cg_clif's Cranelift 0.136.1 at `opt_level=none`): each
  expected function is cg_clif's own dump after `Context::optimize` (`*.opt.clif`; the input is
  `*.unopt.clif`; the `uN:M` names renamed `%uN_M`, source locations and comments dropped, the
  callee signatures written out). On the 3156 of the 4549 crate functions of `examples/fv-demo`
  and `examples/survey` that the Lean parser reads, `apply` of the solution of the function
  without unreachable blocks equals cg_clif's optimised function (76 change, `cpOk` accepts
  all 76).

`lake build FVTest.Opt.ConstPhiTest`.
-/

open Opt Opt.ConstPhi

namespace ConstPhiTest

/-- The first function of a CLIF text (`default` if it does not parse). -/
def fn (src : String) : Clif.Function :=
  match (Clif.parseFile src).funcs with
  | p :: _ => match p.func with
    | .ok f => f
    | .error _ => default
  | [] => default

/-- `cpOk` on the solution of `f` without its unreachable blocks. -/
def accepts (f : Clif.Function) : Bool :=
  let f1 := removeUnreachable f
  cpOk f1 (solve f1)

/-! ## Filetests -/

def brTableUpperReg := fn "function %br_table_upper_reg() -> i32 {
block0:
    v0 = iconst.i32 -555163938
    v1 = iconst.i8 -34
    jump block1(v0, v1)

block1(v2: i32, v3: i8):
    v4 = ishl.i32 v2, v2
    v5 = rotr v4, v3
    br_table v5, block2, [block2, block2, block3]

block2 cold:
    v100 = iconst.i32 100
    return v100

block3 cold:
    v200 = iconst.i32 200
    return v200
}"

def brTableUpperReg' := fn "function %br_table_upper_reg() -> i32 {
block0:
    v0 = iconst.i32 -555163938
    v1 = iconst.i8 -34
    jump block1

block1:
    v4 = ishl.i32 v0, v0
    v5 = rotr v4, v1
    br_table v5, block2, [block2, block2, block3]

block2 cold:
    v100 = iconst.i32 100
    return v100

block3 cold:
    v200 = iconst.i32 200
    return v200
}"

def brifDifferentArgs := fn "function %brif_different_args(i8) -> i8 {
block0(v0: i8):
    brif v0, block1(v0, v0), block2(v0)

block1(v1: i8, v2: i8):
    v3 = iadd v1, v2
    return v3

block2(v4: i8):
    return v4
}"

def brifDifferentArgs' := fn "function %brif_different_args(i8) -> i8 {
block0(v0: i8):
    brif v0, block1, block2

block1:
    v3 = iadd v0, v0
    return v3

block2:
    return v0
}"

def fuzzgen1 := fn "function %fuzzgen_1() -> i8 system_v {
block0:
    v1 = iconst.i8 35
    brif v1, block1(v1), block1(v1)

block1(v0: i8):
    return v0
}"

def fuzzgen2 := fn "function %fuzzgen_2(i16) -> i16, i16 system_v {
block0(v0: i16):
    brif v0, block1(v0, v0), block2(v0, v0)

block1(v1: i16, v2: i16):
    brif v1, block2(v2, v2), block2(v2, v2)

block2(v3: i16, v4: i16):
    return v3, v4
}"

def fuzzgen2' := fn "function %fuzzgen_2(i16) -> i16, i16 system_v {
block0(v0: i16):
    brif v0, block1, block2

block1:
    brif v0, block2, block2

block2:
    return v0, v0
}"

def fibonacci := fn "function %fibonacci(i32) -> i32 {
block0(v0: i32):
    v21 = iconst.i32 2
    v1 = icmp ule v0, v21
    v2 = iconst.i32 1
    brif v1, block3(v2), block1(v0, v2)

block1(v4: i32, v5:i32):
    v6 = iconst.i32 1
    v23 = iconst.i32 -2
    v7 = iadd v4, v23
    jump block2(v7, v5, v6)

block2(v10: i32, v11: i32, v12: i32):
    v13 = iadd v11, v12
    v24 = iconst.i32 -1
    v14 = iadd v10, v24
    v22 = iconst.i32 0
    v15 = icmp eq v14, v22
    brif v15, block3(v13), block2(v14, v13, v11)

block3(v20: i32):
    return v20
}"

def fibonacci' := fn "function %fibonacci(i32) -> i32 {
block0(v0: i32):
    v21 = iconst.i32 2
    v1 = icmp ule v0, v21
    v2 = iconst.i32 1
    brif v1, block3(v2), block1

block1:
    v6 = iconst.i32 1
    v23 = iconst.i32 -2
    v7 = iadd v0, v23
    jump block2(v7, v2, v6)

block2(v10: i32, v11: i32, v12: i32):
    v13 = iadd v11, v12
    v24 = iconst.i32 -1
    v14 = iadd v10, v24
    v22 = iconst.i32 0
    v15 = icmp eq v14, v22
    brif v15, block3(v13), block2(v14, v13, v11)

block3(v20: i32):
    return v20
}"

/-- No constant phi: `block5(v5)` receives four values. -/
def brTableI32 := fn "function %br_table_i32(i32) -> i32 {
block0(v0: i32):
  br_table v0, block4, [block1, block2, block2, block3]

block1:
  v1 = iconst.i32 1
  jump block5(v1)

block2:
  v2 = iconst.i32 2
  jump block5(v2)

block3:
  v3 = iconst.i32 3
  jump block5(v3)

block4:
  v4 = iconst.i32 4
  jump block5(v4)

block5(v5: i32):
  v6 = iadd.i32 v0, v5
  return v6
}"

-- every fixture parses (`fn` gives `default`, without blocks, otherwise)
#guard [brTableUpperReg, brTableUpperReg', brifDifferentArgs, brifDifferentArgs', fuzzgen1,
  fuzzgen2, fuzzgen2', fibonacci, fibonacci', brTableI32].all (·.blocks.length > 1)
-- Cranelift's solutions
#guard solve brTableUpperReg == [(2, 0), (3, 1)]
#guard solve brifDifferentArgs == [(1, 0), (2, 0), (4, 0)]
#guard solve fuzzgen1 == [(0, 1)]
#guard solve fuzzgen2 == [(1, 0), (2, 0), (3, 0), (4, 0)]
#guard solve fibonacci == [(4, 0), (5, 2)]
#guard solve brTableI32 == []
-- the pass gives the stock compiler's input after `remove_constant_phis`
#guard run brTableUpperReg == brTableUpperReg'
#guard run brifDifferentArgs == brifDifferentArgs'
#guard run fuzzgen2 == fuzzgen2'
#guard run fibonacci == fibonacci'
#guard (run fuzzgen1).blocks.map (·.params) == [[], []]
#guard run brTableI32 == brTableI32
-- the checker accepts every solution
#guard [brTableUpperReg, brifDifferentArgs, fuzzgen1, fuzzgen2, fibonacci].all accepts

/-! ## Crate functions (`examples/survey`, cg_clif's `*.unopt.clif` and `*.opt.clif`) -/

/-- `_RNxC6values12H…` (`u0:11`): `block3(v7)` receives `v2` and `v16`, aliases of `v0`;
`block7` is unreachable. -/
def crateA := fn "function %u0_11(i64) -> i8 uext system_v {
block0(v0: i64):
    v2 -> v0
    v16 -> v0
    nop
    jump block1
block1:
    nop
    v1 = iconst.i32 97
    v3 = load.i32 notrap v2
    v4 = icmp ule v1, v3
    brif v4, block5, block3(v2)
block2:
    nop
    v5 = iconst.i8 0
    return v5
block3(v7: i64):
    v10 -> v7
    nop
    v6 = iconst.i32 65
    v8 = load.i32 notrap v7
    v9 = icmp ule v6, v8
    brif v9, block4, block2
block4:
    nop
    v11 = iconst.i32 90
    v12 = load.i32 notrap v10
    v13 = icmp ule v12, v11
    v14 = iconst.i8 0
    v15 = icmp ne v13, v14
    return v15
block5:
    nop
    v17 = iconst.i32 122
    v18 = load.i32 notrap v16
    v19 = icmp ule v18, v17
    brif v19, block6, block3(v16)
block6:
    nop
    v20 = iconst.i8 1
    return v20
block7:
    v22 = iconst.i8 0
    v21 -> v22
    nop
    return v21
}"

def crateA' := fn "function %u0_11(i64) -> i8 uext system_v {
block0(v0: i64):
    nop
    jump block1
block1:
    nop
    v1 = iconst.i32 97
    v3 = load.i32 notrap v0
    v4 = icmp ule v1, v3
    brif v4, block5, block3
block2:
    nop
    v5 = iconst.i8 0
    return v5
block3:
    nop
    v6 = iconst.i32 65
    v8 = load.i32 notrap v0
    v9 = icmp ule v6, v8
    brif v9, block4, block2
block4:
    nop
    v11 = iconst.i32 90
    v12 = load.i32 notrap v0
    v13 = icmp ule v12, v11
    v14 = iconst.i8 0
    v15 = icmp ne v13, v14
    return v15
block5:
    nop
    v17 = iconst.i32 122
    v18 = load.i32 notrap v0
    v19 = icmp ule v18, v17
    brif v19, block6, block3
block6:
    nop
    v20 = iconst.i8 1
    return v20
}"

/-- `u0:107`: the normal-return successor of a `try_call_indirect` and a `brif` both pass
aliases of `v0` to `block4(v9)`; the handler parameter `v7` (`exn0`) stays. -/
def crateB := fn "function %u0_107(i64) system_v {
    sig0 = (i64) system_v
    sig1 = (i64) system_v
    sig2 = (i64) system_v
    sig3 = (i64) system_v
    sig4 = () system_v
    fn0 = %u0_458(i64) system_v
    fn1 = colocated %u0_150(i64) system_v
    fn2 = colocated %u0_150(i64) system_v
    fn3 = %u0_463() system_v
block0(v0: i64):
    v1 -> v0
    v13 -> v0
    v10 -> v13
    nop
    jump block1
block1:
    nop
    v2 = load.i64 notrap v1
    v3 = load.i64 notrap v1+8
    v4 = load.i64 notrap aligned readonly v3
    v5 = iconst.i64 0
    v6 = icmp eq v4, v5
    brif v6, block4(v1), block6
block6:
    try_call_indirect.i64 v4(v2), sig0, block4(v13), [ tag0: block8(exn0) ]
block8(v7: i64) cold:
    v12 -> v7
    v8 -> v12
    jump block5
block2:
    nop
    return
block3 cold:
    nop
    call fn0(v8)
    trap user1
block4(v9: i64):
    nop
    nop
    call fn1(v9)
    jump block2
block5 cold:
    nop
    nop
    try_call fn2(v10), sig3, block9, [ tag0: block10(exn0) ]
block10(v11: i64) cold:
    nop
    call fn3()
    trap user1
block9:
    nop
    jump block3
}"

def crateB' := fn "function %u0_107(i64) system_v {
    sig0 = (i64) system_v
    sig1 = (i64) system_v
    sig2 = (i64) system_v
    sig3 = (i64) system_v
    sig4 = () system_v
    fn0 = %u0_458(i64) system_v
    fn1 = colocated %u0_150(i64) system_v
    fn2 = colocated %u0_150(i64) system_v
    fn3 = %u0_463() system_v
block0(v0: i64):
    nop
    jump block1
block1:
    nop
    v2 = load.i64 notrap v0
    v3 = load.i64 notrap v0+8
    v4 = load.i64 notrap aligned readonly v3
    v5 = iconst.i64 0
    v6 = icmp eq v4, v5
    brif v6, block4, block6
block6:
    try_call_indirect.i64 v4(v2), sig0, block4, [ tag0: block8(exn0) ]
block8(v7: i64) cold:
    jump block5
block2:
    nop
    return
block3 cold:
    nop
    call fn0(v7)
    trap user1
block4:
    nop
    nop
    call fn1(v0)
    jump block2
block5 cold:
    nop
    nop
    try_call fn2(v0), sig3, block9, [ tag0: block10(exn0) ]
block10(v11: i64) cold:
    nop
    call fn3()
    trap user1
block9:
    nop
    jump block3
}"

/-- `u0:6`: both parameters of `block4(v33, v34)` are constant (aliases of `v12` and `v10`). -/
def crateC := fn "function %u0_6(i64, i64, i64, i64, i64) -> i64, i64 system_v {
    ss0 = explicit_slot 16, align = 8
    ss1 = explicit_slot 16, align = 8
    ss2 = explicit_slot 16, align = 8
    ss3 = explicit_slot 16, align = 8
    sig0 = (i64, i64, i64, i64) system_v
    fn0 = %u0_60(i64, i64, i64, i64) system_v
block0(v0: i64, v1: i64, v2: i64, v3: i64, v4: i64):
    nop
    v5 = stack_addr.i64 ss0
    store notrap v0, v5
    v6 = stack_addr.i64 ss0+8
    store notrap v1, v6
    v7 = stack_addr.i64 ss1
    store notrap v2, v7
    v8 = stack_addr.i64 ss1+8
    store notrap v3, v8
    jump block1
block1:
    nop
    v9 = stack_addr.i64 ss0+8
    v10 = load.i64 notrap v9
    v35 -> v10
    v49 -> v10
    v11 = stack_addr.i64 ss0
    v12 = load.i64 notrap v11
    v36 -> v12
    v48 -> v12
    v18 -> v36
    v13 = icmp ult v10, v12
    brif v13, block5, block6
block2:
    nop
    v14 = stack_addr.i64 ss1
    v15 = load.i64 notrap v14
    v16 = stack_addr.i64 ss1+8
    v17 = load.i64 notrap v16
    v19 = iconst.i64 1
    v20 = imul.i64 v18, v19
    v21 = iadd v15, v20
    v23 = stack_addr.i64 ss3
    store notrap v21, v23
    v24 = stack_addr.i64 ss3+8
    store.i64 notrap v22, v24
    v25 = stack_addr.i64 ss3
    v26 = load.i64 notrap v25
    v27 = stack_addr.i64 ss3+8
    v28 = load.i64 notrap v27
    return v26, v28
block3:
    nop
    jump block4(v36, v35)
block4(v33: i64, v34: i64) cold:
    nop
    v29 = stack_addr.i64 ss1
    v30 = load.i64 notrap v29
    v31 = stack_addr.i64 ss1+8
    v32 = load.i64 notrap v31
    nop
    call fn0(v33, v34, v32, v4)
    trap user1
block5:
    nop
    jump block4(v48, v49)
block6:
    nop
    v37 = isub.i64 v35, v36
    v38 = stack_addr.i64 ss2+8
    store notrap v37, v38
    v39 = iconst.i64 1
    v40 = stack_addr.i64 ss2
    store notrap v39, v40
    v41 = stack_addr.i64 ss2+8
    v42 = load.i64 notrap v41
    v22 -> v42
    v43 = stack_addr.i64 ss1
    v44 = load.i64 notrap v43
    v45 = stack_addr.i64 ss1+8
    v46 = load.i64 notrap v45
    v47 = icmp.i64 ule v35, v46
    brif v47, block2, block3
}"

def crateC' := fn "function %u0_6(i64, i64, i64, i64, i64) -> i64, i64 system_v {
    ss0 = explicit_slot 16, align = 8
    ss1 = explicit_slot 16, align = 8
    ss2 = explicit_slot 16, align = 8
    ss3 = explicit_slot 16, align = 8
    sig0 = (i64, i64, i64, i64) system_v
    fn0 = %u0_60(i64, i64, i64, i64) system_v
block0(v0: i64, v1: i64, v2: i64, v3: i64, v4: i64):
    nop
    v5 = stack_addr.i64 ss0
    store notrap v0, v5
    v6 = stack_addr.i64 ss0+8
    store notrap v1, v6
    v7 = stack_addr.i64 ss1
    store notrap v2, v7
    v8 = stack_addr.i64 ss1+8
    store notrap v3, v8
    jump block1
block1:
    nop
    v9 = stack_addr.i64 ss0+8
    v10 = load.i64 notrap v9
    v11 = stack_addr.i64 ss0
    v12 = load.i64 notrap v11
    v13 = icmp ult v10, v12
    brif v13, block5, block6
block2:
    nop
    v14 = stack_addr.i64 ss1
    v15 = load.i64 notrap v14
    v16 = stack_addr.i64 ss1+8
    v17 = load.i64 notrap v16
    v19 = iconst.i64 1
    v20 = imul.i64 v12, v19
    v21 = iadd v15, v20
    v23 = stack_addr.i64 ss3
    store notrap v21, v23
    v24 = stack_addr.i64 ss3+8
    store.i64 notrap v42, v24
    v25 = stack_addr.i64 ss3
    v26 = load.i64 notrap v25
    v27 = stack_addr.i64 ss3+8
    v28 = load.i64 notrap v27
    return v26, v28
block3:
    nop
    jump block4
block4 cold:
    nop
    v29 = stack_addr.i64 ss1
    v30 = load.i64 notrap v29
    v31 = stack_addr.i64 ss1+8
    v32 = load.i64 notrap v31
    nop
    call fn0(v12, v10, v32, v4)
    trap user1
block5:
    nop
    jump block4
block6:
    nop
    v37 = isub.i64 v10, v12
    v38 = stack_addr.i64 ss2+8
    store notrap v37, v38
    v39 = iconst.i64 1
    v40 = stack_addr.i64 ss2
    store notrap v39, v40
    v41 = stack_addr.i64 ss2+8
    v42 = load.i64 notrap v41
    v43 = stack_addr.i64 ss1
    v44 = load.i64 notrap v43
    v45 = stack_addr.i64 ss1+8
    v46 = load.i64 notrap v45
    v47 = icmp.i64 ule v10, v46
    brif v47, block2, block3
}"

#guard [crateA, crateA', crateB, crateB', crateC, crateC'].all (·.blocks.length > 1)
-- `block7` of `crateA` is unreachable; the solution ignores it
#guard (removeUnreachable crateA).blocks.length + 1 == crateA.blocks.length
#guard solve crateA == [(7, 0)]
#guard solve (removeUnreachable crateA) == [(7, 0)]
#guard solve crateB == [(9, 0)]
#guard solve crateC == [(33, 12), (34, 10)]
-- the pass gives cg_clif's optimised function
#guard run crateA == crateA'
#guard run crateB == crateB'
#guard run crateC == crateC'
#guard [crateA, crateB, crateC].all accepts

/-! ## Rejections: corrupted solutions -/

-- a wrong value (`block2(v4)` receives `v0`)
#guard !cpOk brifDifferentArgs [(1, 0), (2, 0), (4, 3)]
-- a parameter receiving two values (`block2(v10)` receives `v7` and `v14`)
#guard !cpOk fibonacci [(10, 7)]
#guard !cpOk fibonacci [(4, 0), (5, 2), (12, 6)]
-- a chain (`v2` to the solved `v1`)
#guard !cpOk brifDifferentArgs [(1, 0), (2, 1)]
-- an entry-block parameter, an instruction result
#guard !cpOk brifDifferentArgs [(0, 0)]
#guard !cpOk brifDifferentArgs [(3, 0)]
-- a parameter solved twice
#guard !cpOk brifDifferentArgs [(1, 0), (1, 0), (2, 0), (4, 0)]
-- the handler parameter of a `try_call_indirect` (an exception payload)
#guard !cpOk crateB [(7, 0)]
#guard !cpOk crateB [(9, 0), (7, 0)]
-- an ill-formed input (block1 is unreachable: `Opt.check` asks every block to be reachable)
#guard !cpOk crateA [(7, 0)]
#guard cpOk (removeUnreachable crateA) [(7, 0)]

/-! ## The fresh value of a function with a `try_call` -/

/-- `block1(v5)` is constant and `v5` is the largest value: removing it would move the values a
`try_call` binds its results to (`Clif.Function.freshValue`). -/
def freshTop := fn "function %fresh_top(i64) -> i64 system_v {
    sig0 = (i64) -> i64 system_v
    fn0 = %g(i64) -> i64 system_v
block0(v0: i64):
    jump block1(v0)
block1(v5: i64):
    try_call fn0(v5), sig0, block2(ret0), [ default: block3(exn0) ]
block2(v1: i64):
    return v1
block3(v2: i64):
    return v2
}"

/-- The same with the constant parameter numbered below the others. -/
def freshLow := fn "function %fresh_low(i64) -> i64 system_v {
    sig0 = (i64) -> i64 system_v
    fn0 = %g(i64) -> i64 system_v
block0(v0: i64):
    jump block1(v0)
block1(v1: i64):
    try_call fn0(v1), sig0, block2(ret0), [ default: block3(exn0) ]
block2(v4: i64):
    return v4
block3(v5: i64):
    return v5
}"

/-- A constant phi whose other incoming edge is from an unreachable block. -/
def unreach := fn "function %unreach(i32) -> i32 {
block0(v0: i32):
    jump block2(v0)
block1:
    v1 = iconst.i32 1
    jump block2(v1)
block2(v2: i32):
    return v2
}"

def unreach' := fn "function %unreach(i32) -> i32 {
block0(v0: i32):
    jump block2
block2:
    return v0
}"

#guard [unreach, unreach'].all (·.blocks.length > 1)
#guard solve unreach == [(2, 0)]
#guard solve (removeUnreachable unreach) == [(2, 0)]
-- the solution applies after the unreachable block is removed
#guard run unreach == unreach'
#guard accepts unreach

/-- No constant phi, an unreachable block: `run` still removes it (as Cranelift does). -/
def unreachNoPhi := fn "function %unreach_no_phi(i32) -> i32 {
block0(v0: i32):
    brif v0, block2(v0), block3
block1:
    v1 = iconst.i32 1
    jump block2(v1)
block3:
    v3 = iconst.i32 3
    jump block2(v3)
block2(v2: i32):
    return v2
}"

#guard unreachNoPhi.blocks.length == 4
#guard solve unreachNoPhi == []
#guard (run unreachNoPhi).blocks.map (·.id) == [0, 3, 2]
#guard run unreachNoPhi == removeUnreachable unreachNoPhi

#guard [freshTop, freshLow].all (·.blocks.length > 1)
#guard freshTop.freshValue == 6 && (apply freshTop [(5, 0)]).freshValue == 3
#guard solve freshTop == [(5, 0)]
#guard !accepts freshTop
-- rejected: `run` gives the function without unreachable blocks (none here)
#guard run freshTop == freshTop
#guard solve freshLow == [(1, 0)]
#guard accepts freshLow
#guard (run freshLow).blocks.map (·.params.map (·.1)) == [[0], [], [4], [5]]

/-! ## The arity of `try_call` successors (`Opt.check` does not check it) -/

/-- The normal-return successor `block2(v2)` is passed two arguments. -/
def badArity := fn "function %bad_arity(i64) -> i64 system_v {
    sig0 = (i64) -> i64 system_v
    fn0 = %g(i64) -> i64 system_v
block0(v0: i64):
    jump block1(v0)
block1(v1: i64):
    try_call fn0(v1), sig0, block2(ret0, v1), [ default: block3(exn0) ]
block2(v2: i64):
    return v2
block3(v3: i64):
    return v3
}"

/-- The same with the right arity. -/
def goodArity := fn "function %good_arity(i64) -> i64 system_v {
    sig0 = (i64) -> i64 system_v
    fn0 = %g(i64) -> i64 system_v
block0(v0: i64):
    jump block1(v0)
block1(v1: i64):
    try_call fn0(v1), sig0, block2(ret0), [ default: block3(exn0) ]
block2(v2: i64):
    return v2
block3(v3: i64):
    return v3
}"

#guard [badArity, goodArity].all (·.blocks.length == 4)
#guard (Opt.check badArity).toBool
#guard !cpOk badArity [(1, 0)]
#guard solve goodArity == [(1, 0)]
#guard cpOk goodArity [(1, 0)]

end ConstPhiTest
