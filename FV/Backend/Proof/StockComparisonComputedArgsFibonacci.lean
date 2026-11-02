import FV.Clif.Parse
import FV.Backend.Proof.StockComparisonComputedArgsLoopCheck

/-! The loop of `runtests/fibonacci.clif` in the loop class with computed comparisons and block
arguments (#140, CB-9).

The witness is the first function `%fibonacci` of the Cranelift runtest
`third_party/wasmtime/cranelift/filetests/filetests/runtests/fibonacci.clif`, unchanged, with its
comments and its eight `; run:` lines (file lines 12-44):

```
function %fibonacci(i32) -> i32 {
block0(v0: i32):
    v21 = iconst.i32 2
    v1 = icmp ule v0, v21
    v2 = iconst.i32 1
    ; handle base case, n <= 2
    brif v1, block3(v2), block1(v0, v2)

block1(v4: i32, v5:i32):
    v6 = iconst.i32 1
    v23 = iconst.i32 -2
    v7 = iadd v4, v23
    jump block2(v7, v5, v6)

block2(v10: i32, v11: i32, v12: i32): ; params: n, fib(n-1), fib(n-2)
    v13 = iadd v11, v12
    v24 = iconst.i32 -1
    v14 = iadd v10, v24
    v22 = iconst.i32 0
    v15 = icmp eq v14, v22
    brif v15, block3(v13), block2(v14, v13, v11)

block3(v20: i32): ; early return and end of loop
    return v20
}
; run: %fibonacci(0) == 1
; run: %fibonacci(1) == 1
; run: %fibonacci(2) == 1
; run: %fibonacci(3) == 2
; run: %fibonacci(4) == 3
; run: %fibonacci(5) == 5
; run: %fibonacci(6) == 8
; run: %fibonacci(10) == 55
```

The entry `block0` handles `n <= 2` with `icmp ule v0, (iconst 2)`: a comparison of a parameter
with an encodable 12-bit constant (`subs wzr, w0, #2; b.ls`), with block arguments on both edges.
The loop header `block2` counts `v10` down: it branches on `icmp eq v14, (iconst 0)` where
`v14 = iadd v10, v24` is computed, and passes block arguments on both edges, the next state back
to itself and the sum to the exit. This is the zero form with a computed first operand: Stock
selects `emit_icmp` rule 5170 and `is_nonzero` rule 4977, and the branch is one `cbz w` on `v14`.
The edges `block0 → block3`, `block2 → block3` and `block2 → block2` are critical, so Stock lowers
them through edge nodes; the lowering is not legacy-compatible.

The earlier loop classes reject the function: the comparison loop class (T7b-7) and the computed
comparison loop class (CB-8) reject the block arguments, the parameter loop class with block
arguments (T7b-8) rejects the comparison conditions, and the comparison loop class with block
arguments (T7b-9) rejects the computed first operand of the header comparison. The new selector
accepts the function, and the checker accepts the actual split code.

Every `; run:` line holds in the source semantics with fuel `100`. The run `%fibonacci(10) == 55`
returns with fuel `57` and runs out of fuel with fuel `56`: one fuel unit is one instruction or
terminator, so it executes `57 = 4 + 4 + 8 * 6 + 1` steps: the entry block, `block1`, eight passes
through the 6 steps of `block2` (seven back edges), and the return. -/

namespace Backend.Stock.ComparisonComputedArgsLoopCfg.Fibonacci
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The text of `%fibonacci` and its run lines in `runtests/fibonacci.clif` (file lines 12-44). -/
def fibonacciSource : String := "function %fibonacci(i32) -> i32 {
block0(v0: i32):
    v21 = iconst.i32 2
    v1 = icmp ule v0, v21
    v2 = iconst.i32 1
    ; handle base case, n <= 2
    brif v1, block3(v2), block1(v0, v2)

block1(v4: i32, v5:i32):
    v6 = iconst.i32 1
    v23 = iconst.i32 -2
    v7 = iadd v4, v23
    jump block2(v7, v5, v6)

block2(v10: i32, v11: i32, v12: i32): ; params: n, fib(n-1), fib(n-2)
    v13 = iadd v11, v12
    v24 = iconst.i32 -1
    v14 = iadd v10, v24
    v22 = iconst.i32 0
    v15 = icmp eq v14, v22
    brif v15, block3(v13), block2(v14, v13, v11)

block3(v20: i32): ; early return and end of loop
    return v20
}
; run: %fibonacci(0) == 1
; run: %fibonacci(1) == 1
; run: %fibonacci(2) == 1
; run: %fibonacci(3) == 2
; run: %fibonacci(4) == 3
; run: %fibonacci(5) == 5
; run: %fibonacci(6) == 8
; run: %fibonacci(10) == 55
"

/-- `%fibonacci` of `runtests/fibonacci.clif`, with its run commands, as a `Clif.Function`
literal. -/
def fibonacci : Clif.Function := {
  name := "fibonacci"
  sig := { params := [⟨.i32,.none,.normal⟩], returns := [⟨.i32,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i32)],
      body := [⟨[21],.iconst .i32 2⟩,⟨[1],.icmp .ule .i32 0 21⟩,⟨[2],.iconst .i32 1⟩],
      term := .brif 1 ⟨3,[2]⟩ ⟨1,[0,2]⟩ },
    { id := 1, params := [(4,.i32),(5,.i32)],
      body := [⟨[6],.iconst .i32 1⟩,⟨[23],.iconst .i32 (-2)⟩,⟨[7],.binary .iadd .i32 4 23⟩],
      term := .jump ⟨2,[7,5,6]⟩ },
    { id := 2, params := [(10,.i32),(11,.i32),(12,.i32)],
      body := [⟨[13],.binary .iadd .i32 11 12⟩,⟨[24],.iconst .i32 (-1)⟩,⟨[14],.binary .iadd .i32 10 24⟩,
        ⟨[22],.iconst .i32 0⟩,⟨[15],.icmp .eq .i32 14 22⟩],
      term := .brif 15 ⟨3,[13]⟩ ⟨2,[14,13,11]⟩ },
    { id := 3, params := [(20,.i32)], body := [], term := .ret [20] }]
  runs := [
    { func := "fibonacci", args := [⟨.i32,0⟩], expect := .eq [⟨.i32,1⟩] },
    { func := "fibonacci", args := [⟨.i32,1⟩], expect := .eq [⟨.i32,1⟩] },
    { func := "fibonacci", args := [⟨.i32,2⟩], expect := .eq [⟨.i32,1⟩] },
    { func := "fibonacci", args := [⟨.i32,3⟩], expect := .eq [⟨.i32,2⟩] },
    { func := "fibonacci", args := [⟨.i32,4⟩], expect := .eq [⟨.i32,3⟩] },
    { func := "fibonacci", args := [⟨.i32,5⟩], expect := .eq [⟨.i32,5⟩] },
    { func := "fibonacci", args := [⟨.i32,6⟩], expect := .eq [⟨.i32,8⟩] },
    { func := "fibonacci", args := [⟨.i32,10⟩], expect := .eq [⟨.i32,55⟩] }] }

/-- The source outcome from the entry with fuel `fuel` for the arguments `args`. -/
def sourceOutcome (fuel : Nat) (args : List Clif.Val) : Option Clif.Outcome :=
  match Clif.enterFunc fibonacci args Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} fuel ⟨fr,[],cm⟩)
  | _ => none

/-- The run command `r` holds in the source semantics with fuel `fuel`. -/
def runHolds (fuel : Nat) (r : Clif.RunCommand) : Bool :=
  match r.expect with
  | .eq vals => match sourceOutcome fuel r.args with
    | some (.returned vals' _) => decide (vals' = vals)
    | _ => false
  | _ => false

/-- The header's branch is a 32-bit `cbz`. -/
def hasCbz32 (vc : VCode) : Bool :=
  vc.blocks.any fun vb => vb.insts.any fun inst => inst matches .condBr _ _ (.zero _ .size32)

private def checks : Bool :=
  decide ((Clif.parseFile fibonacciSource).funcs.map (·.func.toOption) = [some fibonacci]) &&
  fibonacci.runs.all (runHolds 100) &&
  (match sourceOutcome 57 [⟨.i32,10⟩] with | some (.returned vals _) => decide (vals = [⟨.i32,55⟩]) | _ => false) &&
  (match sourceOutcome 56 [⟨.i32,10⟩] with | some .outOfFuel => true | _ => false) &&
  sourceOk fibonacci && !ComparisonArgsLoopCfg.sourceOk fibonacci &&
  !ComparisonComputedLoopCfg.sourceOk fibonacci && !ComparisonLoopCfg.sourceOk fibonacci &&
  !ParameterArgsLoopCfg.sourceOk fibonacci &&
  match Stock.lower fibonacci with
  | .error _ => false
  | .ok result =>
    result.order.nodes.contains (.edge 2 1 2) &&
    !edgeLegacyCompatibleB result.code result.edgeArgs &&
    match splitEdgesChecked result.code result.edgeArgs with
    | .ok split => hasCbz32 split.code && check fibonacci split.code
    | .error _ => false

-- witness: native_decide (the fixed function's parse, source runs, selectors, input checks, lowering, split and checker only)
private theorem checks_true : checks = true := by native_decide

private theorem run_sound {fuel : Nat} {r : Clif.RunCommand} (holds : runHolds fuel r = true) :
    ∃ vals mem,r.expect = .eq vals ∧ sourceOutcome fuel r.args = some (.returned vals mem) := by
  unfold runHolds at holds
  cases expect : r.expect with
  | eq vals =>
    rw [expect] at holds
    dsimp only at holds
    cases outcome : sourceOutcome fuel r.args with
    | none => rw [outcome] at holds; cases holds
    | some o =>
      rw [outcome] at holds
      cases o with
      | returned vals' mem =>
        simp only [decide_eq_true_eq] at holds
        exact ⟨vals,mem,rfl,by rw [holds]⟩
      | _ => cases holds
  | _ => rw [expect] at holds; cases holds

/-- **`%fibonacci` of `runtests/fibonacci.clif` is in the checked class.** The literal is the
parse of the filetest text, with its run commands; the selector derives `Scalar.DomainAt`; every
run command of the filetest holds in the source semantics, and `%fibonacci(10)` returns `55` after
`57` steps (seven back edges) and not within `56`; the loop classes of T7b-7, CB-8, T7b-8 and T7b-9
reject the function; its actual lowering has the critical-edge node of the back edge, is not
legacy-compatible, its actual split code has a 32-bit `cbz`, and the split code passes the checker,
which derives the code domain. -/
theorem fibonacci_witness :
    (Clif.parseFile fibonacciSource).funcs.map (·.func.toOption) = [some fibonacci] ∧
    Scalar.DomainAt fibonacci ∧
    (∀ r ∈ fibonacci.runs,∃ vals mem,r.expect = .eq vals ∧ sourceOutcome 100 r.args = some (.returned vals mem)) ∧
    (∃ mem,sourceOutcome 57 [⟨.i32,10⟩] = some (.returned [⟨.i32,55⟩] mem)) ∧
    (∃ outcome,sourceOutcome 56 [⟨.i32,10⟩] = some outcome ∧ ∀ vals mem,outcome ≠ .returned vals mem) ∧
    ComparisonArgsLoopCfg.sourceOk fibonacci = false ∧ ComparisonComputedLoopCfg.sourceOk fibonacci = false ∧
    ComparisonLoopCfg.sourceOk fibonacci = false ∧ ParameterArgsLoopCfg.sourceOk fibonacci = false ∧
    ∃ result split,Stock.lower fibonacci = .ok result ∧ Node.edge 2 1 2 ∈ result.order.nodes ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = false ∧
      splitEdgesChecked result.code result.edgeArgs = .ok split ∧ hasCbz32 split.code = true ∧
      check fibonacci split.code = true ∧ Scalar.CodeDomain fibonacci split.code := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨parsed,runs⟩,returns⟩,outOfFuel⟩,source⟩,notArgs⟩,notComputed⟩,notComparison⟩,
    notParameter⟩,lowered⟩ := h
  refine ⟨of_decide_eq_true parsed,source_ok_sound source,
    fun r member => run_sound (List.all_eq_true.mp runs r member),?_,?_,by simpa using notArgs,
    by simpa using notComputed,by simpa using notComparison,by simpa using notParameter,?_⟩
  · cases outcome : sourceOutcome 57 [⟨.i32,10⟩] with
    | none => rw [outcome] at returns; cases returns
    | some o =>
      rw [outcome] at returns
      cases o with
      | returned vals mem =>
        simp only [decide_eq_true_eq] at returns
        exact ⟨mem,by rw [returns]⟩
      | _ => cases returns
  · cases outcome : sourceOutcome 56 [⟨.i32,10⟩] with
    | none => rw [outcome] at outOfFuel; cases outOfFuel
    | some o =>
      rw [outcome] at outOfFuel
      cases o with
      | outOfFuel => exact ⟨.outOfFuel,rfl,fun vals mem same => by cases same⟩
      | _ => cases outOfFuel
  · cases run : Stock.lower fibonacci with
    | error message => rw [run] at lowered; cases lowered
    | ok result =>
      rw [run] at lowered
      dsimp only at lowered
      simp only [Bool.and_eq_true] at lowered
      obtain ⟨⟨edge,incompatible⟩,rest⟩ := lowered
      cases splitRun : splitEdgesChecked result.code result.edgeArgs with
      | error message => rw [splitRun] at rest; cases rest
      | ok split =>
        rw [splitRun] at rest
        simp only [Bool.and_eq_true] at rest
        obtain ⟨cbz,accepted⟩ := rest
        exact ⟨result,split,rfl,Array.contains_iff_mem.mp edge,by simpa using incompatible,splitRun,cbz,
          accepted,check_sound accepted⟩

end Backend.Stock.ComparisonComputedArgsLoopCfg.Fibonacci
