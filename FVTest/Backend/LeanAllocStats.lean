module

public import FV.Backend
public import FV.Backend.LinearScan
public import FV.Opt.Legalize128Pass

@[expose] public section

/-!
`lake exe lean-alloc-stats [--regalloc2] [--verbose] FILE.clif...`: measure the Lean
allocator (`leanAlloc`, `FV/Backend/LinearScan.lean`, V4b #57). For every function of the
files that lowers and whose spill allocation `lowerRFunc` lowers (the others have no allocation
the backend lowers, e.g. `ctlCheck` rejects their control forms: counted apart): whether
`checkAlloc` accepts `leanAlloc`'s allocation and `lowerRFunc`/`emitReady` accept it (else the
backend uses the spill allocation), and its `lean-regalloc`-format answer rebuilds it
(`raAnswerRoundTrip`, else `lean-link` would use the spill allocation) — else a fallback line
with the reason —, and the code size (bytes) of the function the
backend emits with the Lean allocator, with the spill allocation, and (with `--regalloc2`:
`lean-regalloc`, `$LEAN_REGALLOC` or the checkout's `rust/target/release/lean-regalloc`) with
regalloc2. Prints one line per fallback (every function with `--verbose`), one line per function
whose first linear-scan plan the validator (`LinearScan.Ctx.structOk`, or the builder) rejects
(`RETRY`, with the reason), and a summary line:

`lean-alloc-stats: N functions, A accepted, F fallback; bytes lean L, spill S, regalloc2 R; U not lowerable with any allocation; P first plans rejected by the validator`
-/

open Backend

/-- Emitted size of a lowered function (0 if emission fails). -/
def codeBytes (af : Except String AFunc) : Nat :=
  match af.bind (emitFunc 0 ·) with
  | .ok fa => fa.size
  | .error _ => 0

def main (args : List String) : IO UInt32 := do
  let ra2 := args.contains "--regalloc2"
  let verbose := args.contains "--verbose"
  let files := args.filter (!·.startsWith "--")
  let bin ← defaultRegallocBin
  let mut n := 0
  let mut nl := 0
  let mut acc := 0
  let mut fb := 0
  let mut bl := 0
  let mut bs := 0
  let mut br := 0
  let mut rep := 0
  for file in files do
    let pf := (Opt.Legalize128.parsedFile128 (Clif.parseFile (← IO.FS.readFile file))).file
    let vcps : Array (String × VCode) := pf.funcs.toArray.filterMap fun p =>
      match p.func with
      | .ok f => match lowerForAllocation f false true >>= prepareChecked with
        | .ok vcp => some (p.name, vcp)
        | .error _ => none
      | .error _ => none
    let ras : Array (Except String RFunc) ← if ra2 then do
        match ← runLeanRegalloc bin aarch64Env (vcps.map (·.2)) with
        | .ok rs => pure (rs.map (·.bind RAResult.oracle))
        | .error e => pure (vcps.map fun _ => .error e)
      else pure (vcps.map fun _ => .error "not run")
    for ((name, vcp), ra) in vcps.zip ras do
      -- a function whose spill allocation does not lower either (e.g. `ctlCheck` rejects its
      -- control forms) has no allocation the backend lowers: not counted
      if (lowerRFunc vcp (spillAlloc vcp)).toOption.isNone then
        nl := nl + 1
        if verbose then IO.println s!"unlowerable {file} %{name}"
        continue
      n := n + 1
      let la := leanAlloc vcp
      -- the linear scan's first plan is used unless the validator rejects it
      let why := match LinearScan.Fn.make vcp with
        | .ok fn => (LinearScan.Ctx.ofPlan fn (fn.plan (LinearScan.reserved 0))).whyNot
        | .error e => s!"Fn.make: {e}"
      if why != "ok" then
        rep := rep + 1
        IO.println s!"RETRY {file} %{name}: first plan rejected: {why.take 200}"
      let verdict := match la with
        | .ok rf => match checkAlloc vcp rf with
          | .ok () => match lowerRFunc vcp rf with
            | .ok af =>
              if !emitReady af then some "not emitReady"
              -- the answer `lean-backend` writes to `$FV_RA_OUT` must rebuild the allocation
              else if !raAnswerRoundTrip vcp rf then some "raAnswerJson does not rebuild it"
              else none
            | .error e => some s!"lowerRFunc: {e}"
          | .error e => some s!"checkAlloc: {e}"
        | .error e => some s!"leanAlloc: {e}"
      let sl := codeBytes (lowerAllocReady vcp la)
      let ss := codeBytes (lowerRFunc vcp (spillAlloc vcp))
      let sr := if ra2 then codeBytes (lowerAllocReady vcp ra) else 0
      bl := bl + sl
      bs := bs + ss
      br := br + sr
      match verdict with
      | none =>
        acc := acc + 1
        if verbose then IO.println s!"ok {file} %{name}: lean {sl} spill {ss} regalloc2 {sr}"
      | some e =>
        fb := fb + 1
        IO.println s!"FALLBACK {file} %{name}: {e.take 300}"
  IO.println s!"lean-alloc-stats: {n} functions, {acc} accepted, {fb} fallback; bytes lean {bl}, spill {bs}, regalloc2 {br}; {nl} not lowerable with any allocation; {rep} first plans rejected by the validator"
  pure (if fb == 0 then 0 else 1)
