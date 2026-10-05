import FV.Backend

/-!
# Register-allocation checker tests (`lake exe lean-backend-regalloc-test`,
`docs/contracts/regalloc.md`)

`lean-backend-regalloc-test [--small] [FILE.clif...]` (default: `corpus/clif/*.clif`,
`corpus/clif/extrt/*.clif` and Cranelift's `runtests/*.clif`). Every function the backend
lowers is allocated by regalloc2 (`lean-regalloc`; `--small`: the stress environment
`smallEnv`), and:

1. **Acceptance**: the Lean checker (`checkAlloc`) and regalloc2's own checker must both
   accept the allocation (counts and every rejection are printed).
2. **Negative tests**: each accepted allocation is mutated, and the Lean checker must reject
   every mutant. Mutations (each applied at up to `perKind` sites per function):
   * `swap`: exchange the locations of two operands of one instruction (different vregs,
     different registers of the same class);
   * `drop-reload`: delete a reload (a move from a spill slot to a register) whose register an
     instruction of the same block overwrote before (a reload into a register that may still
     hold the value, e.g. at a block entry, can be legitimately redundant);
   * `drop-restore`: delete the restores of a saved callee-saved register before the returns
     (every return; one alone may be redundant on a path that never writes the register);
   * `call-clobber`: move every use of a callee-saved integer register that is read after a
     call with no write in between (so it carries a value across the call) to a caller-saved
     register the function does not use, dropping its save and restores — the call clobbers
     the value.
   A mutant that is accepted is printed; the exit status is 0 iff every allocation is accepted
   by both checkers and every mutant is rejected.
-/

open Backend

def defaultFiles : IO (List String) := do
  let mut out : Array String := #[]
  for dir in ["corpus/clif", "corpus/clif/extrt",
              "third_party/wasmtime/cranelift/filetests/filetests/runtests"] do
    let entries ← System.FilePath.readDir dir
    out := out ++ ((entries.filter (·.path.extension == some "clif")).map (·.path.toString)
      |>.qsort (· < ·))
  return out.toList

def perKind : Nat := 5

/-- All `(block, item index)` positions of an allocated function. -/
def positions (rf : RFunc) : List (Nat × Nat × RItem) :=
  (rf.blocks.toList.zipIdx).flatMap fun (items, b) =>
    (items.toList.zipIdx).map fun (it, i) => (b, i, it)

def Backend.RFunc.setItems (rf : RFunc) (b : Nat) (items : Array RItem) : RFunc :=
  { rf with blocks := rf.blocks.set! b items }

def Backend.RFunc.deleteAt (rf : RFunc) (b i : Nat) : RFunc :=
  rf.setItems b ((rf.blocks[b]!).eraseIdx! i)

/-- `swap` mutants. -/
def swaps (vc : VCode) (rf : RFunc) : List (String × RFunc) :=
  let cands := (positions rf).filterMap fun (b, i, it) => match it with
    | .op k allocs => do
      let inst ← (vc.blocks[b]?).bind (·.insts[k]?)
      let ops ← inst.operands.toOption
      let n := ops.size
      let pairs := (List.range n).flatMap fun x => (List.range n).filterMap fun y =>
        if x < y then some (x, y) else none
      let (x, y) ← pairs.find? fun (x, y) =>
        ops[x]!.vreg != ops[y]!.vreg && ops[x]!.cls == ops[y]!.cls &&
        allocs[x]!.isReg && allocs[y]!.isReg && allocs[x]! != allocs[y]!
      let allocs' := (allocs.set! x allocs[y]!).set! y allocs[x]!
      pure (s!"swap operands {x},{y} of block {b} inst {k}",
            rf.setItems b ((rf.blocks[b]!).set! i (.op k allocs')))
    | _ => none
  cands.take perKind

/-- Does item `it` (of VCode block `vb`) write register `r` (a def operand, a clobber, a move)? -/
def writes (vb : VBlock) (r : Reg) (it : RItem) : Bool :=
  match it with
  | .move _ d => d == .reg r
  | .op k allocs =>
    let inst := vb.insts[k]!
    inst.clobbers.contains r ||
      ((inst.operands.toOption.getD #[]).zip allocs).any fun (o, l) => o.kind == .def && l == .reg r

/-- Does item `it` read register `r`? -/
def reads (vb : VBlock) (r : Reg) (it : RItem) : Bool :=
  match it with
  | .move s _ => s == .reg r
  | .op k allocs =>
    ((vb.insts[k]!.operands.toOption.getD #[]).zip allocs).any fun (o, l) => o.kind == .use && l == .reg r

/-- `drop-reload` mutants: reloads whose register was overwritten by an instruction (a def or a
clobber, not a move) earlier in the block, so it cannot still hold the value. (A reload into a
register that may already hold the value, e.g. on entry to the block, can be redundant.) -/
def dropReloads (vc : VCode) (rf : RFunc) : List (String × RFunc) :=
  ((positions rf).filterMap fun (b, i, it) => match it with
    | .move (.stack s _) (.reg r) =>
      let vb := vc.blocks[b]!
      let before := ((rf.blocks[b]!).extract 0 i).toList
      match (before.reverse.find? (writes vb r)) with
      | some (.op ..) => some (s!"drop reload s{s} → {repr r} in block {b}", rf.deleteAt b i)
      | _ => none
    | _ => none).take perKind

/-- `drop-restore` mutants: all restores of one saved register. (Dropping a single restore
can be harmless: on a path that never writes the register it still holds its entry value.) -/
def dropRestores (rf : RFunc) : List (String × RFunc) :=
  (rf.saved.take perKind).map fun r =>
    (s!"drop the restores of {repr r}",
     { rf with blocks := rf.blocks.map (·.filter (· != .move (.save r) (.reg r))) })

def Backend.Loc.rename (a c : Reg) : Loc → Loc
  | .reg r => .reg (if r == a then c else r)
  | l => l

def isCallItem (vb : VBlock) : RItem → Bool
  | .op k _ => match vb.insts[k]! with
    | .call _ => true
    | _ => false
  | _ => false

/-- Is callee-saved `r` read after a call in some block with no write in between (so it
carries a value across the call)? -/
def liveAcrossCall (vc : VCode) (rf : RFunc) (r : Reg) : Bool :=
  (rf.blocks.zip vc.blocks).any fun (items, vb) =>
    let (_, found) := items.foldl (init := (false, false)) fun (afterCall, found) it =>
      let isCall := isCallItem vb it
      if found then (afterCall, true)
      else if afterCall && reads vb r it then (true, true)
      else if writes vb r it then (false, false)
      else (afterCall || isCall, false)
    found

/-- `call-clobber` mutants: a callee-saved integer register that carries a value across a call
is renamed to a caller-saved register the function does not use (its save and restores
dropped). -/
def callClobbers (vc : VCode) (rf : RFunc) : List (String × RFunc) :=
  let used := (positions rf).flatMap fun (_, _, it) => it.locs
  let free := ((List.range 7).map fun i => Reg.x (9 + i)).filter fun c => !used.contains (.reg c)
  match free with
  | [] => []
  | c :: _ =>
    (rf.saved.filter fun r => r.realClass? == some .int && liveAcrossCall vc rf r).take perKind
      |>.map fun r =>
      let blocks := rf.blocks.map fun items => items.filterMap fun it => match it with
        | .move (.save _) _ | .move _ (.save _) =>
          if it.locs.contains (.save r) then none else some it
        | .move s d => some (.move (s.rename r c) (d.rename r c))
        | .op k allocs => some (.op k (allocs.map (Loc.rename r c)))
      (s!"move {repr r} to caller-saved {repr c}", { rf with blocks, saved := rf.saved.erase r })

structure Tally where
  funcs : Nat := 0
  leanOk : Nat := 0
  rustOk : Nat := 0
  errors : Nat := 0
  withSpills : Nat := 0
  withSaves : Nat := 0
  /-- rejected mutants lowered through the spill fallback (`RAResult.finish`), and failures -/
  fallback : Nat := 0
  fallbackBad : Nat := 0
  /-- `(kind, mutants, rejected)` -/
  muts : Array (String × Nat × Nat) := #[("swap", 0, 0), ("drop-reload", 0, 0),
    ("drop-restore", 0, 0), ("call-clobber", 0, 0)]
  bad : Nat := 0
  /-- Items of the accepted allocations: instructions, register moves, spills, reloads,
  callee-saved saves + restores; and instructions whose results are all unused. -/
  insts : Nat := 0
  regMoves : Nat := 0
  spills : Nat := 0
  reloads : Nat := 0
  saveRestores : Nat := 0
  deadInsts : Nat := 0

def main (args : List String) : IO UInt32 := do
  let (small, files) := match args with
    | "--small" :: rest => (true, rest)
    | rest => (false, rest)
  let files ← if files.isEmpty then defaultFiles else pure files
  let bin ← defaultRegallocBin
  let env := if small then smallEnv else aarch64Env
  let mut t : Tally := {}
  for file in files do
    let pf := Clif.parseFile (← IO.FS.readFile file)
    let vcs := pf.funcs.toArray.filterMap fun p => (p.func.toOption.bind (lowerFunction · |>.toOption))
    let prepared := vcs.filterMap fun vc => (prepare vc).toOption
    if prepared.isEmpty then continue
    match ← runLeanRegalloc bin env prepared with
    | .error e =>
      IO.println s!"{file}: lean-regalloc failed: {e}"
      t := { t with errors := t.errors + prepared.size, bad := t.bad + 1 }
    | .ok rs =>
      for (r, vc) in rs.zip prepared do
        t := { t with funcs := t.funcs + 1 }
        let res ← match r with
          | .ok res => pure res
          | .error e =>
            IO.println s!"{file}: %{vc.name}: {e}"
            t := { t with errors := t.errors + 1, bad := t.bad + 1 }
            continue
        if res.rustChecker == "ok" then t := { t with rustOk := t.rustOk + 1 }
        else
          IO.println s!"{file}: %{vc.name}: regalloc2's checker rejects: {res.rustChecker}"
          t := { t with bad := t.bad + 1 }
        match checkAlloc res.prepared res.rf with
        | .ok () => t := { t with leanOk := t.leanOk + 1 }
        | .error e =>
          IO.println s!"{file}: %{vc.name}: Lean checker rejects: {e}"
          t := { t with bad := t.bad + 1 }
          continue
        let rf := res.rf
        let used : Std.HashSet Nat := res.prepared.blocks.foldl (init := {}) fun acc b =>
          let acc := b.branchArgs.foldl (fun acc r => match r with | .vreg n _ => acc.insert n | _ => acc) acc
          b.insts.foldl (fun acc i => ((i.operands.toOption.getD #[]).filter (·.kind == .use)).foldl
            (fun acc o => acc.insert o.vreg) acc) acc
        for b in res.prepared.blocks do
          for i in b.insts do
            let defs := (i.operands.toOption.getD #[]).filter (·.kind == .def)
            let pure_ := match i with
              | .call _ | .args _ | .store .. | .load .. | .rets _ => false
              | _ => !i.isBranch
            if pure_ && !defs.isEmpty && defs.all (!used.contains ·.vreg) then
              t := { t with deadInsts := t.deadInsts + 1 }
        for (_, _, it) in positions rf do
          t := match it with
            | .op .. => { t with insts := t.insts + 1 }
            | .move (.reg _) (.reg _) => { t with regMoves := t.regMoves + 1 }
            | .move (.reg _) (.stack ..) => { t with spills := t.spills + 1 }
            | .move (.stack ..) (.reg _) => { t with reloads := t.reloads + 1 }
            | .move _ _ => { t with saveRestores := t.saveRestores + 1 }
        if (positions rf).any (fun (_, _, it) => it.locs.any fun | .stack .. => true | _ => false) then
          t := { t with withSpills := t.withSpills + 1 }
        if !rf.saved.isEmpty then t := { t with withSaves := t.withSaves + 1 }
        let kinds := [swaps res.prepared rf, dropReloads res.prepared rf, dropRestores rf,
                      callClobbers res.prepared rf]
        for (ms, ki) in kinds.zipIdx do
          for (what, m) in ms do
            let rejected := (checkAlloc res.prepared m).isOk == false
            let (kn, n, rj) := t.muts[ki]!
            t := { t with muts := t.muts.set! ki (kn, n + 1, if rejected then rj + 1 else rj) }
            if !rejected then
              IO.println s!"{file}: %{vc.name}: mutant ACCEPTED: {what}"
              t := { t with bad := t.bad + 1 }
            else
              -- the backend lowers the spill allocation instead (`allocResult`)
              match ({ res with rf := m } : RAResult).finish, lowerRFunc res.prepared (spillAlloc res.prepared) with
              | .ok af, .ok af' =>
                if af.blocks == af'.blocks && af.frameSize == af'.frameSize then
                  t := { t with fallback := t.fallback + 1 }
                else
                  IO.println s!"{file}: %{vc.name}: fallback for {what} is not the spill allocation"
                  t := { t with fallbackBad := t.fallbackBad + 1, bad := t.bad + 1 }
              | _, _ =>
                IO.println s!"{file}: %{vc.name}: no fallback for rejected mutant {what}"
                t := { t with fallbackBad := t.fallbackBad + 1, bad := t.bad + 1 }
  IO.println s!"functions {t.funcs}: Lean checker accepts {t.leanOk}, regalloc2 checker accepts {t.rustOk}, allocation errors {t.errors}"
  IO.println s!"functions with spill slots {t.withSpills}, with callee-saved registers {t.withSaves}"
  IO.println s!"items: instructions {t.insts} (results all unused: {t.deadInsts}), register moves {t.regMoves}, spills {t.spills}, reloads {t.reloads}, callee-saved saves/restores {t.saveRestores}"
  for (k, n, rj) in t.muts do
    IO.println s!"mutation {k}: {n} mutants, {rj} rejected"
  IO.println s!"fallback: {t.fallback} rejected mutants lowered through the spill allocation, {t.fallbackBad} failures"
  return if t.bad == 0 then 0 else 1
