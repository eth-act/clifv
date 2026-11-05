import FV.Backend
import FV.Backend.Lowering.Stock
import FV.Backend.RegallocPerEdgeDriver

/-!
# regalloc2's input as Cranelift builds it (#551, #586, #587)

regalloc2's answer depends on more than the code it allocates: its bundles are created in vreg
order and a bundle's probe into the register list starts at the bundle's index plus its first
instruction (`ion/process.rs`), so the vreg numbers and the instruction indices matter. This
module gives `lean-regalloc` the prepared VCode `vcp` of a function lowered by the legacy driver
(`lowerFunction`) in the form Cranelift's lowering (`machinst/lower.rs`) hands to regalloc2:

* **numbering**: Cranelift reserves 192 numbers, gives the CLIF values vregs in layout order
  (block parameters, then the results of each instruction, and the return/payload vregs of a
  `try_call` at its terminator: `Lower::new`), then numbers the temporaries as its backward pass
  allocates them: lowered blocks last to first, in each the terminator first, then the
  instructions last to first (`Lower::lower`, `lower_clif_block`). `lowerFunction` numbers
  values by id and temporaries forward; the lowering replay `Proof.Driver.lowBlocks` gives the
  temporaries of every instruction, so `numbering` renames each to Cranelift's number;
* **`args`**: Cranelift's `gen_arg_setup` skips the entry parameters without IR uses
  (`ValueUseState::Unused`) and `take_args` emits no `args` when none is left; `lowerFunction`
  lists every register-passed parameter and emits `args []` (#586). Here a pair is dropped when
  its parameter has no CLIF use (and its vreg no use in `vcp`), and an empty `args` is dropped;
* **calls to an `sret` callee**: Cranelift's `gen_call_output` allocates a vreg per CLIF
  return only and `gen_call_rets` skips the `StructReturn` return (`machinst/abi.rs`), so such
  a call has no def and clobbers x0; `lowerFunction` makes x0 a def of a fresh, unused vreg
  (#587). Here that def is dropped (x0 becomes a clobber again).

Nothing here is trusted: the dropped operands are fixed-register defs of vregs with no use, and
an empty `args` does nothing, so regalloc2's answer for `code` is read back against `vcp`
(`readBack`: the dropped operands get their fixed registers, the instruction indices of the
edits are shifted over the dropped instructions) and then rebuilt (`buildRFunc vcp`) and checked
by `checkAlloc` on `vcp` exactly as before. A function `lowerFunction` did not lower (a Stock
route, `FV/Backend/ScalarNIProduction.lean`), or whose replay fails, is given as it is.
-/

namespace Backend.CraneliftInput

open Backend.Proof.Driver

/-- The fresh vregs of one block's lowering: per statement `[lo, hi)`, the terminator's
temporaries `[lo, hi)`, and a `try_call`'s return/payload vregs. -/
structure BlockVregs where
  stmts : Array (Nat × Nat)
  term : Nat × Nat
  tryRegs : Option (List Reg × List Reg)

/-- `lowerFunction`'s lowering calls replayed (the calls of `Proof.Driver.lowBlocks`, keeping only
the current state, so memory stays linear in the function): the fresh vregs of every block,
the x0 defs of the calls to an `sret` callee without returns (`sigRets`: Cranelift's call has no
such def, `gen_call_rets` skips the `StructReturn` return), and the first temporary. -/
def replay (f : Clif.Function) :
    Except String (Ctx × Array (Nat × Nat) × Array BlockVregs × Std.HashSet Nat × Nat) := do
  let (ctx, ranges, st0) ← buildCtx f
  let sretSig (s : Clif.Signature) : Bool :=
    s.returns.isEmpty && s.params.any (·.purpose == .sret)
  let mut st := st0
  let mut nl := f.blocks.length
  let mut ii := 0
  let mut out : Array BlockVregs := #[]
  let mut sdefs : Std.HashSet Nat := {}
  for B in f.blocks do
    let mut sr : Array (Nat × Nat) := #[]
    for stm in B.body do
      let s0 : LState := { st with emitted := #[] }
      let (o, st', _) ← stmtCall ctx ii s0
      if (regsOf o).isNone then throw s!"no lowering of instruction {ii}"
      sr := sr.push (s0.nextVreg, st'.nextVreg)
      let sig? : Option Clif.Signature := match stm.inst with
        | .call fn _ => (f.extern? fn).map (·.sig)
        | .callIndirect sig _ _ => f.sigDecls.lookup sig
        | _ => none
      if sig?.any sretSig then
        for i in st'.emitted do
          if let .call info := i then
            for (p, r) in info.defs do
              if let (.x 0, .vreg t _) := (p, r) then sdefs := sdefs.insert t
      st := { st' with emitted := #[] }
      ii := ii + 1
    let tst : LState := { st with emitted := #[] }
    let some (_, _, tl, tst', nl') := lowTerm f (termCallF ctx) (tryCallF ctx) ii B.term tst nl
      | throw s!"no lowering of terminator {ii}"
    out := out.push { stmts := sr, term := ((tl.map (·.st1.nextVreg)).getD tst.nextVreg, tst'.nextVreg),
                      tryRegs := tl.map (·.regs) }
    st := { tst' with emitted := #[] }
    nl := nl'
    ii := ii + 1
  pure (ctx, ranges, out, sdefs, st0.nextVreg)

/-- Cranelift's vreg number of every vreg number `lowerFunction f` uses (values by id,
temporaries from `firstTemp` on; `bvs`, `ranges` from `replay f`), and the number of vregs.
`drop b j`: statement `j` of block `b` was skipped (`skipDead`), so, as in Cranelift, which never
lowers it, its temporaries get no number. -/
def numbering (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat))
    (bvs : Array BlockVregs) (firstTemp : Nat) (drop : Nat → Nat → Bool) :
    Except String (Std.HashMap Nat Nat × Nat) := do
  let reqs ← Stock.allocationRequests f ranges
  let alloc := Stock.allocateRequests ctx.valTy.size ctx.insts.size reqs
  let mut m : Std.HashMap Nat Nat := {}
  for v in [0:firstTemp] do
    if let some (some (.vreg n _)) := alloc.valReg[v]? then m := m.insert v n
  let order ← Stock.blockOrder f
  let mut next := alloc.base.nextVreg
  for node in order.nodes.reverse do
    let .original bi := node | continue
    let some bv := bvs[bi]? | throw s!"no lowering of block {bi}"
    -- a `try_call`'s return/payload vregs are Cranelift's values (`Lower::new`)
    if let some (rets, pays) := bv.tryRegs then
      let (srets, spays) := alloc.tryRegs[(ranges[bi]?.map (·.2 - 1)).getD 0]?.getD ([], [])
      for (r, s) in rets.zip srets ++ pays.zip spays do
        if let (.vreg a _, .vreg b _) := (r, s) then
          if !m.contains a then m := m.insert a b
    -- the backward pass: the terminator, then the statements last to first
    for t in [bv.term.1:bv.term.2] do
      m := m.insert t next
      next := next + 1
    for ((lo, hi), j) in bv.stmts.zipIdx.reverse do
      if drop bi j then continue
      for t in [lo:hi] do
        m := m.insert t next
        next := next + 1
  pure (m, next)

/-- The vreg numbers the instructions of `vc` use (operands of kind `use`) or pass as branch
arguments. -/
def usedVregs (vc : VCode) : Std.HashSet Nat :=
  vc.blocks.foldl (init := {}) fun s b =>
    let s := b.branchArgs.foldl (fun s r => match r with | .vreg n _ => s.insert n | _ => s) s
    b.insts.foldl (fun s i => match i.operands with
      | .ok ops => ops.foldl (fun s o => if o.kind == .use then s.insert o.vreg else s) s
      | .error _ => s) s

/-- The values of `f` with a CLIF use (`compute_use_states`: every instruction's and
terminator's value operands; the `sret` parameter has the epilogue's implicit use). -/
def irUsed (f : Clif.Function) : Std.HashSet Nat := Id.run do
  let mut s : Std.HashSet Nat := {}
  for b in f.blocks do
    for st in b.body do
      for v in instArgs st.inst do s := s.insert v
    for v in termArgs b.term do s := s.insert v
  for v in sretRet f do s := s.insert v
  pure s

/-- regalloc2's input for a prepared `vcp` and how to read its answer back. Per instruction of
`vcp` (in block order): `dropInst` (not in `code`) and `dropOps` (operand indices not in
`code`'s instruction; all fixed-register defs). `edges`: the branch arguments of `code` per
block and successor (`vcodeJsonAt`; `none`: each block's `branchArgs`, `vcodeJson`). -/
structure Shape where
  code : VCode
  edges : Option (Array (Array (Array Reg))) := none
  dropInst : Array Bool
  dropOps : Array (List Nat)
  /-- what was done (`FV_RA_DIAG`) -/
  why : String

/-- `vcp` given as it is. -/
def Shape.same (vcp : VCode) (why : String) : Shape :=
  let n := vcp.blocks.foldl (fun n b => n + b.insts.size) 0
  { code := vcp, dropInst := Array.replicate n false, dropOps := Array.replicate n [], why }

/-- The operand allocations of a `vcp` instruction from those of its `code` counterpart: the
dropped operands get their fixed registers. -/
def mergeAllocs (ops : Array Operand) (dropped : List Nat) (given : Array String) :
    Except String (Array String) := do
  let mut out : Array String := #[]
  let mut j := 0
  for (o, k) in ops.zipIdx do
    if dropped.contains k then
      let .fixed r := o.con | throw "dropped operand without a fixed register"
      out := out.push r.pregName
    else
      let some s := given[j]? | throw "regalloc2: allocation count"
      out := out.push s
      j := j + 1
  if j != given.size then throw "regalloc2: allocation count"
  pure out

/-- regalloc2's answer for `sh.code` as an answer for `vcp`. -/
def Shape.readBack (sh : Shape) (vcp : VCode) (o : RAOut) : Except String RAOut := do
  let insts := vcp.blocks.foldl (fun acc b => acc ++ b.insts) #[]
  let kept : Array Nat := (Array.range insts.size).filter fun g => !(sh.dropInst[g]?.getD false)
  if o.allocs.size != kept.size then throw "regalloc2: allocation count differs"
  let mut allocs : Array (Array String) := #[]
  let mut i := 0
  for (inst, g) in insts.zipIdx do
    let ops ← inst.operands
    if sh.dropInst[g]?.getD false then
      allocs := allocs.push (← mergeAllocs ops (List.range ops.size) #[])
    else
      allocs := allocs.push (← mergeAllocs ops (sh.dropOps[g]?.getD []) o.allocs[i]!)
      i := i + 1
  let edits ← o.edits.mapM fun (ig, after, a, b) => match kept[ig]? with
    | some g => pure (g, after, a, b)
    | none => throw "regalloc2: edit at a missing instruction"
  pure { o with allocs, edits }

/-- Rename the vregs of `vc` by `m` (`next`: the number of vregs). -/
def rename (m : Std.HashMap Nat Nat) (next : Nat) (vc : VCode) : VCode :=
  let R : Reg → Reg := fun
    | .vreg n c => .vreg (m.getD n n) c
    | r => r
  let classes := vc.classes.zipIdx.foldl (init := Array.replicate next RegClass.int)
    fun cs (c, n) => match m[n]? with
      | some n' => cs.set! n' c
      | none => cs
  { vc with
    classes
    blocks := vc.blocks.map fun b => { b with
      insts := b.insts.map (·.mapRegs R)
      params := b.params.map R
      branchArgs := b.branchArgs.map R } }

/-- `skipDead f vc` with the statements it skipped (`drop b j`: statement `j` of block `b`;
none when the skip does not apply), recomputed as `skipDeadImpl` computes them (the set of
skipped statements built once). -/
def skipDeadDrops (f : Clif.Function) (vc : VCode) : VCode × (Nat → Nat → Bool) :=
  match buildCtx f with
  | .error _ => (vc, fun _ _ => false)
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => (vc, fun _ _ => false)
    | some bl =>
      let R := renOf (gnAt (gnTable st0.nextVreg (aliasOf f bl)))
      let tbl := skipDropSet f R bl vc
      let drop := skipAt f fun b j => tbl.contains (b, j)
      let mask := skipMask f R bl vc drop
      if deleteCheck vc mask then (deleteWith vc mask, drop) else (vc, fun _ _ => false)

theorem skipDeadDrops_fst (f : Clif.Function) (vc : VCode) :
    (skipDeadDrops f vc).1 = skipDead f vc := by
  rw [skipDead_eq_impl]
  unfold skipDeadDrops skipDeadImpl
  cases buildCtx f with
  | error => rfl
  | ok x =>
    obtain ⟨ctx, _, st0⟩ := x
    dsimp only
    cases lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => rfl
    | some bl => dsimp only; split <;> rfl

/-- Is `a` the VCode `b`, block by block? -/
def sameCode (a b : VCode) : Bool :=
  a.blocks.size == b.blocks.size && (a.blocks.zip b.blocks).all fun (x, y) =>
    x.label == y.label && x.insts == y.insts && x.params == y.params && x.branchArgs == y.branchArgs

/-- The vregs of `vc`. -/
def vregsOf (vc : VCode) : Std.HashSet Nat :=
  let add (s : Std.HashSet Nat) (r : Reg) := match r with | .vreg n _ => s.insert n | _ => s
  vc.blocks.foldl (init := {}) fun s b =>
    let s := b.params.foldl add s
    let s := b.branchArgs.foldl add s
    b.insts.foldl (fun s i => match i.operands with
      | .ok ops => ops.foldl (fun s o => s.insert o.vreg) s
      | .error _ => s) s

/-- The CLIF predecessor edges of every block of `f` (`block_in_count` of
`BlockLoweringOrder::new`: every successor edge of every block, duplicates and unreachable
predecessors included). -/
def indegrees (f : Clif.Function) : Array Nat := Id.run do
  let mut n := Array.replicate f.blocks.length 0
  for b in f.blocks do
    for (id, _) in Stock.destinations b.term do
      if let some i := f.blocks.findIdx? (·.id == id) then n := n.modify i (· + 1)
  pure n

/-- `vcp` without the `args` pairs of parameters without IR use (`ir`) or use in `vcp`, without
an empty `args`, without the x0 defs `sdefs` of calls to `sret` callees, and without the edge
blocks Cranelift does not make; renamed by `m`. `lowerFunction` reaches every successor of a
`try_call`, and every successor with block arguments of a `brif`/`br_table`, through an edge
block of its own (labels `nb` on, `nb` the number of CLIF blocks: one `jump` with the
arguments). Cranelift's `BlockLoweringOrder::new` makes an edge block only for a successor
with several CLIF predecessor edges (`indeg`, unreachable predecessors and duplicate edges
included; `machinst/blockorder.rs:204-225`); otherwise the branch passes the arguments to the
successor itself (regalloc2's per-successor branch arguments, `vcodeJsonAt`). -/
def reshape (vcp : VCode) (ir sdefs : Std.HashSet Nat) (m : Std.HashMap Nat Nat) (next : Nat)
    (nb : Nat) (indeg : Array Nat) : Shape := Id.run do
  let used := usedVregs vcp
  let mut dropInst : Array Bool := #[]
  let mut dropOps : Array (List Nat) := #[]
  let mut blocks : Array VBlock := #[]
  let mut nArgs := 0
  let mut nSret := 0
  for (b, bi) in vcp.blocks.zipIdx do
    let mut insts : Array MInst := #[]
    for (i, k) in b.insts.zipIdx do
      let mut ds : List Nat := []
      let mut i' : Option MInst := some i
      match i with
      | .args ps =>
        if bi == 0 && k == 0 then
          let dead : Reg × Reg → Bool := fun
            | (.vreg n _, _) => !ir.contains n && !used.contains n
            | _ => false
          -- every pair of `args` is one operand (a vreg defined in its fixed register)
          ds := (ps.zipIdx.filter fun (q, _) => dead q).map (·.2)
          let keep := ps.filter fun q => !dead q
          nArgs := nArgs + ds.length
          i' := if keep.isEmpty then none else some (.args keep)
      | .call info =>
        let dead : Reg × Reg → Bool := fun
          | (.x 0, .vreg t _) => sdefs.contains t && !used.contains t
          | _ => false
        -- operands: the destination register, the uses, then the defs (vregs only)
        let nUses := (match info.dest with | .reg (.vreg ..) => 1 | _ => 0) +
          (info.uses.filter fun (r, _) => r matches .vreg ..).length
        let vdefs := info.defs.filter fun (_, r) => r matches .vreg ..
        ds := (vdefs.zipIdx.filter fun (q, _) => dead q).map (nUses + ·.2)
        nSret := nSret + ds.length
        i' := some (.call { info with defs := info.defs.filter fun q => !dead q })
      | _ => pure ()
      dropInst := dropInst.push i'.isNone
      dropOps := dropOps.push (if i'.isNone then [] else ds)
      if let some j := i' then insts := insts.push j
    blocks := blocks.push { b with insts }
  -- edge blocks: those of `lowerFunction` with one predecessor, to a block with one CLIF
  -- predecessor edge
  let preds := match vcp.cfg with | .ok (_, p) => p | .error _ => #[]
  let idx : Std.HashMap Label Nat := blocks.zipIdx.foldl (fun h (b, i) => h.insert b.label i) {}
  let starts := (vcp.blocks.foldl (fun (acc, s) b => (acc.push s, s + b.insts.size)) (#[], 0)).1
  let direct (l : Label) : Option (Nat × Label × Array Reg) := do
    let j ← idx[l]?
    let E ← blocks[j]?
    if l < nb || !E.params.isEmpty || (preds[j]?.map (·.size)) != some 1 then none
    match E.insts.toList with
    | [.jump t] => if t < nb && indeg[t]? == some 1 then some (j, t, E.branchArgs) else none
    | _ => none
  let mut gone : Std.HashSet Nat := {}
  let mut code : Array VBlock := #[]
  let mut edges : Array (Array (Array Reg)) := #[]
  for b in blocks do
    let t := b.insts.back?.getD (.udf (.user 0))
    let ts := t.targets
    if ts.length < 2 && !(t matches .tryCall ..) then
      code := code.push b
      edges := edges.push (if ts.isEmpty then #[] else #[b.branchArgs])
      continue
    let mut ls : Array Label := #[]
    let mut row : Array (Array Reg) := #[]
    for l in ts do
      match direct l with
      | some (j, tl, args) =>
        gone := gone.insert j
        ls := ls.push tl
        row := row.push args
      | none =>
        ls := ls.push l
        row := row.push #[]
    match t.setTargets ls.toList with
    | some t' =>
      code := code.push { b with insts := b.insts.pop.push t' }
      edges := edges.push row
    | none => return .same vcp "setTargets"
  let mut code' : Array VBlock := #[]
  let mut edges' : Array (Array (Array Reg)) := #[]
  for ((b, row), j) in (code.zip edges).zipIdx do
    if gone.contains j then
      for k in [0:b.insts.size] do
        if let some s := starts[j]? then dropInst := dropInst.set! (s + k) true
    else
      code' := code'.push b
      edges' := edges'.push row
  let dropped := dropInst.foldl (fun n d => if d then n + 1 else n) 0
  let R : Reg → Reg := fun
    | .vreg n c => .vreg (m.getD n n) c
    | r => r
  pure { code := rename m next { vcp with blocks := code' },
         edges := some (edges'.map (·.map (·.map R))), dropInst, dropOps,
         why := s!"cranelift (args pairs -{nArgs}, insts -{dropped}, sret call defs -{nSret}, edge blocks -{gone.size})" }

/-- regalloc2's input for the prepared `vcp` of `f` (`deadCleanup`: the allocator's input went
through the cleanup stage: on subset E possibly Cranelift's skip of unused statements, `skipDead`,
then the dead-producer cleanup), in Cranelift's form when `vcp` is `lowerFunction f`'s code. -/
def shape (f : Option Clif.Function) (deadCleanup : Bool) (vcp : VCode) : Shape :=
  match f with
  | none => .same vcp "no CLIF function"
  | some f =>
    let noDrop : Nat → Nat → Bool := fun _ _ => false
    let legacy : Except String (VCode × (Nat → Nat → Bool)) := do
      let vc ← lowerFunction f
      let lv ← prepare (if deadCleanup then DeadCleanup.prune vc else vc)
      if !deadCleanup || sameCode lv vcp || !Compile.functionE f then return (lv, noDrop)
      -- the skip ran (`cleanupStageChecked`): its statements are not lowered
      let (sk, drop) := skipDeadDrops f vc
      match prepare (DeadCleanup.prune sk) with
      | .ok lv' => return (if sameCode lv' vcp then (lv', drop) else (lv, noDrop))
      | .error _ => return (lv, noDrop)
    match legacy with
    | .error e => .same vcp s!"not lowerFunction's code: {e}"
    | .ok (lv, drop) =>
      if !sameCode lv vcp then .same vcp "not lowerFunction's code (another lowering route)"
      else
        let r := do
          let (ctx, ranges, bvs, sdefs, firstTemp) ← replay f
          pure (← numbering f ctx ranges bvs firstTemp drop, sdefs)
        match r with
        | .error e => .same vcp s!"numbering: {e}"
        | .ok ((m, next), sdefs) =>
          if !(vregsOf vcp).toList.all m.contains then .same vcp "numbering: unmapped vreg"
          else reshape vcp (irUsed f) sdefs m next f.blocks.length (indegrees f)

/-- `runLeanRegalloc` on the prepared `vcs`, giving `lean-regalloc` the code `sh.code` of each
(`shapes`, one per function); the answers are read back (`Shape.readBack`) and rebuilt against
`vcp` itself. -/
def runLeanRegallocVia (bin : String) (env : MachineEnv) (shapes : Array Shape)
    (vcs : Array VCode) : IO (Except String (Array (Except String RAResult))) := do
  if vcs.isEmpty then return .ok #[]
  if shapes.size != vcs.size then return .error "lean-regalloc: shape count differs"
  let mut funcs : Array String := #[]
  for (vc, sh) in vcs.zip shapes do
    match (match sh.edges with | some e => vcodeJsonAt sh.code e | none => vcodeJson sh.code) with
    | .ok j => funcs := funcs.push j
    | .error e => return .error s!"%{vc.name}: {e}"
  let input := s!"\{\"env\":{envJson env},\"functions\":[" ++ ",".intercalate funcs.toList ++ "]}\n"
  let (h, path) ← IO.FS.createTempFile
  h.putStr input
  h.flush
  if let some keep ← IO.getEnv "LEAN_REGALLOC_KEEP" then IO.FS.writeFile keep input
  let out ← IO.Process.output { cmd := bin, args := #[path.toString] }
  IO.FS.removeFile path
  if out.exitCode != 0 then
    return .error s!"lean-regalloc ({bin}) failed with status {out.exitCode}: {out.stderr}"
  match Lean.Json.parse out.stdout with
  | .error e => return .error s!"lean-regalloc output: {e}"
  | .ok j =>
    let arr := ((j.getObjVal? "functions").bind (·.getArr?)).toOption.getD #[]
    if arr.size != vcs.size then return .error "lean-regalloc: function count differs"
    return .ok <| ((vcs.zip shapes).zip arr).map fun ((vc, sh), fj) => do
      let o ← parseRAOut fj
      let o ← sh.readBack vc o
      let rf ← buildRFunc vc o
      pure { prepared := vc, rf, rustChecker := o.checker }

end Backend.CraneliftInput
