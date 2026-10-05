import FV.Backend.Proof.LowerSpec

/-!
# `lowerFunction`, restated with named loop bodies

`lowerFunction` (`FV/Backend/Isel.lean`) is one `do` program with nested `for` loops. This file
names its loop bodies (`resBody`, `stmtBody`, `entryBody`, `destBody`, `tryBody`, `blockBody`) and
proves, by `rfl`, that `lowerFunction` is the program built from them (`lowerFunction_eq`), so the
loop simulation (`LowerLoopRun.lean`) can state facts about each body separately.
-/

namespace Backend.Proof.Driver

open Backend

/-- `lowerFunction`'s `blockIdx`. -/
def blockIdxE (f : Clif.Function) (b : Nat) : Except String Nat :=
  match f.blocks.findIdx? (·.id == b) with
  | some i => pure i
  | none => throw s!"unknown block{b}"

/-- The body of the loop over a statement's results (alias or `mov`). -/
def resBody (ctx : Ctx) (x : Nat × List Reg) (s : DState × Array MInst) :
    Except String (ForInStep (DState × Array MInst)) :=
  match x with
  | (r, rs) =>
    match ctx.valueReg? r with
    | some vr =>
      match rs with
      | [.vreg o _] =>
        match vr with
        | .vreg n _ =>
          let alias := if s.1.alias.size ≤ n then
              s.1.alias ++ Array.replicate (n + 1 - s.1.alias.size) none
            else s.1.alias
          pure (.yield ({ s.1 with alias := alias.set! n (some o) }, s.2))
        | _ => throw "value register is not virtual"
      | [out] => pure (.yield (s.1, s.2.push (.mov .size64 vr out)))
      | _ => throw "multi-register result"
    | _ => throw s!"unknown value v{r}"

/-- The body of the statement loop. -/
def stmtBody (ctx : Ctx) (i : Nat) (s : DState × Array MInst) :
    Except String (ForInStep (DState × Array MInst)) := do
  let info := ctx.insts[i]!
  let (out, st, n) ← runTerm ctx "lower" [.inst i] { s.1.st with emitted := #[] }
  match out with
  | some (.regsVec rss) =>
    if (rss.length != info.results.length && !info.results.isEmpty) = true then
      throw "lowering produced a wrong number of results"
    else
      let q ← forIn (info.results.zip rss) (s.1, (#[] : Array MInst)) (resBody ctx)
      pure (.yield ({ q.1 with st := { st with emitted := #[] }, rules := q.1.rules ++ n.toArray },
        s.2 ++ st.emitted ++ q.2))
  | _ => throw s!"no lowering rule for {(repr info.clif).pretty.take 80}"

/-- The body of the entry block's argument-setup loop. -/
def entryBody (ctx : Ctx) (x : ((Clif.ValueId × Clif.Ty) × ArgLoc) × Nat)
    (s : Array MInst × Array (Reg × Reg)) :
    Except String (ForInStep (Array MInst × Array (Reg × Reg))) :=
  match x with
  | (((v, _), loc), bytes) =>
    match ctx.valueReg? v with
    | some r =>
      match loc with
      | .reg p => pure (.yield (s.1, s.2.push (r, p)))
      | .stack off =>
        pure (.yield (s.1.push (.load (loadOpOfBytes bytes) r (.fpOffset (16 + off)) trustedFlags), s.2))
    | _ => throw s!"unknown value v{v}"

/-- The state after creating an edge block jumping to `tl` with arguments `args`. -/
def edgeD (d : DState) (tl : Label) (args : Array Reg) : DState :=
  { d with nextLabel := d.nextLabel + 1,
           edges := d.edges.push { label := d.nextLabel, insts := #[MInst.jump tl], branchArgs := args } }

/-- The body of the loop over a branch's successors. -/
def destBody (f : Clif.Function) (ctx : Ctx) (bc : Clif.BlockCall) (s : DState × Array Label) :
    Except String (ForInStep (DState × Array Label)) := do
  let tl ← blockIdxE f bc.block
  if bc.args.isEmpty = true then pure (.yield (s.1, s.2.push tl))
  else
    let args ← blockArgRegs ctx f bc
    pure (.yield (edgeD s.1 tl args, s.2.push s.1.nextLabel))

/-- A `try_call` successor argument. -/
def tryArgE (ctx : Ctx) (rets pays : Array Reg) (nh k : Nat) : Clif.TryArg → Except String Reg
  | .val v => match ctx.valueReg? v with
    | some r => pure r
    | none => throw s!"unknown value v{v}"
  | .ret i => if k < nh then throw s!"try_call: ret{i} on an exception edge"
    else match rets[i]? with
      | some r => pure r
      | none => throw s!"try_call: ret{i} out of range"
  | .exn i => if k == nh then throw s!"try_call: exn{i} on the normal-return edge"
    else match pays[i]? with
      | some r => pure r
      | none => throw s!"try_call: exn{i} out of range"

/-- The body of the loop over a `try_call`'s successors. -/
def tryBody (f : Clif.Function) (ctx : Ctx) (rets pays : Array Reg) (nh : Nat)
    (x : Clif.TryDest × Nat) (s : DState × Array Label) :
    Except String (ForInStep (DState × Array Label)) :=
  match x with
  | (td, k) => do
    let tl ← blockIdxE f td.block
    match f.block? td.block with
    | some tb =>
      if (tb.params.length != td.args.length) = true then throw s!"block{td.block}: argument count"
      else
        let args ← td.args.toArray.mapM (tryArgE ctx rets pays nh k)
        pure (.yield (edgeD s.1 tl args, s.2.push s.1.nextLabel))
    | _ => throw s!"unknown block{td.block}"

/-- The successors of a terminator (`lowerFunction`'s `dests`). -/
def destsOf (t : Clif.Terminator) : List Clif.BlockCall :=
  match t with
  | .jump bc => [bc]
  | .brif _ t e => [t, e]
  | .brTable _ dflt tbl => dflt :: tbl
  | _ => []

/-- The terminator call's root term and arguments. -/
def termArgsOf (t : Clif.Terminator) (ti : Nat) (targets : Array Label) : String × List V :=
  match t with
  | .ret _ | .trap _ => ("lower", [.inst ti])
  | _ => ("lower_branch", [.inst ti, .labels targets.toList])

/-- The state after a block `vb` whose terminator's lowering ended in `st` (rules `n`). -/
def blockD (d : DState) (st : LState) (n : List Isle.RuleId) (vb : VBlock) : DState :=
  { d with st := { st with emitted := #[] }, rules := d.rules ++ n.toArray, blocks := d.blocks.push vb }

/-- The block's parameters and the block, after the terminator's lowering (`st`, rules `n`). -/
def paramsPart (ctx : Ctx) (b : Clif.Block) (bi : Nat) (code : Array MInst) (d : DState)
    (st : LState) (n : List Isle.RuleId) (jumpArgs : Array Reg) (emitted : Array MInst) :
    Except String (ForInStep DState) :=
  if (bi == 0) = true then
    pure (.yield (blockD d st n { label := bi, insts := code ++ emitted, params := #[],
                                  branchArgs := jumpArgs }))
  else do
    let params ← b.params.toArray.mapM fun (v, _) => match ctx.valueReg? v with
      | some r => pure r
      | none => throw s!"unknown value v{v}"
    pure (.yield (blockD d st n { label := bi, insts := code ++ emitted, params,
                                  branchArgs := jumpArgs }))

/-- The end of a block: the terminator's lowering, the block's parameters, the block. -/
def finishBlock (ctx : Ctx) (b : Clif.Block) (bi ti : Nat) (code : Array MInst)
    (d : DState) (ctx' : Ctx) (targets : Array Label) (jumpArgs : Array Reg)
    (tryInfo : Option TryInfo) : Except String (ForInStep DState) :=
  match termArgsOf b.term ti targets with
  | (term, args) => do
    let (out, st, n) ← runTerm ctx' term args { d.st with emitted := #[] }
    if out.isNone = true then
      throw s!"no lowering rule for terminator {(repr b.term).pretty.take 80}"
    else
      match tryInfo with
      | none => paramsPart ctx b bi code d st n jumpArgs st.emitted
      | some t => match st.emitted.back? with
        | some (.call c) => paramsPart ctx b bi code d st n jumpArgs (st.emitted.pop.push (.tryCall c t))
        | _ => throw "try_call: the lowering does not end in a call"

/-- A `try_call` terminator: return/payload vregs, edge blocks, then `finishBlock`. -/
def tryTerm (f : Clif.Function) (ctx : Ctx) (b : Clif.Block) (bi ti : Nat) (code : Array MInst)
    (d : DState) (ctx' : Ctx) (et : Clif.ExnTable) : Except String (ForInStep DState) := do
  let (sig, items) ← exnTableOpnd f et
  match tryRegsOf sig d.st with
  | some ((retsL, paysL), st) =>
    if (sig.returns.any fun x => x.ty == Clif.Ty.i128) = true then throw "try_call returning i128"
    else
      let s ← forIn et.dests.zipIdx ({ d with st }, (#[] : Array Label))
        (tryBody f ctx retsL.toArray paysL.toArray et.handlers.length)
      match tryInfoOf sig items s.2.toList with
      | some t =>
        finishBlock ctx b bi ti code s.1 { ctx' with tryRegs := (retsL.toArray.toList, paysL.toArray.toList) }
          s.2 #[] (some t)
      | none => throw "try_call: successor count"
  | _ => throw "try_call: more than 8 return values"

/-- A `return` of an `sret` signature without the struct pointer (`lowerFunction` rejects it). -/
def sretBad (f : Clif.Function) (t : Clif.Terminator) : Bool :=
  (match t with | .ret _ => true | _ => false) && (sretRet f).isEmpty && sigRets f.sig != f.sig.returns

/-- The terminator part of a block's lowering (`code`: the code so far). -/
def termPart (f : Clif.Function) (ctx : Ctx) (b : Clif.Block) (bi stop : Nat) (code : Array MInst)
    (d : DState) (data : V) : Except String (ForInStep DState) :=
  if sretBad f b.term = true then
    throw "sret parameter is not an entry-block parameter"
  else
    match b.term with
    | .jump bc => do
      let jumpArgs ← blockArgRegs ctx f bc
      let tl ← blockIdxE f bc.block
      finishBlock ctx b bi (stop - 1) code d (termCtx ctx (stop - 1) data) ((#[] : Array Label).push tl)
        jumpArgs none
    | .tryCall _ _ et => tryTerm f ctx b bi (stop - 1) code d (termCtx ctx (stop - 1) data) et
    | .tryCallIndirect _ _ et => tryTerm f ctx b bi (stop - 1) code d (termCtx ctx (stop - 1) data) et
    | _ => do
      let s ← forIn (destsOf b.term) (d, (#[] : Array Label)) (destBody f ctx)
      finishBlock ctx b bi (stop - 1) code s.1 (termCtx ctx (stop - 1) data) s.2 #[] none

/-- The block part after the argument setup: the statements, then the terminator. -/
def bodyPart (f : Clif.Function) (ctx : Ctx) (b : Clif.Block) (bi start stop : Nat)
    (d : DState) (code : Array MInst) : Except String (ForInStep DState) := do
  let s ← forIn [start:stop - 1] (d, code) (stmtBody ctx)
  match b.term with
  | .tryCall .. => do
    let data ← tryCallData f b.term
    termPart f ctx b bi stop s.2 s.1 data
  | .tryCallIndirect .. => do
    let data ← tryCallData f b.term
    termPart f ctx b bi stop s.2 s.1 data
  | _ => do
    let data ← termData (abiTerm f b.term)
    termPart f ctx b bi stop s.2 s.1 data

/-- The body of the block loop. -/
def blockBody (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (paramBytes : List Nat)
    (x : Clif.Block × Nat) (d : DState) : Except String (ForInStep DState) :=
  match x with
  | (b, bi) =>
    match ranges[bi]! with
    | (start, stop) =>
      if (bi == 0) = true then do
        let (locs, _) ← sigArgLocs f.sig
        let s ← forIn ((b.params.zip locs).zip paramBytes) ((#[] : Array MInst), (#[] : Array (Reg × Reg)))
          (entryBody ctx)
        bodyPart f ctx b bi start stop d (#[MInst.args s.2.toList] ++ s.1)
      else bodyPart f ctx b bi start stop d #[]

/-- The VCode of the final loop state. -/
def finishVC (f : Clif.Function) (d : DState) (slotBytes : Nat) : VCode :=
  let R := lowerFunction.resolve d.alias (d.alias.size + 1)
  { name := f.name, blocks := (d.blocks ++ d.edges).map fun vb =>
      { vb with insts := vb.insts.map (MInst.mapRegs R), branchArgs := vb.branchArgs.map R },
    classes := d.st.classes, slotBytes, outgoing := d.st.outgoing, rulesFired := d.rules }

/-- `lowerFunction`, restated. -/
def lowerFunction' (f : Clif.Function) : Except String VCode :=
  if (!aapcsConv f.sig.callConv) = true then throw s!"calling convention {repr f.sig.callConv}"
  else do
    let paramBytes ← sigParamBytes f.sig
    if (f.sig.returns.any (·.ty == .i128)) = true then throw "i128 return value"
    else if (f.sig.params.any (·.purpose == .sret) && !f.sig.returns.isEmpty) = true then
      throw "sret parameter together with return values (Cranelift rejects this)"
    else if (retRegs (sigRets f.sig).length).isNone = true then throw "more than 8 return values"
    else do
      let (ctx, ranges, st0) ← buildCtx f
      let d ← forIn f.blocks.zipIdx ({ st := st0, alias := #[], nextLabel := f.blocks.length } : DState)
        (blockBody f ctx ranges paramBytes)
      match slotLayout f.slots with
      | (_, slotBytes) => pure (finishVC f d slotBytes)

set_option maxRecDepth 100000 in
/-- `lowerFunction` is `lowerFunction'` (definitionally). -/
theorem lowerFunction_eq (f : Clif.Function) : lowerFunction f = lowerFunction' f := rfl

end Backend.Proof.Driver
