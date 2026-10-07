import FV.Backend
import FV.Backend.Proof.DriverCheck
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.PrepareCheck
import FV.Backend.Proof.RegallocCover
import FV.Backend.Proof.SpillArity
import FV.Backend.Proof.SpillAvail
import FV.Backend.Proof.RelaxReady
import FV.E2E.EmitSize
import FV.E2E.SizeDefs
import FV.E2E.EmitNear
import FV.E2E.EmitLabels
import FV.E2E.EmitEnc
import FV.Backend.Proof.IselEmitDefs
import FV.Opt.Legalize128Pass
import FVTest.Opt.Common

/-!
# The M7 validators on real code (`lake exe lean-e2e-check [FILE.clif...]`)

Runs the lowering validator `lowerCheck f vc` and the `prepare` validator `prepCheck vc vcp` on
every function the backend lowers (default:
`corpus/clif/*.clif`, `corpus/clif/extrt/*.clif`, the hand-written regression files
`corpus/clif-regress/*.clif`, Cranelift's `runtests/*.clif`) and prints
every rejection with the failing part. Exit status 0 iff every lowered function is accepted.

It also decides `formsCoveredB` (the `FormsCovered` premise of `E2E.backend_correct_final`) on
every prepared VCode and reports the number of covered functions and, for the others, the
uncovered instruction forms (constructor and operation) with their counts. An uncovered
function is not rejected: it is compiled but outside the end-to-end theorem.

It runs the checker on the spill allocation (`spillAlloc`, the fallback when `checkAlloc`
rejects regalloc2's allocation or `lowerRFunc` cannot lower it) of every prepared VCode — the
conclusion of the hypothesis `E2E.SpillAccepted` of `E2E.backend_correct_final_alloc` — and
reports how many are accepted (a rejection fails the run) and how many `lowerRFunc` lowers (a
rejection contradicts `E2E.lowerRFunc_spillAlloc` and fails the run); and `Spill.killFreeB` on
every prepared VCode (the conclusion of the hypothesis `E2E.SpillKillFree`, which gives
`E2E.SpillAvailable`; a rejection fails the run).

It reports how many in-scope functions satisfy the input conditions of `lowerCheck_complete`
(`dominatedB`, `lowerScopeB`: on these the lowering validator is a theorem, `Compiled.of_lower`),
and names the others.

Every file is first legalised (`Opt.Legalize128.parsedFile128`, as `lean-backend` does): a
legalised `i128` function the validator `Opt.Legal.check` accepts is in scope (covered by
`E2E.backend_correct_legal`) and checked like any other; the rejected ones are out of scope
and counted separately.

With `--opt [--opt-* options]`, the functions are first optimised by the mid-end
(`Opt.optimize`), i.e. the validators run on the code `lean-backend --opt` compiles; the
legalised functions are then out of scope (no theorem composes the legalisation with the
mid-end).
-/

open Backend Backend.Proof.Driver

/-- An instruction's `repr` on one line. -/
def oneLine (i : MInst) : String :=
  String.intercalate " " (((toString (repr i)).splitOn "\n").map String.trim)

/-- The form of an instruction: constructor and first argument of its `repr`. -/
def formKey (i : MInst) : String :=
  let ws := ((oneLine i).splitOn " ").filter (· ≠ "")
  String.intercalate " " (ws.take 2)

/-- The straight-line instructions of `vc` that are neither control forms nor `FormOk`. -/
def uncovered (vc : VCode) : List MInst :=
  vc.blocks.toList.flatMap fun vb =>
    vb.insts.toList.filter fun i => !(i.isCtl || Backend.Proof.FormOk default i)

def defaultFiles : IO (List String) := do
  let mut out : Array String := #[]
  for dir in ["corpus/clif", "corpus/clif/extrt", "corpus/clif-regress",
              "third_party/wasmtime/cranelift/filetests/filetests/runtests"] do
    let entries ← System.FilePath.readDir dir
    out := out ++ ((entries.filter (·.path.extension == some "clif")).map (·.path.toString)
      |>.qsort (· < ·))
  return out.toList

/-- Which part of `lowerCheck` fails. -/
def diagnose (f : Clif.Function) (vc : VCode) : String :=
  match buildCtx f with
  | .error e => s!"buildCtx: {e}"
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length with
    | none => "lowBlocks"
    | some bl =>
      let gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))
      let In := inFix f ctx gn
      let parts : List (String × Bool) := [
        ("ctxOk", ctxOk f ctx),
        ("valsBelow", decide (ctx.valReg.size ≤ st0.nextVreg)),
        ("params", f.blocks.all (fun B => B.params.all fun p => decide (gn p.1 = p.1))),
        ("len", decide (bl.length = f.blocks.length)),
        ("size", decide (f.blocks.length ≤ vc.blocks.size)),
        ("labels", (List.range vc.blocks.size).all (fun l => match vc.blocks[l]? with
          | some vb => decide (vb.label = l) | none => true))] ++
        ((List.range f.blocks.length).map fun bi => (s!"block {bi}",
          match f.blocks[bi]?, bl[bi]? with
          | some B, some L => blockOk f vc ctx st0 (renOf gn) gn bl bi B L
          | _, _ => false)) ++
        ((List.range f.blocks.length).map fun bi => (s!"cert block {bi}",
          match f.blocks[bi]?, bl[bi]? with
          | some B, some L => certBlockOk f ctx st0 gn f.blocks.toArray bl.toArray In bi B L
          | _, _ => true)) ++
        [("cert", certOk f ctx st0 gn bl In)]
      String.intercalate ", " ((parts.filter (!·.2)).map (·.1))

/-- Details of a failing block (shape and certificate conjuncts). -/
def detail (f : Clif.Function) (vc : VCode) : String :=
  match buildCtx f with
  | .error _ => ""
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length with
    | none => ""
    | some bl =>
      let gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))
      let R := renOf gn
      let In := inFix f ctx gn
      String.intercalate "\n" <| (List.range f.blocks.length).filterMap fun bi =>
        match f.blocks[bi]?, bl[bi]?, vc.blocks[bi]? with
        | some B, some L, some vb =>
          let a := Avail.of B L In bi
          let n := B.body.length
          let A (j : Nat) : List Clif.ValueId := (a.ent ++ B.body.flatMap (·.results)).filter (a.mem ctx j)
          let sh : List (String × Bool) := [
            ("stmts", (List.range B.body.length).all (fun j => match B.body[j]?, L.sl[j]? with
              | some stm, some sl => stmtOk ctx st0 gn (L.start + j) stm sl | _, _ => false)),
            ("code", decide (vb.insts.toList = pre f R bi ++ ((List.range B.body.length).map (seg f R bl bi)).flatten ++ tseg R bl bi)),
            ("params", decide (vb.params = (if bi = 0 then #[] else (B.params.map fun p => Reg.vreg p.1 .int).toArray))),
            ("bargs", decide (vb.branchArgs = (match B.term with
              | .jump bc => (bc.args.map fun a => R (.vreg a .int)).toArray | _ => #[]))),
            ("succ", succOk f vc R B L),
            ("cdefs", (List.range n).all fun k => match B.body[k]? with
              | some stm => stm.results.all fun r => decide (ctx.defInst? r = some (L.start + k))
              | none => true),
            ("csmall", (A n).all (fun x => decide (x < st0.nextVreg))),
            ("cclosed", (A n).all (fun x => (defArgs ctx x).all fun y =>
              a.mem ctx n y && decide (a.first ctx y ≤ a.first ctx x))),
            ("cargs", (List.range n).all (fun j => match B.body[j]? with
              | some stm => (instArgs stm.inst).all (a.mem ctx j) | none => true)),
            ("cclob", (List.range n).all (fun j => match L.sl[j]? with
              | some sl => (A j).all fun x => !(decide (sl.st.nextVreg ≤ gn x) && decide (gn x < sl.st'.nextVreg))
              | none => true)),
            ("targs", (termArgs (abiTerm f B.term)).all (a.mem ctx n)),
            ("tclob", (A n).all (fun x => !(decide (L.tst.nextVreg ≤ gn x) && decide (gn x < L.tst'.nextVreg)))),
            ("edges", (edgeIds B.term).all (fun b => decide (blockIdx? f b ≠ some 0) &&
              edgeOk f ctx gn f.blocks.toArray bl.toArray In a n b))]
          let bad := (sh.filter (!·.2)).map (·.1)
          if bad.isEmpty then none else
          some s!"  block {bi}: {bad}; A0={A 0} Aend={A n} params={B.params.map (·.1)} term={repr B.term}; In={In.getD bi []}"
        | _, _, _ => none

def main (args : List String) : IO UInt32 := do
  let (optCfg, args) ← match Opt.parseOptArgs args with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  let files ← if args.isEmpty then defaultFiles else pure args
  let mut ok := 0
  let mut bad := 0
  let mut skipped := 0
  let mut pok := 0
  let mut tLower := 0
  let mut tCheck := 0
  let mut tPrep := 0
  let mut tPCheck := 0
  let mut pbad := 0
  let mut cov := 0
  let mut uncov := 0
  let mut forms : Std.HashMap String Nat := {}
  let mut legal := 0
  let mut legalOut := 0
  let mut dom := 0
  let mut scope := 0
  let mut both := 0
  let mut spillOk := 0
  let mut spillBad := 0
  let mut kfOk := 0
  let mut kfBad := 0
  let mut kfKilled := 0
  let mut spillLow := 0
  let mut spillRej := 0
  let mut tSpill := 0
  let mut arity := 0
  let mut extW := 0
  let mut szIn := 0
  let mut szInMax := 0
  let mut emitOk := 0
  let mut emitBad := 0
  let mut readyOk := 0
  let mut readyBad := 0
  let mut emitMax := 0
  let mut sizeOk := 0
  let mut sizeBad := 0
  let mut sizeMax := 0
  let mut naOk := 0
  let mut naBad := 0
  let mut tgtOk := 0
  let mut tgtBad := 0
  let mut immOk := 0
  let mut immBad := 0
  for file in files do
    let lg := Opt.Legalize128.parsedFile128 (Clif.parseFile (← IO.FS.readFile file))
    let pf := match optCfg with | some c => Opt.optimizeParsedFile c lg.file | none => lg.file
    for p in pf.funcs do
      let .ok f := p.func | continue
      -- legalised functions outside `E2E.backend_correct_legal`
      if (lg.unverified.lookup p.name).isSome ||
          (optCfg.isSome && lg.accepted.contains p.name) then
        legalOut := legalOut + 1
        continue
      -- `backend_correct_opt_proven` covers functions without `try_call`/`try_call_indirect`
      -- and `call_indirect` only
      if optCfg.isSome && Opt.hasCallIndirect f then
        skipped := skipped + 1
        continue
      let t0 ← IO.monoMsNow
      let .ok vc ← IO.lazyPure (fun _ => lowerFunction f) | continue
      let t1 ← IO.monoMsNow
      -- the end-to-end theorem covers `E2E.InSubset` functions only; functions outside
      -- clif-subset-v2 E (i128, floats, vectors — which `lowerFunction` rejects anyway —
      -- and, since the atomics/bmask support, the atomic/bmask/fence forms, which compile
      -- but are flagged unverified) are out of scope like the ABI-skipped ones
      if !Compile.functionE f then
        skipped := skipped + 1
        continue
      if !Backend.abiSigs f || !Backend.indSigsOk f then
        skipped := skipped + 1
        continue
      if lg.accepted.contains p.name then legal := legal + 1
      let d := dominatedB f
      let sc := lowerScopeB f
      if d then dom := dom + 1
      if sc then scope := scope + 1
      if d && sc then both := both + 1
      else IO.println s!"{file}: %{f.name}: outside lowerCheck_complete's conditions (dominatedB {d}, lowerScopeB {sc})"
      if Backend.Proof.Spill.arityOkB f then arity := arity + 1
      else IO.println s!"{file}: %{f.name}: arityOkB fails (a branch argument count differs from its target's parameter count)"
      if Backend.Proof.Driver.extendsWidenB f then extW := extW + 1
      else IO.println s!"{file}: %{f.name}: extendsWidenB fails (a uextend/sextend that does not widen)"
      let bIn := E2E.sizeBoundIn f
      if bIn > szInMax then szInMax := bIn
      if E2E.sizeOkB f then szIn := szIn + 1
      else IO.println s!"{file}: %{f.name}: sizeOkB fails ({bIn} words, need < 2^24): out of scope"
      let r ← IO.lazyPure (fun _ => lowerCheck f vc)
      let t2 ← IO.monoMsNow
      if t2 - t0 > 2000 then IO.println s!"{file}: %{f.name}: lowerFunction {t1 - t0} ms, lowerCheck {t2 - t1} ms"
      tLower := tLower + (t1 - t0)
      tCheck := tCheck + (t2 - t1)
      let t3 ← IO.monoMsNow
      let pr ← IO.lazyPure (fun _ => prepare vc)
      let t4 ← IO.monoMsNow
      tPrep := tPrep + (t4 - t3)
      match pr with
      | .ok vcp =>
        if Backend.Proof.formsCoveredB default vcp then cov := cov + 1
        else
          uncov := uncov + 1
          let us := uncovered vcp
          IO.println s!"{file}: %{f.name}: not covered: {us.map oneLine}"
          for i in us do
            forms := forms.insert (formKey i) (forms.getD (formKey i) 0 + 1)
        -- the spill fallback (`spillAlloc`, `E2E.SpillAccepted`) and its lowering
        let ts0 ← IO.monoMsNow
        let rf := spillAlloc vcp
        -- the size bound (`E2E.spillSizeOkB`, input condition of `backend_correct_final_total_emit`)
        let w := E2E.rfWords vcp rf
        if w > sizeMax then sizeMax := w
        if w < 2 ^ 24 then sizeOk := sizeOk + 1
        else
          sizeBad := sizeBad + 1
          IO.println s!"{file}: %{f.name}: spillSizeOkB fails ({w} words, need < 2^24): out of scope"
        if Backend.VCode.noAlwaysB vcp then naOk := naOk + 1
        else
          naBad := naBad + 1
          IO.println s!"{file}: %{f.name}: noAlwaysB fails (a condBr/trapIf with an al/nv condition)"
        if E2E.branchTargetsOkB vcp then tgtOk := tgtOk + 1
        else
          tgtBad := tgtBad + 1
          IO.println s!"{file}: %{f.name}: branchTargetsOkB fails (a branch target is not a block label)"
        if E2E.immsOkB vcp then immOk := immOk + 1
        else
          immBad := immBad + 1
          IO.println s!"{file}: %{f.name}: immsOkB fails (an immediate outside the encoder's range)"
        match ← IO.lazyPure (fun _ => checkAlloc vcp rf) with
        | .ok () => spillOk := spillOk + 1
        | .error e =>
          spillBad := spillBad + 1
          IO.println s!"{file}: %{f.name}: checkAlloc rejects the spill allocation: {e}"
        match ← IO.lazyPure (fun _ => lowerRFunc vcp rf) with
        | .ok af =>
          spillLow := spillLow + 1
          match ← IO.lazyPure (fun _ => emitFunc 0 af) with
          | .ok fa =>
            emitOk := emitOk + 1
            if fa.size > emitMax then emitMax := fa.size
            if ← IO.lazyPure (fun _ => fa.layoutReadyB) then readyOk := readyOk + 1
            else
              readyBad := readyBad + 1
              IO.println s!"{file}: %{f.name}: layoutReadyB fails on the spill allocation's code"
          | .error e =>
            emitBad := emitBad + 1
            IO.println s!"{file}: %{f.name}: emitPre rejects the spill allocation's code: {e}"
        | .error e =>
          spillRej := spillRej + 1
          IO.println s!"{file}: %{f.name}: lowerRFunc rejects the spill allocation: {e}"
        -- the syntactic availability facts (`Spill.killFreeB`, `E2E.SpillKillFree`)
        if !(Backend.Proof.Spill.killedOf vcp).isEmpty then kfKilled := kfKilled + 1
        if ← IO.lazyPure (fun _ => Backend.Proof.Spill.killFreeB vcp) then kfOk := kfOk + 1
        else
          kfBad := kfBad + 1
          IO.println s!"{file}: %{f.name}: killFreeB rejects (a killed vreg is read, or a killed branch argument is not stored on entry)"
        tSpill := tSpill + ((← IO.monoMsNow) - ts0)
        let t5 ← IO.monoMsNow
        let pc ← IO.lazyPure (fun _ => prepCheck vc vcp)
        let t6 ← IO.monoMsNow
        tPCheck := tPCheck + (t6 - t5)
        if pc then pok := pok + 1
        else
          pbad := pbad + 1
          IO.println s!"{file}: %{f.name}: prepCheck rejects"
      | .error _ => pure ()
      if r then ok := ok + 1
      else
        bad := bad + 1
        IO.println s!"{file}: %{f.name}: lowerCheck rejects ({diagnose f vc})"
        IO.println (detail f vc)
  IO.println s!"lowerCheck: {ok} accepted, {bad} rejected, {skipped} out of scope (stack-passed arguments of an indirect call, special-purpose parameters other than one sret, outside clif-subset-v2 E, or a try_call/call_indirect under --opt)"
  IO.println s!"legalised i128 functions: {legal} in scope (Opt.Legal.check accepts; counted above), {legalOut} out of scope (validator rejects, extern named like a function of the file, a call_indirect whose file's externs do not extend, or --opt)"
  IO.println s!"prepCheck: {pok} accepted, {pbad} rejected"
  IO.println s!"lowerCheck_complete conditions: dominatedB {dom}, lowerScopeB {scope}, both {both} (of {ok + bad} checked)"
  IO.println s!"arityOkB {arity} of {ok + bad}"
  IO.println s!"extendsWidenB (IselEmitDefs, every uextend/sextend widens; input condition of backend_correct_final_total_emit_in) {extW} of {ok + bad}"
  IO.println s!"sizeOkB (SizeDefs, input-side size bound; input condition of backend_correct_final_total_emit_input) {szIn} of {ok + bad}; largest bound {szInMax} words (limit 2^24)"
  IO.println s!"formsCoveredB: {cov} covered, {uncov} not covered"
  for (k, n) in forms.toList.mergeSort (fun a b => a.2 ≥ b.2) do
    IO.println s!"  uncovered form {k}: {n} instructions"
  IO.println s!"spill fallback (SpillAccepted): checkAlloc accepts {spillOk}, rejects {spillBad}"
  IO.println s!"spill lowering (lowerRFunc_spillAlloc): lowerRFunc lowers {spillLow}, rejects {spillRej}"
  IO.println s!"spill emission: emitPre succeeds {emitOk}, rejects {emitBad}; layoutReadyB {readyOk} pass, {readyBad} fail; largest function {emitMax} bytes"
  IO.println s!"spillSizeOkB (EmitSize, size input condition): {sizeOk} pass, {sizeBad} fail; largest bound {sizeMax} words (limit 2^24)"
  IO.println s!"noAlwaysB (EmitNear, no al/nv branch condition): {naOk} pass, {naBad} fail"
  IO.println s!"branchTargetsOkB (EmitLabels, every branch target a block label): {tgtOk} pass, {tgtBad} fail"
  IO.println s!"immsOkB (EmitEnc, encodable immediates): {immOk} pass, {immBad} fail"
  IO.println s!"killFreeB (SpillKillFree, gives SpillAvailable): {kfOk} accepted ({kfKilled} with killed vregs: scratch or terminator defs), {kfBad} rejected"
  IO.println s!"time (ms): lowerFunction {tLower}, lowerCheck {tCheck}, prepare {tPrep}, prepCheck {tPCheck}, spill fallback {tSpill}"
  return if bad == 0 && pbad == 0 && spillBad == 0 && kfBad == 0 && spillRej == 0 && emitBad == 0 && readyBad == 0 && naBad == 0 && tgtBad == 0 && immBad == 0 then 0 else 1
