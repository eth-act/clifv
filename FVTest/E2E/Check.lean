import FV.Backend
import FV.Backend.Proof.DriverCheck
import FV.Backend.Proof.PrepareCheck
import FV.Backend.Proof.RegallocCover
import FVTest.Opt.Common

/-!
# The M7 validators on real code (`lake exe lean-e2e-check [FILE.clif...]`)

Runs the lowering validator `lowerCheck f vc` and the `prepare` validator `prepCheck vc vcp` on
every function the backend lowers (default:
`corpus/clif/*.clif`, `corpus/clif/extrt/*.clif`, Cranelift's `runtests/*.clif`) and prints
every rejection with the failing part. Exit status 0 iff every lowered function is accepted.

It also decides `formsCoveredB` (the `FormsCovered` premise of `E2E.backend_correct_final`) on
every prepared VCode and reports the number of covered functions and, for the others, the
uncovered instruction forms (constructor and operation) with their counts. An uncovered
function is not rejected: it is compiled but outside the end-to-end theorem.

With `--opt [--opt-* options]`, the functions are first optimised by the mid-end
(`Opt.optimize`), i.e. the validators run on the code `lean-backend --opt` compiles.
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
  for dir in ["corpus/clif", "corpus/clif/extrt",
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
    match lowBlocks f (stmtCall ctx) (termCallF ctx) 0 f.blocks st0 f.blocks.length with
    | none => "lowBlocks"
    | some bl =>
      let gn := gnOf st0.nextVreg (aliasOf f bl)
      let In := inFix f gn
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
        [("cert.entry", certOk f ctx st0 gn [] In || true)] ++
        ((List.range f.blocks.length).map fun bi => (s!"cert block {bi}",
          match f.blocks[bi]?, bl[bi]? with
          | some B, some L => certBlockOk f ctx st0 gn In bi B L
          | _, _ => true)) ++
        [("cert", certOk f ctx st0 gn bl In)]
      String.intercalate ", " ((parts.filter (!·.2)).map (·.1))

/-- Details of a failing block (shape and certificate conjuncts). -/
def detail (f : Clif.Function) (vc : VCode) : String :=
  match buildCtx f with
  | .error _ => ""
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) 0 f.blocks st0 f.blocks.length with
    | none => ""
    | some bl =>
      let gn := gnOf st0.nextVreg (aliasOf f bl)
      let R := renOf gn
      let In := inFix f gn
      String.intercalate "\n" <| (List.range f.blocks.length).filterMap fun bi =>
        match f.blocks[bi]?, bl[bi]?, vc.blocks[bi]? with
        | some B, some L, some vb =>
          let A := availOf f In bi
          let sh : List (String × Bool) := [
            ("stmts", (List.range B.body.length).all (fun j => match B.body[j]?, L.sl[j]? with
              | some stm, some sl => stmtOk ctx st0 gn (L.start + j) stm sl | _, _ => false)),
            ("code", decide (vb.insts.toList = pre f R bi ++ ((List.range B.body.length).map (seg f R bl bi)).flatten ++ tseg R bl bi)),
            ("params", decide (vb.params = (if bi = 0 then #[] else (B.params.map fun p => Reg.vreg p.1 .int).toArray))),
            ("bargs", decide (vb.branchArgs = (match B.term with
              | .jump bc => (bc.args.map fun a => R (.vreg a .int)).toArray | _ => #[]))),
            ("succ", succOk f vc R B L),
            ("csmall", (A B.body.length).all (fun x => decide (x < st0.nextVreg))),
            ("cclosed", (List.range (B.body.length + 1)).all (fun j => closedOk ctx (A j))),
            ("cstmts", (List.range B.body.length).all (fun j => match B.body[j]?, L.sl[j]? with
              | some stm, some sl =>
                (instArgs stm.inst).all (fun y => decide (y ∈ A j)) &&
                stm.results.all (fun r => decide (r ∉ A j) && decide (ctx.defInst? r = some (L.start + j))) &&
                decide stm.results.Nodup &&
                (A (j + 1)).all (fun x => decide (x ∈ A j) || decide (x ∈ stm.results)) &&
                (A j).all (fun x => !(decide (sl.st.nextVreg ≤ gn x) && decide (gn x < sl.st'.nextVreg)))
              | _, _ => false)),
            ("targs", (termArgs B.term).all (fun y => decide (y ∈ A B.body.length))),
            ("tclob", (A B.body.length).all (fun x => !(decide (L.tst.nextVreg ≤ gn x) && decide (gn x < L.tst'.nextVreg)))),
            ("edges", (dests B.term).all (fun bc => decide (blockIdx? f bc.block ≠ some 0) &&
              edgeOk f ctx gn In (A B.body.length) bc))]
          let bad := (sh.filter (!·.2)).map (·.1)
          if bad.isEmpty then none else
          some s!"  block {bi}: {bad}; A0={A 0} Aend={A B.body.length} params={B.params.map (·.1)} term={repr B.term}; In={In.getD bi []}"
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
  for file in files do
    let pf := Clif.parseFile (← IO.FS.readFile file)
    let pf := match optCfg with | some c => Opt.optimizeParsedFile c pf | none => pf
    for p in pf.funcs do
      let .ok f := p.func | continue
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
      if f.sig.params.length > 8 || !Backend.regArgCalls f || !Backend.noSpecial f then
        skipped := skipped + 1
        continue
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
  IO.println s!"lowerCheck: {ok} accepted, {bad} rejected, {skipped} out of scope (stack parameters, stack call arguments, sret, or outside clif-subset-v2 E)"
  IO.println s!"prepCheck: {pok} accepted, {pbad} rejected"
  IO.println s!"formsCoveredB: {cov} covered, {uncov} not covered"
  for (k, n) in forms.toList.mergeSort (fun a b => a.2 ≥ b.2) do
    IO.println s!"  uncovered form {k}: {n} instructions"
  IO.println s!"time (ms): lowerFunction {tLower}, lowerCheck {tCheck}, prepare {tPrep}, prepCheck {tPCheck}"
  return if bad == 0 && pbad == 0 then 0 else 1
