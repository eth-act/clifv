import FV.Opt.MidValFold

/-!
# Store-to-load forwarding before the branch folds (#1119, `rewrite:blocks`, family A)

Cranelift's alias analysis replaces a load whose location holds a value it knows (the value a
dominating store wrote, or a dominating load read, with no writer in between: `LastStores`, one
region) by that value; its mid-end then folds a branch whose condition became a constant. The
fold prep (`foldPre`, `FV/Opt/MidValFold.lean`) folds only conditions with syntactic constants.
`fwdPre` forwards first, so that `foldPre` sees the constants.

* `fwdRun f` (untrusted): the walk of the checker's `f` side (`Opt.MidVal.checkBlock`: terms with
  the default normaliser, memory versions, facts at a location found in a dominating block) over
  `f` alone, in which a load whose location holds a fact is not kept: its result is the fact's
  value. It records the forwarded loads with the value of `f` holding the fact (`FwdSt.sub`: the
  stored value, or the result of the earlier load), and the pure statements whose term is an
  integer constant (`FwdSt.cst`).
* `fwdFn f fs`: `f` without the forwarded loads, their results renamed to the values holding
  them, and the pure statements with a constant term replaced by `iconst` of it.
* `fwdPre f`: `fwdFn f (fwdRun f)` when the walk succeeds and changes something; `f` otherwise.
* `fwdOk f`: the checker accepts `fwdPre f` against `f`: `checkCert f (fwdPre f) cert` for the
  certificate `emit f (fwdPre f)` gives (`emit` is untrusted; only `checkCert`'s verdict is
  used). Then `fwdPre f` simulates `f` (`Opt.MidVal.check_sound`: `FunSimMU f (fwdPre f)`), with
  the checker's memory facts as the invariant that justifies each forwarded load.

`checkCertC` (`FV/Opt/MidValCond.lean`) tries, after `foldPre f bs` and `foldPreK f bs`, the
same on `fwdPre f` when `fwdOk f`.
-/

namespace Opt.MidVal

open Clif

/-- What `fwdRun` records (module doc). -/
structure FwdSt where
  /-- Forwarded load result ↦ the value of `f` holding the location's value. -/
  sub : Std.HashMap ValueId ValueId := {}
  /-- Location ↦ (defining block, value of `f` holding it), in walk order. -/
  src : Std.HashMap Key (Array (Nat × ValueId)) := {}
  /-- Results of pure statements whose term is an integer constant. -/
  cst : Std.HashMap ValueId Val := {}
  deriving Inhabited

/-- One block of `fwdRun` (layout index `bi`), as `checkBlock` walks `f`'s side. -/
def fwdBlock (c : Ctx) (bi : Nat) (b : Block) (fs0 : FwdSt) : M FwdSt := do
  let mut fs := fs0
  for ((p, _), i) in b.params.zipIdx do
    let t ← intern (.param bi i)
    modify fun s => { s with envF := s.envF.insert p t }
  let mut ver := c.ver[bi]!
  for (st, k) in b.body.zipIdx do
    if st.inst == .nop then continue
    if pureK st.inst then
      bindPure c "f" st bi 0 true
      if let [r] := st.results then
        let s ← get
        match constOf s.tms (s.envF.getD r 0), st.inst with
        | _, .iconst .. => pure ()
        | some v, _ =>
          if v.ty.isInt && v.ty != .i128 then fs := { fs with cst := fs.cst.insert r v }
        | none, _ => pure ()
      continue
    let s' ← liftE (mapM' (← get).envF "f" st.inst)
    if writerK st.inst then ver := .at bi k
    match st.inst, keyOf ver s', st.results with
    | .load .., some (key, _), [r] =>
      match (fs.src.getD key #[]).find? (fun (d, _) => c.dom d bi) with
      | some (_, x) =>
        fs := { fs with sub := fs.sub.insert r x }
        let tx := (← get).envF.getD x 0
        modify fun s => { s with envF := s.envF.insert r tx }
      | none =>
        discard (bindRes true [r] bi k)
        fs := { fs with src := fs.src.insert key ((fs.src.getD key #[]).push (bi, r)) }
    | .store _ _ _ x _ _, some (key, _), rs =>
      discard (bindRes true rs bi k)
      let x' := fs.sub.getD x x
      fs := { fs with src := fs.src.insert key ((fs.src.getD key #[]).push (bi, x')) }
    | _, _, rs => discard (bindRes true rs bi k)
  return fs

/-- **The forwarding walk** (untrusted; module doc). -/
def fwdRun (f : Function) : Except Reject FwdSt := do
  let fi ← (wfCheck f).mapError (s!"wf:f {·}")
  let (pre, post, order) := domIntervals fi.cfg.idom
  let c : Ctx := { pre, post, ver := versions f fi.cfg, fty := fi.types.get?,
                   gty := fi.types.get? }
  let fbs := f.blocks.toArray
  let go : M FwdSt := do
    let mut fs : FwdSt := {}
    for bi in order do
      fs ← fwdBlock c bi fbs[bi]! fs
    return fs
  let (r, _) := (go.run).run { norm := Norm.stdD f, aty := atomTy f }
  r

/-- A statement of `fwdFn`: dropped if a forwarded load, `iconst` if its term is a constant,
else with its operands renamed. -/
def fwdStmt (fs : FwdSt) (st : Stmt) : Option Stmt :=
  match st.results with
  | [r] =>
    if fs.sub.contains r then none
    else match fs.cst.get? r with
      | some v => some ⟨[r], .iconst v.ty v.bits⟩
      | none => some { st with inst := mapOperands (fun x => fs.sub.getD x x) st.inst }
  | _ => some { st with inst := mapOperands (fun x => fs.sub.getD x x) st.inst }

/-- `f` with the forwarding of `fs` applied (module doc). -/
def fwdFn (f : Function) (fs : FwdSt) : Function :=
  { f with blocks := f.blocks.map fun b =>
      { b with body := b.body.filterMap (fwdStmt fs),
               term := mapTerm (fun x => fs.sub.getD x x) b.term } }

/-- **Store-to-load forwarding** (module doc): `f` with its forwarded loads removed and its
constant pure statements as `iconst`, or `f`. -/
def fwdPre (f : Function) : Function :=
  match fwdRun f with
  | .ok fs => if fs.sub.isEmpty && fs.cst.isEmpty then f else fwdFn f fs
  | .error _ => f

/-- **The checker accepts the forwarding** (module doc): `checkCert f (fwdPre f)` with the
certificate `emit` gives. -/
def fwdOk (f : Function) : Bool :=
  match emit f (fwdPre f) with
  | .ok cert => checkCert f (fwdPre f) cert
  | .error _ => false

end Opt.MidVal
